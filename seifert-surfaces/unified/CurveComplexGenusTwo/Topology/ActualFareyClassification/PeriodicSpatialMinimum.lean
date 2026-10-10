import CurveComplexGenusTwo.Topology.ActualFareyClassification.InnermostFiberBigon
import CurveComplexGenusTwo.Topology.ActualFareyClassification.PeriodicFiberEventsLocallyFinite

open Set Topology Schoenflies

/-- Spatial contacts, rather than parameter contacts, permit comparison across
all translated copies of the lifted line. -/
theorem finite_fiber_select_minimum_spatial_contacts
    (G : ℝ → Plane) (c : ℝ) (E : Set Plane)
    (hfinite : {t : ℝ | G t 0=c}.Finite)
    (x y : ℝ) (hxy : x < y) (hx : G x 0=c) (hy : G y 0=c) :
    ∃ r s : ℝ, r < s ∧ G r 0=c ∧ G s 0=c ∧
      (∀ t ∈ Ioo r s, G t 0 ≠ c) ∧
      ∀ a b : ℝ, a < b → G a 0=c → G b 0=c →
        (∀ t ∈ Ioo a b, G t 0 ≠ c) →
        (E ∩ segment ℝ (G r) (G s)).ncard ≤
          (E ∩ segment ℝ (G a) (G b)).ncard := by
  classical
  let count (r s : ℝ) := (E ∩ segment ℝ (G r) (G s)).ncard
  let Q : ℕ → Prop := fun n => ∃ r s : ℝ,
    r < s ∧ G r 0=c ∧ G s 0=c ∧ (∀ t ∈ Ioo r s, G t 0 ≠ c) ∧ count r s=n
  have hex : ∃ n, Q n := by
    obtain ⟨r,s,hrs,hr,hs,hno⟩ := finite_fiber_select_consecutive_hits G c hfinite x y hxy hx hy
    exact ⟨count r s,r,s,hrs,hr,hs,hno,rfl⟩
  obtain ⟨r,s,hrs,hr,hs,hno,hn⟩ := Nat.find_spec hex
  refine ⟨r,s,hrs,hr,hs,hno,?_⟩
  intro a b hab ha hb havoid
  change count r s ≤ count a b
  rw [hn]
  exact Nat.find_min' hex ⟨a,b,hab,ha,hb,havoid,rfl⟩

/-- An actual proper subsegment loses a contact whenever its endpoints do not
reproduce the old corners. No assumption of strict cardinal reduction occurs. -/
theorem spatial_fiber_contacts_strict_subsegment
    (E : Set Plane) (p q u v : Plane)
    (hfinite : (E ∩ segment ℝ p q).Finite)
    (hp : p ∈ E) (hq : q ∈ E) (hpq : p ≠ q)
    (hvertical : p 0=q 0)
    (hu : u ∈ segment ℝ p q) (hv : v ∈ segment ℝ p q)
    (hnot : ¬ (u=p ∧ v=q)) (hnot' : ¬ (u=q ∧ v=p)) :
    (E ∩ segment ℝ u v).ncard < (E ∩ segment ℝ p q).ncard := by
  have hsub : E ∩ segment ℝ u v ⊆ E ∩ segment ℝ p q := by
    intro z hz
    exact ⟨hz.1,(convex_segment (𝕜:=ℝ) p q).segment_subset hu hv hz.2⟩
  have hn : ¬ (p ∈ segment ℝ u v ∧ q ∈ segment ℝ u v) := by
    rintro ⟨hpp,hqq⟩
    have ha := vertical_segment_endpoint_extreme p q u v hvertical hu hv hpp
    have hb := vertical_segment_endpoint_extreme q p u v hvertical.symm
      (by rwa [segment_symm]) (by rwa [segment_symm]) hqq
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact hpq (ha.symm.trans hb)
    · exact hnot ⟨ha,hb⟩
    · exact hnot' ⟨hb,ha⟩
    · exact hpq (ha.symm.trans hb)
  apply ncard_lt_ncard _ hfinite
  apply ssubset_iff_subset_ne.mpr
  refine ⟨hsub,?_⟩
  intro he
  apply hn
  have hpp : p ∈ E ∩ segment ℝ p q := ⟨hp,left_mem_segment ℝ _ _⟩
  have hqq : q ∈ E ∩ segment ℝ p q := ⟨hq,right_mem_segment ℝ _ _⟩
  rw [← he] at hpp hqq
  exact ⟨hpp.2,hqq.2⟩

/-- Spatial contact counts are unchanged by an actual translation preserving
its event set. This is a set image identity, not a cardinality certificate. -/
theorem translation_invariant_spatial_segment_count
    (E : Set Plane) (d p q : Plane)
    (hE : ∀ z : Plane, d+z ∈ E ↔ z ∈ E) :
    (E ∩ segment ℝ (d+p) (d+q)).ncard =
      (E ∩ segment ℝ p q).ncard := by
  have he : (fun z : Plane => d+z) '' (E ∩ segment ℝ p q) =
      E ∩ segment ℝ (d+p) (d+q) := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact ⟨(hE w).mpr hw.1,(mem_segment_translate ℝ d).mpr hw.2⟩
    · rintro ⟨hzE,hzS⟩
      refine ⟨z-d,⟨?_,?_⟩,by abel⟩
      · apply (hE (z-d)).mp
        simpa only [show d+(z-d)=z by abel] using hzE
      · apply (mem_segment_translate ℝ d).mp
        simpa only [show d+(z-d)=z by abel] using hzS
  rw [← he]
  exact ncard_image_of_injective _ (fun _ _ h => add_left_cancel h)

#print axioms finite_fiber_select_minimum_spatial_contacts
#print axioms spatial_fiber_contacts_strict_subsegment
#print axioms translation_invariant_spatial_segment_count

/-- The event set produced by the actual vertical deck family is invariant
under every vertical deck translation. -/
theorem actual_vertical_orbit_fiber_translation_invariant
    (G : ℝ → Plane) (T c : ℝ) (j : ℤ) (z : Plane) :
    Plane.mk 0 ((j:ℝ)*T)+z ∈
      (⋃ k : ℤ, range (fun t => G t+Plane.mk 0 ((k:ℝ)*T))) ∩ {w : Plane | w 0=c} ↔
    z ∈ (⋃ k : ℤ, range (fun t => G t+Plane.mk 0 ((k:ℝ)*T))) ∩ {w : Plane | w 0=c} := by
  constructor
  · rintro ⟨hz,hzc⟩
    obtain ⟨k,t,ht⟩ := mem_iUnion.mp hz
    refine ⟨mem_iUnion.mpr ⟨k-j,t,?_⟩,?_⟩
    · have he : G t+Plane.mk 0 (((k-j:ℤ):ℝ)*T) =
          (G t+Plane.mk 0 ((k:ℝ)*T))-Plane.mk 0 ((j:ℝ)*T) := by
        ext i
        fin_cases i
        · simp [Plane.mk]
        · simp [Plane.mk,Int.cast_sub]
          ring
      change G t+Plane.mk 0 (((k-j:ℤ):ℝ)*T)=z
      dsimp only at ht
      rw [he,ht]
      abel
    · simpa [Plane.mk] using hzc
  · rintro ⟨hz,hzc⟩
    obtain ⟨k,t,ht⟩ := mem_iUnion.mp hz
    refine ⟨mem_iUnion.mpr ⟨j+k,t,?_⟩,?_⟩
    · rw [← ht]
      ext i
      fin_cases i
      · simp [Plane.mk]
      · simp [Plane.mk,Int.cast_add]
        ring
    · simpa [Plane.mk] using hzc

#print axioms actual_vertical_orbit_fiber_translation_invariant

/-- Finite full-orbit contacts select a genuinely empty periodic-line bigon.
The local finiteness and pairwise disjointness concern the actual deck family,
not an assumed bigon emptiness or a cardinal reduction certificate. -/
theorem actual_vertical_family_select_interior_empty_bigon
    (G : C(ℝ,Plane)) (hG : IsClosedEmbedding G) (T c : ℝ)
    (hfinite : {t : ℝ | G t 0=c}.Finite)
    (hcount : 1 < {t : ℝ | G t 0=c}.ncard)
    (hpair : Pairwise (fun i j : ℤ => Disjoint
      (range (fun t => G t+Plane.mk 0 ((i:ℝ)*T)))
      (range (fun t => G t+Plane.mk 0 ((j:ℝ)*T)))))
    (hlf : LocallyFinite (fun j : ℤ => range (fun t => G t+Plane.mk 0 ((j:ℝ)*T)))) :
    ∃ r s : ℝ, r < s ∧ G r 0=c ∧ G s 0=c ∧
      IsJordanCurve ((G '' Icc r s) ∪ segment ℝ (G r) (G s)) ∧
      (∀ t ∈ Ioo r s, G t 0 ≠ c) ∧
      Disjoint (inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s)))
        (⋃ j : ℤ, range (fun t => G t+Plane.mk 0 ((j:ℝ)*T))) := by
  let L := fun j : ℤ => range (fun t => G t+Plane.mk 0 ((j:ℝ)*T))
  let E := (⋃ j : ℤ, L j) ∩ {z : Plane | z 0=c}
  obtain ⟨x,y,hx,hy,hne⟩ := (one_lt_ncard_iff hfinite).mp hcount
  have hxy : ∃ x y : ℝ, x < y ∧ G x 0=c ∧ G y 0=c := by
    rcases lt_or_gt_of_ne hne with hh | hh
    · exact ⟨x,y,hh,hx,hy⟩
    · exact ⟨y,x,hh,hy,hx⟩
  obtain ⟨x,y,hxy,hx,hy⟩ := hxy
  obtain ⟨r,s,hrs,hr,hs,hno,hmin⟩ :=
    finite_fiber_select_minimum_spatial_contacts G c E hfinite x y hxy hx hy
  have hC := fiber_free_interval_actual_jordan_candidate G hG.injective c r s hrs hr hs hno
  have hzero : Plane.mk 0 (((0:ℤ):ℝ)*T)=(0:Plane) := by
    ext i
    fin_cases i <;> simp
  have hbase (t : ℝ) : G t ∈ L 0 := ⟨t,by change G t+Plane.mk 0 (((0:ℤ):ℝ)*T)=G t; rw [hzero,add_zero]⟩
  have hsegment (z : Plane) (hz : z ∈ segment ℝ (G r) (G s)) : z 0=c := by
    rw [segment_eq_image_lineMap] at hz
    obtain ⟨v,hv,rfl⟩ := hz
    simp only [AffineMap.lineMap_apply]
    change v*(G s 0-G r 0)+G r 0=c
    rw [hr,hs]
    ring
  have hEf : (E ∩ segment ℝ (G r) (G s)).Finite :=
    actual_vertical_deck_fiber_events_finite_in_compact G T c hfinite hlf
      _ (isCompact_segment (G r) (G s))
  refine ⟨r,s,hrs,hr,hs,hC,hno,disjoint_left.mpr ?_⟩
  intro z hz hzL
  obtain ⟨j,t,ht⟩ := mem_iUnion.mp hzL
  let F : C(ℝ,Plane) := ⟨fun u => G u+Plane.mk 0 ((j:ℝ)*T),
    G.continuous.add continuous_const⟩
  have hF : IsClosedEmbedding F :=
    (Homeomorph.addRight (Plane.mk 0 ((j:ℝ)*T))).isClosedEmbedding.comp hG
  have htI : F t ∈ inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s)) := by
    simpa only [F,ContinuousMap.coe_mk,ht] using hz
  obtain ⟨a,b,hat,htb,haC,hbC,hin,hArc⟩ :=
    proper_line_entering_jordan_has_interval_crosscut F hF _ hC t htI
  have hab : a < b := hat.trans htb
  have hend : F a ∈ segment ℝ (G r) (G s) ∧
      F b ∈ segment ℝ (G r) (G s) ∧
      ¬ (F a=G r ∧ F b=G s) ∧ ¬ (F a=G s ∧ F b=G r) := by
    by_cases hj : j=0
    · subst j
      have hFG : F=G := by
        apply ContinuousMap.ext
        intro u
        change G u+Plane.mk 0 (((0:ℤ):ℝ)*T)=G u
        rw [hzero,add_zero]
      rw [hFG] at haC hbC hin ⊢
      exact interval_crosscut_of_line_bigon_endpoints_on_other_side
        G hG.injective r s a b hrs hab hC haC hbC hin
    · have hdis := hpair hj
      have hn (u : ℝ) : F u ∉ range G := by
        rintro ⟨v,hv⟩
        apply disjoint_left.mp hdis (show F u ∈ L j from ⟨u,rfl⟩)
        rw [← hv]
        exact hbase v
      have ha : F a ∈ segment ℝ (G r) (G s) := by
        rcases haC with ha | ha
        · obtain ⟨u,hu,he⟩ := ha
          exact False.elim (hn a ⟨u,he⟩)
        · exact ha
      have hb : F b ∈ segment ℝ (G r) (G s) := by
        rcases hbC with hb | hb
        · obtain ⟨u,hu,he⟩ := hb
          exact False.elim (hn b ⟨u,he⟩)
        · exact hb
      exact ⟨ha,hb,fun hh => hn a ⟨r,hh.1.symm⟩,fun hh => hn a ⟨s,hh.1.symm⟩⟩
  obtain ⟨ha,hb,hnot,hnot'⟩ := hend
  have ha0 : G a 0=c := by simpa [F,Plane.mk] using hsegment _ ha
  have hb0 : G b 0=c := by simpa [F,Plane.mk] using hsegment _ hb
  have havoid (u : ℝ) (hu : u ∈ Ioo a b) : G u 0≠c := by
    have hh := fiber_free_interval_bigon_inside_avoids_fiber G c r s hr hs hno hC _ (hin u hu)
    simpa [F,Plane.mk] using hh
  have hp : G r ∈ E := ⟨mem_iUnion.mpr ⟨0,hbase r⟩,hr⟩
  have hq : G s ∈ E := ⟨mem_iUnion.mpr ⟨0,hbase s⟩,hs⟩
  have hlt := spatial_fiber_contacts_strict_subsegment E (G r) (G s) (F a) (F b)
    hEf hp hq (fun hh => (ne_of_lt hrs) (hG.injective hh))
    (hr.trans hs.symm) ha hb hnot hnot'
  have heq : (E ∩ segment ℝ (F a) (F b)).ncard =
      (E ∩ segment ℝ (G a) (G b)).ncard := by
    have hh := translation_invariant_spatial_segment_count E
      (Plane.mk 0 ((j:ℝ)*T)) (G a) (G b)
      (actual_vertical_orbit_fiber_translation_invariant G T c j)
    simpa only [F,ContinuousMap.coe_mk,add_comm] using hh
  rw [heq] at hlt
  exact not_lt_of_ge (hmin a b hab ha0 hb0 havoid) hlt

#print axioms actual_vertical_family_select_interior_empty_bigon
