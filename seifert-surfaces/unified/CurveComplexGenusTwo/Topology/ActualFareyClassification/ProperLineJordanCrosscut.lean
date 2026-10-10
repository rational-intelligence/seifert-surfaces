import CurveComplexGenusTwo.Topology.TorusStrip.ArcInterval
import CurveComplexGenusTwo.Topology.TorusStrip.JordanBoxNarrow
import Mathlib

open Set Topology Schoenflies

/-- An actual proper embedded line entering a Jordan disk has a genuine
parameter-interval crosscut. Its endpoints are selected from the actual
preimage component; no crosscut receipt is assumed. -/
theorem proper_line_entering_jordan_has_interval_crosscut
    (G : C(ℝ,Plane)) (hG : IsClosedEmbedding G)
    (C : Set Plane) (hC : IsJordanCurve C)
    (t : ℝ) (ht : G t ∈ inside C) :
    ∃ a b : ℝ, a < t ∧ t < b ∧ G a ∈ C ∧ G b ∈ C ∧
      (∀ u ∈ Ioo a b, G u ∈ inside C) ∧
      IsArcBetween (G '' Icc a b) (G a) (G b) := by
  let U := inside C
  let K := closure U
  have hsep := jordan_curve_theorem hC
  have hK : IsCompact K := Metric.isCompact_of_isClosed_isBounded
    isClosed_closure hsep.isBounded_inside.closure
  have hpre : IsCompact (G ⁻¹' K) := hG.isProperMap.isCompact_preimage hK
  obtain ⟨lo,hlo⟩ := hpre.bddBelow
  obtain ⟨hi,hhi⟩ := hpre.bddAbove
  let l : ℝ := min lo t-1
  let r : ℝ := max hi t+1
  have hlt : l < t := by dsimp [l]; linarith [min_le_right lo t]
  have htr : t < r := by dsimp [r]; linarith [le_max_right hi t]
  have hlK : G l ∉ K := by
    intro hh
    have hh' := hlo hh
    dsimp [l] at hh'
    linarith [min_le_left lo t]
  have hrK : G r ∉ K := by
    intro hh
    have hh' := hhi hh
    dsimp [r] at hh'
    linarith [le_max_left hi t]
  let L := Icc l t ∩ G ⁻¹' Uᶜ
  let R := Icc t r ∩ G ⁻¹' Uᶜ
  have hcomp : IsClosed (G ⁻¹' Uᶜ) := hsep.isOpen_inside.isClosed_compl.preimage G.continuous
  have hLne : L.Nonempty := ⟨l,⟨le_rfl,hlt.le⟩,fun hh => hlK (subset_closure hh)⟩
  have hRne : R.Nonempty := ⟨r,⟨htr.le,le_rfl⟩,fun hh => hrK (subset_closure hh)⟩
  obtain ⟨a,ha,hamax⟩ := (isCompact_Icc.inter_right hcomp).exists_isGreatest hLne
  obtain ⟨b,hb,hbmin⟩ := (isCompact_Icc.inter_right hcomp).exists_isLeast hRne
  have hat : a < t := lt_of_le_of_ne ha.1.2 (by intro he; exact ha.2 (he ▸ ht))
  have htb : t < b := lt_of_le_of_ne hb.1.1 (by intro he; exact hb.2 (he.symm ▸ ht))
  have hab : a < b := hat.trans htb
  have hin (u : ℝ) (hu : u ∈ Ioo a b) : G u ∈ U := by
    by_contra hn
    by_cases hut : u ≤ t
    · have hm : u ∈ L := ⟨⟨ha.1.1.trans hu.1.le,hut⟩,hn⟩
      exact not_le_of_gt hu.1 (hamax hm)
    · have hm : u ∈ R := ⟨⟨le_of_not_ge hut,hu.2.le.trans hb.1.2⟩,hn⟩
      exact not_le_of_gt hu.2 (hbmin hm)
  have hclosed : IsClosed (G ⁻¹' K) := isClosed_closure.preimage G.continuous
  have hIcc : Icc a b ⊆ G ⁻¹' K := by
    rw [← closure_Ioo hab.ne]
    apply hclosed.closure_subset_iff.mpr
    exact fun u hu => subset_closure (hin u hu)
  have hboundary (u : ℝ) (huK : G u ∈ K) (huU : G u ∉ U) : G u ∈ C := by
    rw [← hsep.frontier_inside]
    change G u ∈ closure U \ interior U
    rw [hsep.isOpen_inside.interior_eq]
    exact ⟨huK,huU⟩
  exact ⟨a,b,hat,htb,hboundary a (hIcc ⟨le_rfl,hab.le⟩) ha.2,
    hboundary b (hIcc ⟨hab.le,le_rfl⟩) hb.2,hin,
    continuous_injective_interval_isArcBetween G hG.injective hab⟩

#print axioms proper_line_entering_jordan_has_interval_crosscut

theorem interval_crosscut_of_line_bigon_endpoints_on_other_side
    (G : C(ℝ,Plane)) (hinj : Function.Injective G) (r s a b : ℝ)
    (hrs : r < s) (hab : a < b)
    (_hC : IsJordanCurve ((G '' Icc r s) ∪ segment ℝ (G r) (G s)))
    (haC : G a ∈ (G '' Icc r s) ∪ segment ℝ (G r) (G s))
    (hbC : G b ∈ (G '' Icc r s) ∪ segment ℝ (G r) (G s))
    (hin : ∀ u ∈ Ioo a b, G u ∈ inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s))) :
    G a ∈ segment ℝ (G r) (G s) ∧ G b ∈ segment ℝ (G r) (G s) ∧
      ¬ (G a=G r ∧ G b=G s) ∧ ¬ (G a=G s ∧ G b=G r) := by
  have houtside (u : ℝ) (hu : u ∈ Ioo a b) : u ∉ Icc r s := by
    intro hh
    exact inside_subset_compl (hin u hu) (Or.inl ⟨u,hh,rfl⟩)
  have haS : G a ∈ segment ℝ (G r) (G s) := by
    by_contra hn
    obtain ⟨v,hv,he⟩ := haC.resolve_right hn
    have hva : v=a := hinj he
    subst v
    have har : a ≠ r := by intro hh; subst a; exact hn (left_mem_segment ℝ _ _)
    have has : a ≠ s := by intro hh; subst a; exact hn (right_mem_segment ℝ _ _)
    have ha1 : r < a := lt_of_le_of_ne hv.1 (Ne.symm har)
    have ha2 : a < s := lt_of_le_of_ne hv.2 has
    let u := (a+min b s)/2
    have haum : a < min b s := lt_min hab ha2
    have hu : u ∈ Ioo a b := by
      dsimp [u]
      constructor <;> linarith [min_le_left b s]
    have hur : u ∈ Icc r s := by
      dsimp [u]
      constructor <;> linarith [min_le_right b s]
    exact houtside u hu hur
  have hbS : G b ∈ segment ℝ (G r) (G s) := by
    by_contra hn
    obtain ⟨v,hv,he⟩ := hbC.resolve_right hn
    have hvb : v=b := hinj he
    subst v
    have hbr : b ≠ r := by intro hh; subst b; exact hn (left_mem_segment ℝ _ _)
    have hbs : b ≠ s := by intro hh; subst b; exact hn (right_mem_segment ℝ _ _)
    have hb1 : r < b := lt_of_le_of_ne hv.1 (Ne.symm hbr)
    have hb2 : b < s := lt_of_le_of_ne hv.2 hbs
    let u := (max a r+b)/2
    have humb : max a r < b := max_lt hab hb1
    have hu : u ∈ Ioo a b := by
      dsimp [u]
      constructor <;> linarith [le_max_left a r]
    have hur : u ∈ Icc r s := by
      dsimp [u]
      constructor <;> linarith [le_max_right a r]
    exact houtside u hu hur
  refine ⟨haS,hbS,?_,?_⟩
  · rintro ⟨ha,hb⟩
    have har := hinj ha
    have hbs := hinj hb
    subst a
    subst b
    have hu : (r+s)/2 ∈ Ioo r s := by constructor <;> linarith
    exact houtside _ hu ⟨hu.1.le,hu.2.le⟩
  · rintro ⟨ha,hb⟩
    have has := hinj ha
    have hbr := hinj hb
    subst a
    subst b
    linarith

#print axioms interval_crosscut_of_line_bigon_endpoints_on_other_side

theorem jordan_inside_avoids_supporting_vertical_fiber
    (C : Set Plane) (hC : IsJordanCurve C) (c : ℝ)
    (hside : (∀ z ∈ C, z 0 ≤ c) ∨ (∀ z ∈ C, c ≤ z 0)) :
    ∀ z ∈ inside C, z 0 ≠ c := by
  intro z hz hzc
  let q : ℝ → Plane := fun u => z+Plane.mk u 0
  have hq : Continuous q := by dsimp [q]; fun_prop
  have hqzero : q 0=z := by
    ext i
    fin_cases i <;> simp [q,Plane.mk]
  have hpre : q ⁻¹' inside C ∈ 𝓝 (0:ℝ) :=
    ((jordan_curve_theorem hC).isOpen_inside.preimage hq).mem_nhds (by
      change q 0 ∈ inside C
      rw [hqzero]
      exact hz)
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hpre
  rcases hside with hupper | hlower
  · have hu : ε/2 ∈ Metric.ball (0:ℝ) ε := by
      rw [Metric.mem_ball,Real.dist_eq,abs_lt]
      constructor <;> linarith
    have hin := hball hu
    have hb := jordan_coordinate_upper_bound hC 0 c hupper _ (subset_closure hin)
    change z 0+ε/2 ≤ c at hb
    linarith
  · have hu : -ε/2 ∈ Metric.ball (0:ℝ) ε := by
      rw [Metric.mem_ball,Real.dist_eq,abs_lt]
      constructor <;> linarith
    have hin := hball hu
    have hb := jordan_coordinate_lower_bound hC 0 c hlower _ (subset_closure hin)
    change c ≤ z 0+(-ε/2) at hb
    linarith

theorem fiber_free_interval_bigon_inside_avoids_fiber
    (G : C(ℝ,Plane)) (c r s : ℝ)
    (hr : G r 0=c) (hs : G s 0=c)
    (hno : ∀ t ∈ Ioo r s, G t 0 ≠ c)
    (hC : IsJordanCurve ((G '' Icc r s) ∪ segment ℝ (G r) (G s))) :
    ∀ z ∈ inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s)), z 0 ≠ c := by
  let f : ℝ → ℝ := fun u => G u 0
  have hf : Continuous f := by dsimp [f]; fun_prop
  let S : Set ℝ := f '' Ioo r s
  have hconn : IsPreconnected S := isPreconnected_Ioo.image f hf.continuousOn
  have hpart : S ⊆ Iio c ∪ Ioi c := by
    rintro z ⟨t,ht,rfl⟩
    exact lt_or_gt_of_ne (hno t ht)
  have hdis : Disjoint (Iio c) (Ioi c) := disjoint_left.mpr (by
    intro u hu hv
    exact lt_asymm (show u<c from hu) (show c<u from hv))
  have hsign := hconn.subset_or_subset isOpen_Iio isOpen_Ioi hdis hpart
  have hsegment : ∀ z ∈ segment ℝ (G r) (G s), z 0=c := by
    intro z hz
    rw [segment_eq_image_lineMap] at hz
    obtain ⟨t,ht,rfl⟩ := hz
    simp only [AffineMap.lineMap_apply]
    change t*(G s 0-G r 0)+G r 0=c
    rw [hr,hs]
    ring
  apply jordan_inside_avoids_supporting_vertical_fiber _ hC c
  have hendpoint (t : ℝ) (ht : t ∈ Icc r s) :
      t=r ∨ t=s ∨ t ∈ Ioo r s := by
    by_cases htr : t=r
    · exact Or.inl htr
    by_cases hts : t=s
    · exact Or.inr (Or.inl hts)
    exact Or.inr (Or.inr ⟨lt_of_le_of_ne ht.1 (Ne.symm htr),lt_of_le_of_ne ht.2 hts⟩)
  rcases hsign with hleft | hright
  · left
    rintro z (⟨t,ht,rfl⟩ | hz)
    · rcases hendpoint t ht with he | he | hi
      · simp [he,hr]
      · simp [he,hs]
      · exact (hleft (mem_image_of_mem _ hi)).le
    · exact (hsegment z hz).le
  · right
    rintro z (⟨t,ht,rfl⟩ | hz)
    · rcases hendpoint t ht with he | he | hi
      · simp [he,hr]
      · simp [he,hs]
      · exact (hright (mem_image_of_mem _ hi)).le
    · exact (hsegment z hz).ge

#print axioms jordan_inside_avoids_supporting_vertical_fiber
#print axioms fiber_free_interval_bigon_inside_avoids_fiber

theorem endpoint_of_nested_real_segment
    (p q u v : ℝ) (hu : u ∈ segment ℝ p q) (hv : v ∈ segment ℝ p q)
    (hp : p ∈ segment ℝ u v) : u=p ∨ v=p := by
  rw [segment_eq_Icc'] at hu hv hp
  by_cases hpq : p ≤ q
  · simp only [min_eq_left hpq,max_eq_right hpq] at hu hv
    rcases le_total u v with huv | hvu
    · rw [min_eq_left huv] at hp
      exact Or.inl (le_antisymm hp.1 hu.1)
    · rw [min_eq_right hvu] at hp
      exact Or.inr (le_antisymm hp.1 hv.1)
  · have hqp : q ≤ p := le_of_not_ge hpq
    simp only [min_eq_right hqp,max_eq_left hqp] at hu hv
    rcases le_total u v with huv | hvu
    · rw [max_eq_right huv] at hp
      exact Or.inr (le_antisymm hv.2 hp.2)
    · rw [max_eq_left hvu] at hp
      exact Or.inl (le_antisymm hu.2 hp.2)

theorem vertical_segment_endpoint_extreme
    (p q u v : Plane) (hvertical : p 0=q 0)
    (hu : u ∈ segment ℝ p q) (hv : v ∈ segment ℝ p q)
    (hp : p ∈ segment ℝ u v) : u=p ∨ v=p := by
  have coord (i : Fin 2) {a b z : Plane} (hz : z ∈ segment ℝ a b) :
      z i ∈ segment ℝ (a i) (b i) := by
    have hh := mem_image_of_mem (EuclideanSpace.proj i).toAffineMap hz
    rwa [image_segment] at hh
  have hu0 : u 0=p 0 := by
    have hh := coord 0 hu
    rw [← hvertical,segment_same] at hh
    exact hh
  have hv0 : v 0=p 0 := by
    have hh := coord 0 hv
    rw [← hvertical,segment_same] at hh
    exact hh
  have hh := endpoint_of_nested_real_segment (p 1) (q 1) (u 1) (v 1)
    (coord 1 hu) (coord 1 hv) (coord 1 hp)
  rcases hh with hh | hh
  · left
    ext i
    fin_cases i
    · exact hu0
    · exact hh
  · right
    ext i
    fin_cases i
    · exact hv0
    · exact hh

theorem fiber_side_count_strict_of_new_endpoints
    (G : ℝ → Plane) (hinj : Function.Injective G) (c r s a b : ℝ)
    (hfinite : {t : ℝ | G t 0=c}.Finite) (hrs : r < s) (_hab : a < b)
    (hr : G r 0=c) (hs : G s 0=c)
    (ha : G a ∈ segment ℝ (G r) (G s))
    (hb : G b ∈ segment ℝ (G r) (G s))
    (hnot : ¬ (G a=G r ∧ G b=G s))
    (hnot' : ¬ (G a=G s ∧ G b=G r)) :
    {t : ℝ | G t 0=c ∧ G t ∈ segment ℝ (G a) (G b)}.ncard <
      {t : ℝ | G t 0=c ∧ G t ∈ segment ℝ (G r) (G s)}.ncard := by
  let E := {t : ℝ | G t 0=c ∧ G t ∈ segment ℝ (G r) (G s)}
  let F := {t : ℝ | G t 0=c ∧ G t ∈ segment ℝ (G a) (G b)}
  have hEF : F ⊆ E := by
    intro t ht
    exact ⟨ht.1,(convex_segment (𝕜:=ℝ) (G r) (G s)).segment_subset ha hb ht.2⟩
  have hn : ¬ (r ∈ F ∧ s ∈ F) := by
    rintro ⟨hrr,hss⟩
    have hp := vertical_segment_endpoint_extreme (G r) (G s) (G a) (G b)
      (hr.trans hs.symm) ha hb hrr.2
    have hq := vertical_segment_endpoint_extreme (G s) (G r) (G a) (G b)
      (hs.trans hr.symm) (by rwa [segment_symm]) (by rwa [segment_symm]) hss.2
    rcases hp with hp | hp <;> rcases hq with hq | hq
    · exact (ne_of_lt hrs) (hinj (hp.symm.trans hq))
    · exact hnot ⟨hp,hq⟩
    · exact hnot' ⟨hq,hp⟩
    · exact (ne_of_lt hrs) (hinj (hp.symm.trans hq))
  have hstrict : F ⊂ E := by
    apply ssubset_iff_subset_ne.mpr
    refine ⟨hEF,?_⟩
    intro he
    apply hn
    rw [he]
    exact ⟨⟨hr,left_mem_segment ℝ _ _⟩,⟨hs,right_mem_segment ℝ _ _⟩⟩
  exact ncard_lt_ncard hstrict (hfinite.subset (fun _ h => h.1))

#print axioms endpoint_of_nested_real_segment
#print axioms vertical_segment_endpoint_extreme
#print axioms fiber_side_count_strict_of_new_endpoints
