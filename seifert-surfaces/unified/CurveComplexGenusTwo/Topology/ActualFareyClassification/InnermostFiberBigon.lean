import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualFiberBigonSelection
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ProperLineJordanCrosscut

open Set Topology Schoenflies

theorem fiber_free_interval_actual_jordan_candidate
    (G : C(ℝ,Plane)) (hinj : Function.Injective G) (c r s : ℝ)
    (hrs : r < s) (hr : G r 0=c) (hs : G s 0=c)
    (hno : ∀ u ∈ Ioo r s, G u 0 ≠ c) :
    IsJordanCurve ((G '' Icc r s) ∪ segment ℝ (G r) (G s)) := by
  have hA := continuous_injective_interval_isArcBetween G hinj hrs
  have hB := isArcBetween_segment (fun he => (ne_of_lt hrs) (hinj he))
  have hsegment : ∀ z ∈ segment ℝ (G r) (G s), z 0=c := by
    intro z hz
    rw [segment_eq_image_lineMap] at hz
    obtain ⟨t,ht,rfl⟩ := hz
    simp only [AffineMap.lineMap_apply]
    change t*(G s 0-G r 0)+G r 0=c
    rw [hr,hs]
    ring
  apply isJordanCurve_union hA hB
  rintro z ⟨u,hu,rfl⟩ hz
  by_cases hur : u=r
  · exact Or.inl (congrArg G hur)
  by_cases hus : u=s
  · exact Or.inr (congrArg G hus)
  exact False.elim (hno u ⟨lt_of_le_of_ne hu.1 (Ne.symm hur),
    lt_of_le_of_ne hu.2 hus⟩ (hsegment _ hz))

/-- The source's actual minimum-side-count descent yields a Jordan bigon whose
open disk contains no point of the old proper embedded line. No smaller disk,
innermostness, or empty-interior certificate is assumed. -/
theorem actual_finite_fiber_select_interior_empty_bigon
    (G : C(ℝ,Plane)) (hG : IsClosedEmbedding G) (c : ℝ)
    (hfinite : {t : ℝ | G t 0=c}.Finite)
    (hcount : 1 < {t : ℝ | G t 0=c}.ncard) :
    ∃ r s : ℝ, r < s ∧ G r 0=c ∧ G s 0=c ∧
      IsJordanCurve ((G '' Icc r s) ∪ segment ℝ (G r) (G s)) ∧
      (∀ t ∈ Ioo r s, G t 0 ≠ c) ∧
      Disjoint (inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s))) (range G) := by
  obtain ⟨x,y,hx,hy,hne⟩ := (one_lt_ncard_iff hfinite).mp hcount
  have hpair : ∃ x y : ℝ, x < y ∧ G x 0=c ∧ G y 0=c := by
    rcases lt_or_gt_of_ne hne with hh | hh
    · exact ⟨x,y,hh,hx,hy⟩
    · exact ⟨y,x,hh,hy,hx⟩
  obtain ⟨x,y,hxy,hx,hy⟩ := hpair
  obtain ⟨r,s,hrs,hr,hs,hno,hmin⟩ :=
    finite_fiber_select_minimum_side_crossings G c hfinite x y hxy hx hy
  have hC := fiber_free_interval_actual_jordan_candidate G hG.injective c r s hrs hr hs hno
  refine ⟨r,s,hrs,hr,hs,hC,hno,?_⟩
  apply disjoint_left.mpr
  rintro z hz ⟨t,rfl⟩
  obtain ⟨a,b,hat,htb,haC,hbC,hin,hArc⟩ :=
    proper_line_entering_jordan_has_interval_crosscut G hG _ hC t hz
  have hab : a < b := hat.trans htb
  obtain ⟨ha,hb,hnot,hnot'⟩ := interval_crosscut_of_line_bigon_endpoints_on_other_side
    G hG.injective r s a b hrs hab hC haC hbC hin
  have hsegment : ∀ w ∈ segment ℝ (G r) (G s), w 0=c := by
    intro w hw
    rw [segment_eq_image_lineMap] at hw
    obtain ⟨v,hv,rfl⟩ := hw
    simp only [AffineMap.lineMap_apply]
    change v*(G s 0-G r 0)+G r 0=c
    rw [hr,hs]
    ring
  have ha0 := hsegment _ ha
  have hb0 := hsegment _ hb
  have havoid (u : ℝ) (hu : u ∈ Ioo a b) : G u 0 ≠ c :=
    fiber_free_interval_bigon_inside_avoids_fiber G c r s hr hs hno hC _ (hin u hu)
  have hlt := fiber_side_count_strict_of_new_endpoints G hG.injective c r s a b
    hfinite hrs hab hr hs ha hb hnot hnot'
  have hle := hmin a b hab ha0 hb0 havoid
  exact not_lt_of_ge hle hlt

#print axioms fiber_free_interval_actual_jordan_candidate
#print axioms actual_finite_fiber_select_interior_empty_bigon
