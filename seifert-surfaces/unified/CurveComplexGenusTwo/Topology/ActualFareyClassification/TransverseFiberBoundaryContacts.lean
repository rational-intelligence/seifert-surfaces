import CurveComplexGenusTwo.Topology.ActualFareyClassification.FiberSetCrossing

open Set Topology Schoenflies Metric

/-- A common-axis crossing on the straight fiber side of an actual empty
Jordan bigon cannot belong to any other lifted line: both fiber sides are
actually reached, and one half-ball belongs to the disk interior. -/
theorem transverse_fiber_contact_of_empty_bigon_on_curve_side
    (G : C(ℝ,Plane)) (r s c : ℝ) (hr : G r 0=c) (hs : G s 0=c)
    (hJ : IsJordanCurve ((G '' Icc r s) ∪ segment ℝ (G r) (G s)))
    (L : Set Plane)
    (he : Disjoint (inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s))) L)
    (hside : (∀ z∈(G '' Icc r s) ∪ segment ℝ (G r) (G s), z 0≤c) ∨
      (∀ z∈(G '' Icc r s) ∪ segment ℝ (G r) (G s), c≤z 0))
    (q : Plane) (hq : q∈segment ℝ (G r) (G s)) (_hqL : q∈L)
    (U : Set Plane) (V : Set (ℝ×ℝ)) (hqU : q∈U) (h : U ≃ₜ V)
    (hU : IsOpen U) (hV : IsOpen V)
    (hq0 : ((h ⟨q,hqU⟩ : V) : ℝ×ℝ)=(0,0))
    (haxes : ∀ z (hz : z∈U),
      (z 0=c ↔ ((h ⟨z,hz⟩ : V) : ℝ×ℝ).1=0) ∧
      (z∈L ↔ ((h ⟨z,hz⟩ : V) : ℝ×ℝ).2=0)) : q∈G '' Icc r s := by
  by_contra hqG
  have hqcoord : q 0=c := by
    rw [segment_eq_image_lineMap] at hq
    obtain ⟨u,hu,heq⟩ := hq
    have hh := congrArg (fun z : Plane => z 0) heq
    simp only [AffineMap.lineMap_apply] at hh
    change u*(G s 0-G r 0)+G r 0=q 0 at hh
    rw [hr,hs] at hh
    linarith
  have hclosed : IsClosed (G '' Icc r s) := (isCompact_Icc.image G.continuous).isClosed
  obtain ⟨ρ,hρ,hball⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl q hqG
  let C := (G '' Icc r s) ∪ segment ℝ (G r) (G s)
  have hlocal (z : Plane) (hz : z∈ball q ρ) (hzC : z∈C) : z 0=c := by
    rcases hzC with hzC|hzC
    · exact False.elim (hball hz hzC)
    · rw [segment_eq_image_lineMap] at hzC
      obtain ⟨u,hu,rfl⟩ := hzC
      simp only [AffineMap.lineMap_apply]
      change u*(G s 0-G r 0)+G r 0=c
      rw [hr,hs]
      ring
  obtain ⟨hleft,hright⟩ := actual_fiber_set_crossing_has_both_sides L q c hqcoord U V hqU h hU hV hq0 haxes
    (ball q ρ) isOpen_ball (mem_ball_self hρ)
  rcases hside with hl|hr
  · obtain ⟨z,⟨hzB,hzL⟩,hzleft⟩ := hleft
    have hzin := jordan_straight_fiber_left_halfball_inside C hJ q (Or.inr hq) c ρ hqcoord hρ hl hlocal ⟨hzB,hzleft⟩
    exact disjoint_left.mp he hzin hzL
  · obtain ⟨z,⟨hzB,hzL⟩,hzright⟩ := hright
    have hzin := jordan_straight_fiber_right_halfball_inside C hJ q (Or.inr hq) c ρ hqcoord hρ hr hlocal ⟨hzB,hzright⟩
    exact disjoint_left.mp he hzin hzL

#print axioms transverse_fiber_contact_of_empty_bigon_on_curve_side
