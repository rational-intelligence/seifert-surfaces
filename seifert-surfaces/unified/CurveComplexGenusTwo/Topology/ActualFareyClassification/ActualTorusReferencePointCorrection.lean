import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualGroupPointNormalization

open Set Topology Schoenflies CurveComplex

/-- An actual outside point can be moved off the reference circle while the
whole source curve is fixed at every time. The periodic bump is constructed
from the actual closed projection preimage, not from an isolation certificate. -/
theorem actual_torus_outside_point_moves_off_reference_fixing_source
    (b : Curve (Circle×Circle)) (c : ℝ) (p : Circle×Circle) (hp : p∉b.image) :
    ∃ J : AmbientIsotopy (Circle×Circle), ∃ q : Plane,
      (∀ t z, z∈b.image → J.map (t,z)=z) ∧
      J.finalMap p=(Circle.exp (q 0),Circle.exp (q 1)) ∧
      (∀ i : ℤ, q 0≠c+(i:ℝ)*(2*Real.pi)) := by
  let π : Plane → Circle×Circle := fun z => (Circle.exp (z 0),Circle.exp (z 1))
  have hπ : Continuous π := by fun_prop
  have hsurj : Function.Surjective π := by
    rintro ⟨x,y⟩
    obtain ⟨a,ha⟩ := Circle.exp_surjective x
    obtain ⟨d,hd⟩ := Circle.exp_surjective y
    exact ⟨Plane.mk a d,Prod.ext ha hd⟩
  let L := π ⁻¹' b.image
  have hL : IsClosed L := (isCompact_range b.embedded.continuous).isClosed.preimage hπ
  have hInv : ∀ (i : ℤ×ℤ) z,
      z+Plane.mk ((i.1:ℝ)*(2*Real.pi)) ((i.2:ℝ)*(2*Real.pi))∈L ↔ z∈L := by
    intro i z
    have he : π (z+Plane.mk ((i.1:ℝ)*(2*Real.pi)) ((i.2:ℝ)*(2*Real.pi)))=π z := by
      simp [π,Plane.mk,Circle.exp_add]
    change π _∈b.image ↔ π z∈b.image
    rw [he]
  obtain ⟨p₀,hp₀⟩ := hsurj p
  have hpL : p₀∉L := by change π p₀∉b.image; rw [hp₀]; exact hp
  obtain ⟨A,hAeq,hAfix,hAvoid⟩ := actual_outside_point_can_avoid_grid_fixing_family
    L hL (2*Real.pi) c (by positivity) hInv p₀ hpL
  obtain ⟨z₀,hz₀⟩ := hsurj (b.map 1)
  have hzL : z₀∈L := by
    change π z₀∈b.image
    rw [hz₀]
    exact mem_range_self 1
  obtain ⟨J,hJcomm,_⟩ := actual_lattice_isotopy_descends_to_marked_torus
    A hAeq z₀ (fun t => hAfix t z₀ hzL)
  refine ⟨J,A.finalMap p₀,?_,?_,hAvoid⟩
  · intro t z hz
    obtain ⟨w,rfl⟩ := hsurj z
    change π w∈b.image at hz
    have hw : w∈L := hz
    change J.map (t,π w)=π w
    rw [hJcomm,hAfix t w hw]
  · have hh := hJcomm (⟨1,by norm_num⟩ : Interval) p₀
    change J.finalMap (π p₀)=π (A.finalMap p₀) at hh
    rw [hp₀] at hh
    exact hh

#print axioms actual_torus_outside_point_moves_off_reference_fixing_source
