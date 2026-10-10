import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualMarkedPunctureRestriction

open Set Topology Schoenflies CurveComplex

/-- Projection of the actual entire reference grid is exactly its torus circle. -/
theorem actual_vertical_grid_projection_is_reference_circle (c : ℝ) :
    (fun z : Plane => (Circle.exp (z 0),Circle.exp (z 1))) ''
      {z : Plane | ∃ i : ℤ, z 0=c+(i:ℝ)*(2*Real.pi)}=
      {z : Circle×Circle | z.1=Circle.exp c} := by
  ext z
  constructor
  · rintro ⟨x,⟨i,hi⟩,rfl⟩
    change Circle.exp (x 0)=Circle.exp c
    rw [hi]
    simp [Circle.exp_add]
  · intro hz
    obtain ⟨y,hy⟩ := Circle.exp_surjective z.2
    refine ⟨Plane.mk c y,⟨0,by simp⟩,?_⟩
    exact Prod.ext hz.symm hy

/-- Literal quotient commutation transports arbitrary actual images. -/
theorem actual_quotient_commutation_transports_final_image
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (q : X → Y) (H : AmbientIsotopy X) (K : AmbientIsotopy Y)
    (hcomm : ∀ t x, K.map (t,q x)=q (H.map (t,x))) (A : Set X) :
    K.finalMap '' (q '' A)=q '' (H.finalMap '' A) := by
  ext z
  constructor
  · rintro ⟨_,⟨x,hx,rfl⟩,rfl⟩
    exact ⟨H.finalMap x,⟨x,hx,rfl⟩,(hcomm _ x).symm⟩
  · rintro ⟨_,⟨x,hx,rfl⟩,rfl⟩
    exact ⟨q x,⟨x,hx,rfl⟩,hcomm _ x⟩

#print axioms actual_vertical_grid_projection_is_reference_circle
#print axioms actual_quotient_commutation_transports_final_image
