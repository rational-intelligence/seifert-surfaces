import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualSurvivingEventLocality

open Set Topology Schoenflies CurveComplex

/-- Actual equivariance transports the entire lifted row family; no family
image identity is supplied as a certificate. -/
theorem actual_equivariant_final_map_row_family_image
    (G : ℝ→Plane) (H : AmbientIsotopy Plane) (T : ℝ)
    (heq : ∀ t (i : ℤ×ℤ) z,
      H.map (t,z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))=
        H.map (t,z)+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) :
    H.finalMap '' (⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T)))=
      ⋃ j : ℤ, range (fun x : ℝ => H.finalMap (G x)+Plane.mk 0 ((j:ℝ)*T)) := by
  have hrow (j : ℤ) (x : ℝ) : H.finalMap (G x+Plane.mk 0 ((j:ℝ)*T))=
      H.finalMap (G x)+Plane.mk 0 ((j:ℝ)*T) := by
    simpa only [AmbientIsotopy.finalMap,Int.cast_zero,zero_mul] using
      heq ⟨1,by norm_num⟩ (0,j) (G x)
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    obtain ⟨j,x,rfl⟩ := mem_iUnion.mp hw
    exact mem_iUnion.mpr ⟨j,x,(hrow j x).symm⟩
  · intro hz
    obtain ⟨j,x,rfl⟩ := mem_iUnion.mp hz
    exact ⟨G x+Plane.mk 0 ((j:ℝ)*T),mem_iUnion.mpr ⟨j,x,rfl⟩,hrow j x⟩

/-- On an actually fixed open neighborhood the old and new WHOLE family
memberships agree. Final-map injectivity excludes an outside point moving in. -/
theorem actual_fixed_neighborhood_row_family_membership
    (G : ℝ→Plane) (H : AmbientIsotopy Plane) (T : ℝ)
    (heq : ∀ t (i : ℤ×ℤ) z,
      H.map (t,z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))=
        H.map (t,z)+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))
    (N : Set Plane) (hfix : ∀ t z, z∈N → H.map (t,z)=z)
    (z : Plane) (hz : z∈N) :
    (z∈⋃ j : ℤ, range (fun x : ℝ => H.finalMap (G x)+Plane.mk 0 ((j:ℝ)*T))) ↔
      z∈⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T)) := by
  rw [←actual_equivariant_final_map_row_family_image G H T heq]
  have hFinal : H.finalMap z=z := hfix ⟨1,by norm_num⟩ z hz
  obtain ⟨e,he⟩ := H.homeomorphism_at ⟨1,by norm_num⟩
  have hInj : Function.Injective H.finalMap := by
    intro x y hxy
    apply e.injective
    simpa only [he,AmbientIsotopy.finalMap] using hxy
  constructor
  · rintro ⟨w,hw,he⟩
    have hwz := hInj (he.trans hFinal.symm)
    exact hwz ▸ hw
  · intro hzG
    exact ⟨z,hzG,hFinal⟩

#print axioms actual_equivariant_final_map_row_family_image
#print axioms actual_fixed_neighborhood_row_family_membership
