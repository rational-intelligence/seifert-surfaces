import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualTorusImageTransport

open Set Topology Schoenflies CurveComplex

/-- Point normalization of an actual group-valued ambient isotopy constructs
an all-time point-fixed ambient isotopy, retaining its literal final translate. -/
theorem actual_group_isotopy_has_point_fixed_normalization
    {X : Type*} [TopologicalSpace X] [Group X] [IsTopologicalGroup X]
    (H : AmbientIsotopy X) (p : X) :
    ∃ P : AmbientIsotopy X,
      (∀ t, P.map (t,p)=p) ∧
      (∀ t z, P.map (t,z)=H.map (t,z)*(H.map (t,p))⁻¹*p) := by
  let P : AmbientIsotopy X := {
    map := ⟨fun tx => H.map tx*(H.map (tx.1,p))⁻¹*p,by fun_prop⟩
    homeomorphism_at := by
      intro t
      obtain ⟨e,he⟩ := H.homeomorphism_at t
      refine ⟨e.trans (Homeomorph.mulRight ((H.map (t,p))⁻¹*p)),?_⟩
      intro z
      change e z*((H.map (t,p))⁻¹*p)=H.map (t,z)*(H.map (t,p))⁻¹*p
      rw [he,mul_assoc]
    at_zero := by
      intro z
      change H.map (⟨0,by norm_num⟩,z)*(H.map (⟨0,by norm_num⟩,p))⁻¹*p=z
      rw [H.at_zero,H.at_zero]
      simp [mul_assoc] }
  exact ⟨P,by intro t; change H.map (t,p)*(H.map (t,p))⁻¹*p=p; simp,fun _ _ => rfl⟩

#print axioms actual_group_isotopy_has_point_fixed_normalization
