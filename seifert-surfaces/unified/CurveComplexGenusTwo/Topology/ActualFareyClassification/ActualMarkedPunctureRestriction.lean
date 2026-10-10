import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualTorusIsotopyDescent

open Set Topology Schoenflies CurveComplex

/-- Restrict an actual marked ambient isotopy to the punctured space. -/
theorem actual_point_fixed_isotopy_restricts_to_puncture_complement
    {X : Type*} [TopologicalSpace X] (H : AmbientIsotopy X) (p : X)
    (hfix : ∀ t, H.map (t,p)=p) :
    ∃ K : AmbientIsotopy {x : X | x≠p},
      ∀ t x, (K.map (t,x) : X)=H.map (t,(x:X)) := by
  have havoid (t : Interval) (x : {x : X | x≠p}) : H.map (t,(x:X))≠p := by
    obtain ⟨e,he⟩ := H.homeomorphism_at t
    intro hx
    apply x.property
    apply e.injective
    rw [he,he,hfix]
    exact hx
  let M : C(Interval×{x : X | x≠p},{x : X | x≠p}) :=
    ⟨fun tx => ⟨H.map (tx.1,tx.2.val),havoid tx.1 tx.2⟩,
      (H.map.continuous.comp (continuous_fst.prodMk
        (continuous_subtype_val.comp continuous_snd))).subtype_mk _⟩
  let K : AmbientIsotopy {x : X | x≠p} := {
    map := M
    homeomorphism_at := by
      intro t
      obtain ⟨e,he⟩ := H.homeomorphism_at t
      have hep : e p=p := (he p).trans (hfix t)
      have hinv (x : {x : X | x≠p}) : e.symm (x:X)≠p := by
        intro hx
        apply x.property
        have hh := congrArg e hx
        simpa [hep] using hh
      let E : {x : X | x≠p} ≃ₜ {x : X | x≠p} := {
        toFun := fun x => ⟨H.map (t,(x:X)),havoid t x⟩
        invFun := fun x => ⟨e.symm (x:X),hinv x⟩
        left_inv := by
          intro x
          apply Subtype.ext
          change e.symm (H.map (t,(x:X)))=(x:X)
          rw [← he,e.symm_apply_apply]
        right_inv := by
          intro x
          apply Subtype.ext
          change H.map (t,e.symm (x:X))=(x:X)
          rw [← he,e.apply_symm_apply]
        continuous_toFun := by
          apply Continuous.subtype_mk
          exact H.map.continuous.comp (continuous_const.prodMk continuous_subtype_val)
        continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _ }
      exact ⟨E,fun _ => rfl⟩
    at_zero := by
      intro x
      apply Subtype.ext
      exact H.at_zero (x:X) }
  exact ⟨K,fun _ _ => rfl⟩

#print axioms actual_point_fixed_isotopy_restricts_to_puncture_complement
