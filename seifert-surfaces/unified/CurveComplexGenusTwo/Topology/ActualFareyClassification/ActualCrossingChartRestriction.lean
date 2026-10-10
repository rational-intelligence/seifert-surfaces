import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualSurvivingEventLocality

open Set Topology Schoenflies CurveComplex

/-- Restrict an actual simultaneous-axis chart to an actual prescribed open
neighborhood. The target open set and restricted homeomorphism are constructed. -/
theorem actual_crossing_chart_restrict_to_open
    (U : Set Plane) (V : Set (ℝ×ℝ)) (_hU : IsOpen U) (hV : IsOpen V)
    (h : U ≃ₜ V) (N : Set Plane) (hN : IsOpen N) :
    ∃ W : Set (ℝ×ℝ), IsOpen W ∧
    ∃ e : ↥(U∩N) ≃ₜ W,
      ∀ z (hz : z∈U∩N), ((e ⟨z,hz⟩ : W) : ℝ×ℝ)=((h ⟨z,hz.1⟩ : V) : ℝ×ℝ) := by
  let S : Set U := {u | (u : Plane)∈N}
  let W := Subtype.val '' (h '' S)
  have hW : IsOpen W := hV.isOpenMap_subtype_val _
    (h.isOpenMap _ (hN.preimage continuous_subtype_val))
  have hWV : W⊆V := by rintro z ⟨v,_,rfl⟩; exact v.property
  have hInv (w : W) : ((h.symm ⟨w.val,hWV w.property⟩ : U) : Plane)∈N := by
    obtain ⟨v,⟨u,hu,he⟩,hv⟩ := w.property
    have hv' : v=⟨w.val,hWV w.property⟩ := Subtype.ext hv
    have hu' : h u=⟨w.val,hWV w.property⟩ := he.trans hv'
    change (u : Plane)∈N at hu
    simpa only [←hu',h.symm_apply_apply] using hu
  let e : ↥(U∩N) ≃ₜ W := {
    toFun := fun z => ⟨((h ⟨z.val,z.property.1⟩ : V) : ℝ×ℝ),
      ⟨h ⟨z.val,z.property.1⟩,⟨⟨z.val,z.property.1⟩,z.property.2,rfl⟩,rfl⟩⟩
    invFun := fun w => ⟨((h.symm ⟨w.val,hWV w.property⟩ : U) : Plane),
      ⟨(h.symm ⟨w.val,hWV w.property⟩).property,hInv w⟩⟩
    left_inv := by intro z; apply Subtype.ext; exact congrArg (fun u : U => (u : Plane)) (h.symm_apply_apply ⟨z.val,z.property.1⟩)
    right_inv := by intro w; apply Subtype.ext; exact congrArg (fun v : V => (v : ℝ×ℝ)) (h.apply_symm_apply ⟨w.val,hWV w.property⟩)
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact continuous_subtype_val.comp (h.continuous.comp (continuous_subtype_val.subtype_mk _))
    continuous_invFun := by
      apply Continuous.subtype_mk
      exact continuous_subtype_val.comp (h.symm.continuous.comp (continuous_subtype_val.subtype_mk _)) }
  exact ⟨W,hW,e,by intro z hz; rfl⟩

#print axioms actual_crossing_chart_restrict_to_open
