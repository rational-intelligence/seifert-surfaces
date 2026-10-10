import B1ActualInteriorSlicePoint_v475
noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- The actual exterior interior has open image in the sphere, by the
codimension-zero normal form of its supplied smooth inclusion. -/
theorem native_actual_exterior_interior_image_open_v475 :
    IsOpen (E.toSphere '' (𝓡∂ 3).interior E.Carrier) := by
  classical
  rw [isOpen_iff_mem_nhds]
  rintro p ⟨x,hx,rfl⟩
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  let hi := hinc.isImmersion.isImmersionAt x
  let F := hi.complement
  let h := hi.isImmersionAtOfComplement_complement
  letI : FiniteDimensional ℝ (E3 × F) :=
    FiniteDimensional.of_injective h.equiv.toLinearEquiv.toLinearMap h.equiv.injective
  letI : FiniteDimensional ℝ F :=
    FiniteDimensional.of_injective (LinearMap.inr ℝ E3 F) LinearMap.inr_injective
  have hdim : Module.finrank ℝ F=Module.finrank ℝ PUnit := by
    have hh := h.equiv.toLinearEquiv.finrank_eq
    change Module.finrank ℝ (E3 × F)=Module.finrank ℝ E3 at hh
    rw [Module.finrank_prod] at hh
    simp only [Module.finrank_eq_zero_of_subsingleton]
    omega
  let h' := h.trans_F (ContinuousLinearEquiv.ofFinrankEq hdim)
  let L : E3 ≃L[ℝ] E3 :=
    (ContinuousLinearEquiv.prodUnique ℝ E3 PUnit).symm.trans h'.equiv
  let c := h'.domChart.extend (𝓡∂ 3)
  let d : OpenPartialHomeomorph ThreeSphere E3 :=
    h'.codChart.transHomeomorph (𝓡 3).toHomeomorph
  let U : Set E3 := L '' interior c.target
  have hU : IsOpen U := L.toHomeomorph.isOpen_image.2 isOpen_interior
  have hUt : U ⊆ d.target := by
    rintro z ⟨v,hv,rfl⟩
    have hm := h'.map_target_subset_target (mem_image_of_mem (h'.equiv ∘ fun v : E3 => (v,0)) (interior_subset hv))
    change L v ∈ d.target
    have he : L v=h'.equiv (v,0) := rfl
    rw [he]
    change (𝓡 3).symm (h'.equiv (v,0)) ∈ h'.codChart.target
    rw [h'.codChart.extend_target] at hm
    exact hm.1
  let V := d.symm '' U
  have hV : IsOpen V := d.isOpen_image_symm_of_subset_target hU hUt
  have hxi : (𝓡∂ 3).IsInteriorPoint x := hx
  have hxc : c x ∈ interior c.target :=
    (ModelWithCorners.isInteriorPoint_iff_of_mem_maximalAtlas
      (I := 𝓡∂ 3) (by simp) h'.domChart_mem_maximalAtlas h'.mem_domChart_source).mp hxi
  have hxD : E.toSphere x ∈ d.source := h'.mem_codChart_source
  have hcoord : d (E.toSphere x)=L (c x) := by
    exact h'.equiv_symm_extend_codChart_apply h'.mem_domChart_source |>
      congrArg h'.equiv |>
      (fun hh => by simpa [L,c,d] using hh)
  have hxV : E.toSphere x ∈ V := by
    refine ⟨L (c x),⟨c x,hxc,rfl⟩,?_⟩
    rw [← hcoord,d.left_inv hxD]
  have hVE : V ⊆ E.toSphere '' (𝓡∂ 3).interior E.Carrier := by
    rintro a ⟨z,⟨v,hv,rfl⟩,rfl⟩
    let q := c.symm v
    have hq : q ∈ h'.domChart.source := by
      have hh := c.map_target (interior_subset hv)
      change q ∈ c.source at hh
      simpa only [c,OpenPartialHomeomorph.extend_source] using hh
    have hvc : c q=v := c.right_inv (interior_subset hv)
    have hqi : (𝓡∂ 3).IsInteriorPoint q := by
      apply (ModelWithCorners.isInteriorPoint_iff_of_mem_maximalAtlas
        (I := 𝓡∂ 3) (by simp) h'.domChart_mem_maximalAtlas hq).mpr
      change c q ∈ interior c.target
      rwa [hvc]
    have hcoordq : d (E.toSphere q)=L v := by
      have hh := h'.equiv_symm_extend_codChart_apply hq
      have hk := congrArg h'.equiv hh
      have hk' : d (E.toSphere q)=L (c q) := by simpa [L,c,d] using hk
      rwa [hvc] at hk'
    refine ⟨q,hqi,?_⟩
    rw [← hcoordq]
    exact (d.left_inv (h'.source_subset_preimage_source hq)).symm
  exact Filter.mem_of_superset (hV.mem_nhds hxV) hVE

#print axioms native_actual_exterior_interior_image_open_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
