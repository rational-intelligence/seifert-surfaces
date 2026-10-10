import A5NativeHalfspaceImageChart

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.AppendixACoordinates

/-- An actual Euclidean coordinate change preserving the half-space sign
restricts to an open half-space coordinate change with the same regularity
and exact forward and inverse formulas. -/
theorem halfspace_coordinate_restriction
    (e : OpenPartialHomeomorph E2 E2) (n : ℕ∞ω)
    (he : ContDiffOn ℝ n e e.source) (hi : ContDiffOn ℝ n e.symm e.target)
    (hside : ∀ z ∈ e.source, 0 ≤ e z 0 ↔ 0 ≤ z 0) :
    ∃ d : OpenPartialHomeomorph (EuclideanHalfSpace 2) (EuclideanHalfSpace 2),
      d.source = (𝓡∂ 2) ⁻¹' e.source ∧ d.target = (𝓡∂ 2) ⁻¹' e.target ∧
      (∀ z ∈ d.source, (𝓡∂ 2) (d z) = e ((𝓡∂ 2) z)) ∧
      (∀ z ∈ d.target, (𝓡∂ 2) (d.symm z) = e.symm ((𝓡∂ 2) z)) ∧
      ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) n d d.source ∧
      ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) n d.symm d.target := by
  have hm (z : EuclideanHalfSpace 2) (hz : (𝓡∂ 2) z ∈ e.source) :
      e ((𝓡∂ 2) z) ∈ range (𝓡∂ 2) := by
    rw [range_modelWithCornersEuclideanHalfSpace]
    exact (hside _ hz).mpr z.property
  have hmi (z : EuclideanHalfSpace 2) (hz : (𝓡∂ 2) z ∈ e.target) :
      e.symm ((𝓡∂ 2) z) ∈ range (𝓡∂ 2) := by
    rw [range_modelWithCornersEuclideanHalfSpace]
    apply (hside _ (e.map_target hz)).mp
    rw [e.right_inv hz]
    exact z.property
  let d : OpenPartialHomeomorph (EuclideanHalfSpace 2) (EuclideanHalfSpace 2) := {
    toFun := (𝓡∂ 2).symm ∘ e ∘ (𝓡∂ 2)
    invFun := (𝓡∂ 2).symm ∘ e.symm ∘ (𝓡∂ 2)
    source := (𝓡∂ 2) ⁻¹' e.source
    target := (𝓡∂ 2) ⁻¹' e.target
    map_source' := by
      intro z hz
      change (𝓡∂ 2) ((𝓡∂ 2).symm (e ((𝓡∂ 2) z))) ∈ e.target
      rw [(𝓡∂ 2).right_inv (hm z hz)]
      exact e.map_source hz
    map_target' := by
      intro z hz
      change (𝓡∂ 2) ((𝓡∂ 2).symm (e.symm ((𝓡∂ 2) z))) ∈ e.source
      rw [(𝓡∂ 2).right_inv (hmi z hz)]
      exact e.map_target hz
    left_inv' := by
      intro z hz
      simp only [Function.comp_apply,(𝓡∂ 2).right_inv (hm z hz),e.left_inv hz,
        ModelWithCorners.left_inv]
    right_inv' := by
      intro z hz
      simp only [Function.comp_apply,(𝓡∂ 2).right_inv (hmi z hz),e.right_inv hz,
        ModelWithCorners.left_inv]
    continuousOn_toFun := (𝓡∂ 2).continuous_symm.comp_continuousOn
      (e.continuousOn.comp (𝓡∂ 2).continuous.continuousOn (fun _ hz => hz))
    continuousOn_invFun := (𝓡∂ 2).continuous_symm.comp_continuousOn
      (e.symm.continuousOn.comp (𝓡∂ 2).continuous.continuousOn (fun _ hz => hz))
    open_source := e.open_source.preimage (𝓡∂ 2).continuous
    open_target := e.open_target.preimage (𝓡∂ 2).continuous }
  refine ⟨d,rfl,rfl,fun z hz => (𝓡∂ 2).right_inv (hm z hz),
    fun z hz => (𝓡∂ 2).right_inv (hmi z hz),?_,?_⟩
  · exact (𝓡∂ 2).contMDiffOn_symm.comp
      (he.contMDiffOn.comp (𝓡∂ 2).contMDiff.contMDiffOn (fun _ hz => hz))
      (fun z hz => hm z hz)
  · exact (𝓡∂ 2).contMDiffOn_symm.comp
      (hi.contMDiffOn.comp (𝓡∂ 2).contMDiff.contMDiffOn (fun _ hz => hz))
      (fun z hz => hmi z hz)

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
