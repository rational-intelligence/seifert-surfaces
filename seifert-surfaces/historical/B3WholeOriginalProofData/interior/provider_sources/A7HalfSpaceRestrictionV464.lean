import EndpointGeometry
import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Chart
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Function Filter
open scoped Manifold ContDiff Topology
namespace SeifertSurfaces.OriginalEndpoints.A7Support

variable {n m : ℕ} [NeZero n] [NeZero m]

/-- Restriction of an actual Euclidean local homeomorphism to corresponding
closed half-spaces. The source and target remain open in the native models. -/
def halfSpaceRestriction
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))
    (he : e.IsImage (range (𝓡∂ n)) (range (𝓡∂ m))) :
    OpenPartialHomeomorph (EuclideanHalfSpace n) (EuclideanHalfSpace m) where
  toFun := (𝓡∂ m).symm ∘ e ∘ (𝓡∂ n)
  invFun := (𝓡∂ n).symm ∘ e.symm ∘ (𝓡∂ m)
  source := (𝓡∂ n) ⁻¹' e.source
  target := (𝓡∂ m) ⁻¹' e.target
  map_source' := by
    intro x hx
    have hxR : e ((𝓡∂ n) x) ∈ range (𝓡∂ m) :=
      (he.apply_mem_iff hx).2 (mem_range_self _)
    change (𝓡∂ m) ((𝓡∂ m).symm (e ((𝓡∂ n) x))) ∈ e.target
    rw [(𝓡∂ m).right_inv hxR]
    exact e.map_source hx
  map_target' := by
    intro y hy
    have hyR : e.symm ((𝓡∂ m) y) ∈ range (𝓡∂ n) :=
      (he.symm_apply_mem_iff hy).2 (mem_range_self _)
    change (𝓡∂ n) ((𝓡∂ n).symm (e.symm ((𝓡∂ m) y))) ∈ e.source
    rw [(𝓡∂ n).right_inv hyR]
    exact e.map_target hy
  left_inv' := by
    intro x hx
    have hxR : e ((𝓡∂ n) x) ∈ range (𝓡∂ m) :=
      (he.apply_mem_iff hx).2 (mem_range_self _)
    change (𝓡∂ n).symm (e.symm ((𝓡∂ m) ((𝓡∂ m).symm (e ((𝓡∂ n) x))))) = x
    rw [(𝓡∂ m).right_inv hxR,e.left_inv hx,(𝓡∂ n).left_inv]
  right_inv' := by
    intro y hy
    have hyR : e.symm ((𝓡∂ m) y) ∈ range (𝓡∂ n) :=
      (he.symm_apply_mem_iff hy).2 (mem_range_self _)
    change (𝓡∂ m).symm (e ((𝓡∂ n) ((𝓡∂ n).symm (e.symm ((𝓡∂ m) y))))) = y
    rw [(𝓡∂ n).right_inv hyR,e.right_inv hy,(𝓡∂ m).left_inv]
  open_source := e.open_source.preimage (𝓡∂ n).continuous
  open_target := e.open_target.preimage (𝓡∂ m).continuous
  continuousOn_toFun := (𝓡∂ m).continuous_symm.comp_continuousOn
    (e.continuousOn.comp (𝓡∂ n).continuous.continuousOn (fun _ hx => hx))
  continuousOn_invFun := (𝓡∂ n).continuous_symm.comp_continuousOn
    (e.continuousOn_symm.comp (𝓡∂ m).continuous.continuousOn (fun _ hy => hy))

theorem halfSpaceRestriction_coordinate
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))
    (he : e.IsImage (range (𝓡∂ n)) (range (𝓡∂ m)))
    (x : EuclideanHalfSpace n) (hx : (𝓡∂ n) x ∈ e.source) :
    (𝓡∂ m) (halfSpaceRestriction e he x) = e ((𝓡∂ n) x) :=
  (𝓡∂ m).right_inv ((he.apply_mem_iff hx).2 (mem_range_self _))

theorem halfSpaceRestriction_smooth
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))
    (he : e.IsImage (range (𝓡∂ n)) (range (𝓡∂ m)))
    (hes : ContDiffOn ℝ ∞ e e.source) :
    ContMDiffOn (𝓡∂ n) (𝓡∂ m) ∞ (halfSpaceRestriction e he) (halfSpaceRestriction e he).source := by
  have hI : ContMDiffOn (𝓡∂ n) (𝓡 n) ∞ (𝓡∂ n) ((𝓡∂ n) ⁻¹' e.source) :=
    fun x _ => ((𝓡∂ n).contMDiff x).contMDiffWithinAt
  apply (𝓡∂ m).contMDiffOn_symm.comp
    (hes.contMDiffOn.comp hI (fun _ hx => hx))
  intro x hx
  exact (he.apply_mem_iff hx).2 (mem_range_self _)

theorem halfSpaceRestriction_inverse_smooth
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))
    (he : e.IsImage (range (𝓡∂ n)) (range (𝓡∂ m)))
    (hes : ContDiffOn ℝ ∞ e.symm e.target) :
    ContMDiffOn (𝓡∂ m) (𝓡∂ n) ∞ (halfSpaceRestriction e he).symm (halfSpaceRestriction e he).target := by
  have hI : ContMDiffOn (𝓡∂ m) (𝓡 m) ∞ (𝓡∂ m) ((𝓡∂ m) ⁻¹' e.target) :=
    fun y _ => ((𝓡∂ m).contMDiff y).contMDiffWithinAt
  apply (𝓡∂ n).contMDiffOn_symm.comp
    (hes.contMDiffOn.comp hI (fun _ hy => hy))
  intro y hy
  exact (he.symm_apply_mem_iff hy).2 (mem_range_self _)

end SeifertSurfaces.OriginalEndpoints.A7Support
