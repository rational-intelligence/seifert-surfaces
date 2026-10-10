import A5NativeCoordinateTransport
import Mathlib.Geometry.Manifold.Immersion

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations

/-- Smoothness and rank of the actual sphere-coordinate graph give
smoothness and rank into the literal exterior manifold. The inclusion is
the original smooth embedding of the exterior, including its boundary. -/
theorem native_exterior_smooth_rank_of_coordinate_graph
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    (f : Euc 2 → E.Carrier) (U : Set (Euc 2)) (hU : IsOpen U)
    (hf : ContinuousOn f U) (c : SmoothAmbientChart ThreeSphere)
    (hchart : MapsTo (E.toSphere ∘ f) U c.chart.source)
    (hsmooth : ContDiffOn ℝ ∞ (c.chart ∘ E.toSphere ∘ f) U)
    (hrank : ∀ x ∈ U, Function.Injective
      (fderiv ℝ (c.chart ∘ E.toSphere ∘ f) x)) :
    ContMDiffOn 𝓘(ℝ, Euc 2) (𝓡∂ 3) ∞ f U ∧
    ∀ x ∈ U, Function.Injective
      (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 3) f U x) := by
  have hinc : Manifold.IsImmersion (𝓡∂ 3) (𝓡 3) ∞ E.toSphere :=
    by
      let : ChartedSpace (EuclideanHalfSpace 3) T.Carrier := E.charted
      let : IsManifold (𝓡∂ 3) ∞ T.Carrier := E.smooth
      exact E.inclusion.isImmersion
  have hsphere : ContMDiffOn 𝓘(ℝ, Euc 2) (𝓡 3) ∞ (E.toSphere ∘ f) U := by
    have hc := c.inverse_smooth.comp hsmooth.contMDiffOn
      (fun x hx => c.chart.map_source (hchart hx))
    apply hc.congr
    intro x hx
    exact (c.chart.left_inv (hchart hx)).symm
  have hn : ContMDiffOn 𝓘(ℝ, Euc 2) (𝓡∂ 3) ∞ f U := by
    intro x hx
    apply ContMDiffAt.contMDiffWithinAt
    apply (ContMDiffAt.iff_comp_isImmersionAt (hinc.isImmersionAt (f x))).mpr
    exact ⟨hf.continuousAt (hU.mem_nhds hx),
      hsphere.contMDiffAt (hU.mem_nhds hx)⟩
  refine ⟨hn, ?_⟩
  intro x hx
  have hfd := (hn.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hsd := (hsphere.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hcd := (c.smooth.contMDiffAt
    (c.chart.open_source.mem_nhds (hchart hx))).mdifferentiableAt (by simp)
  have hcoord : Function.Injective
      (mfderiv 𝓘(ℝ, Euc 2) 𝓘(ℝ, Euc 3) (c.chart ∘ E.toSphere ∘ f) x) := by
    rw [mfderiv_eq_fderiv]
    exact (NormedSpace.fromTangentSpace (c.chart (E.toSphere (f x)))).symm.injective.comp
      ((hrank x hx).comp (NormedSpace.fromTangentSpace x).injective)
  rw [mfderivWithin_eq_mfderiv (hU.uniqueMDiffWithinAt hx) hfd]
  have hcchain := mfderiv_comp x hcd hsd
  have hsformula := mfderiv_comp x (hinc.contMDiff.mdifferentiable (by simp) (f x)) hfd
  rw [hcchain, hsformula] at hcoord
  exact Function.Injective.of_comp (Function.Injective.of_comp hcoord)

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
