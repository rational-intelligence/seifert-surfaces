import A5NativeStabilityConsumer
import A5NearbyCompetitorsV472

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
universe u

/-- A joint smooth deformation of the reconstructed embedding gives nearby
competitors in the FULL original geometric class, including its anchored
C1 rank-three GeometricTrack and both geometric source morphisms. -/
theorem reconstructed_smooth_family_nearby_original_competitors
    {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
    {S R : CompactOrientedSurface.{u}} {g : SmoothMetric E.Carrier}
    {F : GeometricPiecewiseSurface S E.Carrier}
    {Fprime : GeometricPiecewiseSurface R E.Carrier}
    (hminimum : FixedBoundaryMinimizer E g F Fprime)
    (Q : GlobalSmoothSource.SmoothSourceReconstruction E Fprime)
    (H : ℝ → ProperSmoothEmbedding Q.source E.Carrier)
    (hzero : (H 0).toFun = Q.embedding.toFun)
    (hsmooth : ContMDiff (𝓘(ℝ).prod (𝓡∂ 2)) (𝓡∂ 3) ∞
      (fun p : ℝ × Q.source => (H p.1).toFun p.2))
    (hboundary : ∀ t x, x ∈ Q.source.boundary →
      (H t).toFun x = Q.embedding.toFun x) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∃ C : GeometricPiecewiseSurface Q.source E.Carrier,
      C.map = (H t).continuousMap ∧ FixedBoundaryImageIsotopic E F C := by
  exact Filter.Eventually.of_forall
    (NearbyDeformations.reconstructed_smooth_family_all_original_competitors
      hminimum Q H hzero hsmooth hboundary)

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
