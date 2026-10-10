import A5GlobalSmoothSourceV466
import A5MinimizerConsequences

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
universe u
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}

/-- Consume the sealed global smooth-source producer in the actual original
minimizer context. The labelled boundary is that of the initial surface,
and the original pointwise source homeomorphism is retained. -/
theorem minimizer_smooth_source_of_native_image_chart_cover
    {S R : CompactOrientedSurface.{u}}
    (g : SmoothMetric E.Carrier)
    (F : GeometricPiecewiseSurface S E.Carrier)
    (Fprime : GeometricPiecewiseSurface R E.Carrier)
    (hminimum : FixedBoundaryMinimizer E g F Fprime)
    (hcover : ∀ x : R, ∃ c : SmoothImageChart R Fprime.map, x ∈ c.chart.source) :
    ∃ Q : GlobalSmoothSource.SmoothSourceReconstruction E Fprime,
      Q.embedding.toFun '' Q.source.boundary = F.map '' S.boundary ∧
      Fprime.image ∩ (𝓡∂ 3).boundary E.Carrier = F.map '' S.boundary := by
  obtain ⟨Q⟩ := GlobalSmoothSource.smooth_source_of_native_image_chart_cover E Fprime hcover
  exact ⟨Q, Q.boundary_image_eq.trans hminimum.in_class.boundary_image_eq,
    hminimum.ambient_boundary_eq⟩

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
