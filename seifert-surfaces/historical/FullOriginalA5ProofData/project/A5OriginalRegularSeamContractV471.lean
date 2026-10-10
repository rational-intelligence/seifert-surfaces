import A5RegularArcProducerV472
import A5RegularCircleProducerV472

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
universe u

/-- Full ordinary arc/circle seam regularity under the unchanged original A5
context. The exact paid A2 theorem is a dependency, not an added premise. -/
theorem original_minimizer_regular_seam_image_charts
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    (G : A7.SourceGeometry E) (J : LongitudeFoliation.{u} E)
    {S R : CompactOrientedSurface.{u}} [ConnectedSpace S]
    (F : GeometricPiecewiseSurface S E.Carrier)
    (hF_incompressible : F.Incompressible) (hF_boundary : J.BoundaryIn F.map)
    (Fprime : GeometricPiecewiseSurface R E.Carrier)
    (hminimum : FixedBoundaryMinimizer E G.metric F Fprime) :
    (∀ (a : Fin Fprime.seam.arcCount) (s : Time), 0 < s → s < 1 →
      ∃ C : SmoothImageChart R Fprime.map, Fprime.seam.arc a s ∈ C.chart.source) ∧
    (∀ (a : Fin Fprime.seam.circleCount) (s : Circle),
      ∃ C : SmoothImageChart R Fprime.map, Fprime.seam.circle a s ∈ C.chart.source) := by
  have hA2 := A2_original E G J F hF_incompressible hF_boundary Fprime hminimum
  refine ⟨?_,?_⟩
  · intro a s hs0 hs1
    exact original_stationary_regular_arc_image_chart E G Fprime hA2.1 hA2.2.1 a s hs0 hs1
  · intro a s
    exact original_stationary_regular_circle_image_chart E G Fprime hA2.1 hA2.2.1 a s

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
