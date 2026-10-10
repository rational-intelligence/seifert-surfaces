import OriginalA25SourceDefinitionsV464
import A5PaidBoundaryGeometryCompatibility

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
universe u
variable {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)

/-- Original Proposition A.5, full fixed-boundary regularity and stability.
No smooth representative, graph, arc-removal, vertex-removal or stationarity
certificate is input. The original surface F' is only geometric piecewise smooth. -/
theorem A5_original (G : A7.SourceGeometry E) (J : LongitudeFoliation.{u} E)
    {S R : CompactOrientedSurface.{u}} [ConnectedSpace S]
    (F : GeometricPiecewiseSurface S E.Carrier)
    (hF_incompressible : F.Incompressible) (hF_boundary : J.BoundaryIn F.map)
    (Fprime : GeometricPiecewiseSurface R E.Carrier)
    (hminimum : FixedBoundaryMinimizer E G.metric F Fprime) :
    Nonempty (SmoothStableMinimalImage.{u} E G Fprime.image
      (F.map '' S.boundary)) := by
  exact original_A5_certificate_of_native_boundary_C1_image_charts
    E G J F hF_incompressible hF_boundary Fprime hminimum
    (original_minimizer_boundary_C1_image_charts
      E G J F hF_incompressible hF_boundary Fprime hminimum)

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
