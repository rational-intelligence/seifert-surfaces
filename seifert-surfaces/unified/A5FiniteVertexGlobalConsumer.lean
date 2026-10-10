import A5FiniteInteriorVertexRemoval
import A5GlobalSourceConsumer

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC

/-- Consume native finite interior-vertex removal and the paid global
smooth-source construction in the actual fixed-boundary minimizer context.
Both labelled boundary equalities and the exact same-image source are retained. -/
theorem minimizer_smooth_source_after_finite_vertex_removal
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S R : CompactOrientedSurface}
    (g : SmoothMetric E.Carrier) (h : AmbientMetric ThreeSphere)
    (F : GeometricPiecewiseSurface S E.Carrier)
    (Fprime : GeometricPiecewiseSurface R E.Carrier)
    (hminimum : FixedBoundaryMinimizer E g F Fprime)
    (A : Set R) (hA : A.Finite) (hAboundary : A ⊆ R.boundaryᶜ)
    (hpieces : ∀ i j, IsMinimalPatch h
      (E.toSphere ∘ sectorCoordinateMap (Fprime.map ∘ Fprime.parametrization i) j)
      (interior ((Fprime.domain i).chart j).map.target))
    (hcover : ∀ x ∉ A, ∃ C : SmoothImageChart R Fprime.map, x ∈ C.chart.source) :
    ∃ Q : GlobalSmoothSource.SmoothSourceReconstruction E Fprime,
      Q.embedding.toFun '' Q.source.boundary = F.map '' S.boundary ∧
      Fprime.image ∩ (𝓡∂ 3).boundary E.Carrier = F.map '' S.boundary := by
  exact minimizer_smooth_source_of_native_image_chart_cover g F Fprime hminimum
    (native_image_chart_cover_of_finite_interior_exceptional_set E Fprime h A hA hAboundary hpieces hcover)

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
