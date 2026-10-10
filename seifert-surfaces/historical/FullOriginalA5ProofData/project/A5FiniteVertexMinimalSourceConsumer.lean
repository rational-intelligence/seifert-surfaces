import A5FiniteVertexGlobalConsumer
import A5GlobalSourceMinimality

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
universe u

/-- Same-image smooth minimal source and the full original labelled
boundary, after finite interior-vertex removal. All minimality is deduced
from the native pieces in the original metric extension. -/
theorem minimizer_smooth_minimal_source_after_finite_vertex_removal
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    (G : A7.SourceGeometry E) {S R : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier)
    (Fprime : GeometricPiecewiseSurface R E.Carrier)
    (hminimum : FixedBoundaryMinimizer E G.metric F Fprime)
    (A : Set R) (hA : A.Finite) (hAboundary : A ⊆ R.boundaryᶜ)
    (hpieces : ∀ i j, IsMinimalPatch G.extension
      (E.toSphere ∘ sectorCoordinateMap (Fprime.map ∘ Fprime.parametrization i) j)
      (interior ((Fprime.domain i).chart j).map.target))
    (hcover : ∀ x ∉ A, ∃ C : SmoothImageChart R Fprime.map, x ∈ C.chart.source) :
    ∃ Q : GlobalSmoothSource.SmoothSourceReconstruction E Fprime,
      MinimalEmbedding E G Q.embedding ∧
      Q.embedding.toFun '' Q.source.boundary = F.map '' S.boundary ∧
      Fprime.image ∩ (𝓡∂ 3).boundary E.Carrier = F.map '' S.boundary := by
  obtain ⟨Q, hboundary, hambient⟩ := minimizer_smooth_source_after_finite_vertex_removal
    E G.metric G.extension F Fprime hminimum A hA hAboundary hpieces hcover
  exact ⟨Q, smooth_source_reconstruction_minimal_of_pieces E G Fprime Q hpieces, hboundary, hambient⟩

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
