import OriginalA25SourceDefinitionsV464

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
universe u v

/-- A C1 chart of the actual surface image, with the original source boundary
carried exactly onto the flat boundary of its open half-space target. No
smoothness of the topological source coordinate map is required. -/
structure BoundaryC1ImageChart (S : CompactOrientedSurface.{u}) (M : Type v)
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] (f : S → M) where
  chart : PartialHomeomorph S (EuclideanHalfSpace 2)
  source_open : IsOpen chart.source
  target_open : IsOpen chart.target
  cOne : ContMDiffOn (𝓡∂ 2) (𝓡∂ 3) 1 (f ∘ chart.symm) chart.target
  differential_injective : ∀ y ∈ chart.target, Function.Injective
    (mfderivWithin (𝓡∂ 2) (𝓡∂ 3) (f ∘ chart.symm) chart.target y)
  boundary_image : chart '' (S.boundary ∩ chart.source) =
    ((𝓡∂ 2).boundary (EuclideanHalfSpace 2)) ∩ chart.target

/-- Proposition A.5, boundary geometry through its C1 graph conclusion:
source lines 1243–1275. The entire original minimizer context produces the
actual same-map half-space image chart, including exceptional seam endpoints.
Fan order, graph single-sheetness, the A.4 witness, and source smoothness are
construction obligations and do not appear as hypotheses. -/
theorem original_minimizer_boundary_C1_image_charts
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    (G : A7.SourceGeometry E) (J : LongitudeFoliation.{u} E)
    {S R : CompactOrientedSurface.{u}} [ConnectedSpace S]
    (F : GeometricPiecewiseSurface S E.Carrier)
    (hF_incompressible : F.Incompressible) (hF_boundary : J.BoundaryIn F.map)
    (Fprime : GeometricPiecewiseSurface R E.Carrier)
    (hminimum : FixedBoundaryMinimizer E G.metric F Fprime) :
    ∀ x ∈ R.boundary,
      ∃ C : BoundaryC1ImageChart R E.Carrier Fprime.map, x ∈ C.chart.source := by
  sorry

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
