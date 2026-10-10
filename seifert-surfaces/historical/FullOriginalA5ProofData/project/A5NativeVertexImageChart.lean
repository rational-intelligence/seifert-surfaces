import A5NativeMinimalityOnOpenGraph
import A5NativeGraphImageChart

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
universe u

/-- Punctured native graph smoothness and actual whole-piece minimality
produce a smooth minimal graph and the original source's image chart at
the vertex. Punctured graph minimality and its weak equation are derived. -/
theorem native_vertex_image_chart_of_punctured_smoothness
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (h : AmbientMetric ThreeSphere) (G : NativeMetricGraph h)
    (e : OpenPartialHomeomorph S E2) (x : S)
    (hx : x ∈ e.source) (hxboundary : x ∉ S.boundary)
    (P : E3 →L[ℝ] E2)
    (he : ∀ y ∈ e.source, e y = P (G.coordinates.chart (E.toSphere (F.map y))))
    (ha : P G.origin = e x)
    (hmaps : MapsTo (E.toSphere ∘ F.map) e.source G.coordinates.chart.source)
    (hpieces : ∀ i j, IsMinimalPatch h
      (E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j)
      (interior ((F.domain i).chart j).map.target))
    (htrans : ∀ i j z, z ∈ interior ((F.domain i).chart j).map.target →
      F.parametrization i (((F.domain i).chart j).map.symm z) ∈ e.source →
      Function.Bijective (P.comp (fderivWithin ℝ
        (G.coordinates.chart ∘ E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j)
        ((F.domain i).chart j).map.target z)))
    (hgraph : ∀ z ∈ G.disc, e x + z ∈ e.target ∧
      graphMap G.origin G.plane G.normal G.height z =
        G.coordinates.chart (E.toSphere (F.map (e.symm (e x + z)))))

    (hsmooth : ContDiffOn ℝ ∞ G.height (G.disc \ {0})) :
    ContDiffOn ℝ ∞ G.height G.disc ∧
    IsMinimalParametrizationOn (actualChartTensor h G.coordinates)
      (graphMap G.origin G.plane G.normal G.height) G.disc ∧
    ∃ C : SmoothImageChart S F.map, x ∈ C.chart.source ∧ C.chart.source ⊆ e.source := by
  have hU : IsOpen (G.disc \ {0}) := Metric.isOpen_ball.sdiff isClosed_singleton
  have hmin := native_metric_graph_minimal_on_open_of_pieces E F h G e P (e x)
    he ha hmaps hpieces htrans (G.disc \ {0}) hU sdiff_subset
    (fun y hy => (hgraph y hy.1).1) (fun y hy => (hgraph y hy.1).2) hsmooth
  obtain ⟨hs, hm⟩ := native_metric_graph_smooth_minimal_of_punctured_minimal G 0
    (Metric.mem_ball_self G.radius_pos) hsmooth hmin
  exact ⟨hs, hm, native_interior_image_chart_of_smooth_metric_graph E F e x hx hxboundary
    h G P he hmaps hgraph hs⟩

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
