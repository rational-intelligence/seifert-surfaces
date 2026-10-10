import A5NativeOffSeamGraph
import A5NativeArcMinimality

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC CurvedDivergence
universe u

/-- Native piece minimality and the actual signed seam geometry produce
the original image's smooth chart and metric minimality. All open-side
charts, coordinate lifts, elliptic operators, weak equations and regularity
steps are constructed internally. -/
theorem native_seam_image_chart_and_graph_minimality
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
    (s : E2 → ℝ) (γ : ℝ → E2) (left right : ℝ)
    (hgeom : SignedArcGeometry G.disc s γ left right)
    (hseam : ∀ y ∈ G.disc, e.symm (e x + y) ∈ F.seam.carrier ∪ S.boundary → s y = 0) :
    ContDiffOn ℝ ∞ G.height G.disc ∧
    IsMinimalParametrizationOn (actualChartTensor h G.coordinates)
      (graphMap G.origin G.plane G.normal G.height) G.disc ∧
    ∃ C : SmoothImageChart S F.map, x ∈ C.chart.source ∧ C.chart.source ⊆ e.source := by
  have hside (p : Bool) :
      ContDiffOn ℝ ∞ G.height (signedDomain G.disc s p) ∧
      IsMinimalParametrizationOn (actualChartTensor h G.coordinates)
        (graphMap G.origin G.plane G.normal G.height) (signedDomain G.disc s p) := by
    have ho : IsOpen (signedDomain G.disc s p) := by
      cases p
      · exact hgeom.signed_smooth.continuousOn.isOpen_inter_preimage hgeom.disc_open isOpen_Iio
      · exact hgeom.signed_smooth.continuousOn.isOpen_inter_preimage hgeom.disc_open isOpen_Ioi
    apply native_graph_smooth_minimal_off_seam E F h G e P (e x) he ha hmaps hpieces htrans
      (signedDomain G.disc s p) ho (fun y hy => (hgraph y hy.1).1) _
      (fun y hy => (hgraph y hy.1).2)
    intro y hy hm
    have hz := hseam y hy.1 hm
    cases p
    · exact (ne_of_lt hy.2) hz
    · exact (ne_of_gt hy.2) hz
  obtain ⟨hs, hm⟩ := native_metric_graph_smooth_minimal_across_arc G s γ left right hgeom
    (fun p => (hside p).1) (fun p => (hside p).2)
  exact ⟨hs, hm, native_interior_image_chart_of_smooth_metric_graph E F e x hx hxboundary
    h G P he hmaps hgraph hs⟩

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
