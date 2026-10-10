import A5InteriorNativeImageChart
import A5NativeMetricGraphRegularity

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
universe u

/-- Local graph smoothness from the metric PDE constructs an actual image
chart of the original surface. The exact graph identity keeps the source
point, ambient image, and projection fixed. -/
theorem native_interior_image_chart_of_smooth_metric_graph
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (e : OpenPartialHomeomorph S (Euc 2)) (x : S)
    (hx : x ∈ e.source) (hxboundary : x ∉ S.boundary)
    (h : AmbientMetric ThreeSphere) (G : NativeMetricGraph h)
    (P : Euc 3 →L[ℝ] Euc 2)
    (he : ∀ z ∈ e.source, e z = P (G.coordinates.chart (E.toSphere (F.map z))))
    (hchart : MapsTo (E.toSphere ∘ F.map) e.source G.coordinates.chart.source)
    (hgraph : ∀ z ∈ G.disc, e x + z ∈ e.target ∧
      graphMap G.origin G.plane G.normal G.height z =
        G.coordinates.chart (E.toSphere (F.map (e.symm (e x + z)))))
    (hsmooth : ContDiffOn ℝ ∞ G.height G.disc) :
    ∃ C : SmoothImageChart S F.map, x ∈ C.chart.source ∧ C.chart.source ⊆ e.source := by
  let V : Set (Euc 2) := {y | y - e x ∈ G.disc}
  have hV : IsOpen V := Metric.isOpen_ball.preimage (continuous_id.sub continuous_const)
  let er := (e.symm.restrOpen V hV).symm
  have hxr : x ∈ er.source := by
    refine ⟨hx, ?_⟩
    change e x - e x ∈ G.disc
    rw [sub_self]
    exact Metric.mem_ball_self G.radius_pos
  have ht (y : Euc 2) (hy : y ∈ er.target) :
      y ∈ e.target ∧ y - e x ∈ G.disc := hy
  have hg : ContDiffOn ℝ ∞ (graphMap G.origin G.plane G.normal G.height) G.disc :=
    (contDiffOn_const.add G.plane.contDiff.contDiffOn).add
      (hsmooth.smul contDiffOn_const)
  have hc : ContDiffOn ℝ ∞
      (G.coordinates.chart ∘ E.toSphere ∘ F.map ∘ er.symm) er.target := by
    have hh := hg.comp (contDiffOn_id.sub contDiffOn_const) (fun y hy => (ht y hy).2)
    apply hh.congr
    intro y hy
    have heq := (hgraph (y - e x) (ht y hy).2).2
    have hid : e x + (y - e x) = y := by abel
    rw [hid] at heq
    exact heq.symm
  obtain ⟨C, hxC, hC⟩ := native_interior_image_chart_of_smooth_projection E F er x
    hxr hxboundary G.coordinates P
    (fun z hz => he z hz.1) (fun y hy => hchart (e.map_target (ht y hy).1)) hc
  exact ⟨C, hxC, fun z hz => (hC hz).1⟩

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
