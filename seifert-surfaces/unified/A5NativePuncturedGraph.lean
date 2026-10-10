import A5NativeGraphSmoothFromCharts
import A5NativeVertexImageChart

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
universe u

/-- The punctured source image-chart cover supplies the punctured smooth
height of the actual metric graph. No regularity of the auxiliary source
coordinates is assumed. -/
theorem native_metric_graph_smooth_puncture_of_image_chart_cover
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (h : AmbientMetric ThreeSphere) (G : NativeMetricGraph h)
    (e : OpenPartialHomeomorph S E2) (x : S)
    (P : E3 →L[ℝ] E2)
    (he : ∀ z ∈ e.source, e z = P (G.coordinates.chart (E.toSphere (F.map z))))
    (hmaps : MapsTo (E.toSphere ∘ F.map) e.source G.coordinates.chart.source)
    (hboundary : e.source ⊆ S.boundaryᶜ)
    (hgraph : ∀ z ∈ G.disc, e x + z ∈ e.target ∧
      graphMap G.origin G.plane G.normal G.height z =
        G.coordinates.chart (E.toSphere (F.map (e.symm (e x + z)))))
    (hcover : ∀ z ∈ e.source, z ≠ x →
      ∃ C : SmoothImageChart S F.map, z ∈ C.chart.source) :
    ContDiffOn ℝ ∞ G.height (G.disc \ {0}) := by
  let U : Set E2 := {y | y - e x ∈ G.disc \ {0}}
  have hU : IsOpen U := (Metric.isOpen_ball.sdiff isClosed_singleton).preimage
    (continuous_id.sub continuous_const)
  have hsub (y : E2) (hy : y ∈ U) : y ∈ e.target := by
    have hh := (hgraph (y - e x) hy.1).1
    have hid : e x + (y - e x) = y := by abel
    rwa [hid] at hh
  have hC1graph : ContDiffOn ℝ 1 (graphMap G.origin G.plane G.normal G.height) G.disc :=
    (contDiffOn_const.add G.plane.contDiff.contDiffOn).add
      ((G.height_C1.mono (by
        intro z hz
        have hh : dist z 0 < G.radius := hz
        change dist z 0 ≤ 2 * G.radius
        linarith [G.radius_pos])).smul_const G.normal)
  have hC1 : ContDiffOn ℝ 1
      (G.coordinates.chart ∘ E.toSphere ∘ F.map ∘ e.symm) U := by
    apply (hC1graph.comp (contDiffOn_id.sub contDiffOn_const) (fun y hy => hy.1)).congr
    intro y hy
    have hh := (hgraph (y - e x) hy.1).2
    have hid : e x + (y - e x) = y := by abel
    rw [hid] at hh
    exact hh.symm
  have hs := native_projection_smooth_of_image_chart_cover E F e G.coordinates P he hmaps U hU
    (fun y hy => hsub y hy) hC1 (fun y hy => hboundary (e.map_target (hsub y hy))) (by
      intro y hy
      apply hcover (e.symm y) (e.map_target (hsub y hy))
      intro heq
      have hye : y = e x := by rw [← e.right_inv (hsub y hy), heq]
      exact hy.2 (by rw [hye, sub_self]; exact mem_singleton 0))
  apply native_graph_height_smooth_of_graph_smooth G (G.disc \ {0})
  have hshift : MapsTo (fun y : E2 => e x + y) (G.disc \ {0}) U := by
    intro y hy
    change e x + y - e x ∈ G.disc \ {0}
    rwa [add_sub_cancel_left]
  apply (hs.comp (contDiffOn_const.add contDiffOn_id) hshift).congr
  intro y hy
  exact (hgraph y hy.1).2

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
