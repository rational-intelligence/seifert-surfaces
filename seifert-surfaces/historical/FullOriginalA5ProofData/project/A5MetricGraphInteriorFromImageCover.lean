import A5NativeGraphSmoothFromCharts
import A5NativeSmoothImageMinimality
import A5NativeBoundaryMetricEquation

set_option autoImplicit false
set_option maxHeartbeats 1500000
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
universe u

/-- The paid smooth native image cover and native piece minimality imply
the actual smooth minimal graph equation on an arbitrary open portion of
a C1 projection graph. This also applies to the open half-disc inside a
straightened boundary graph. -/
theorem native_metric_graph_smooth_minimal_of_image_cover
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (h : AmbientMetric ThreeSphere) (G : NativeMetricGraph h)
    (e : OpenPartialHomeomorph S E2) (P : E3 →L[ℝ] E2)
    (he : ∀ x ∈ e.source, e x = P (G.coordinates.chart (E.toSphere (F.map x))))
    (hmaps : MapsTo (E.toSphere ∘ F.map) e.source G.coordinates.chart.source)
    (U : Set E2) (hU : IsOpen U) (hUe : U ⊆ e.target) (hUG : U ⊆ G.disc)
    (hgraph : ∀ z ∈ U, graphMap G.origin G.plane G.normal G.height z =
      G.coordinates.chart (E.toSphere (F.map (e.symm z))))
    (hboundary : ∀ z ∈ U, e.symm z ∉ S.boundary)
    (hcover : ∀ z ∈ U, ∃ C : SmoothImageChart S F.map, e.symm z ∈ C.chart.source)
    (hpieces : ∀ i j, IsMinimalPatch h
      (E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j)
      (interior ((F.domain i).chart j).map.target)) :
    ContDiffOn ℝ ∞ G.height U ∧
    IsMinimalParametrizationOn (actualChartTensor h G.coordinates)
      (graphMap G.origin G.plane G.normal G.height) U := by
  let Φ := G.coordinates.chart ∘ E.toSphere ∘ F.map ∘ e.symm
  have hC1 : ContDiffOn ℝ 1 Φ U := by
    have hh : ContDiffOn ℝ 1 (graphMap G.origin G.plane G.normal G.height) U :=
      (contDiffOn_const.add G.plane.contDiff.contDiffOn).add
        ((G.height_C1_disc.mono hUG).smul contDiffOn_const)
    exact hh.congr (fun z hz => (hgraph z hz).symm)
  have hs : ContDiffOn ℝ ∞ Φ U := native_projection_smooth_of_image_chart_cover
    E F e G.coordinates P he hmaps U hU hUe hC1 hboundary hcover
  have hrank : ∀ z ∈ U, Function.Injective (fderiv ℝ Φ z) := by
    intro z hz
    have hf := (hs.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
    have hproj : P ∘ Φ =ᶠ[𝓝 z] id := by
      filter_upwards [hU.mem_nhds hz] with y hy
      change P (G.coordinates.chart (E.toSphere (F.map (e.symm y)))) = y
      rw [← he _ (e.map_target (hUe hy)),e.right_inv (hUe hy)]
    have hi : Function.Injective (P.comp (fderiv ℝ Φ z)) := by
      rw [← (P.hasFDerivAt.comp z hf.hasFDerivAt).fderiv,hproj.fderiv_eq,fderiv_id]
      exact Function.injective_id
    exact Function.Injective.of_comp hi
  obtain ⟨hex,hexr⟩ := native_exterior_smooth_rank_of_coordinate_graph E (F.map ∘ e.symm)
    U hU (F.map.continuous.comp_continuousOn (e.symm.continuousOn.mono hUe))
    G.coordinates (fun z hz => hmaps (e.map_target (hUe hz))) hs hrank
  have hmin := native_smooth_image_chart_minimal_of_pieces E F h e U hU hUe hex
    (fun z hz => by
      have hh := hexr z hz
      rwa [mfderivWithin_of_mem_nhds (hU.mem_nhds hz)] at hh) hpieces
  have hmΦ : IsMinimalParametrizationOn (actualChartTensor h G.coordinates) Φ U :=
    ⟨(hmin.2.2 G.coordinates).1.mono (fun z hz => ⟨hz,hmaps (e.map_target (hUe hz))⟩),
      fun z hz => (hmin.2.2 G.coordinates).2 z ⟨hz,hmaps (e.map_target (hUe hz))⟩⟩
  have hm := coordinate_minimality_congr (actualChartTensor h G.coordinates) Φ
    (graphMap G.origin G.plane G.normal G.height) U hU hmΦ
    (fun z hz => hgraph z hz)
  exact ⟨native_graph_height_smooth_of_graph_smooth G U hm.1,hm⟩

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
