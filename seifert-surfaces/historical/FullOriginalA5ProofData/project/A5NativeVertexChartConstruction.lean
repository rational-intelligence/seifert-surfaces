import A5NativeMetricGraphConstruction
import A5NativePuncturedGraph

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC

/-- Complete native interior vertex removal from the punctured image-chart
cover and actual finite-piece tangent data. The C¹ graph, punctured smooth
height, dense minimality, weak equation and point removal are all constructed. -/
theorem native_vertex_chart_from_punctured_image_charts
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface} (F : GeometricPiecewiseSurface S E.Carrier)
    (h : SeifertSurfaces.AppendixC.AmbientMetric ThreeSphere)
    (x : S) (c : SmoothAmbientChart ThreeSphere) (P : Euc 3 →L[ℝ] Euc 2)
    (height : Euc 3 →L[ℝ] ℝ)
    (hsep : Function.Injective (fun z => (P z, height z)))
    (e : OpenPartialHomeomorph S (Euc 2)) (hx : x ∈ e.source)
    (hxboundary : x ∉ S.boundary)
    (he : ∀ z, e z = P (c.chart (E.toSphere (F.map z))))
    (hmaps : MapsTo (E.toSphere ∘ F.map) e.source c.chart.source)
    (htrans : ∀ i j z, z ∈ ((F.domain i).chart j).map.target →
      F.parametrization i (((F.domain i).chart j).map.symm z) ∈ e.source →
      Function.Bijective (P.comp (fderivWithin ℝ
        (c.chart ∘ E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j)
        ((F.domain i).chart j).map.target z)))
    (htangent : ∀ i j k l z w,
      z ∈ ((F.domain i).chart j).map.target → w ∈ ((F.domain k).chart l).map.target →
      F.parametrization i (((F.domain i).chart j).map.symm z) =
        F.parametrization k (((F.domain k).chart l).map.symm w) →
      F.parametrization i (((F.domain i).chart j).map.symm z) ∈ e.source →
      F.parametrization i (((F.domain i).chart j).map.symm z) ≠ x →
      (fderivWithin ℝ
        (c.chart ∘ E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j)
        ((F.domain i).chart j).map.target z).toLinearMap.range =
      (fderivWithin ℝ
        (c.chart ∘ E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization k) l)
        ((F.domain k).chart l).map.target w).toLinearMap.range)
    (hpieces : ∀ i j, IsMinimalPatch h
      (E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j)
      (interior ((F.domain i).chart j).map.target))
    (hcover : ∀ z ∈ e.source, z ≠ x →
      ∃ C : SmoothImageChart S F.map, z ∈ C.chart.source) :
    ∃ C : SmoothImageChart S F.map, x ∈ C.chart.source ∧ C.chart.source ⊆ e.source := by
  have hb : IsClosed S.boundary := (𝓡∂ 2).isClosed_boundary (n := ∞) (by simp)
  let er := e.restrOpen S.boundaryᶜ hb.isOpen_compl
  have hxr : x ∈ er.source := ⟨hx, hxboundary⟩
  obtain ⟨e', G, he', _, hx', hsub, hGc, _, hGo, _, _, hg⟩ :=
    native_metric_graph_from_projection_and_tangents E F h x c P height hsep er hxr
      he (fun y hy => hmaps hy.1)
      (fun i j z hz hzs => htrans i j z hz hzs.1)
      (fun i j k l z w hz hw heq hzs hne => htangent i j k l z w hz hw heq hzs.1 hne)
  have hhe : ∀ y ∈ e'.source, e' y = P (G.coordinates.chart (E.toSphere (F.map y))) := by
    intro y _
    rw [hGc, he']
    exact he y
  have hmapG : MapsTo (E.toSphere ∘ F.map) e'.source G.coordinates.chart.source := by
    rw [hGc]
    exact fun y hy => hmaps (hsub hy).1
  have hgraph : ∀ z ∈ G.disc, e' x + z ∈ e'.target ∧
      graphMap G.origin G.plane G.normal G.height z =
        G.coordinates.chart (E.toSphere (F.map (e'.symm (e' x + z)))) := by
    intro z hz
    have hh : z ∈ Metric.closedBall 0 (2 * G.radius) := by
      have hd : dist z 0 < G.radius := hz
      change dist z 0 ≤ 2 * G.radius
      linarith [G.radius_pos]
    simpa only [hGc] using hg z hh
  have hpunc := native_metric_graph_smooth_puncture_of_image_chart_cover E F h G e' x P
    hhe hmapG (fun y hy => (hsub hy).2) hgraph
    (fun y hy hne => hcover y (hsub hy).1 hne)
  obtain ⟨_, _, C, hxC, hC⟩ := native_vertex_image_chart_of_punctured_smoothness E F h G
    e' x hx' hxboundary P hhe hGo hmapG hpieces
    (fun i j z hz hzs => by
      rw [hGc]
      exact htrans i j z (interior_subset hz) (hsub hzs).1) hgraph hpunc
  exact ⟨C, hxC, fun y hy => (hsub (hC hy)).1⟩

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
