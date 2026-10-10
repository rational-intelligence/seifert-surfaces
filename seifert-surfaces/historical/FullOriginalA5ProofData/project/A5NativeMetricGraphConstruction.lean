import A5NativeVertexGraphLocalization
import A5MetricGraphConstruction

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC

/-- The actual native finite piece data construct the whole C¹ metric graph
at an interior vertex. No native inverse lift, common derivative field,
projected region or graph height is supplied. -/
theorem native_metric_graph_from_projection_and_tangents
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface} (F : GeometricPiecewiseSurface S E.Carrier)
    (h : SeifertSurfaces.AppendixC.AmbientMetric ThreeSphere)
    (x : S) (c : SmoothAmbientChart ThreeSphere) (P : Euc 3 →L[ℝ] Euc 2)
    (height : Euc 3 →L[ℝ] ℝ)
    (hsep : Function.Injective (fun z => (P z, height z)))
    (e : OpenPartialHomeomorph S (Euc 2)) (hx : x ∈ e.source)
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
        ((F.domain k).chart l).map.target w).toLinearMap.range) :
    ∃ e' : OpenPartialHomeomorph S E2, ∃ G : NativeMetricGraph h,
      (e' : S → E2) = e ∧ (e'.symm : E2 → S) = e.symm ∧
      x ∈ e'.source ∧ e'.source ⊆ e.source ∧
      G.coordinates = c ∧ G.origin = c.chart (E.toSphere (F.map x)) ∧
      P G.origin = e' x ∧
      (∀ v, P (G.plane v) = v) ∧ P G.normal = 0 ∧
      ∀ z ∈ Metric.closedBall 0 (2 * G.radius),
        e' x + z ∈ e'.target ∧
        graphMap G.origin G.plane G.normal G.height z =
          c.chart (E.toSphere (F.map (e'.symm (e' x + z)))) := by
  obtain ⟨e', he', hei', hx', hsub, hf⟩ :=
    native_projection_graph_C1_after_restriction E F x c P e hx he hmaps htrans htangent
  let f := c.chart ∘ E.toSphere ∘ F.map ∘ e'.symm
  have hmaps' : MapsTo (E.toSphere ∘ F.map) e'.source c.chart.source :=
    fun y hy => hmaps (hsub hy)
  have heq (y : S) : e' y = P (c.chart (E.toSphere (F.map y))) := by
    rw [he']
    exact he y
  have hsection (y : E2) (hy : y ∈ e'.target) : P (f y) = y := by
    change P (c.chart (E.toSphere (F.map (e'.symm y)))) = y
    rw [← heq, e'.right_inv hy]
  have hchart : MapsTo f e'.target c.chart.target :=
    fun y hy => c.chart.map_source (hmaps' (e'.map_target hy))
  obtain ⟨G, hGc, hGo, hplane, hn, _, _, hG⟩ :=
    native_metric_graph_of_C1_section h c e'.target e'.open_target (e' x)
      (e'.map_source hx') f hf hchart P height hsep hsection
  have hcenter : f (e' x) = c.chart (E.toSphere (F.map x)) := by
    dsimp [f]
    rw [e'.left_inv hx']
  refine ⟨e', G, he', hei', hx', hsub, hGc, hGo.trans hcenter, ?_,
    fun v => (hplane v).1, hn, hG⟩
  rw [hGo]
  exact hsection _ (e'.map_source hx')

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
