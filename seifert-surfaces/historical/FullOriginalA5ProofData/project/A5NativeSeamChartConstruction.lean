import A5NativeMetricGraphConstruction
import A5NativeSeamImageChart
import A5GraphRadiusLocalization

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC CurvedDivergence

/-- Native finite pieces and tangent agreement construct the C¹ graph,
then actual piece minimality removes the curved seam and gives an image chart.
The graph and signed arc are localized to a common positive radius internally. -/
theorem native_seam_chart_from_projection_and_tangents
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
    (ρ : ℝ) (hρ : 0 < ρ) (s : E2 → ℝ) (γ : ℝ → E2) (left right : ℝ)
    (hgeom : SignedArcGeometry (Metric.ball 0 ρ) s γ left right)
    (hseam : ∀ y ∈ Metric.ball 0 ρ, e x + y ∈ e.target →
      e.symm (e x + y) ∈ F.seam.carrier ∪ S.boundary → s y = 0) :
    ∃ C : SmoothImageChart S F.map, x ∈ C.chart.source ∧ C.chart.source ⊆ e.source := by
  obtain ⟨e', G, he', hei', hx', hsub, hGc, _, hGo, _, _, hgraph⟩ :=
    native_metric_graph_from_projection_and_tangents E F h x c P height hsep e hx
      he hmaps htrans htangent
  let r := min G.radius ρ
  have hr : 0 < r := lt_min G.radius_pos hρ
  let H := G.restrictRadius r hr (min_le_left _ _)
  have hHG : H.disc ⊆ Metric.closedBall 0 (2 * G.radius) := by
    intro y hy
    have hh : dist y 0 < r := hy
    change dist y 0 ≤ 2 * G.radius
    have hh' : r ≤ G.radius := min_le_left _ _
    linarith [G.radius_pos]
  have hHρ : H.disc ⊆ Metric.ball 0 ρ := Metric.ball_subset_ball (min_le_right _ _)
  have hHc : H.coordinates = c := hGc
  have hhe : ∀ y ∈ e'.source, e' y = P (H.coordinates.chart (E.toSphere (F.map y))) := by
    intro y _
    rw [hHc, he']
    exact he y
  have hmapH : MapsTo (E.toSphere ∘ F.map) e'.source H.coordinates.chart.source := by
    rw [hHc]
    exact fun y hy => hmaps (hsub hy)
  have hgH : ∀ y ∈ H.disc, e' x + y ∈ e'.target ∧
      graphMap H.origin H.plane H.normal H.height y =
        H.coordinates.chart (E.toSphere (F.map (e'.symm (e' x + y)))) := by
    intro y hy
    simpa only [H, NativeMetricGraph.restrictRadius, hGc] using hgraph y (hHG hy)
  obtain ⟨_, _, C, hxC, hC⟩ := native_seam_image_chart_and_graph_minimality E F h H
    e' x hx' hxboundary P hhe hGo hmapH hpieces
    (fun i j z hz hzs => by
      rw [hHc]
      exact htrans i j z (interior_subset hz) (hsub hzs)) hgH s γ left right
    (signed_arc_geometry_restrict hgeom Metric.isOpen_ball hHρ) (by
      intro y hy hs
      have hexy : e' x = e x := congrFun he' x
      have hty : e x + y ∈ e.target := by
        have hh := e.map_source (hsub (e'.map_target (hgH y hy).1))
        have heq : e (e'.symm (e' x + y)) = e' x + y := by
          rw [← congrFun he' _, e'.right_inv (hgH y hy).1]
        rwa [heq, hexy] at hh
      apply hseam y (hHρ hy) hty
      simpa only [hei', hexy] using hs)
  exact ⟨C, hxC, hC.trans hsub⟩

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
