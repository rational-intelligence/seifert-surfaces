import A5RegularSeamAssemblyV472

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC CurvedDivergence
universe u

/-- Chart independence at a literally equal source point. -/
theorem native_piece_tangent_ranges_at_equal_source
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j k : Fin (F.domain i).count) (y z : E2)
    (hy : y ∈ ((F.domain i).chart j).map.target)
    (hz : z ∈ ((F.domain i).chart k).map.target)
    (heq : F.parametrization i (((F.domain i).chart j).map.symm y) =
      F.parametrization i (((F.domain i).chart k).map.symm z))
    (c : SmoothAmbientChart ThreeSphere)
    (hc : pieceSphereCoordinate E F i j y ∈ c.chart.source) :
    (fderivWithin ℝ (c.chart ∘ pieceSphereCoordinate E F i j)
      ((F.domain i).chart j).map.target y).toLinearMap.range =
    (fderivWithin ℝ (c.chart ∘ pieceSphereCoordinate E F i k)
      ((F.domain i).chart k).map.target z).toLinearMap.range := by
  let a := ((F.domain i).chart j).map.symm y
  have haj : a ∈ ((F.domain i).chart j).map.source := ((F.domain i).chart j).map.map_target hy
  have haeq : ((F.domain i).chart k).map.symm z = a :=
    (F.parametrization_embedding i).injective heq.symm
  have hak : a ∈ ((F.domain i).chart k).map.source := haeq ▸ ((F.domain i).chart k).map.map_target hz
  have hay : ((F.domain i).chart j).map a = y := ((F.domain i).chart j).map.right_inv hy
  have haz : ((F.domain i).chart k).map a = z := by
    rw [← haeq]
    exact ((F.domain i).chart k).map.right_inv hz
  have hh := native_piece_tangent_ranges_eq E F i j k a haj hak c hc
  simpa only [hay,haz,pieceSphereCoordinate,sectorCoordinateMap,Function.comp_def] using hh

/-- Exact two-sheet incidence along the actual trace, together with equal
sheet tangent planes, supplies agreement for all native charts nearby.
Off the trace the original smooth-off-seam image charts supply agreement. -/
theorem native_tangent_ranges_of_exact_pair_incidence
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin 2 → Fin F.pieceCount) (j : ∀ k, Fin (F.domain (i k)).count)
    (trace : SeamLocalTime → S) (q : Fin 2 → SeamLocalTime → E2)
    (hq : ∀ k t, q k t ∈ ((F.domain (i k)).chart (j k)).map.target)
    (hpoint : ∀ k t, F.parametrization (i k) (((F.domain (i k)).chart (j k)).map.symm (q k t)) = trace t)
    (hincident : ∀ t v, trace t ∈ range (F.parametrization v) ↔ v = i 0 ∨ v = i 1)
    (V : Set S) (hVboundary : V ⊆ S.boundaryᶜ)
    (htrace : ∀ z ∈ V, z ∈ F.seam.carrier → ∃ t, trace t = z)
    (c : SmoothAmbientChart ThreeSphere)
    (hpairs : ∀ t, E.toSphere (F.map (trace t)) ∈ c.chart.source →
      (fderivWithin ℝ (c.chart ∘ pieceSphereCoordinate E F (i 0) (j 0))
        ((F.domain (i 0)).chart (j 0)).map.target (q 0 t)).toLinearMap.range =
      (fderivWithin ℝ (c.chart ∘ pieceSphereCoordinate E F (i 1) (j 1))
        ((F.domain (i 1)).chart (j 1)).map.target (q 1 t)).toLinearMap.range) :
    ∀ v a w b y z, y ∈ ((F.domain v).chart a).map.target →
      z ∈ ((F.domain w).chart b).map.target →
      F.parametrization v (((F.domain v).chart a).map.symm y) =
        F.parametrization w (((F.domain w).chart b).map.symm z) →
      F.parametrization v (((F.domain v).chart a).map.symm y) ∈ V →
      pieceSphereCoordinate E F v a y ∈ c.chart.source →
      (fderivWithin ℝ (c.chart ∘ pieceSphereCoordinate E F v a)
        ((F.domain v).chart a).map.target y).toLinearMap.range =
      (fderivWithin ℝ (c.chart ∘ pieceSphereCoordinate E F w b)
        ((F.domain w).chart b).map.target z).toLinearMap.range := by
  intro v a w b y z hy hz heq hyV hc
  let p := F.parametrization v (((F.domain v).chart a).map.symm y)
  by_cases hs : p ∈ F.seam.carrier
  · obtain ⟨t,ht⟩ := htrace p hyV hs
    have hct : E.toSphere (F.map (trace t)) ∈ c.chart.source := ht.symm ▸ hc
    have hrange : ∀ v a y, y ∈ ((F.domain v).chart a).map.target →
        F.parametrization v (((F.domain v).chart a).map.symm y) = trace t →
        (fderivWithin ℝ (c.chart ∘ pieceSphereCoordinate E F v a)
          ((F.domain v).chart a).map.target y).toLinearMap.range =
        (fderivWithin ℝ (c.chart ∘ pieceSphereCoordinate E F (i 0) (j 0))
          ((F.domain (i 0)).chart (j 0)).map.target (q 0 t)).toLinearMap.range := by
      intro v a y hy he
      have hv : trace t ∈ range (F.parametrization v) := ⟨_,he⟩
      rcases (hincident t v).mp hv with hv0 | hv1
      · subst v
        exact native_piece_tangent_ranges_at_equal_source E F (i 0) a (j 0) y (q 0 t)
          hy (hq 0 t) (he.trans (hpoint 0 t).symm) c (by change E.toSphere (F.map (F.parametrization _ _)) ∈ _; rw [he]; exact hct)
      · subst v
        exact (native_piece_tangent_ranges_at_equal_source E F (i 1) a (j 1) y (q 1 t)
          hy (hq 1 t) (he.trans (hpoint 1 t).symm) c (by change E.toSphere (F.map (F.parametrization _ _)) ∈ _; rw [he]; exact hct)).trans (hpairs t hct).symm
    exact (hrange v a y hy ht.symm).trans (hrange w b z hz (heq.symm.trans ht.symm)).symm
  · obtain ⟨C,hpC,_⟩ := F.smooth_off_seam p hs
    obtain ⟨d,hpd,_,hds,hdr⟩ := native_image_chart_plane_parametrization S F.map C p hpC (hVboundary hyV)
    have h1 := native_sector_tangent_matches_smooth_plane_chart E F d hds hdr v a y hy hpd c hc
    have hwD : F.parametrization w (((F.domain w).chart b).map.symm z) ∈ d.source := heq ▸ hpd
    have hwc : pieceSphereCoordinate E F w b z ∈ c.chart.source := by
      change E.toSphere (F.map (F.parametrization w _)) ∈ _
      rw [← heq]
      exact hc
    have h2 := native_sector_tangent_matches_smooth_plane_chart E F d hds hdr w b z hz hwD c hwc
    rw [← heq] at h2
    exact h1.trans h2.symm

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
