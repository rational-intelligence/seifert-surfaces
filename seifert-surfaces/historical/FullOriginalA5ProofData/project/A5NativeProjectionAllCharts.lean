import A5NativeChartTangents

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations

/-- Equal points in two charts of the same embedded whole piece have the
same transversality, with no relationship assumed between the chart choices. -/
theorem native_projection_transverse_at_equal_piece_image
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j k : Fin (F.domain i).count) (y z : Euc 2)
    (hy : y ∈ ((F.domain i).chart j).map.target)
    (hz : z ∈ ((F.domain i).chart k).map.target)
    (heq : sectorCoordinateMap (F.map ∘ F.parametrization i) j y =
      sectorCoordinateMap (F.map ∘ F.parametrization i) k z)
    (c : SmoothAmbientChart ThreeSphere)
    (hc : E.toSphere (sectorCoordinateMap (F.map ∘ F.parametrization i) j y) ∈ c.chart.source)
    (P : Euc 3 →L[ℝ] Euc 2)
    (hP : Function.Bijective (P.comp (fderivWithin ℝ
      (c.chart ∘ E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j)
      ((F.domain i).chart j).map.target y))) :
    Function.Bijective (P.comp (fderivWithin ℝ
      (c.chart ∘ E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) k)
      ((F.domain i).chart k).map.target z)) := by
  let a := ((F.domain i).chart j).map.symm y
  have haj : a ∈ ((F.domain i).chart j).map.source :=
    ((F.domain i).chart j).map.map_target hy
  have hae : ((F.domain i).chart k).map.symm z = a :=
    (F.piece_topological_embedding i).injective heq.symm
  have hak : a ∈ ((F.domain i).chart k).map.source :=
    hae ▸ ((F.domain i).chart k).map.map_target hz
  have hay : ((F.domain i).chart j).map a = y := ((F.domain i).chart j).map.right_inv hy
  have haz : ((F.domain i).chart k).map a = z := by
    rw [← hae]
    exact ((F.domain i).chart k).map.right_inv hz
  have hh := native_projection_transverse_change_chart E F i j k a haj hak c hc P
    (by simpa only [hay] using hP)
  simpa only [haz] using hh

/-- The finite native common projection stays transverse in every chart of
every incident sheet near the source point. This strengthens chart selection
to chart independence and is suitable for externally constructed seam data. -/
theorem native_projection_isolated_fiber_all_charts
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface} (F : GeometricPiecewiseSurface S E.Carrier)
    (x : S) (c : SmoothAmbientChart ThreeSphere)
    (hc : E.toSphere (F.map x) ∈ c.chart.source) :
    ∃ P : Euc 3 →L[ℝ] Euc 2, ∃ height : Euc 3 →L[ℝ] ℝ,
      Function.Injective (fun z => (P z, height z)) ∧
      ∃ U : Set S, IsOpen U ∧ x ∈ U ∧
        MapsTo (E.toSphere ∘ F.map) U c.chart.source ∧
        ContinuousOn (P ∘ c.chart ∘ E.toSphere ∘ F.map) U ∧
        ContinuousOn (height ∘ c.chart ∘ E.toSphere ∘ F.map) U ∧
        InjOn (fun z => (P (c.chart (E.toSphere (F.map z))),
          height (c.chart (E.toSphere (F.map z))))) U ∧
        (∀ z ∈ U, ∀ i j y, y ∈ ((F.domain i).chart j).map.target →
          sectorCoordinateMap (F.map ∘ F.parametrization i) j y = F.map z →
          Function.Bijective (P.comp (fderivWithin ℝ
            (c.chart ∘ E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j)
            ((F.domain i).chart j).map.target y))) ∧
        ∀ z ∈ U, P (c.chart (E.toSphere (F.map z))) =
          P (c.chart (E.toSphere (F.map x))) → z = x := by
  obtain ⟨P, height, hsep, U, hU, hxU, hmaps, hp, hh, hinj, hcharts, hfiber⟩ :=
    native_projection_isolated_fiber E F x c hc
  refine ⟨P, height, hsep, U, hU, hxU, hmaps, hp, hh, hinj, ?_, hfiber⟩
  intro z hz i j y hy heq
  have hiz : z ∈ range (F.parametrization i) := by
    refine ⟨((F.domain i).chart j).map.symm y, ?_⟩
    exact F.embedding.injective heq
  obtain ⟨j', y', hy', he', hP'⟩ := hcharts i z ⟨hiz, hz⟩
  exact native_projection_transverse_at_equal_piece_image E F i j' j y' y hy' hy
    (he'.trans heq.symm) c (by rw [he']; exact hmaps hz) P hP'

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
