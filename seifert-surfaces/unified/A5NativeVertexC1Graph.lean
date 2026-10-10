import A5NativeProjectionRegions
import A5RelativeVertexGluing

set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations

/-- Native finite-piece graph regularity across an isolated vertex. All
projected regions, lifts and derivative fields are constructed from the
actual projection homeomorphism. Tangent agreement is needed only away
from the vertex; connected planar punctures force the remaining match. -/
theorem native_projection_graph_C1_across_vertex
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface} (F : GeometricPiecewiseSurface S E.Carrier)
    (x : S) (c : SmoothAmbientChart ThreeSphere) (P : Euc 3 →L[ℝ] Euc 2)
    (e : OpenPartialHomeomorph S (Euc 2)) (hx : x ∈ e.source)
    (he : ∀ z, e z = P (c.chart (E.toSphere (F.map z))))
    (hmaps : MapsTo (E.toSphere ∘ F.map) e.source c.chart.source)
    (havoid : ∀ i, x ∉ range (F.parametrization i) →
      range (F.parametrization i) ∩ e.source = ∅)
    (hcharts : ∀ i, x ∈ range (F.parametrization i) →
      ∃ j : Fin (F.domain i).count, ∀ a, F.parametrization i a ∈ e.source →
        a ∈ ((F.domain i).chart j).map.source)
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
    ContDiffOn ℝ 1 (c.chart ∘ E.toSphere ∘ F.map ∘ e.symm) e.target := by
  classical
  let I := {i : Fin F.pieceCount // x ∈ range (F.parametrization i)}
  let j (i : I) := (hcharts i.val i.property).choose
  have hj (i : I) : ∀ a, F.parametrization i.val a ∈ e.source →
      a ∈ ((F.domain i.val).chart (j i)).map.source := (hcharts i.val i.property).choose_spec
  let R (i : I) := e.target ∩ e.symm ⁻¹' range (F.parametrization i.val)
  let f := c.chart ∘ E.toSphere ∘ F.map ∘ e.symm
  obtain ⟨hcoverAll, hclosedAll, _, hsection, _⟩ := native_projection_whole_piece_regions E F c P e he hmaps
  have hcover : (⋃ i, R i) = e.target := by
    ext y
    constructor
    · intro hy
      obtain ⟨i, hi⟩ := mem_iUnion.mp hy
      exact hi.1
    · intro hy
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hcoverAll.symm ▸ hy)
      have hix : x ∈ range (F.parametrization i) := by
        by_contra hn
        have hemt : e.symm y ∈ range (F.parametrization i) ∩ e.source := ⟨hi.2, e.map_target hy⟩
        rw [havoid i hn] at hemt
        exact hemt
      exact mem_iUnion.mpr ⟨⟨i, hix⟩, hi⟩
  have hpiece (i : I) := native_piece_projection_graph E F c P e he hmaps i.val (j i) (hj i)
    (htrans i.val (j i))
  have hincident (i : I) : e x ∈ R i := by
    refine ⟨e.map_source hx, ?_⟩
    change e.symm (e x) ∈ range (F.parametrization i.val)
    rw [e.left_inv hx]
    exact i.property
  have hpoint (i : I) (y : Euc 2) (hy : y ∈ R i) :
      ∃ z ∈ ((F.domain i.val).chart (j i)).map.target,
        F.parametrization i.val (((F.domain i.val).chart (j i)).map.symm z) = e.symm y := by
    obtain ⟨a, ha⟩ := hy.2
    have hs := hj i a (ha ▸ e.map_target hy.1)
    refine ⟨((F.domain i.val).chart (j i)).map a,
      ((F.domain i.val).chart (j i)).map.map_source hs, ?_⟩
    rw [((F.domain i.val).chart (j i)).map.left_inv hs, ha]
  have hrange (i : I) (y : Euc 2) (hy : y ∈ R i)
      (z : Euc 2) (hz : z ∈ ((F.domain i.val).chart (j i)).map.target)
      (hzp : F.parametrization i.val (((F.domain i.val).chart (j i)).map.symm z) = e.symm y) :
      (fderivWithin ℝ f (R i) y).toLinearMap.range =
      (fderivWithin ℝ
        (c.chart ∘ E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i.val) (j i))
        ((F.domain i.val).chart (j i)).map.target z).toLinearMap.range := by
    have hzs := hzp ▸ e.map_target hy.1
    have hh := (hpiece i).2.2 z hz hzs
    have hez : P (c.chart (E.toSphere
        (sectorCoordinateMap (F.map ∘ F.parametrization i.val) (j i) z))) = y := by
      change P (c.chart (E.toSphere (F.map (F.parametrization i.val
        (((F.domain i.val).chart (j i)).map.symm z))))) = y
      rw [hzp, ← he, e.right_inv hy.1]
    rwa [hez] at hh
  apply C1_graph_on_open_across_finite_vertex e.target e.open_target (e x) (e.map_source hx)
    R (fun i => hclosedAll i.val) hcover hincident (fun i => (hpiece i).1) f
    (fun i => (hpiece i).2.1)
  intro i k y hi hk hy
  have hder (a : I) (ha : y ∈ R a) :
      P.comp (fderivWithin ℝ f (R a) y) = ContinuousLinearMap.id ℝ (Euc 2) := by
    have hd := P.hasFDerivAt.comp_hasFDerivWithinAt y
      (((hpiece a).2.1 y ha).differentiableWithinAt (by norm_num)).hasFDerivWithinAt
    have heq : EqOn (P ∘ f) id (R a) := fun z hz => hsection z hz.1
    exact ((hd.congr heq.symm (heq ha).symm).fderivWithin ((hpiece a).1 y ha)).symm.trans
      ((hasFDerivWithinAt_id y (R a)).fderivWithin ((hpiece a).1 y ha))
  apply section_derivatives_eq_of_range_eq P _ _ (hder i hi) (hder k hk)
  obtain ⟨z, hz, hzp⟩ := hpoint i y hi
  obtain ⟨w, hw, hwp⟩ := hpoint k y hk
  rw [hrange i y hi z hz hzp, hrange k y hk w hw hwp]
  apply htangent i.val (j i) k.val (j k) z w hz hw (hzp.trans hwp.symm)
    (hzp ▸ e.map_target hi.1)
  intro heq
  apply hy
  rw [← e.right_inv hi.1, ← hzp, heq]

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
