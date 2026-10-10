import A5NativeEndpointTangentAgreement
import Mathlib.Analysis.Calculus.TangentCone.DimOne

set_option autoImplicit false
set_option maxHeartbeats 1500000
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations

/-- A differentiable ambient curve in a finite native piecewise surface has
its actual velocity in at least one incident tangent plane, even when the
curve changes pieces infinitely often. No differentiability of its source
lift is assumed. -/
theorem native_curve_endpoint_velocity_in_incident_tangent
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface} (F : GeometricPiecewiseSurface S E.Carrier)
    (b : ℝ → S) (t : ℝ) (hb : ContinuousAt b t)
    (c : SmoothAmbientChart ThreeSphere) (hc : E.toSphere (F.map (b t)) ∈ c.chart.source)
    (v : Euc 3) (hv : HasDerivAt (c.chart ∘ E.toSphere ∘ F.map ∘ b) v t) :
    ∃ (i : Fin F.pieceCount) (j : Fin (F.domain i).count) (z : Euc 2),
      z ∈ ((F.domain i).chart j).map.target ∧
      F.parametrization i (((F.domain i).chart j).map.symm z) = b t ∧
      v ∈ (fderivWithin ℝ
        (c.chart ∘ E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j)
        ((F.domain i).chart j).map.target z).toLinearMap.range := by
  classical
  let A (i : Fin F.pieceCount) := b ⁻¹' range (F.parametrization i)
  have htotal : (⋃ i, A i \ {t}) = ({t}ᶜ : Set ℝ) := by
    ext s
    simp only [mem_iUnion, Set.mem_sdiff, mem_compl_iff, mem_singleton_iff]
    constructor
    · rintro ⟨i,hi,hst⟩; exact hst
    · intro hst
      have hs : b s ∈ ⋃ i, range (F.parametrization i) := by rw [F.covers]; trivial
      obtain ⟨i,hi⟩ := mem_iUnion.mp hs
      exact ⟨i,hi,hst⟩
  have htacc : t ∈ closure (⋃ i, A i \ {t}) := by
    rw [htotal]
    exact dense_compl_singleton t t
  rw [closure_iUnion_of_finite] at htacc
  obtain ⟨i,hiacc⟩ := mem_iUnion.mp htacc
  have hix : b t ∈ range (F.parametrization i) := by
    apply (isCompact_range (F.parametrization i).continuous).isClosed.closure_subset
    apply closure_mono (fun y hy => ?_) (hb.continuousWithinAt.mem_closure_image hiacc)
    obtain ⟨s,hs,rfl⟩ := hy
    exact hs.1
  obtain ⟨a,ha⟩ := hix
  have hacover : a ∈ ⋃ j, ((F.domain i).chart j).map.source := by rw [(F.domain i).covers]; trivial
  obtain ⟨j,haj⟩ := mem_iUnion.mp hacover
  obtain ⟨U,hU,haU,q,hqa,hqc,hqm,hqe⟩ := native_piece_source_coordinate_lift F i j a haj
  have hbtU : b t ∈ U := ha ▸ haU
  let B := A i ∩ b ⁻¹' U
  have htB : t ∈ B := ⟨⟨a,ha⟩,hbtU⟩
  have hBacc : t ∈ closure (B \ {t}) := by
    apply mem_closure_iff_nhds.mpr
    intro O hO
    obtain ⟨s,hs,hsi,hst⟩ := mem_closure_iff_nhds.mp hiacc (O ∩ b ⁻¹' U)
      (inter_mem hO (hb.preimage_mem_nhds (hU.mem_nhds hbtU)))
    exact ⟨s,hs.1,⟨hsi,hs.2⟩,hst⟩
  have hBunique : UniqueDiffWithinAt ℝ B t := uniqueDiffWithinAt_iff_accPt.mpr
    (accPt_principal_iff_clusterPt.mpr (mem_closure_iff_clusterPt.mp hBacc))
  let z := ((F.domain i).chart j).map a
  have hz : z ∈ ((F.domain i).chart j).map.target := ((F.domain i).chart j).map.map_source haj
  have hez : F.parametrization i (((F.domain i).chart j).map.symm z) = b t := by
    rw [((F.domain i).chart j).map.left_inv haj,ha]
  have hqbt : q (b t) = z := by rw [← ha]; exact hqa
  have hqcont : ContinuousWithinAt (q ∘ b) B t := by
    have hqAt := hqc (b t) ⟨⟨a,ha⟩,hbtU⟩
    exact hqAt.comp (f := b) hb.continuousWithinAt (fun s hs => hs)
  have hqmaps : MapsTo (q ∘ b) B ((F.domain i).chart j).map.target :=
    fun s hs => hqm hs
  have heq (s : ℝ) (hs : s ∈ B) :
      (c.chart ∘ E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j) ((q ∘ b) s) =
      (c.chart ∘ E.toSphere ∘ F.map ∘ b) s := by
    change c.chart (E.toSphere (F.map (F.parametrization i
      (((F.domain i).chart j).map.symm (q (b s)))))) = _
    rw [hqe (b s) hs]
    rfl
  obtain ⟨hD,hDi⟩ := native_piece_chart_C1_rank_at E F i j z hz c (by
    change E.toSphere (F.map (F.parametrization i _)) ∈ c.chart.source
    rw [hez]; exact hc)
  refine ⟨i,j,z,hz,hez,?_⟩
  have hD' := (hD.differentiableWithinAt (by norm_num)).hasFDerivWithinAt
  rw [← hqbt] at hD' hDi ⊢
  exact curve_derivative_mem_relative_tangent_range _ B t htB hBunique _ _ (q ∘ b) _ v
    hD' hDi hv.hasDerivWithinAt hqcont hqmaps heq

/-- A regular smooth curve through a punctured smooth-image endpoint remains
regular under any projection transverse to all actual native incident
sectors. This includes the original labelled boundary longitude. -/
theorem native_curve_endpoint_transverse_velocity_nonzero
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface} (F : GeometricPiecewiseSurface S E.Carrier)
    (b : ℝ → S) (t : ℝ) (hb : ContinuousAt b t)
    (c : SmoothAmbientChart ThreeSphere) (hc : E.toSphere (F.map (b t)) ∈ c.chart.source)
    (v : Euc 3) (hv : HasDerivAt (c.chart ∘ E.toSphere ∘ F.map ∘ b) v t) (hvn : v ≠ 0)
    (P : Euc 3 →L[ℝ] Euc 2)
    (htrans : ∀ i j z, z ∈ ((F.domain i).chart j).map.target →
      F.parametrization i (((F.domain i).chart j).map.symm z) = b t →
      Function.Bijective (P.comp (fderivWithin ℝ
        (c.chart ∘ E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j)
        ((F.domain i).chart j).map.target z))) :
    P v ≠ 0 := by
  obtain ⟨i,j,z,hz,hez,w,hw⟩ := native_curve_endpoint_velocity_in_incident_tangent E F b t hb c hc v hv
  intro hPv
  let D := fderivWithin ℝ
    (c.chart ∘ E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j)
    ((F.domain i).chart j).map.target z
  have hw' : D w = v := hw
  have hw0 : w = 0 := (htrans i j z hz hez).1 (by
    change P (D w) = P (D 0)
    rw [hw',map_zero,map_zero]
    exact hPv)
  apply hvn
  rw [← hw,hw0,map_zero]

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
