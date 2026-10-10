import OriginalA2ScaffoldV464
import A5NativeSeamChartConstruction
import A5NativeCircleSignedCoverage
import A5NativeSeamLocalHomeomorph
import A5NativeProjectionAllCharts
import A5NativeSmoothImageTangents
import A5NativeImageChartPlane

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

def regularSeamLiftExtension (q : SeamLocalTime → E2) (t : ℝ) : E2 :=
  if h : t ∈ Ioo (-1 : ℝ) 1 then q ⟨t,h⟩ else 0

theorem regularSeamLiftExtension_apply (q : SeamLocalTime → E2)
    (t : SeamLocalTime) : regularSeamLiftExtension q t = q t := by
  unfold regularSeamLiftExtension
  split
  · rfl
  · exact False.elim (‹¬(t : ℝ) ∈ Ioo (-1 : ℝ) 1› t.property)

/-- The actual two metric conormals give equal native coordinate tangent
ranges at every point of their original clock. -/
theorem balanced_native_pair_tangent_ranges
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin 2 → Fin F.pieceCount) (j : ∀ k, Fin (F.domain (i k)).count)
    (edge : ℝ → ThreeSphere) (hsmooth : ContMDiffOn 𝓘(ℝ) (𝓡 3) 1 edge (Ioo (-1 : ℝ) 1))
    (hregular : ∀ t : SeamLocalTime, mfderiv 𝓘(ℝ) (𝓡 3) edge (t : ℝ) 1 ≠ 0)
    (q n : Fin 2 → SeamLocalTime → E2)
    (hq : ∀ k t, q k t ∈ ((F.domain (i k)).chart (j k)).map.target)
    (him : ∀ k t, pieceSphereCoordinate E F (i k) (j k) (q k t) = edge t)
    (inner : ∀ t : SeamLocalTime, TangentSpace (𝓡 3) (edge t) →L[ℝ]
      TangentSpace (𝓡 3) (edge t) →L[ℝ] ℝ)
    (hu : ∀ k t, inner t
      (actualPieceConormal E F (i k) (j k) (q k t) (n k t) (edge t) (him k t))
      (actualPieceConormal E F (i k) (j k) (q k t) (n k t) (edge t) (him k t)) = 1)
    (ho : ∀ k t, inner t
      (actualPieceConormal E F (i k) (j k) (q k t) (n k t) (edge t) (him k t))
      (mfderiv 𝓘(ℝ) (𝓡 3) edge (t : ℝ) 1) = 0)
    (hbal : ∀ t, actualPieceConormal E F (i 0) (j 0) (q 0 t) (n 0 t) (edge t) (him 0 t) +
      actualPieceConormal E F (i 1) (j 1) (q 1 t) (n 1 t) (edge t) (him 1 t) = 0)
    (t : SeamLocalTime) (c : SmoothAmbientChart ThreeSphere) (hc : edge t ∈ c.chart.source) :
    (fderivWithin ℝ (c.chart ∘ pieceSphereCoordinate E F (i 0) (j 0))
      ((F.domain (i 0)).chart (j 0)).map.target (q 0 t)).toLinearMap.range =
    (fderivWithin ℝ (c.chart ∘ pieceSphereCoordinate E F (i 1) (j 1))
      ((F.domain (i 1)).chart (j 1)).map.target (q 1 t)).toLinearMap.range := by
  let D := fun k => fderivWithin ℝ (c.chart ∘ pieceSphereCoordinate E F (i k) (j k))
    ((F.domain (i k)).chart (j k)).map.target (q k t)
  let N := fun k => actualPieceConormal E F (i k) (j k) (q k t) (n k t) (edge t) (him k t)
  obtain ⟨C,hC⟩ := ambient_chart_tangent_equivalence c (edge t) hc
  have hN (k : Fin 2) : D k (n k t) = C (N k) := by
    rw [hC]
    apply ambient_chart_within_derivative_transport
    · rw [((F.domain (i k)).chart (j k)).target_eq]
      exact ((F.domain (i k)).chart (j k)).model.uniqueDiffOn_domain _
        (by simpa only [← ((F.domain (i k)).chart (j k)).target_eq] using hq k t)
    · exact ((native_piece_sphere_C1_rank E F (i k) (j k)).1 _ (hq k t)).mdifferentiableWithinAt (by norm_num)
    · exact hc
  have hvelocity : deriv (c.chart ∘ edge) t = C (mfderiv 𝓘(ℝ) (𝓡 3) edge (t : ℝ) 1) := by
    rw [hC]
    exact ambient_chart_curve_derivative_transport edge t
      ((hsmooth.contMDiffAt (isOpen_Ioo.mem_nhds t.property)).mdifferentiableAt (by norm_num)) c hc
  have hv : deriv (c.chart ∘ edge) t ≠ 0 := by
    rw [hvelocity]
    simpa only [C.map_zero] using C.injective.ne (hregular t)
  have hvmem (k : Fin 2) : deriv (c.chart ∘ edge) t ∈ (D k).toLinearMap.range := by
    have hmaps : MapsTo (regularSeamLiftExtension (q k)) (Ioo (-1 : ℝ) 1)
        ((F.domain (i k)).chart (j k)).map.target := by
      intro z hz
      change regularSeamLiftExtension (q k) (⟨z,hz⟩ : SeamLocalTime) ∈ _
      rw [regularSeamLiftExtension_apply]
      exact hq k ⟨z,hz⟩
    have he : ∀ z ∈ Ioo (-1 : ℝ) 1,
        pieceSphereCoordinate E F (i k) (j k) (regularSeamLiftExtension (q k) z) = edge z := by
      intro z hz
      change pieceSphereCoordinate E F (i k) (j k) (regularSeamLiftExtension (q k) (⟨z,hz⟩ : SeamLocalTime)) = _
      rw [regularSeamLiftExtension_apply]
      exact him k ⟨z,hz⟩
    simpa only [regularSeamLiftExtension_apply,D,pieceSphereCoordinate,sectorCoordinateMap,Function.comp_def] using
      native_curve_velocity_mem_piece_tangent E F (i k) (j k) (Ioo (-1 : ℝ) 1)
        isOpen_Ioo edge (regularSeamLiftExtension (q k)) hsmooth hmaps he t t.property c hc
  let L := ((inner t) (N 0)).comp C.symm.toContinuousLinearMap
  have hlu : L (D 0 (n 0 t)) = 1 := by
    rw [hN]
    simpa only [L,N,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,C.symm_apply_apply] using hu 0 t
  have hlo : L (deriv (c.chart ∘ edge) t) = 0 := by
    rw [hvelocity]
    simpa only [L,N,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,C.symm_apply_apply] using ho 0 t
  have hb : D 0 (n 0 t) + D 1 (n 1 t) = 0 := by
    rw [hN,hN,← C.map_add,hbal t,C.map_zero]
  apply tangent_ranges_eq_of_opposite_conormals (D 0) (D 1) _ _
    (deriv (c.chart ∘ edge) t) (D 0 (n 0 t)) (D 1 (n 1 t)) hv
    (hvmem 0) (hvmem 1) ⟨n 0 t,rfl⟩ ⟨n 1 t,rfl⟩ L hlu hlo hb
  · exact (native_piece_chart_C1_rank_at E F (i 0) (j 0) (q 0 t) (hq 0 t) c
      (by change pieceSphereCoordinate E F _ _ _ ∈ _; rw [him]; exact hc)).2
  · exact (native_piece_chart_C1_rank_at E F (i 1) (j 1) (q 1 t) (hq 1 t) c
      (by change pieceSphereCoordinate E F _ _ _ ∈ _; rw [him]; exact hc)).2

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
