import A5RegularArcGeometry
import A5ConormalEuclideanAdapter

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC CurvedDivergence

/-- The actual native smooth seam and a transverse projection construct
the full signed geometry of the projected arc. No smoothness of the native
coordinate lift, planar embedding, defining function or compact arc control
is assumed. -/
theorem native_projected_arc_signed_geometry
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count)
    (U : Set ℝ) (hU : IsOpen U) (hzero : (0 : ℝ) ∈ U)
    (γ : ℝ → ThreeSphere) (q : ℝ → Euc 2)
    (hγ : ContMDiffOn 𝓘(ℝ) (𝓡 3) ∞ γ U)
    (hq : MapsTo q U ((F.domain i).chart j).map.target)
    (heq : ∀ t ∈ U, E.toSphere (sectorCoordinateMap (F.map ∘ F.parametrization i) j (q t)) = γ t)
    (hregular : mfderiv 𝓘(ℝ) (𝓡 3) γ 0 1 ≠ 0)
    (c : SmoothAmbientChart ThreeSphere) (hc : γ 0 ∈ c.chart.source)
    (P : Euc 3 →L[ℝ] Euc 2)
    (hP : Function.Bijective (P.comp (fderivWithin ℝ
      (c.chart ∘ E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j)
      ((F.domain i).chart j).map.target (q 0)))) :
    let δ := fun t => P (c.chart (γ t)) - P (c.chart (γ 0))
    ∃ r : ℝ, 0 < r ∧ ∃ left right : ℝ, left < 0 ∧ 0 < right ∧
      ∃ s : Euc 2 → ℝ, SignedArcGeometry (Metric.ball 0 r) s δ left right := by
  let δ := fun t => P (c.chart (γ t)) - P (c.chart (γ 0))
  let V := U ∩ γ ⁻¹' c.chart.source
  have hV : IsOpen V := hγ.continuousOn.isOpen_inter_preimage hU c.chart.open_source
  have hzV : (0 : ℝ) ∈ V := ⟨hzero, hc⟩
  have hcoord : ContDiffOn ℝ ∞ (c.chart ∘ γ) V :=
    (c.smooth.comp (hγ.mono inter_subset_left) (fun _ ht => ht.2)).contDiffOn
  have hδ : ContDiffOn ℝ ∞ δ V :=
    (P.contDiff.comp_contDiffOn hcoord).sub contDiffOn_const
  have hγd := (hγ.contMDiffAt (hU.mem_nhds hzero)).mdifferentiableAt (by simp)
  obtain ⟨C, hC⟩ := ambient_chart_tangent_equivalence c (γ 0) hc
  have hvelocity : deriv (c.chart ∘ γ) 0 = C (mfderiv 𝓘(ℝ) (𝓡 3) γ 0 1) := by
    rw [hC]
    exact ambient_chart_curve_derivative_transport γ 0 hγd c hc
  have hv : deriv (c.chart ∘ γ) 0 ≠ 0 := by
    rw [hvelocity]
    exact fun hz => hregular (C.injective (by simpa only [map_zero] using hz))
  obtain ⟨w, hw⟩ := native_curve_velocity_mem_piece_tangent E F i j U hU γ q
    (hγ.of_le (by simp)) hq heq 0 hzero c hc
  have hPv : P (deriv (c.chart ∘ γ) 0) ≠ 0 := by
    intro hpv
    have hPw : (P.comp (fderivWithin ℝ
        (c.chart ∘ E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j)
        ((F.domain i).chart j).map.target (q 0))) w = 0 := by
      change P _ = 0
      rw [hw]
      exact hpv
    have hwzero : w = 0 := hP.1 (by simpa only [map_zero] using hPw)
    apply hv
    rw [← hw, hwzero, map_zero]
  have hdδ : HasDerivAt δ (P (deriv (c.chart ∘ γ) 0)) 0 :=
    (P.hasFDerivAt.comp_hasDerivAt 0
      ((hcoord.contDiffAt (hV.mem_nhds hzV)).differentiableAt (by simp)).hasDerivAt).sub_const _
  obtain ⟨r, hr, a, b, ha, hb, s, hs⟩ := local_signed_geometry_of_regular_curve δ V hV hzV hδ
    (by rw [hdδ.deriv]; exact hPv)
  refine ⟨r, hr, a, b, ha, hb, s, ?_⟩
  simpa only [δ, sub_self] using hs

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
