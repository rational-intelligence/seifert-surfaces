import NativeBoundaryClosedLinearDifference

set_option autoImplicit false
set_option maxHeartbeats 50000
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization

theorem native_tangential_cap_quotient_limit
    (c : E2) (r : ℝ) (v : E2 → ℝ)
    (hv : ContDiffOn ℝ 1 v (nativeClosedBoundaryCap c r))
    (x : E2) (hx : x ∈ Metric.ball c r) (hn : 0 ≤ x 0) :
    Tendsto (fun h => differenceQuotient v 1 h x) (𝓝[>] 0)
      (𝓝 (fderivWithin ℝ v (nativeClosedBoundaryCap c r) x (coordinateVector 2 1))) := by
  have hxd : x ∈ nativeClosedBoundaryCap c r := ⟨Metric.ball_subset_closedBall hx, hn⟩
  have hd := (hv.differentiableOn (by norm_num) x hxd).hasFDerivWithinAt
  have hpath : HasDerivAt (fun t : ℝ => x + t • coordinateVector 2 1)
      (coordinateVector 2 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (coordinateVector 2 1)).const_add x
  have hmaps : ∀ᶠ t : ℝ in 𝓝 0, x + t • coordinateVector 2 1 ∈ nativeClosedBoundaryCap c r := by
    have hp : Continuous (fun t : ℝ => x + t • coordinateVector 2 1) := by fun_prop
    have hb := hp.continuousAt.eventually_mem (show Metric.ball c r ∈ 𝓝 (x + (0 : ℝ) • coordinateVector 2 1) by
      simpa only [zero_smul, add_zero] using Metric.isOpen_ball.mem_nhds hx)
    filter_upwards [hb] with t ht
    exact ⟨Metric.ball_subset_closedBall ht, by
      change 0 ≤ shift 1 t x 0
      rwa [tangent_shift_normal]⟩
  have hh := hd.comp_hasDerivAt_of_eq 0 hpath hmaps (by simp)
  simpa [differenceQuotient, shift, div_eq_mul_inv, smul_eq_mul, mul_comm] using
    hh.tendsto_slope_zero_right

theorem native_tangential_cap_derivative_zero_trace
    (c : E2) (r : ℝ) (v : E2 → ℝ)
    (hv : ContDiffOn ℝ 1 v (nativeClosedBoundaryCap c r))
    (hz : ∀ x ∈ Metric.ball c r ∩ {x : E2 | x 0 = 0}, v x = 0)
    (x : E2) (hx : x ∈ Metric.ball c r) (hn : x 0 = 0) :
    fderivWithin ℝ v (nativeClosedBoundaryCap c r) x (coordinateVector 2 1) = 0 := by
  have hlim := native_tangential_cap_quotient_limit c r v hv x hx hn.ge
  have hmaps : ∀ᶠ h : ℝ in 𝓝[>] 0, shift 1 h x ∈ Metric.ball c r := by
    have hp : Continuous (fun h : ℝ => shift 1 h x) := by unfold shift; fun_prop
    exact (hp.continuousAt.eventually_mem (show Metric.ball c r ∈ 𝓝 (shift 1 0 x) by
      simpa [shift] using Metric.isOpen_ball.mem_nhds hx)).filter_mono nhdsWithin_le_nhds
  have hEq : (fun h => differenceQuotient v 1 h x) =ᶠ[𝓝[>] 0] (fun _ => 0) := by
    filter_upwards [hmaps] with h hh
    simp only [differenceQuotient, hz x ⟨hx, hn⟩,
      hz (shift 1 h x) ⟨hh, by change shift 1 h x 0 = 0; rwa [tangent_shift_normal]⟩, sub_self, zero_div]
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' hEq.symm)

theorem native_tangential_cap_quotient_C1_zero_trace
    (c : E2) (r : ℝ) (hr : 0 < r) (v : E2 → ℝ)
    (hv : ContDiffOn ℝ 1 v (nativeClosedBoundaryCap c (2 * r)))
    (hz : ∀ x ∈ Metric.ball c (2 * r) ∩ {x : E2 | x 0 = 0}, v x = 0)
    (h : ℝ) (hsmall : |h| < r) :
    ContDiffOn ℝ 1 (differenceQuotient v 1 h) (nativeClosedBoundaryCap c r) ∧
      (∀ x ∈ Metric.ball c r ∩ {x : E2 | x 0 = 0}, differenceQuotient v 1 h x = 0) := by
  have hshift : MapsTo (shift 1 h) (nativeClosedBoundaryCap c r) (nativeClosedBoundaryCap c (2 * r)) := by
    intro x hx
    refine ⟨?_, by change 0 ≤ shift 1 h x 0; rw [tangent_shift_normal]; exact hx.2⟩
    have hn : dist (shift 1 h x) x = |h| := by
      simp [shift, dist_eq_norm, norm_smul, QuotientHelpers.coordinate_norm]
    have hd := dist_triangle (shift 1 h x) x c
    have hx' : dist x c ≤ r := hx.1
    change dist (shift 1 h x) c ≤ 2 * r
    linarith
  have hsub : nativeClosedBoundaryCap c r ⊆ nativeClosedBoundaryCap c (2 * r) := fun x hx =>
    ⟨Metric.closedBall_subset_closedBall (by linarith) hx.1, hx.2⟩
  have hs : ContDiff ℝ 1 (shift 1 h) := by unfold shift; fun_prop
  have hc := ((hv.comp hs.contDiffOn hshift).sub (hv.mono hsub)).const_smul h⁻¹
  have hEq : differenceQuotient v 1 h = h⁻¹ • (v ∘ shift 1 h - v) := by
    funext x
    simp [differenceQuotient, div_eq_mul_inv, mul_comm]
  refine ⟨by rwa [hEq], ?_⟩
  intro x hx
  have hx2 : x ∈ Metric.ball c (2 * r) := Metric.ball_subset_ball (by linarith) hx.1
  have hs2 : shift 1 h x ∈ Metric.ball c (2 * r) := by
    have hd := dist_triangle (shift 1 h x) x c
    have hn : dist (shift 1 h x) x = |h| := by
      simp [shift, dist_eq_norm, norm_smul, QuotientHelpers.coordinate_norm]
    have hx' : dist x c < r := hx.1
    change dist (shift 1 h x) c < 2 * r
    linarith
  simp only [differenceQuotient, hz x ⟨hx2, hx.2⟩,
    hz (shift 1 h x) ⟨hs2, by change shift 1 h x 0 = 0; rw [tangent_shift_normal]; exact hx.2⟩, sub_self, zero_div]

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
