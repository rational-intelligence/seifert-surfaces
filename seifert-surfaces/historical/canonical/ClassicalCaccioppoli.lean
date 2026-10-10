import EnergyAlgebra
import EnergyCutoff

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology BigOperators ContDiff
namespace SeifertSurfaces.QuasilinearLocalization
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.QuasilinearProviderBridge
open SeifertSurfaces.QuasilinearProviderBridge.EnergyHelpers

theorem R2_Caccioppoli_classical
    (x₀ : E2) (r κ M : ℝ) (hr : 0 < r) (hκ : 0 < κ) (hM : 1 ≤ M) :
    ∃ Cenergy : ℝ, 0 ≤ Cenergy ∧ ∀ (coeff : LinearizedCoefficients) (v : E2 → ℝ),
      ContDiffOn ℝ 1 v (Metric.ball x₀ (2 * r)) →
      MemLp v 2 (volume.restrict (Metric.ball x₀ (2 * r))) →
      MemLp (planarGradient v) 2 (volume.restrict (Metric.ball x₀ (2 * r))) →
      CoefficientMeasurableOn (Metric.ball x₀ (2 * r)) coeff →
      CoefficientBounds (Metric.ball x₀ (2 * r)) coeff κ M →
      LinearWeakEquation (Metric.ball x₀ (2 * r)) coeff v (planarGradient v) →
      (∫ x in Metric.ball x₀ r, ‖planarGradient v x‖ ^ 2) ≤
        Cenergy * (∫ x in Metric.ball x₀ (2 * r), |v x| ^ 2 + 1) := by
  obtain ⟨η, D, hη, hηc, hηB, hη01, hηone, hD, hDη, hDgrad⟩ := cutoff_for_energy x₀ r hr
  let K := (2 * M * (D + 1)) ^ 2 / κ + 4 * M * (D + 1)
  have hM0 : 0 ≤ M := by linarith
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K / (κ / 2), by positivity, ?_⟩
  intro C v hC1 hv hG hmeas hbound hweak
  let B := Metric.ball x₀ (2 * r)
  have hB : IsOpen B := Metric.isOpen_ball
  have hBbdd : Bornology.IsBounded B := Metric.isBounded_ball
  haveI : IsFiniteMeasure (volume.restrict B) :=
    isFiniteMeasure_restrict.mpr hBbdd.measure_lt_top.ne
  obtain ⟨hw, hgrad⟩ := classical_witness B hB v hC1 hv hG
  obtain ⟨hφ, hφw, hφgrad⟩ := squared_cutoff_test B hB v η hw hη hηc hηB hη01 D hD hDη
  have hweakH := R2_smooth_tests_extend_to_H01 B hB hBbdd C v hC1 κ M hbound hmeas
    hw.memW1p hweak
  obtain ⟨hI1, hI2, hIeq⟩ := hweakH.2 hw (fun x => η x ^ 2 * v x) hφ hφw
  let E : E2 → ℝ := fun x => η x ^ 2 * ‖planarGradient v x‖ ^ 2
  let U : E2 → ℝ := fun x => v x ^ 2 + 1
  let I : E2 → ℝ := fun x =>
    inner ℝ (linearizedFlux C v hw.weakGrad x) (hφw.weakGrad x) -
      linearizedSource C v hw.weakGrad x * (η x ^ 2 * v x)
  have hI : Integrable I (volume.restrict B) := hI1.sub hI2
  have hE : Integrable E (volume.restrict B) := by
    apply hG.norm.integrable_sq.mono'
      ((hη.continuous.aestronglyMeasurable.pow 2).mul (hG.aestronglyMeasurable.norm.pow 2))
    filter_upwards [] with x
    change ‖η x ^ 2 * ‖planarGradient v x‖ ^ 2‖ ≤ ‖planarGradient v x‖ ^ 2
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hh : η x ^ 2 ≤ 1 := by nlinarith [(hη01 x).1, (hη01 x).2]
    nlinarith only [mul_le_mul_of_nonneg_right hh (sq_nonneg ‖planarGradient v x‖)]
  have hU : Integrable U (volume.restrict B) := hv.integrable_sq.add (integrable_const 1)
  have hpoint : (fun x => κ / 2 * E x) ≤ᵐ[volume.restrict B]
      (fun x => I x + K * U x) := by
    filter_upwards [ae_restrict_mem hB.measurableSet] with x hx
    change κ / 2 * (η x ^ 2 * ‖planarGradient v x‖ ^ 2) ≤ _
    dsimp [I, U, K]
    rw [hφgrad x, hgrad]
    exact cutoff_pointwise_energy (C.a x) (C.c x) (C.d x) (planarGradient v x)
      (planarGradient η x) (C.b x) (C.q x) (C.f x) (v x) (η x) κ M D
      hκ hM0 hD (hη01 x).1 (hη01 x).2 (hbound.2.2.1 x hx _)
      (hbound.2.2.2 x hx).1 (hbound.2.2.2 x hx).2.1 (hbound.2.2.2 x hx).2.2.1
      (hbound.2.2.2 x hx).2.2.2.1 (hbound.2.2.2 x hx).2.2.2.2.1
      (hbound.2.2.2 x hx).2.2.2.2.2 (hDgrad x)
  have hint := integral_mono_ae (hE.const_mul (κ / 2)) (hI.add (hU.const_mul K)) hpoint
  change (∫ x in B, κ / 2 * E x) ≤ ∫ x in B, I x + K * U x at hint
  rw [integral_const_mul, integral_add hI (hU.const_mul K), integral_const_mul] at hint
  have hIzero : (∫ x in B, I x) = 0 := hIeq
  rw [hIzero, zero_add] at hint
  have hsmall : (∫ x in Metric.ball x₀ r, ‖planarGradient v x‖ ^ 2) ≤ ∫ x in B, E x := by
    calc
      _ = ∫ x in Metric.ball x₀ r, E x := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
        simp [E, hηone x hx]
      _ ≤ _ := setIntegral_mono_set hE (ae_of_all _ fun x => by dsimp [E]; positivity)
        (ae_of_all _ fun x hx => Metric.ball_subset_ball (by linarith) hx)
  have hh : κ / 2 * (∫ x in Metric.ball x₀ r, ‖planarGradient v x‖ ^ 2) ≤
      K * ∫ x in B, U x := (mul_le_mul_of_nonneg_left hsmall (by positivity)).trans hint
  have hk2 : 0 < κ / 2 := by positivity
  have hres := (le_div_iff₀ hk2).mpr (show
    (∫ x in Metric.ball x₀ r, ‖planarGradient v x‖ ^ 2) * (κ / 2) ≤ K * ∫ x in B, U x by
      simpa only [mul_comm (κ / 2)] using hh)
  simpa only [B, U, sq_abs, div_mul_eq_mul_div] using hres

end SeifertSurfaces.QuasilinearLocalization
