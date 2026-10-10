import ClassicalCaccioppoli
import QuotientWeakEquation

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology BigOperators ContDiff
namespace SeifertSurfaces.QuasilinearLocalization
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.QuasilinearProviderBridge
open SeifertSurfaces.QuasilinearProviderBridge.EnergyHelpers

theorem R2_uniform_differenceQuotient_energy
    (Ω : Set E2) (hΩ : IsOpen Ω) (J : Set Jet) (hJ : IsOpen J)
    (Q : SmoothQuasilinearOperator J) (u : E2 → ℝ) (hC1 : ContDiffOn ℝ 1 u Ω)
    (hjets : ∀ x ∈ Ω, firstJet u x ∈ J)
    (hweak : IsWeakDivergenceSolutionOn Ω Q.flux Q.lowerOrder u)
    (x₀ : E2) (r κ M : ℝ) (hr : 0 < r) (T : Set Jet)
    (hball : Metric.closedBall x₀ (4 * r) ⊆ Ω)
    (hT : Convex ℝ T) (hTJ : closure T ⊆ J)
    (hjetsT : ∀ x ∈ Metric.closedBall x₀ (4 * r), firstJet u x ∈ T)
    (hbound : JetTubeBounds Q u x₀ r κ M T) :
    ∃ Cenergy : ℝ, 0 ≤ Cenergy ∧ ∀ (k : Fin 2) (h : ℝ), 0 < |h| → |h| < r →
      MemLp (planarGradient (differenceQuotient u k h)) 2
        (volume.restrict (Metric.ball x₀ r)) ∧
      (∫ x in Metric.ball x₀ r, ‖planarGradient (differenceQuotient u k h) x‖ ^ 2) ≤ Cenergy := by
  obtain ⟨C₀, hC₀, henergy⟩ := R2_Caccioppoli_classical x₀ r κ M hr hbound.1 hbound.2.1
  let B := Metric.ball x₀ (2 * r)
  have hB : IsOpen B := Metric.isOpen_ball
  have hBbdd : Bornology.IsBounded B := Metric.isBounded_ball
  haveI : IsFiniteMeasure (volume.restrict B) :=
    isFiniteMeasure_restrict.mpr hBbdd.measure_lt_top.ne
  refine ⟨C₀ * ∫ x in B, (M ^ 2 + 1), mul_nonneg hC₀ (integral_nonneg (by intro x; positivity)), ?_⟩
  intro k h hh hhr
  have hTJ' : T ⊆ J := subset_closure.trans hTJ
  obtain ⟨hCq, hweakq⟩ := R2_differenceQuotient_weak_equation Ω hΩ J hJ Q u hC1 hjets hweak
    x₀ r hr T hball hT hTJ' hjetsT k h hh hhr
  obtain ⟨hcoeff, hqbound⟩ := R2_uniform_coefficient_and_quotient_bounds Ω hΩ J hJ Q u hC1
    x₀ r κ M hr T hball hT hTJ hjetsT hbound k h hh hhr
  have hmeas := (R2_averaged_coefficients_continuous Ω hΩ J hJ Q u hC1
    x₀ r hr T hball hT hTJ' hjetsT k h hh hhr).2
  have hqLp : MemLp (differenceQuotient u k h) 2 (volume.restrict B) := by
    apply MemLp.of_bound (hCq.continuousOn.aestronglyMeasurable hB.measurableSet) M
    filter_upwards [ae_restrict_mem hB.measurableSet] with x hx
    exact hqbound x hx
  have hGLp : MemLp (planarGradient (differenceQuotient u k h)) 2 (volume.restrict B) := by
    apply MemLp.of_bound
      ((Helpers.gradient_continuousOn B hB _ hCq).aestronglyMeasurable hB.measurableSet)
      (|h|⁻¹ * (2 * M))
    filter_upwards [ae_restrict_mem hB.measurableSet] with x hx
    have hx4 : x ∈ Metric.closedBall x₀ (4 * r) :=
      (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))) hx
    have hs4 := QuotientHelpers.shift_mem_closedBall x₀ x r hr
      (QuotientHelpers.ball_two_subset_closed_three x₀ r hr hx) k h hhr
    rw [R2_differenceQuotient_gradient Ω hΩ u hC1 k h (ne_of_apply_ne abs (by simpa using hh.ne'))
      x (hball hx4) (hball hs4), norm_smul, Real.norm_eq_abs, abs_inv]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact (norm_sub_le _ _).trans (by linarith [(hbound.2.2.1 _ hs4).2, (hbound.2.2.1 _ hx4).2])
  have hsmall : Metric.ball x₀ r ⊆ B := Metric.ball_subset_ball (by linarith)
  refine ⟨hGLp.mono_measure (Measure.restrict_mono_set _ hsmall), ?_⟩
  apply (henergy _ _ hCq hqLp hGLp hmeas hcoeff hweakq).trans
  apply mul_le_mul_of_nonneg_left _ hC₀
  have hInt : Integrable (fun x => differenceQuotient u k h x ^ 2 + 1)
      (volume.restrict B) := hqLp.integrable_sq.add (integrable_const 1)
  have hIntAbs : Integrable (fun x => |differenceQuotient u k h x| ^ 2 + 1)
      (volume.restrict B) := by simpa only [sq_abs] using hInt
  apply integral_mono_ae hIntAbs (integrable_const (M ^ 2 + 1))
  filter_upwards [ae_restrict_mem hB.measurableSet] with x hx
  have hhq := hqbound x hx
  have hM0 : 0 ≤ M := by linarith [hbound.2.1]
  nlinarith [abs_nonneg (differenceQuotient u k h x)]

end SeifertSurfaces.QuasilinearLocalization
