import NativeBoundaryLinearTranslation
import ClassicalCaccioppoli
import WeakDerivativeLimit

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization
open SeifertSurfaces.QuasilinearProviderBridge

theorem native_coefficient_bounds_restrict
    (U B : Set E2) (hsub : B ⊆ U) (C : LinearizedCoefficients) (κ M : ℝ)
    (hb : CoefficientBounds U C κ M) (hm : CoefficientMeasurableOn U C) :
    CoefficientBounds B C κ M ∧ CoefficientMeasurableOn B C :=
  ⟨⟨hb.1, hb.2.1, fun x hx => hb.2.2.1 x (hsub hx), fun x hx => hb.2.2.2 x (hsub hx)⟩,
    ⟨hm.1.mono_measure (Measure.restrict_mono hsub le_rfl),
      hm.2.1.mono_measure (Measure.restrict_mono hsub le_rfl),
      hm.2.2.1.mono_measure (Measure.restrict_mono hsub le_rfl),
      hm.2.2.2.1.mono_measure (Measure.restrict_mono hsub le_rfl),
      hm.2.2.2.2.1.mono_measure (Measure.restrict_mono hsub le_rfl),
      hm.2.2.2.2.2.mono_measure (Measure.restrict_mono hsub le_rfl)⟩⟩

theorem native_odd_extension_bound
    (ρ L : ℝ) (v : E2 → ℝ) (hb : ∀ x ∈ closedHalfDisc ρ, |v x| ≤ L) :
    ∀ x ∈ Metric.ball (0 : E2) ρ, |nativeOddExtension v x| ≤ L := by
  intro x hx
  by_cases hn : 0 ≤ x 0
  · simpa only [nativeOddExtension, ite_eq_left hn] using hb x ⟨Metric.ball_subset_closedBall hx, hn⟩
  · have hxR : normalReflection x ∈ closedHalfDisc ρ :=
      ⟨Metric.ball_subset_closedBall (normalReflection_maps_ball ρ hx), by
        change 0 ≤ normalReflection x 0
        rw [normalReflection_zero]
        linarith [not_le.mp hn]⟩
    simpa only [nativeOddExtension, ite_eq_right hn, abs_neg] using hb _ hxR

/-- Boundary Caccioppoli energy for the actual odd extension, uniformly over
all coefficient and solution data with the stated native bounds. -/
theorem uniform_energy_native_zero_trace_linear_solutions
    (ρ κ M L : ℝ) (hρ : 0 < ρ) (hκ : 0 < κ) (hM : 1 ≤ M) (hL : 0 ≤ L) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (C : LinearizedCoefficients) (v : E2 → ℝ),
      ContDiffOn ℝ 1 v (closedHalfDisc ρ) →
      (∀ x ∈ flatBoundary ρ, v x = 0) →
      CoefficientBounds (openHalfDisc ρ) C κ M →
      CoefficientMeasurableOn (openHalfDisc ρ) C →
      LinearWeakEquation (openHalfDisc ρ) C v (planarGradient v) →
      (∀ x ∈ closedHalfDisc ρ, |v x| ≤ L) →
      ContDiffOn ℝ 1 (nativeOddExtension v) (Metric.ball 0 ρ) ∧
      MemLp (planarGradient (nativeOddExtension v)) 2 (volume.restrict (Metric.ball 0 (ρ / 4))) ∧
      (∫ x in Metric.ball 0 (ρ / 4), ‖planarGradient (nativeOddExtension v) x‖ ^ 2) ≤ E := by
  let r := ρ / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have hM' : 1 ≤ M + κ := by linarith
  obtain ⟨E₀, hE₀, henergy⟩ := R2_Caccioppoli_classical 0 r κ (M + κ) hr hκ hM'
  let E := E₀ * (L ^ 2 + 1) * volume.real (Metric.ball (0 : E2) (2 * r))
  refine ⟨E, by dsimp [E]; positivity, ?_⟩
  intro C v hv hz hb hm hw hvalue
  let w := nativeOddExtension v
  let C' := reflectLinearizedCoefficients C κ
  obtain ⟨hwC1, hb', hw'⟩ := native_c1_zero_trace_reflected_linear_equation ρ κ M hρ C v hv hz hb hm hw
  have hm' := native_reflected_coefficients_measurable 0 (by simp) ρ κ C hm
  have hlarge : Metric.closedBall (0 : E2) (2 * r) ⊆ Metric.ball 0 ρ :=
    Metric.closedBall_subset_ball (by dsimp [r]; linarith)
  have hsmall : Metric.ball (0 : E2) (2 * r) ⊆ Metric.ball 0 ρ := Metric.ball_subset_closedBall.trans hlarge
  obtain ⟨hbB, hmB⟩ := native_coefficient_bounds_restrict _ _ hsmall C' κ (M + κ) hb' hm'
  have hwB := native_linear_weak_restrict _ _ Metric.isOpen_ball hsmall C' w (planarGradient w) hw'
  have hc : ContDiffOn ℝ 1 w (Metric.ball 0 (2 * r)) := hwC1.mono hsmall
  haveI : IsFiniteMeasure (volume.restrict (Metric.ball (0 : E2) (2 * r))) :=
    isFiniteMeasure_restrict.mpr Metric.isBounded_ball.measure_lt_top.ne
  have hv2 : MemLp w 2 (volume.restrict (Metric.ball 0 (2 * r))) :=
    Helpers.continuousOn_closedBall_memLp w 0 (2 * r) (hwC1.continuousOn.mono hlarge)
  have hG2 : MemLp (planarGradient w) 2 (volume.restrict (Metric.ball 0 (2 * r))) := by
    have hGc := QuasilinearLocalization.Helpers.gradient_continuousOn _ Metric.isOpen_ball w hwC1
    obtain ⟨D, hD⟩ := (isCompact_closedBall (0 : E2) (2 * r)).exists_bound_of_continuousOn (hGc.mono hlarge)
    apply MemLp.of_bound ((hGc.mono hsmall).aestronglyMeasurable Metric.isOpen_ball.measurableSet) D
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    exact hD x (Metric.ball_subset_closedBall hx)
  have hbound : ∀ x ∈ Metric.ball 0 (2 * r), |w x| ≤ L :=
    fun x hx => native_odd_extension_bound ρ L v hvalue x (hsmall hx)
  have he := henergy C' w hc hv2 hG2 hmB hbB hwB
  have hu : Integrable (fun x => |w x| ^ 2 + (1 : ℝ))
      (volume.restrict (Metric.ball 0 (2 * r))) := by
    exact ((((hwC1.continuousOn.mono hlarge).abs.pow 2).add continuousOn_const).integrableOn_compact
      (isCompact_closedBall _ _)).mono_set Metric.ball_subset_closedBall
  have hi : (∫ x in Metric.ball 0 (2 * r), |w x| ^ 2 + 1) ≤
      (L ^ 2 + 1) * volume.real (Metric.ball (0 : E2) (2 * r)) := by
    calc
      _ ≤ ∫ x : E2 in Metric.ball 0 (2 * r), (L ^ 2 + 1) := by
        apply integral_mono_ae hu (integrable_const _)
        filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
        have hh := hbound x hx
        nlinarith [abs_nonneg (w x)]
      _ = _ := by simp [integral_const, Measure.real, mul_comm]
  refine ⟨hwC1, hG2.mono_measure (Measure.restrict_mono_set _ (Metric.ball_subset_ball (by dsimp [r]; linarith))), ?_⟩
  exact he.trans ((mul_le_mul_of_nonneg_left hi hE₀).trans_eq (by dsimp [E]; ring))

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
