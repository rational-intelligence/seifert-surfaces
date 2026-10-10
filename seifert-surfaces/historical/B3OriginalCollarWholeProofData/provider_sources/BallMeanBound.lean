import GradientVariation

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace SeifertSurfaces.WeakSchauder

theorem excess_le_of_ae_sq_bound (G : V → V) (c : V) (r : ℝ) (hr : 0 < r)
    (hG : MemLp G 2 (volume.restrict (Metric.ball c r)))
    (a : V) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ᵐ x ∂volume.restrict (Metric.ball c r), ‖G x - a‖ ^ 2 ≤ B) :
    excess G c r ≤ 4 * B * (volume (Metric.ball c r)).toReal := by
  let μ := volume.restrict (Metric.ball c r)
  haveI : IsFiniteMeasure μ :=
    isFiniteMeasure_restrict.mpr Metric.isBounded_ball.measure_lt_top.ne
  have hvol : 0 < (volume (Metric.ball c r)).toReal :=
    ENNReal.toReal_pos (Metric.isOpen_ball.measure_pos volume (Metric.nonempty_ball.mpr hr)).ne'
      Metric.isBounded_ball.measure_lt_top.ne
  have hGi : Integrable G μ := hG.integrable (by norm_num)
  have hmean : ‖ballMean G c r - a‖ ≤ Real.sqrt B := by
    have hnorm : ∀ᵐ x ∂μ, ‖G x - a‖ ≤ Real.sqrt B := by
      filter_upwards [hb] with x hx
      exact (Real.le_sqrt (norm_nonneg _) hB).mpr hx
    have hi := norm_integral_le_of_norm_le_const hnorm
    have he : ballMean G c r - a =
        (volume (Metric.ball c r)).toReal⁻¹ • ∫ x, (G x - a) ∂μ := by
      rw [integral_sub hGi (integrable_const a), integral_const, smul_sub]
      simp only [μ, Measure.real, Measure.restrict_apply_univ]
      rw [smul_smul, inv_mul_cancel₀ hvol.ne', one_smul]
      rfl
    rw [he, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hvol.le)]
    calc
      _ ≤ (volume (Metric.ball c r)).toReal⁻¹ * (Real.sqrt B * μ.real Set.univ) :=
        mul_le_mul_of_nonneg_left hi (by positivity)
      _ = Real.sqrt B := by
        simp only [μ, Measure.real, Measure.restrict_apply_univ]
        field_simp
  have hp : ∀ᵐ x ∂μ, ‖G x - ballMean G c r‖ ^ 2 ≤ 4 * B := by
    filter_upwards [hb] with x hx
    have hxa : ‖G x - a‖ ≤ Real.sqrt B := (Real.le_sqrt (norm_nonneg _) hB).mpr hx
    have hn : ‖G x - ballMean G c r‖ ≤ 2 * Real.sqrt B := by
      calc
        _ ≤ ‖G x - a‖ + ‖a - ballMean G c r‖ := by simpa only [dist_eq_norm] using dist_triangle (G x) a (ballMean G c r)
        _ ≤ 2 * Real.sqrt B := by rw [norm_sub_rev a]; linarith
    have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
    nlinarith [Real.sq_sqrt hB]
  have hsq : Integrable (fun x => ‖G x - ballMean G c r‖ ^ 2) μ :=
    (hG.sub (memLp_const _)).norm.integrable_sq
  have hi := integral_mono_ae hsq (integrable_const (4 * B)) hp
  simpa only [excess, integral_const, smul_eq_mul, μ, Measure.real,
    Measure.restrict_apply_univ, mul_comm] using hi

end SeifertSurfaces.WeakSchauder
