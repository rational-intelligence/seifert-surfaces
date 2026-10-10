import ConstantGradientVariation

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace SeifertSurfaces.WeakSchauder

/-- R4b: interior excess decay with exponent five in dimension three. -/
theorem constant_gradient_excess_decay (κ Λ : ℝ) (hκ : 0 < κ) (hΛ : κ ≤ Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (center : V) (R : ℝ), 0 < R →
      ∀ (A : Mat), CoefficientBounds (fun _ => A) (Metric.ball center R) κ Λ →
      ∀ (h : V → ℝ) (hh : H1Witness h (Metric.ball center R)),
      WeakEquation (fun _ => A) hh →
      ∀ r : ℝ, 0 < r → r ≤ R / 2 →
        excess hh.weakGrad center r ≤ C * (r / R) ^ (5 : ℕ) * excess hh.weakGrad center R := by
  let L := Real.sqrt Λ
  let N := (Real.sqrt κ)⁻¹
  have hL : 0 < L := Real.sqrt_pos.mpr (hκ.trans_le hΛ)
  have hN : 0 < N := inv_pos.mpr (Real.sqrt_pos.mpr hκ)
  obtain ⟨D, hD, hdet⟩ := exists_det_bound_on_norm_ball N
  let K := 3 * (12288 * DeGiorgi.CMoser 3 * (DeGiorgi.Mst : ℝ) ^ 2) *
    (2 * L) ^ 5 * N ^ 4 * L ^ 2 * D
  let V₁ := (volume (Metric.ball (0 : V) 1)).toReal
  have hK : 0 ≤ K := by
    have hm := DeGiorgi.one_le_C_Moser (d := 3)
    dsimp [K]
    positivity
  have hV₁ : 0 ≤ V₁ := ENNReal.toReal_nonneg
  refine ⟨4 * K * V₁ + 1, by positivity, ?_⟩
  intro c R hR A hA h hh hw r hr hrR
  obtain ⟨P, hfactor, hP, hPi⟩ := constant_linear_factor c R κ Λ hR hκ hΛ A hA
  obtain ⟨a, hpoint⟩ := constant_gradient_variation_bound c R hR A P hfactor L N D hL hN.le hD.le
    hP hPi (hdet _ hPi) h hh hw
  have hsub : Metric.ball c r ⊆ Metric.ball c R := Metric.ball_subset_ball (by linarith)
  have hsub' : Metric.ball c r ⊆ Metric.ball c (R / 2) := Metric.ball_subset_ball hrR
  have hE : 0 ≤ excess hh.weakGrad c R := integral_nonneg fun _ => sq_nonneg _
  have hb : ∀ᵐ x ∂volume.restrict (Metric.ball c r),
      ‖hh.weakGrad x - a‖ ^ 2 ≤ K * (R ^ 5)⁻¹ * excess hh.weakGrad c R * r ^ 2 := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub' hpoint,
      ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx hxB
    exact hx.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (Metric.mem_ball.mp hxB).le 2) (by positivity))
  have hmem := hh.weakGrad_memLp.mono_measure (Measure.restrict_mono hsub le_rfl)
  have he := excess_le_of_ae_sq_bound hh.weakGrad c r hr hmem a
    (K * (R ^ 5)⁻¹ * excess hh.weakGrad c R * r ^ 2) (by positivity) hb
  rw [real_volume_ball_three c r hr] at he
  calc
    _ ≤ 4 * (K * (R ^ 5)⁻¹ * excess hh.weakGrad c R * r ^ 2) * (r ^ 3 * V₁) := he
    _ = 4 * K * V₁ * (r / R) ^ 5 * excess hh.weakGrad c R := by
      rw [div_pow, div_eq_mul_inv]
      ring
    _ ≤ (4 * K * V₁ + 1) * (r / R) ^ 5 * excess hh.weakGrad c R := by
      gcongr
      linarith

end SeifertSurfaces.WeakSchauder
