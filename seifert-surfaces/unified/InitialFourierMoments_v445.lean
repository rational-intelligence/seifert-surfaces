import InitialFourierConstancy_v445

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal

namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates

private theorem full_period_fourier_formula_v445 (n : ℤ) (t : ℝ) :
    fourier n (t : AddCircle (2 * Real.pi)) =
      (Real.cos ((n : ℝ) * t) : ℂ) +
        (Real.sin ((n : ℝ) * t) : ℂ) * Complex.I := by
  rw [fourier_coe_apply]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have harg : (2 : ℂ) * Real.pi * Complex.I * n * t / (2 * Real.pi) =
      (((n : ℝ) * t : ℝ) : ℂ) * Complex.I := by
    push_cast
    field_simp
  push_cast
  rw [harg, Complex.exp_ofReal_mul_I]
  simp

private theorem real_sin_cos_moments_kill_fourier_v445
    (a : ℝ) (u : ℝ → ℝ)
    (hu : MemLp u 2 (volume.restrict (Icc a (a + 2 * Real.pi))))
    (n : ℤ)
    (hcos : (∫ t in Icc a (a + 2 * Real.pi),
      u t * Real.cos ((n : ℝ) * t)) = 0)
    (hsin : (∫ t in Icc a (a + 2 * Real.pi),
      u t * Real.sin ((n : ℝ) * t)) = 0) :
    fourierCoeffOn (lt_add_of_pos_right a (by positivity : 0 < 2 * Real.pi))
      (fun t => (u t : ℂ)) n = 0 := by
  classical
  let S := Icc a (a + 2 * Real.pi)
  let : IsFiniteMeasure (volume.restrict S) :=
    isFiniteMeasure_restrict.mpr measure_Icc_lt_top.ne
  have hui : IntegrableOn u S := hu.integrable (by norm_num)
  have hcosI : IntegrableOn (fun t => u t * Real.cos ((n : ℝ) * t)) S :=
    hui.mul_bdd (by fun_prop)
      (Eventually.of_forall fun t => by simpa [Real.norm_eq_abs] using Real.abs_cos_le_one _)
  have hsinI : IntegrableOn (fun t => u t * Real.sin ((n : ℝ) * t)) S :=
    hui.mul_bdd (by fun_prop)
      (Eventually.of_forall fun t => by simpa [Real.norm_eq_abs] using Real.abs_sin_le_one _)
  have hci : IntegrableOn (fun t => (u t * Real.cos ((n : ℝ) * t) : ℝ)) S := hcosI
  have hsi : IntegrableOn (fun t => (u t * Real.sin ((n : ℝ) * t) : ℝ)) S := hsinI
  have hcC := Complex.ofRealCLM.integrable_comp hci
  have hsC := Complex.ofRealCLM.integrable_comp hsi
  change IntegrableOn (fun t => ((u t * Real.cos ((n : ℝ) * t) : ℝ) : ℂ))
    (Icc a (a + 2 * Real.pi)) at hcC
  change IntegrableOn (fun t => ((u t * Real.sin ((n : ℝ) * t) : ℝ) : ℂ))
    (Icc a (a + 2 * Real.pi)) at hsC
  rw [fourierCoeffOn_eq_integral]
  have hlength : a + 2 * Real.pi - a = 2 * Real.pi := by ring
  rw [hlength, intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    ← integral_Icc_eq_integral_Ioc]
  have he : (fun t : ℝ => fourier (-n) (t : AddCircle (2 * Real.pi)) • (u t : ℂ)) =
      (fun t => ((u t * Real.cos ((n : ℝ) * t) : ℝ) : ℂ) -
        ((u t * Real.sin ((n : ℝ) * t) : ℝ) : ℂ) * Complex.I) := by
    funext t
    rw [full_period_fourier_formula_v445]
    simp only [Int.cast_neg, neg_mul, Real.cos_neg, Real.sin_neg, smul_eq_mul,
      Complex.ofReal_neg, Complex.ofReal_mul]
    ring
  rw [he, integral_sub hcC (hsC.mul_const Complex.I), integral_mul_const]
  have hc := Complex.ofRealCLM.integral_comp_comm hcosI
  have hs := Complex.ofRealCLM.integral_comp_comm hsinI
  simp only [Complex.ofRealCLM_apply] at hc hs
  rw [hc, hs, hcos, hsin]
  simp

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
