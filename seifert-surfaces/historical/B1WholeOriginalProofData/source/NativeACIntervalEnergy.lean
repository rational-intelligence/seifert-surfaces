import NativeScalarCone

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
open SeifertSurfaces.AppendixACoordinates L1Independent
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

 theorem integral_square_bound {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (hμ : 0 < μ.real univ) (f : α → ℝ) (hf : MemLp f 2 μ) :
    (∫ x, f x ∂μ) ^ 2 ≤ μ.real univ * ∫ x, f x ^ 2 ∂μ := by
  let m : ℝ := μ.real univ
  let I : ℝ := ∫ x, f x ∂μ
  have hfi : Integrable f μ := hf.integrable (by norm_num)
  have hsq : Integrable (fun x => f x ^ 2) μ := hf.integrable_sq
  have hpos : 0 ≤ ∫ x, (m * f x - I) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have heq : (∫ x, (m * f x - I) ^ 2 ∂μ) =
      m ^ 2 * (∫ x, f x ^ 2 ∂μ) - 2 * m * I * I + I ^ 2 * m := by
    have hp (x : α) : (m * f x - I) ^ 2 = m ^ 2 * f x ^ 2 - (2 * m * I) * f x + I ^ 2 := by ring
    simp_rw [hp]
    have hAdd := integral_add ((hsq.const_mul (m ^ 2)).sub (hfi.const_mul (2 * m * I))) (integrable_const (I ^ 2))
    have hSub := integral_sub (hsq.const_mul (m ^ 2)) (hfi.const_mul (2 * m * I))
    simp only [Pi.sub_apply] at hAdd
    rw [hAdd, hSub, integral_const_mul, integral_const_mul, integral_const]
    dsimp [I, m]
    ring
  rw [heq] at hpos
  change I ^ 2 ≤ m * _
  have hm : 0 < m := hμ
  nlinarith

 theorem ac_endpoint_square_bound (a b : ℝ) (hab : a < b) (g : ℝ → ℝ)
    (hg : AbsolutelyContinuousOnInterval g a b)
    (hgp : MemLp (deriv g) 2 (volume.restrict (Icc a b))) :
    ∀ t ∈ Icc a b,
      (g t - g a) ^ 2 ≤ (b - a) * ∫ u in Icc a b, deriv g u ^ 2 := by
  intro t ht
  have hsub : uIcc a t ⊆ uIcc a b := by
    rw [uIcc_of_le ht.1, uIcc_of_le hab.le]
    exact Icc_subset_Icc le_rfl ht.2
  have hft := (hg.mono hsub).integral_deriv_eq_sub
  rw [intervalIntegral.integral_of_le ht.1, ← integral_Icc_eq_integral_Ioc] at hft
  have hI : IntegrableOn (fun u => |deriv g u|) (Icc a b) := hgp.norm.integrable (by norm_num)
  have hbound : |g t - g a| ≤ ∫ u in Icc a b, |deriv g u| := by
    rw [← hft, ← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans ?_
    simpa only [Real.norm_eq_abs] using setIntegral_mono_set hI
      (Eventually.of_forall fun u => abs_nonneg (deriv g u))
      (Eventually.of_forall (Icc_subset_Icc le_rfl ht.2))
  have hmass : (volume.restrict (Icc a b)).real univ = b - a := by
    rw [Measure.real, Measure.restrict_apply_univ, Real.volume_Icc, ENNReal.toReal_ofReal]
    exact sub_nonneg.mpr hab.le
  have hCS := integral_square_bound (volume.restrict (Icc a b))
    (by rw [hmass]; exact sub_pos.mpr hab) (fun u => |deriv g u|) hgp.norm
  simp only [hmass, sq_abs] at hCS
  have hpos : 0 ≤ ∫ u in Icc a b, |deriv g u| := integral_nonneg fun u => abs_nonneg _
  nlinarith [abs_nonneg (g t - g a), sq_abs (g t - g a)]

 theorem ac_interval_poincare (a b : ℝ) (hab : a < b) (g : ℝ → ℝ)
    (hg : AbsolutelyContinuousOnInterval g a b)
    (hgp : MemLp (deriv g) 2 (volume.restrict (Icc a b))) :
    (∫ t in Icc a b, (g t - g a) ^ 2) ≤
      (b - a) ^ 2 * ∫ u in Icc a b, deriv g u ^ 2 := by
  have hcont : ContinuousOn g (Icc a b) := by simpa [uIcc_of_le hab.le] using hg.continuousOn
  have hi : IntegrableOn (fun t => (g t - g a) ^ 2) (Icc a b) :=
    (hcont.sub continuousOn_const).pow 2 |>.integrableOn_Icc
  have he := integral_mono_ae hi (integrable_const ((b - a) * ∫ u in Icc a b, deriv g u ^ 2))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact ac_endpoint_square_bound a b hab g hg hgp t ht)
  have hmass : (volume.restrict (Icc a b)).real univ = b - a := by
    rw [Measure.real, Measure.restrict_apply_univ, Real.volume_Icc, ENNReal.toReal_ofReal]
    exact sub_nonneg.mpr hab.le
  rw [integral_const, smul_eq_mul, hmass] at he
  convert he using 1 <;> ring

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
