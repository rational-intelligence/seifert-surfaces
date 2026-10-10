import VM02aDirectMethod
set_option autoImplicit false
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectMethod.CourantTraceFluxAssembly
open SeifertSurfaces.AppendixACoordinates

theorem actual_chord_logarithmic_radius_selection
    (b : ℝ → E2) (hb : Continuous b) (s a z K lambda : ℝ)
    (ha : 0 < a) (haz : a < z) (hz : z < 1) (hK : 0 < K)
    (hlambda : 0 < lambda) :
    let alpha : ℝ → ℝ := fun r => 2 * Real.arcsin (r / 2)
    let g : ℝ → E2 := fun r => b (s - alpha r) - b (s + alpha r)
    IntegrableOn (fun r => ‖g r‖ ^ 2 / r) (Ioo a z) →
      (∫ r in Ioo a z, ‖g r‖ ^ 2 / r) ≤ (2 * Real.pi) * K →
      (2 * Real.pi) * K < lambda ^ 2 * Real.log (z / a) →
      ∃ r ∈ Ioo a z, dist (b (s - alpha r)) (b (s + alpha r)) < lambda := by
  classical
  dsimp only
  intro hint hbound hstrict
  by_contra hn
  push Not at hn
  have hzpos : 0 < z := ha.trans haz
  have hinv : IntegrableOn (fun r : ℝ => r⁻¹) (Ioo a z) :=
    (continuousOn_id.inv₀ (fun r hr => (ha.trans_le hr.1).ne')).integrableOn_Icc.mono_set
      Ioo_subset_Icc_self
  have hlog : (∫ r in Ioo a z, r⁻¹) = Real.log (z / a) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le haz.le]
    exact integral_inv_of_pos ha hzpos
  have hmono : (∫ r in Ioo a z, lambda ^ 2 * r⁻¹) ≤
      ∫ r in Ioo a z, ‖b (s - 2 * Real.arcsin (r / 2)) -
        b (s + 2 * Real.arcsin (r / 2))‖ ^ 2 / r := by
    apply setIntegral_mono_on (hinv.const_mul (lambda ^ 2)) hint measurableSet_Ioo
    intro r hr
    have hchord : lambda ≤ ‖b (s - 2 * Real.arcsin (r / 2)) -
        b (s + 2 * Real.arcsin (r / 2))‖ := by
      simpa only [dist_eq_norm] using hn r hr
    have hsq : lambda ^ 2 ≤ ‖b (s - 2 * Real.arcsin (r / 2)) -
        b (s + 2 * Real.arcsin (r / 2))‖ ^ 2 :=
      (sq_le_sq₀ hlambda.le (norm_nonneg _)).mpr hchord
    simpa only [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_right hsq (inv_nonneg.mpr (ha.trans hr.1).le)
  rw [integral_const_mul, hlog] at hmono
  exact (not_lt_of_ge (hmono.trans hbound)) hstrict

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectMethod.CourantTraceFluxAssembly
