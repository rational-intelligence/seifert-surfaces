import InitialArcResidualGreen_v445

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal

namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates

local macro "paid_fourier_moments" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialFourierMoments_v445 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.real_sin_cos_moments_kill_fourier_v445)⟩
local macro "paid_supported_residual" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialFourierConstancy_v445 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.interval_L2_supported_residual_zero_v445)⟩

/- The actual full-period angular Green equations determine the weak trace
uniquely. Exterior support removes the constant left undetected by derivatives. -/
private theorem real_arc_trace_uniqueness_v445
    (u v : ℝ) (huv : u ≤ v) (hvp : v < u + 2 * Real.pi)
    (F c : ℝ → ℝ)
    (hF : MemLp F 2 (volume.restrict (Icc u (u + 2 * Real.pi))))
    (hc : ContinuousOn c (Icc u v))
    (Foutside : ∀ t ∈ Ioo v (u + 2 * Real.pi), F t = 0)
    (pairing_cos : ∀ n : ℤ, n ≠ 0 →
      (∫ t in Icc u (u + 2 * Real.pi),
        (F t - (Icc u v).indicator c t) *
          deriv (fun z => Real.cos ((n : ℝ) * z)) t) = 0)
    (pairing_sin : ∀ n : ℤ, n ≠ 0 →
      (∫ t in Icc u (u + 2 * Real.pi),
        (F t - (Icc u v).indicator c t) *
          deriv (fun z => Real.sin ((n : ℝ) * z)) t) = 0) :
    F =ᵐ[volume.restrict (Icc u v)] c := by
  classical
  let W := Icc u (u + 2 * Real.pi)
  let V := Icc u v
  let residual : ℝ → ℝ := fun t => F t - V.indicator c t
  have hVW : V ⊆ W := fun t ht => ⟨ht.1, ht.2.trans hvp.le⟩
  let : IsFiniteMeasure (volume.restrict V) :=
    isFiniteMeasure_restrict.mpr measure_Icc_lt_top.ne
  have hcI : IntegrableOn c V := ContinuousOn.integrableOn_compact isCompact_Icc hc
  have hcSq : IntegrableOn (fun t => ‖c t‖ ^ 2) V :=
    ContinuousOn.integrableOn_compact isCompact_Icc (hc.norm.pow 2)
  have hcL2 : MemLp c 2 (volume.restrict V) :=
    (memLp_two_iff_integrable_sq_norm hcI.aestronglyMeasurable).mpr hcSq
  have hci : MemLp (V.indicator c) 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_Icc.nullMeasurableSet).mpr hcL2
  have hR : MemLp residual 2 (volume.restrict W) := hF.sub (hci.restrict W)
  have hRcomplex : MemLp (fun t => (residual t : ℂ)) 2 (volume.restrict W) :=
    hR.continuousLinearMap_comp Complex.ofRealCLM
  have hmem : MemLp (fun t => (residual t : ℂ)) 2
      (volume.restrict (Ioc u (u + 2 * Real.pi))) := hRcomplex.mono_measure
    (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)
  have hcoeff : ∀ n : ℤ, n ≠ 0 →
      fourierCoeffOn (lt_add_of_pos_right u (by positivity : 0 < 2 * Real.pi))
        (fun t => (residual t : ℂ)) n = 0 := by
    intro n hn
    have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hdc : ∀ t : ℝ, deriv (fun z => Real.cos ((n : ℝ) * z)) t =
        -(n : ℝ) * Real.sin ((n : ℝ) * t) := by
      intro t
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (((hasDerivAt_id t).const_mul (n : ℝ)).cos).deriv
    have hds : ∀ t : ℝ, deriv (fun z => Real.sin ((n : ℝ) * z)) t =
        (n : ℝ) * Real.cos ((n : ℝ) * t) := by
      intro t
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (((hasDerivAt_id t).const_mul (n : ℝ)).sin).deriv
    have hcos := pairing_sin n hn
    have hsin := pairing_cos n hn
    simp only [hds] at hcos
    simp only [hdc] at hsin
    have hcosrewrite :
        (fun t => residual t * ((n : ℝ) * Real.cos ((n : ℝ) * t))) =
          (fun t => (n : ℝ) * (residual t * Real.cos ((n : ℝ) * t))) := by
      funext t
      ring
    have hsinrewrite :
        (fun t => residual t * (-(n : ℝ) * Real.sin ((n : ℝ) * t))) =
          (fun t => -(n : ℝ) * (residual t * Real.sin ((n : ℝ) * t))) := by
      funext t
      ring
    change (∫ t in W, residual t * ((n : ℝ) * Real.cos ((n : ℝ) * t))) = 0 at hcos
    change (∫ t in W, residual t * (-(n : ℝ) * Real.sin ((n : ℝ) * t))) = 0 at hsin
    rw [hcosrewrite, integral_const_mul] at hcos
    rw [hsinrewrite, integral_const_mul] at hsin
    exact paid_fourier_moments u residual hR n
      ((mul_eq_zero.mp hcos).resolve_left hnreal)
      ((mul_eq_zero.mp hsin).resolve_left (neg_ne_zero.mpr hnreal))
  let S := Ioo v (u + 2 * Real.pi)
  have hS : volume S ≠ 0 := by
    rw [Real.volume_Ioo]
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hvp)).ne'
  have hsubS : S ⊆ Ioc u (u + 2 * Real.pi) :=
    fun t ht => ⟨huv.trans_lt ht.1, ht.2.le⟩
  have hzero : ∀ t ∈ S, (residual t : ℂ) = 0 := by
    intro t ht
    have htV : t ∉ V := fun hv => (not_le_of_gt ht.1) hv.2
    simp only [residual, V, indicator_of_notMem htV, Foutside t ht, sub_zero,
      Complex.ofReal_zero]
  have hz := paid_supported_residual u (2 * Real.pi) (by positivity)
    (fun t => (residual t : ℂ)) hmem hcoeff S hS hsubS hzero
  have hzcc : ∀ᵐ t ∂volume.restrict W, (residual t : ℂ) = 0 := by
    exact ae_restrict_congr_set Ioc_ae_eq_Icc |>.mp hz
  have hzV := ae_restrict_of_ae_restrict_of_subset hVW hzcc
  filter_upwards [hzV, ae_restrict_mem measurableSet_Icc] with t ht htm
  have hr : residual t = 0 := Complex.ofReal_injective ht
  simpa only [residual, V, indicator_of_mem htm, sub_eq_zero] using hr

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
