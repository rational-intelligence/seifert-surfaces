import InitialArcResidualGreen_v445

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal

namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates

local macro "paid_fourier_moments" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialFourierMoments_v445 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.real_sin_cos_moments_kill_fourier_v445)⟩
local macro "paid_constant_residual" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialFourierConstancy_v445 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.interval_L2_nonconstant_coefficients_vanish_v445)⟩

/- The actual full-period angular Green equations determine the weak trace
uniquely. Exterior support removes the constant left undetected by derivatives. -/
private theorem real_periodic_trace_constant_v460
    (u : ℝ)
    (F c : ℝ → ℝ)
    (hF : MemLp F 2 (volume.restrict (Icc u (u + 2 * Real.pi))))
    (hc : ContinuousOn c (Icc u (u+2*Real.pi)))
    (pairing_cos : ∀ n : ℤ, n ≠ 0 →
      (∫ t in Icc u (u + 2 * Real.pi),
        (F t - c t) *
          deriv (fun z => Real.cos ((n : ℝ) * z)) t) = 0)
    (pairing_sin : ∀ n : ℤ, n ≠ 0 →
      (∫ t in Icc u (u + 2 * Real.pi),
        (F t - c t) *
          deriv (fun z => Real.sin ((n : ℝ) * z)) t) = 0) :
    ∃ k:ℝ,F =ᵐ[volume.restrict (Icc u (u+2*Real.pi))] (fun t=>c t+k) := by
  classical
  let W := Icc u (u + 2 * Real.pi)
  let residual : ℝ → ℝ := fun t=>F t-c t
  have hcI : IntegrableOn c W := ContinuousOn.integrableOn_compact isCompact_Icc hc
  have hcSq : IntegrableOn (fun t=>‖c t‖^2) W :=
    ContinuousOn.integrableOn_compact isCompact_Icc (hc.norm.pow 2)
  have hcL2 : MemLp c 2 (volume.restrict W) :=
    (memLp_two_iff_integrable_sq_norm hcI.aestronglyMeasurable).mpr hcSq
  have hR : MemLp residual 2 (volume.restrict W) := hF.sub hcL2
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
  have hconstant := paid_constant_residual u (2*Real.pi) (by positivity)
    (fun t=>(residual t:ℂ)) hmem hcoeff
  let k : ℝ := (fourierCoeffOn (lt_add_of_pos_right u (by positivity : 0 < 2*Real.pi))
    (fun t=>(residual t:ℂ)) 0).re
  have hcc : ∀ᵐ t ∂volume.restrict W,(residual t:ℂ)=
      fourierCoeffOn (lt_add_of_pos_right u (by positivity : 0 < 2*Real.pi))
        (fun t=>(residual t:ℂ)) 0 := ae_restrict_congr_set Ioc_ae_eq_Icc |>.mp hconstant
  refine ⟨k,?_⟩
  filter_upwards [hcc] with t ht
  have hr : residual t=k := congrArg Complex.re ht
  dsimp only [residual] at hr
  linarith

private theorem real_periodic_trace_constant_positive_v460
    (u : ℝ)
    (F c : ℝ → ℝ)
    (hF : MemLp F 2 (volume.restrict (Icc u (u + 2 * Real.pi))))
    (hc : ContinuousOn c (Icc u (u+2*Real.pi)))
    (pairing_cos : ∀ n : ℕ, 0 < n →
      (∫ t in Icc u (u + 2 * Real.pi),
        (F t - c t) *
          deriv (fun z => Real.cos ((n : ℝ) * z)) t) = 0)
    (pairing_sin : ∀ n : ℕ, 0 < n →
      (∫ t in Icc u (u + 2 * Real.pi),
        (F t - c t) *
          deriv (fun z => Real.sin ((n : ℝ) * z)) t) = 0) :
    ∃ k:ℝ,F =ᵐ[volume.restrict (Icc u (u+2*Real.pi))] (fun t=>c t+k) := by
  apply real_periodic_trace_constant_v460 u F c hF hc
  · intro n hn
    cases n with
    | ofNat n => exact pairing_cos n (Nat.pos_of_ne_zero (by intro h; apply hn; subst n; rfl))
    | negSucc n =>
      have he : (fun z : ℝ => Real.cos ((Int.negSucc n : ℝ) * z)) =
          (fun z : ℝ => Real.cos (((n + 1 : ℕ) : ℝ) * z)) := by
        funext z
        simp only [Int.cast_negSucc, Nat.cast_add, Nat.cast_one, neg_mul, Real.cos_neg]
      rw [he]
      exact pairing_cos (n + 1) (by omega)
  · intro n hn
    cases n with
    | ofNat n => exact pairing_sin n (Nat.pos_of_ne_zero (by intro h; apply hn; subst n; rfl))
    | negSucc n =>
      have he : (fun z : ℝ => Real.sin ((Int.negSucc n : ℝ) * z)) =
          (fun z : ℝ => -Real.sin (((n + 1 : ℕ) : ℝ) * z)) := by
        funext z
        simp only [Int.cast_negSucc, Nat.cast_add, Nat.cast_one, neg_mul, Real.sin_neg]
      rw [he]
      have hd : ∀ t : ℝ, deriv (fun z => -Real.sin (((n + 1 : ℕ) : ℝ) * z)) t =
          -deriv (fun z => Real.sin (((n + 1 : ℕ) : ℝ) * z)) t := by
        intro t
        exact deriv.fun_neg
      simp only [hd, mul_neg, integral_neg, pairing_sin (n + 1) (by omega), neg_zero]

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
