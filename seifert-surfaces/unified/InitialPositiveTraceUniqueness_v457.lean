import InitialArcTraceUniqueness_v445

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates

local macro "paid_arc_trace_uniqueness" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialArcTraceUniqueness_v445 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.real_arc_trace_uniqueness_v445)⟩

private theorem real_arc_trace_uniqueness_positive_v457
    (u v : ℝ) (huv : u ≤ v) (hvp : v < u + 2 * Real.pi)
    (F c : ℝ → ℝ)
    (hF : MemLp F 2 (volume.restrict (Icc u (u + 2 * Real.pi))))
    (hc : ContinuousOn c (Icc u v))
    (Foutside : ∀ t ∈ Ioo v (u + 2 * Real.pi), F t = 0)
    (pairing_cos : ∀ n : ℕ, 0 < n →
      (∫ t in Icc u (u + 2 * Real.pi),
        (F t - (Icc u v).indicator c t) *
          deriv (fun z => Real.cos ((n : ℝ) * z)) t) = 0)
    (pairing_sin : ∀ n : ℕ, 0 < n →
      (∫ t in Icc u (u + 2 * Real.pi),
        (F t - (Icc u v).indicator c t) *
          deriv (fun z => Real.sin ((n : ℝ) * z)) t) = 0) :
    F =ᵐ[volume.restrict (Icc u v)] c := by
  apply paid_arc_trace_uniqueness u v huv hvp F c hF hc Foutside
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

private theorem scaled_angular_green_v457
    (q : ℝ) (hq : q ≠ 0) (n : ℕ) (S : Set ℝ)
    (a F psi : ℝ → ℝ) (hpsi : ContDiff ℝ ∞ psi)
    (u v b0 b1 : ℝ)
    (hscaled :
      (∫ t in S, a t * (q ^ n * psi t) +
        F t * deriv (fun z => q ^ n * psi z) t) =
        b1 * (q ^ n * psi v) - b0 * (q ^ n * psi u)) :
    (∫ t in S, a t * psi t + F t * deriv psi t) = b1 * psi v - b0 * psi u := by
  have hd : ∀ t : ℝ, deriv (fun z => q ^ n * psi z) t = q ^ n * deriv psi t := by
    intro t
    exact ((hpsi.differentiable (by simp) t).hasDerivAt.const_mul (q ^ n)).deriv
  simp only [hd] at hscaled
  have he : (fun t => a t * (q ^ n * psi t) + F t * (q ^ n * deriv psi t)) =
      (fun t => q ^ n * (a t * psi t + F t * deriv psi t)) := by
    funext t
    ring
  rw [he, integral_const_mul] at hscaled
  have hb : b1 * (q ^ n * psi v) - b0 * (q ^ n * psi u) =
      q ^ n * (b1 * psi v - b0 * psi u) := by ring
  rw [hb] at hscaled
  exact mul_left_cancel₀ (pow_ne_zero n hq) hscaled

private theorem nat_frequency_periodic_v457 (n : ℕ) :
    Periodic (fun t : ℝ => Real.cos ((n : ℝ) * t)) (2 * Real.pi) ∧
    Periodic (fun t : ℝ => Real.sin ((n : ℝ) * t)) (2 * Real.pi) := by
  constructor
  · intro t
    dsimp only
    rw [mul_add]
    exact Real.cos_add_nat_mul_two_pi _ n
  · intro t
    dsimp only
    rw [mul_add]
    exact Real.sin_add_nat_mul_two_pi _ n

private theorem periodic_angular_green_shift_v457
    (a F psi : ℝ → ℝ)
    (ha : Periodic a (2 * Real.pi)) (hF : Periodic F (2 * Real.pi))
    (hpsi : Periodic psi (2 * Real.pi))
    (hdpsi : Periodic (deriv psi) (2 * Real.pi)) (u : ℝ) :
    (∫ t in Icc u (u + 2 * Real.pi), a t * psi t + F t * deriv psi t) =
      ∫ t in Ioo (-Real.pi) Real.pi, a t * psi t + F t * deriv psi t := by
  have hperiod : Periodic (fun t => a t * psi t + F t * deriv psi t) (2 * Real.pi) :=
    fun t => by dsimp only; rw [ha t, hF t, hpsi t, hdpsi t]
  have he := hperiod.intervalIntegral_add_eq u (-Real.pi)
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring,
    intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : u ≤ u + 2 * Real.pi),
    intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)] at he
  simp only [integral_Ioc_eq_integral_Ioo] at he
  rw [integral_Icc_eq_integral_Ioo]
  exact he

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
