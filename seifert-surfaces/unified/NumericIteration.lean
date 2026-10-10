import WeakDivergenceData
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
open scoped BigOperators
namespace SeifertSurfaces.WeakSchauder

theorem numeric_coupled_bounds (q L b : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (hL : 0 ≤ L) (hb : 0 ≤ b)
    (hsmall : b * (1 + (1 + L / (1 - q)) ^ 2) ≤ q ^ 2 / 2)
    (e : ℕ → ℝ) (m : ℕ → V) (he : ∀ k, 0 ≤ e k)
    (herec : ∀ k, e (k + 1) ≤ q ^ 2 / 4 * e k +
      b * (q ^ k) ^ 2 * (e k + ‖m k‖ ^ 2))
    (hmrec : ∀ k, ‖m (k + 1) - m k‖ ≤ L * Real.sqrt (e k)) :
    (∀ k, e k ≤ (e 0 + ‖m 0‖ ^ 2) * (q ^ k) ^ 2) ∧
    (∀ k, ‖m k‖ ^ 2 ≤ (1 + L / (1 - q)) ^ 2 * (e 0 + ‖m 0‖ ^ 2)) := by
  let E := e 0 + ‖m 0‖ ^ 2
  let S := Real.sqrt E
  let B := 1 + L / (1 - q)
  have hE : 0 ≤ E := add_nonneg (he 0) (sq_nonneg _)
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hSsq : S ^ 2 = E := Real.sq_sqrt hE
  have hden : 0 < 1 - q := sub_pos.mpr hq1
  have hB : 1 ≤ B := by
    dsimp [B]
    linarith [div_nonneg hL hden.le]
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hpow (k : ℕ) : 0 ≤ q ^ k := pow_nonneg hq.le _
  have hpow1 (k : ℕ) : q ^ k ≤ 1 := pow_le_one₀ hq.le hq1.le
  have hT (k : ℕ) : 0 ≤ 1 + L * ((1 - q ^ k) / (1 - q)) := by
    have : 0 ≤ 1 - q ^ k := sub_nonneg.mpr (hpow1 k)
    positivity
  have hTB (k : ℕ) : 1 + L * ((1 - q ^ k) / (1 - q)) ≤ B := by
    dsimp [B]
    have hquot : (1 - q ^ k) / (1 - q) ≤ 1 / (1 - q) := by
      gcongr
      nlinarith [hpow k]
    have := mul_le_mul_of_nonneg_left hquot hL
    simpa [div_eq_mul_inv] using add_le_add_left this 1
  have hinit : ‖m 0‖ ≤ S := by
    apply (Real.le_sqrt (norm_nonneg _) hE).mpr
    dsimp [E]
    linarith [he 0]
  have hinv : ∀ k, e k ≤ E * (q ^ k) ^ 2 ∧
      ‖m k‖ ≤ S * (1 + L * ((1 - q ^ k) / (1 - q))) := by
    intro k
    induction k with
    | zero =>
        constructor
        · simp only [pow_zero, mul_one]
          dsimp [E]
          linarith [sq_nonneg ‖m 0‖]
        · simpa using hinit
    | succ k ih =>
        have hmk : ‖m k‖ ≤ S * B :=
          ih.2.trans (mul_le_mul_of_nonneg_left (hTB k) hS)
        have hmksq : ‖m k‖ ^ 2 ≤ B ^ 2 * E := by
          have := pow_le_pow_left₀ (norm_nonneg _) hmk 2
          nlinarith only [this, hSsq]
        have hek : e k ≤ E := by
          have hp : (q ^ k) ^ 2 ≤ 1 := pow_le_one₀ (hpow k) (hpow1 k)
          exact ih.1.trans ((mul_le_mul_of_nonneg_left hp hE).trans_eq (mul_one E))
        have henergy : e k + ‖m k‖ ^ 2 ≤ (1 + B ^ 2) * E := by
          nlinarith only [hek, hmksq]
        have he_next : e (k + 1) ≤ E * (q ^ (k + 1)) ^ 2 := by
          calc
            e (k + 1) ≤ q ^ 2 / 4 * e k + b * (q ^ k) ^ 2 *
                (e k + ‖m k‖ ^ 2) := herec k
            _ ≤ q ^ 2 / 4 * (E * (q ^ k) ^ 2) +
                b * (q ^ k) ^ 2 * ((1 + B ^ 2) * E) := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left ih.1 (by positivity)
              · exact mul_le_mul_of_nonneg_left henergy (by positivity)
            _ = (q ^ 2 / 4 + b * (1 + B ^ 2)) * E * (q ^ k) ^ 2 := by ring
            _ ≤ q ^ 2 * E * (q ^ k) ^ 2 := by
              apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
              apply mul_le_mul_of_nonneg_right _ hE
              dsimp [B] at *
              linarith [sq_nonneg q]
            _ = E * (q ^ (k + 1)) ^ 2 := by rw [pow_succ]; ring
        have hsqrt : Real.sqrt (e k) ≤ S * q ^ k := by
          have := Real.sqrt_le_sqrt ih.1
          simpa [Real.sqrt_mul hE, Real.sqrt_sq (hpow k), S] using this
        have hm_next : ‖m (k + 1)‖ ≤
            S * (1 + L * ((1 - q ^ (k + 1)) / (1 - q))) := by
          calc
            ‖m (k + 1)‖ ≤ ‖m k‖ + ‖m (k + 1) - m k‖ := norm_le_insert' _ _
            _ ≤ S * (1 + L * ((1 - q ^ k) / (1 - q))) + L * Real.sqrt (e k) :=
              add_le_add ih.2 (hmrec k)
            _ ≤ S * (1 + L * ((1 - q ^ k) / (1 - q))) + L * (S * q ^ k) := by gcongr
            _ = S * (1 + L * ((1 - q ^ (k + 1)) / (1 - q))) := by
              rw [pow_succ]
              field_simp
              ring
        exact ⟨he_next, hm_next⟩
  refine ⟨fun k => (hinv k).1, ?_⟩
  intro k
  have hmk := (hinv k).2.trans (mul_le_mul_of_nonneg_left (hTB k) hS)
  have := pow_le_pow_left₀ (norm_nonneg _) hmk 2
  nlinarith only [this, hSsq]

end SeifertSurfaces.WeakSchauder
