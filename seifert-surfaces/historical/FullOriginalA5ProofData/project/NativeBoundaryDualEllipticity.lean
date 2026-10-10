import NativeBoundaryConjugateAlgebra

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization QuasilinearBootstrap

def nativeDualMatrix (a : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => a j i / (a 0 0 * a 1 1 - a 0 1 * a 1 0)

theorem native_dual_matrix_coercive_and_bounded
    (a : Matrix (Fin 2) (Fin 2) ℝ) (κ M : ℝ) (hκ : 0 < κ) (hM : 0 ≤ M)
    (he : ∀ ξ : E2, κ * ‖ξ‖ ^ 2 ≤
      ∑ i : Fin 2, ∑ j : Fin 2, a i j * ξ j * ξ i)
    (hb : ∀ i j, |a i j| ≤ M) :
    (∀ ξ : E2, (κ / (2 * M ^ 2 + 1)) * ‖ξ‖ ^ 2 ≤
      ∑ i : Fin 2, ∑ j : Fin 2, nativeDualMatrix a i j * ξ j * ξ i) ∧
    (∀ i j, |nativeDualMatrix a i j| ≤ M / ((κ / 2) ^ 2)) := by
  let Δ := a 0 0 * a 1 1 - a 0 1 * a 1 0
  have hΔlo : (κ / 2) ^ 2 ≤ Δ := native_coercive_matrix_determinant_lower a κ hκ he
  have hΔpos : 0 < Δ := lt_of_lt_of_le (sq_pos_of_pos (by linarith)) hΔlo
  have hΔupper : Δ ≤ 2 * M ^ 2 + 1 := by
    have h₀ := mul_le_mul (hb 0 0) (hb 1 1) (abs_nonneg _) hM
    have h₁ := mul_le_mul (hb 0 1) (hb 1 0) (abs_nonneg _) hM
    have hΔabs : Δ ≤ |a 0 0| * |a 1 1| + |a 0 1| * |a 1 0| := by
      calc
        _ ≤ |a 0 0 * a 1 1| + |a 0 1 * a 1 0| := (le_abs_self _).trans (abs_sub _ _)
        _ = _ := by rw [abs_mul, abs_mul]
    dsimp [Δ] at *
    nlinarith
  refine ⟨?_, ?_⟩
  · intro ξ
    have hnum := he ξ
    have hdiv : κ / (2 * M ^ 2 + 1) ≤ κ / Δ :=
      div_le_div_of_nonneg_left hκ.le hΔpos hΔupper
    have hquad : (∑ i : Fin 2, ∑ j : Fin 2, nativeDualMatrix a i j * ξ j * ξ i) =
        (∑ i : Fin 2, ∑ j : Fin 2, a i j * ξ j * ξ i) / Δ := by
      simp only [nativeDualMatrix, Fin.sum_univ_two]
      dsimp [Δ]
      ring
    rw [hquad]
    calc
      _ ≤ (κ / Δ) * ‖ξ‖ ^ 2 := mul_le_mul_of_nonneg_right hdiv (sq_nonneg _)
      _ = κ * ‖ξ‖ ^ 2 / Δ := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hnum hΔpos.le
  · intro i j
    change |a j i / Δ| ≤ _
    rw [abs_div, abs_of_pos hΔpos]
    exact (div_le_div_of_nonneg_right (hb j i) hΔpos.le).trans
      (div_le_div_of_nonneg_left hM (sq_pos_of_pos (by linarith)) hΔlo)

theorem native_matrix_toEuclideanCLM_norm_bound
    (a : Matrix (Fin 2) (Fin 2) ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ i j, |a i j| ≤ M) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2) a‖ ≤ 4 * M := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro ξ
  have hξ (i : Fin 2) : |ξ i| ≤ ‖ξ‖ := PiLp.norm_apply_le ξ i (p := 2)
  have hi (i : Fin 2) : |(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2) a ξ) i| ≤
      2 * M * ‖ξ‖ := by
    simp only [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    calc
      _ ≤ |a i 0 * ξ 0| + |a i 1 * ξ 1| := abs_add_le _ _
      _ ≤ M * ‖ξ‖ + M * ‖ξ‖ := by
        simp only [abs_mul]
        exact add_le_add
          (mul_le_mul (hb i 0) (hξ 0) (abs_nonneg _) hM)
          (mul_le_mul (hb i 1) (hξ 1) (abs_nonneg _) hM)
      _ = _ := by ring
  calc
    _ ≤ |(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2) a ξ) 0| +
        |(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2) a ξ) 1| := native_planar_norm_le_coordinate_sum _
    _ ≤ 2 * M * ‖ξ‖ + 2 * M * ‖ξ‖ := add_le_add (hi 0) (hi 1)
    _ = _ := by ring

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
