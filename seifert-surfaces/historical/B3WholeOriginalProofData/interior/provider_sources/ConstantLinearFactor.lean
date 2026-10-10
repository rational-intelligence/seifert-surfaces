import WeakDivergenceData
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Positive

noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff
namespace SeifertSurfaces.WeakSchauder

theorem symmetricPart_isHermitian (A : Mat) : (symmetricPart A).IsHermitian := by
  ext i j
  simp [symmetricPart, Matrix.conjTranspose_apply, Matrix.transpose_apply, add_comm, mul_add]

theorem matMulE_eq_toEuclideanCLM (A : Mat) (x : V) :
    DeGiorgi.matMulE A x = (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 3)) A x := rfl

theorem symmetricPart_quadratic (A : Mat) (x : V) :
    inner ℝ x (DeGiorgi.matMulE (symmetricPart A) x) =
      inner ℝ x (DeGiorgi.matMulE A x) := by
  simp only [matMulE_eq_toEuclideanCLM, Matrix.inner_toEuclideanCLM]
  simp [symmetricPart, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

open scoped MatrixOrder in
theorem constant_linear_factor (center : V) (R κ Λ : ℝ)
    (hR : 0 < R) (hκ : 0 < κ) (hΛ : κ ≤ Λ) (A : Mat)
    (hA : CoefficientBounds (fun _ => A) (Metric.ball center R) κ Λ) :
    ∃ P : V ≃L[ℝ] V,
      (∀ ξ : V, DeGiorgi.matMulE (symmetricPart A) ξ =
        P (P.toContinuousLinearMap.adjoint ξ)) ∧
      ‖P.toContinuousLinearMap‖ ≤ Real.sqrt Λ ∧
      ‖P.symm.toContinuousLinearMap‖ ≤ (Real.sqrt κ)⁻¹ := by
  have hcenter : center ∈ Metric.ball center R := Metric.mem_ball_self hR
  have hlower (x : V) : κ * ‖x‖ ^ 2 ≤
      inner ℝ x (DeGiorgi.matMulE (symmetricPart A) x) := by
    rw [symmetricPart_quadratic]
    exact hA.coercive center hcenter x
  have hupper (x : V) : inner ℝ x (DeGiorgi.matMulE (symmetricPart A) x) ≤
      Λ * ‖x‖ ^ 2 := by
    rw [symmetricPart_quadratic, real_inner_comm]
    calc
      _ ≤ |inner ℝ (DeGiorgi.matMulE A x) x| := le_abs_self _
      _ ≤ Λ * ‖x‖ * ‖x‖ := hA.mixed center hcenter x x
      _ = _ := by ring
  have hpos : (symmetricPart A).PosSemidef := by
    apply Matrix.isPositive_toEuclideanLin_iff.mp
    refine ⟨Matrix.isSymmetric_toEuclideanLin_iff.mpr (symmetricPart_isHermitian A), ?_⟩
    intro x
    change 0 ≤ inner ℝ (DeGiorgi.matMulE (symmetricPart A) x) x
    rw [real_inner_comm]
    exact (mul_nonneg hκ.le (sq_nonneg _)).trans (hlower x)
  let B : V →L[ℝ] V := (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 3)) (CFC.sqrt (symmetricPart A))
  have hBstar : B.adjoint = B := by
    change star ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 3)) _) = (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 3)) _
    rw [← map_star]
    exact congrArg (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 3)) (CFC.sqrt_nonneg (symmetricPart A)).isSelfAdjoint.star_eq
  have hBB (x : V) : B (B x) = DeGiorgi.matMulE (symmetricPart A) x := by
    have hm := congrArg (fun M : Mat => (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 3)) M x)
      (CFC.sqrt_mul_sqrt_self (symmetricPart A) hpos.nonneg)
    simpa only [B, matMulE_eq_toEuclideanCLM, map_mul, mul_apply_eq_comp] using hm
  have hnorm (x : V) : ‖B x‖ ^ 2 = inner ℝ x (DeGiorgi.matMulE (symmetricPart A) x) := by
    calc
      ‖B x‖ ^ 2 = inner ℝ x (B.adjoint (B x)) := by
        rw [ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]
      _ = _ := by rw [hBstar, hBB]
  have hinj : Function.Injective B := by
    apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    change B x = 0 at hx
    have hxnorm : ‖x‖ ^ 2 = 0 := by
      have hl := hlower x
      rw [← hnorm, hx, norm_zero, zero_pow (by decide)] at hl
      nlinarith [sq_nonneg ‖x‖]
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hxnorm)
  let P : V ≃L[ℝ] V := (LinearEquiv.ofBijective B.toLinearMap
    ((LinearMap.injective_iff_surjective).mp hinj |> fun hs => ⟨hinj, hs⟩)).toContinuousLinearEquiv
  have hP : P.toContinuousLinearMap = B := rfl
  refine ⟨P, ?_, ?_, ?_⟩
  · intro x
    change DeGiorgi.matMulE (symmetricPart A) x = P.toContinuousLinearMap (P.toContinuousLinearMap.adjoint x)
    rw [hP, hBstar, hBB]
  · rw [hP]
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro x
    apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    rw [← sq, ← sq]
    rw [mul_pow, Real.sq_sqrt (hκ.le.trans hΛ), hnorm]
    exact hupper x
  · apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
    intro x
    have hs : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
    have hl := hlower (P.symm x)
    rw [← hnorm, ← hP] at hl
    change κ * ‖P.symm x‖ ^ 2 ≤ ‖P (P.symm x)‖ ^ 2 at hl
    rw [P.apply_symm_apply] at hl
    have hmul : Real.sqrt κ * ‖P.symm x‖ ≤ ‖x‖ := by
      apply nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _)
      rw [← sq, ← sq]
      rwa [mul_pow, Real.sq_sqrt hκ.le]
    change ‖P.symm x‖ ≤ (Real.sqrt κ)⁻¹ * ‖x‖
    exact (le_inv_mul_iff₀ hs).mpr hmul

end SeifertSurfaces.WeakSchauder
