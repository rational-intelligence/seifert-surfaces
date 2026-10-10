import NativeBoundaryActualNeumannEquation

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization

theorem native_matrix_inner_quadratic (a : Matrix (Fin 2) (Fin 2) ℝ) (ξ : E2) :
    inner ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2) a ξ) ξ =
      ∑ i : Fin 2, ∑ j : Fin 2, a i j * ξ j * ξ i := by
  simp only [PiLp.inner_apply, Real.inner_apply, Matrix.ofLp_toEuclideanCLM,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

theorem native_principalWithin_toEuclideanCLM (ρ : ℝ) {J : Set Jet}
    (Q : SmoothQuasilinearOperator J) (u : E2 → ℝ) (x : E2) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2) (nativePrincipalWithin ρ Q u x) =
      fluxDp Q (firstJetWithin ρ u x) := by
  ext ξ i
  have he : ξ = ξ 0 • coordinateVector 2 0 + ξ 1 • coordinateVector 2 1 := by
    ext j
    fin_cases j <;> simp [coordinateVector]
  have hL := congrArg (fluxDp Q (firstJetWithin ρ u x)) he
  simp only [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    nativePrincipalWithin]
  rw [hL]
  simp only [map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

theorem native_normal_flux_error_bound (ρ : ℝ) {J : Set Jet}
    (Q : SmoothQuasilinearOperator J) (u : E2 → ℝ) (x : E2) (M : ℝ) (hM : 0 ≤ M)
    (hg : ‖planarGradientWithin u (closedHalfDisc ρ) x‖ ≤ M)
    (hB : |Q.lowerOrder (firstJetWithin ρ u x)| ≤ M)
    (hDx : ‖fluxDx Q (firstJetWithin ρ u x)‖ ≤ M)
    (hDz : ‖fluxDz Q (firstJetWithin ρ u x)‖ ≤ M) :
    ‖nativeNormalFluxError ρ Q u x‖ ≤ 3 * M + 2 * M ^ 2 := by
  have hxD (i : Fin 2) : |fluxDx Q (firstJetWithin ρ u x) (coordinateVector 2 1) i| ≤ M := by
    calc
      _ ≤ ‖fluxDx Q (firstJetWithin ρ u x) (coordinateVector 2 1)‖ := PiLp.norm_apply_le _ i (p := 2)
      _ ≤ ‖fluxDx Q (firstJetWithin ρ u x)‖ * ‖coordinateVector 2 1‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ M := by simpa [coordinateVector, PiLp.norm_single] using hDx
  have hzD (i : Fin 2) : |fluxDz Q (firstJetWithin ρ u x) i| ≤ M :=
    (PiLp.norm_apply_le _ i (p := 2)).trans hDz
  have hgD : |planarGradientWithin u (closedHalfDisc ρ) x 1| ≤ M :=
    (PiLp.norm_apply_le _ 1 (p := 2)).trans hg
  have hm (i : Fin 2) : |fluxDz Q (firstJetWithin ρ u x) i *
      planarGradientWithin u (closedHalfDisc ρ) x 1| ≤ M ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul (hzD i) hgD (abs_nonneg _) hM
  apply (native_planar_norm_le_coordinate_sum _).trans
  simp only [nativeNormalFluxError, coordinateVector, PiLp.add_apply, PiLp.smul_apply,
    EuclideanSpace.single_apply, smul_eq_mul, Fin.isValue, ↓reduceIte, mul_one, mul_zero,
    add_zero, zero_add]
  have hzero : |-Q.lowerOrder (firstJetWithin ρ u x) -
      fluxDx Q (firstJetWithin ρ u x) (coordinateVector 2 1) 1 -
      fluxDz Q (firstJetWithin ρ u x) 1 * planarGradientWithin u (closedHalfDisc ρ) x 1| ≤
      M + M + M ^ 2 :=
    (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans
      (add_le_add (by simpa only [abs_neg] using hB) (hxD 1))) (hm 1))
  have hone := (abs_add_le _ _).trans (add_le_add (hxD 0) (hm 0))
  norm_num [coordinateVector] at hzero hone ⊢
  linarith

theorem native_normal_flux_pointwise_dual_bounds (ρ : ℝ) {J : Set Jet}
    (Q : SmoothQuasilinearOperator J) (g : SmoothDirichletDatum ρ) (u : E2 → ℝ)
    (x : E2) (κ M D : ℝ) (hκ : 0 < κ) (hM : 0 ≤ M)
    (he : ∀ ξ : E2, κ * ‖ξ‖ ^ 2 ≤ inner ℝ (fluxDp Q (firstJetWithin ρ u x) ξ) ξ)
    (ha : ‖fluxDp Q (firstJetWithin ρ u x)‖ ≤ M)
    (hg : ‖planarGradientWithin u (closedHalfDisc ρ) x‖ ≤ M)
    (hB : |Q.lowerOrder (firstJetWithin ρ u x)| ≤ M)
    (hDx : ‖fluxDx Q (firstJetWithin ρ u x)‖ ≤ M)
    (hDz : ‖fluxDz Q (firstJetWithin ρ u x)‖ ≤ M)
    (hD : |deriv (deriv g.value) (x 1)| ≤ D) :
    (∀ ξ : E2, (κ / (2 * M ^ 2 + 1)) * ‖ξ‖ ^ 2 ≤
      inner ℝ ((nativeNormalFluxCoefficients ρ Q g u).a x ξ) ξ) ∧
    ‖(nativeNormalFluxCoefficients ρ Q g u).a x‖ ≤ 4 * (M / ((κ / 2) ^ 2)) ∧
    ‖(nativeNormalFluxCoefficients ρ Q g u).d x‖ ≤
      4 * (M / ((κ / 2) ^ 2)) * (3 * M + 2 * M ^ 2) + D := by
  have hquad : ∀ ξ : E2, κ * ‖ξ‖ ^ 2 ≤
      ∑ i : Fin 2, ∑ j : Fin 2, nativePrincipalWithin ρ Q u x i j * ξ j * ξ i := by
    intro ξ
    rw [← native_matrix_inner_quadratic, native_principalWithin_toEuclideanCLM]
    exact he ξ
  have hentry (i j : Fin 2) : |nativePrincipalWithin ρ Q u x i j| ≤ M := by
    calc
      _ ≤ ‖fluxDp Q (firstJetWithin ρ u x) (coordinateVector 2 j)‖ := PiLp.norm_apply_le _ i (p := 2)
      _ ≤ ‖fluxDp Q (firstJetWithin ρ u x)‖ * ‖coordinateVector 2 j‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ M := by simpa [coordinateVector, PiLp.norm_single] using ha
  obtain ⟨hco, hb⟩ := native_dual_matrix_coercive_and_bounded
    (nativePrincipalWithin ρ Q u x) κ M hκ hM hquad hentry
  have hn := native_matrix_toEuclideanCLM_norm_bound
    (nativeDualMatrix (nativePrincipalWithin ρ Q u x)) (M / ((κ / 2) ^ 2)) (by positivity) hb
  refine ⟨fun ξ => by rw [nativeNormalFluxCoefficients, native_matrix_inner_quadratic]; exact hco ξ,
    hn, ?_⟩
  change ‖-_ + _‖ ≤ _
  calc
    _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2) (nativeDualMatrix (nativePrincipalWithin ρ Q u x))
        (nativeNormalFluxError ρ Q u x)‖ + ‖deriv (deriv g.value) (x 1) • coordinateVector 2 0‖ :=
      (norm_add_le _ _).trans_eq (by rw [norm_neg])
    _ ≤ 4 * (M / ((κ / 2) ^ 2)) * (3 * M + 2 * M ^ 2) + D := by
      rw [norm_smul, Real.norm_eq_abs, show ‖coordinateVector 2 0‖ = 1 by simp [coordinateVector, PiLp.norm_single], mul_one]
      exact add_le_add ((ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul hn (native_normal_flux_error_bound ρ Q u x M hM hg hB hDx hDz)
          (norm_nonneg _) (by positivity))) hD

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
