import NativeBoundaryDualEllipticity
import NativeBoundaryCurlIdentity

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization QuasilinearBootstrap

theorem native_raw_matrix_quadratic
    {J : Set Jet} (Q : SmoothQuasilinearOperator J) (u : E2 → ℝ) (x ξ : E2) :
    (∑ i : Fin 2, ∑ j : Fin 2, rawPrincipalMatrix Q u x i j * ξ j * ξ i) =
      inner ℝ (fluxDp Q (firstJet u x) ξ) ξ := by
  have he : ξ = ξ 0 • coordinateVector 2 0 + ξ 1 • coordinateVector 2 1 := by
    ext i
    fin_cases i <;> simp [coordinateVector]
  have hL := congrArg (fluxDp Q (firstJet u x)) he
  rw [hL]
  simp only [rawPrincipalMatrix, map_add, map_smul, PiLp.add_apply, PiLp.smul_apply,
    smul_eq_mul, PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_two]
  ring

theorem native_dual_flux_relation
    (a : Matrix (Fin 2) (Fin 2) ℝ) (F v e : E2)
    (hΔ : a 0 0 * a 1 1 - a 0 1 * a 1 0 ≠ 0)
    (h₀ : F 0 = e 0 - a 1 0 * v 0 - a 1 1 * v 1)
    (h₁ : F 1 = e 1 + a 0 0 * v 0 + a 0 1 * v 1) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2) (nativeDualMatrix a) F -
      Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2) (nativeDualMatrix a) e = nativeQuarterTurn v := by
  have hcon := native_conjugate_flux_algebra a (v 0) (v 1) (F 0) (F 1) (e 0) (e 1) h₀ h₁
  ext i
  simp only [PiLp.sub_apply, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  fin_cases i
  · change (nativeDualMatrix a 0 0 * F 0 + nativeDualMatrix a 0 1 * F 1) -
      (nativeDualMatrix a 0 0 * e 0 + nativeDualMatrix a 0 1 * e 1) = nativeQuarterTurn v 0
    rw [nativeQuarterTurn_zero]
    dsimp [nativeDualMatrix]
    field_simp [hΔ]
    nlinarith [hcon.1]
  · change (nativeDualMatrix a 1 0 * F 0 + nativeDualMatrix a 1 1 * F 1) -
      (nativeDualMatrix a 1 0 * e 0 + nativeDualMatrix a 1 1 * e 1) = nativeQuarterTurn v 1
    rw [nativeQuarterTurn_one]
    dsimp [nativeDualMatrix]
    field_simp [hΔ]
    nlinarith [hcon.2]

theorem C1QuasilinearDirichletSolution.native_normal_flux_dual_relation
    {ρ : ℝ} {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (x : E2) (hx : x ∈ openHalfDisc ρ) :
    let a := rawPrincipalMatrix Q u x
    let v := planarGradient (fun y => fderivWithin ℝ u (closedHalfDisc ρ) y (coordinateVector 2 1)) x
    let F := planarGradient (fun y => Q.flux (firstJetWithin ρ u y) 0) x
    let e := (-Q.lowerOrder (firstJet u x) -
      fluxDx Q (firstJet u x) (coordinateVector 2 1) 1 -
      fluxDz Q (firstJet u x) 1 * planarGradient u x 1) • coordinateVector 2 0 +
      (fluxDx Q (firstJet u x) (coordinateVector 2 1) 0 +
       fluxDz Q (firstJet u x) 0 * planarGradient u x 1) • coordinateVector 2 1
    Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2) (nativeDualMatrix a) F -
      Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2) (nativeDualMatrix a) e = nativeQuarterTurn v := by
  dsimp only
  obtain ⟨κ, hκ, hell⟩ := hsolution.uniformly_elliptic
  have hj : firstJet u x ∈ J := by
    simpa only [← firstJetWithin_eq_firstJet u hx] using
      hsolution.attained_jets x (openHalfDisc_subset_closedHalfDisc ρ hx)
  have he : ∀ ξ : E2, κ * ‖ξ‖ ^ 2 ≤
      ∑ i : Fin 2, ∑ j : Fin 2, rawPrincipalMatrix Q u x i j * ξ j * ξ i := by
    intro ξ
    rw [native_raw_matrix_quadratic]
    exact hell x (u x) (planarGradient u x) ξ hj
  have hΔ := native_coercive_matrix_determinant_lower (rawPrincipalMatrix Q u x) κ hκ he
  have hΔne : rawPrincipalMatrix Q u x 0 0 * rawPrincipalMatrix Q u x 1 1 -
      rawPrincipalMatrix Q u x 0 1 * rawPrincipalMatrix Q u x 1 0 ≠ 0 :=
    (lt_of_lt_of_le (sq_pos_of_pos (by linarith)) hΔ).ne'
  have hcon := hsolution.native_flux_conjugacy x hx
  apply native_dual_flux_relation _ _ _ _ hΔne
  · simpa [coordinateVector] using hcon.1
  · simpa [coordinateVector] using hcon.2

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
