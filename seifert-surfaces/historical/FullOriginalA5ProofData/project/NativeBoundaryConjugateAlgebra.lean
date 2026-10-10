import NativeBoundaryFluxDerivatives

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization QuasilinearBootstrap

theorem native_coercive_matrix_determinant_lower
    (a : Matrix (Fin 2) (Fin 2) ℝ) (κ : ℝ) (hκ : 0 < κ)
    (he : ∀ ξ : E2, κ * ‖ξ‖ ^ 2 ≤
      ∑ i : Fin 2, ∑ j : Fin 2, a i j * ξ j * ξ i) :
    (κ / 2) ^ 2 ≤ a 0 0 * a 1 1 - a 0 1 * a 1 0 := by
  have h00 : κ ≤ a 0 0 := by
    simpa [coordinateVector, Fin.sum_univ_two, PiLp.norm_single] using he (coordinateVector 2 0)
  have h11 : κ ≤ a 1 1 := by
    simpa [coordinateVector, Fin.sum_univ_two, PiLp.norm_single] using he (coordinateVector 2 1)
  let A := a 0 0 - κ / 2
  let B := a 1 1 - κ / 2
  let C := a 0 1 + a 1 0
  have hA : 0 < A := by dsimp [A]; linarith
  have hB : 0 < B := by dsimp [B]; linarith
  let ξ := (-C) • coordinateVector 2 0 + (2 * A) • coordinateVector 2 1
  have hbase : 0 ≤ (∑ i : Fin 2, ∑ j : Fin 2, a i j * ξ j * ξ i) - κ / 2 * ‖ξ‖ ^ 2 := by
    have hh := he ξ
    nlinarith [sq_nonneg ‖ξ‖]
  have hx0 : ξ 0 = -C := by simp [ξ, coordinateVector]
  have hx1 : ξ 1 = 2 * A := by simp [ξ, coordinateVector]
  have hn : ‖ξ‖ ^ 2 = (-C) ^ 2 + (2 * A) ^ 2 := by
    simpa only [Fin.sum_univ_two, hx0, hx1] using EuclideanSpace.real_norm_sq_eq ξ
  have hfact : 0 ≤ A * (4 * A * B - C ^ 2) := by
    have hid : A * (4 * A * B - C ^ 2) =
        (∑ i : Fin 2, ∑ j : Fin 2, a i j * ξ j * ξ i) - κ / 2 * ‖ξ‖ ^ 2 := by
      simp only [Fin.sum_univ_two, hx0, hx1, hn]
      dsimp [A, B, C]
      ring
    rw [hid]
    exact hbase
  have hdisc : 0 ≤ 4 * A * B - C ^ 2 := (mul_nonneg_iff_of_pos_left hA).mp hfact
  dsimp [A, B, C] at hdisc hA hB
  nlinarith [sq_nonneg (a 0 1 - a 1 0), mul_nonneg (le_of_lt hA) (le_of_lt hκ),
    mul_nonneg (le_of_lt hB) (le_of_lt hκ)]

theorem native_conjugate_flux_algebra
    (a : Matrix (Fin 2) (Fin 2) ℝ) (v₀ v₁ F₀ F₁ e₀ e₁ : ℝ)
    (h₀ : F₀ = e₀ - a 1 0 * v₀ - a 1 1 * v₁)
    (h₁ : F₁ = e₁ + a 0 0 * v₀ + a 0 1 * v₁) :
    a 0 0 * (F₀ - e₀) + a 1 0 * (F₁ - e₁) =
        (a 0 0 * a 1 1 - a 0 1 * a 1 0) * (-v₁) ∧
    a 0 1 * (F₀ - e₀) + a 1 1 * (F₁ - e₁) =
        (a 0 0 * a 1 1 - a 0 1 * a 1 0) * v₀ := by
  rw [h₀, h₁]
  constructor <;> ring

theorem C1QuasilinearDirichletSolution.native_flux_conjugacy
    {ρ : ℝ} {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (x : E2) (hx : x ∈ openHalfDisc ρ) :
    let a := rawPrincipalMatrix Q u x
    let v := planarGradient (fun y => fderivWithin ℝ u (closedHalfDisc ρ) y (coordinateVector 2 1)) x
    let F := planarGradient (fun y => Q.flux (firstJetWithin ρ u y) 0) x
    let e₀ := -Q.lowerOrder (firstJet u x) -
      fluxDx Q (firstJet u x) (coordinateVector 2 1) 1 -
      fluxDz Q (firstJet u x) 1 * planarGradient u x 1
    let e₁ := fluxDx Q (firstJet u x) (coordinateVector 2 1) 0 +
      fluxDz Q (firstJet u x) 0 * planarGradient u x 1
    F 0 = e₀ - a 1 0 * v 0 - a 1 1 * v 1 ∧
      F 1 = e₁ + a 0 0 * v 0 + a 0 1 * v 1 := by
  dsimp only
  have hc := hsolution.native_classical_equation_on_openHalfDisc x hx
  dsimp only [LinearClassicalEquation, matrixHessian, classicalSource] at hc
  simp only [Fin.sum_univ_two] at hc
  have hsym := hsolution.native_hessian_symmetry x hx 1 0
  rw [hsym] at hc
  constructor
  · rw [hsolution.native_flux_partial_derivative x hx 0 0]
    simp only [Fin.sum_univ_two, hsolution.native_partial_gradient_hessian x hx, hsym]
    linarith
  · rw [hsolution.native_flux_partial_derivative x hx 0 1]
    simp only [Fin.sum_univ_two, hsolution.native_partial_gradient_hessian x hx,
      hsolution.native_hessian_symmetry x hx 1 0]
    ring

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
