import NativeBoundaryHessianAlgebra
import NativeBoundaryJetTube

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization QuasilinearBootstrap

theorem native_planar_norm_le_coordinate_sum (v : E2) :
    ‖v‖ ≤ |v 0| + |v 1| := by
  have he : v = v 0 • coordinateVector 2 0 + v 1 • coordinateVector 2 1 := by
    ext i
    fin_cases i <;> simp [coordinateVector]
  calc
    ‖v‖ = ‖v 0 • coordinateVector 2 0 + v 1 • coordinateVector 2 1‖ := congrArg norm he
    _ ≤ ‖v 0 • coordinateVector 2 0‖ + ‖v 1 • coordinateVector 2 1‖ := norm_add_le _ _
    _ = _ := by simp [norm_smul, coordinateVector, PiLp.norm_single]

theorem native_classical_coefficient_bounds
    {ρ : ℝ} {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {u : E2 → ℝ} {x : E2} (hx : x ∈ openHalfDisc ρ)
    (κ M : ℝ) (hM : 0 ≤ M)
    (hg : ‖planarGradientWithin u (closedHalfDisc ρ) x‖ ≤ M)
    (hb : |Q.lowerOrder (firstJetWithin ρ u x)| ≤ M)
    (hDx : ‖fluxDx Q (firstJetWithin ρ u x)‖ ≤ M)
    (hDz : ‖fluxDz Q (firstJetWithin ρ u x)‖ ≤ M)
    (hDp : ‖fluxDp Q (firstJetWithin ρ u x)‖ ≤ M)
    (hco : ∀ ξ : E2, κ * ‖ξ‖ ^ 2 ≤
      inner ℝ (fluxDp Q (firstJetWithin ρ u x) ξ) ξ) :
    κ ≤ rawPrincipalMatrix Q u x 0 0 ∧
    (∀ i j, |rawPrincipalMatrix Q u x i j| ≤ M) ∧
    |classicalSource Q u x| ≤ 3 * M + 2 * M ^ 2 := by
  rw [firstJetWithin_eq_firstJet u hx] at hb hDx hDz hDp hco
  rw [planarGradientWithin_closedHalfDisc_eq u hx] at hg
  have hn (i : Fin 2) : ‖coordinateVector 2 i‖ = 1 := by simp [coordinateVector, PiLp.norm_single]
  have he (L : E2 →L[ℝ] E2) (hL : ‖L‖ ≤ M) (i j : Fin 2) :
      |L (coordinateVector 2 j) i| ≤ M := by
    calc
      _ ≤ ‖L (coordinateVector 2 j)‖ := by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (L (coordinateVector 2 j)) i (p := 2)
      _ ≤ ‖L‖ * ‖coordinateVector 2 j‖ := L.le_opNorm _
      _ ≤ M := by simpa only [hn, mul_one] using hL
  have heDz (i : Fin 2) : |fluxDz Q (firstJet u x) i| ≤ M := by
    apply le_trans _ hDz
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (fluxDz Q (firstJet u x)) i (p := 2)
  have heG (i : Fin 2) : |planarGradient u x i| ≤ M := by
    apply le_trans _ hg
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (planarGradient u x) i (p := 2)
  have ht (i : Fin 2) :
      |fluxDx Q (firstJet u x) (coordinateVector 2 i) i +
        fluxDz Q (firstJet u x) i * planarGradient u x i| ≤ M + M ^ 2 := by
    apply (abs_add_le _ _).trans
    rw [abs_mul, pow_two]
    exact add_le_add (he _ hDx i i)
      (mul_le_mul (heDz i) (heG i) (abs_nonneg _) hM)
  refine ⟨?_, fun i j => he _ hDp i j, ?_⟩
  · simpa [rawPrincipalMatrix, coordinateVector, PiLp.norm_single, PiLp.inner_apply,
      Fin.sum_univ_two] using hco (coordinateVector 2 0)
  · unfold classicalSource
    simp only [Fin.sum_univ_two]
    calc
      _ ≤ |Q.lowerOrder (firstJet u x)| +
          |(fluxDx Q (firstJet u x) (coordinateVector 2 0) 0 +
            fluxDz Q (firstJet u x) 0 * planarGradient u x 0) +
           (fluxDx Q (firstJet u x) (coordinateVector 2 1) 1 +
            fluxDz Q (firstJet u x) 1 * planarGradient u x 1)| := by
          simpa only [abs_neg] using abs_sub (-Q.lowerOrder (firstJet u x)) _
      _ ≤ M + ((M + M ^ 2) + (M + M ^ 2)) :=
        add_le_add hb ((abs_add_le _ _).trans (add_le_add (ht 0) (ht 1)))
      _ = _ := by ring

theorem C1QuasilinearDirichletSolution.native_normal_second_gradient_bound
    {ρ : ℝ} {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (x : E2) (hx : x ∈ openHalfDisc ρ)
    (κ M S : ℝ) (hκ : 0 < κ) (hM : 0 ≤ M) (hS : 0 ≤ S)
    (ha : κ ≤ rawPrincipalMatrix Q u x 0 0)
    (he : ∀ i j, |rawPrincipalMatrix Q u x i j| ≤ M)
    (hF : |classicalSource Q u x| ≤ S) :
    ‖planarGradient (fun y => fderivWithin ℝ u (closedHalfDisc ρ) y (coordinateVector 2 0)) x‖ ≤
      κ⁻¹ * S + (3 * M * κ⁻¹ + 1) *
        ‖planarGradient (fun y => fderivWithin ℝ u (closedHalfDisc ρ) y (coordinateVector 2 1)) x‖ := by
  let G := planarGradient (fun y => fderivWithin ℝ u (closedHalfDisc ρ) y (coordinateVector 2 1)) x
  have h01 : |planarHessian u x 0 1| ≤ ‖G‖ := by
    rw [← hsolution.native_partial_gradient_hessian x hx 0 1]
    exact PiLp.norm_apply_le G (0 : Fin 2) (p := 2)
  have h11 : |planarHessian u x 1 1| ≤ ‖G‖ := by
    rw [← hsolution.native_partial_gradient_hessian x hx 1 1]
    exact PiLp.norm_apply_le G (1 : Fin 2) (p := 2)
  have hh := native_normal_hessian_bound (rawPrincipalMatrix Q u x) (planarHessian u x)
    (classicalSource Q u x) κ M S ‖G‖ hκ hM hS (norm_nonneg G) ha he
    (hsolution.native_hessian_symmetry x hx 0 1) h01 h11 hF
    (hsolution.native_classical_equation_on_openHalfDisc x hx)
  calc
    _ ≤ |planarHessian u x 0 0| + |planarHessian u x 1 0| := by
      simpa only [hsolution.native_partial_gradient_hessian x hx] using
        native_planar_norm_le_coordinate_sum
          (planarGradient (fun y => fderivWithin ℝ u (closedHalfDisc ρ) y (coordinateVector 2 0)) x)
    _ ≤ κ⁻¹ * (S + 3 * M * ‖G‖) + ‖G‖ :=
      add_le_add hh (by rw [hsolution.native_hessian_symmetry x hx 1 0]; exact h01)
    _ = _ := by dsimp [G]; ring

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
