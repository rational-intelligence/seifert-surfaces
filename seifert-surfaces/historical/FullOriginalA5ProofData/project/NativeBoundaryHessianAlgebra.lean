import NativeBoundarySobolevTransfer
import NativeBoundaryNormalFlux

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization QuasilinearBootstrap

theorem C1QuasilinearDirichletSolution.native_classical_equation_on_openHalfDisc
    {ρ : ℝ} {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u) :
    LinearClassicalEquation (openHalfDisc ρ) (rawPrincipalMatrix Q u) (classicalSource Q u) u := by
  apply (R5_weak_to_pointwise (openHalfDisc ρ) (openHalfDisc_isOpen ρ) J hsolution.jet_domain_open
    Q u (hsolution.smooth_on_openHalfDisc.of_le (by simp)) ?_ hsolution.weak_equation).1
  intro x hx
  have hh := hsolution.attained_jets x (openHalfDisc_subset_closedHalfDisc ρ hx)
  simpa only [firstJetWithin_eq_firstJet u hx] using hh

theorem C1QuasilinearDirichletSolution.native_partial_gradient_hessian
    {ρ : ℝ} {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (x : E2) (hx : x ∈ openHalfDisc ρ) (i j : Fin 2) :
    planarGradient (fun y => fderivWithin ℝ u (closedHalfDisc ρ) y (coordinateVector 2 j)) x i =
      planarHessian u x i j := by
  have he : (fun y => fderivWithin ℝ u (closedHalfDisc ρ) y (coordinateVector 2 j)) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ u y (coordinateVector 2 j)) := by
    filter_upwards [(openHalfDisc_isOpen ρ).mem_nhds hx] with y hy
    rw [fderivWithin_closedHalfDisc_eq_fderiv u hy]
  rw [QuasilinearLocalization.Helpers.gradient_apply, he.fderiv_eq]
  let e := ContinuousLinearMap.apply ℝ ℝ (coordinateVector 2 j)
  have hd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    ((hsolution.smooth_on_openHalfDisc.fderiv_of_isOpen (openHalfDisc_isOpen ρ) (m := 1) (by simp)).contDiffAt
      ((openHalfDisc_isOpen ρ).mem_nhds hx)).differentiableAt (by simp)
  have hh := e.hasFDerivAt.comp x hd.hasFDerivAt
  have heq := congrArg (fun L : E2 →L[ℝ] ℝ => L (coordinateVector 2 i)) hh.fderiv
  change (fderiv ℝ (fun y => fderiv ℝ u y (coordinateVector 2 j)) x)
      (coordinateVector 2 i) = _
  simpa only [planarHessian, Function.comp_def, ContinuousLinearMap.comp_apply, e,
    ContinuousLinearMap.apply_apply] using heq

theorem C1QuasilinearDirichletSolution.native_hessian_symmetry
    {ρ : ℝ} {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (x : E2) (hx : x ∈ openHalfDisc ρ) (i j : Fin 2) :
    planarHessian u x i j = planarHessian u x j i := by
  exact ((hsolution.smooth_on_openHalfDisc.of_le (by simp : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω))).contDiffAt
    ((openHalfDisc_isOpen ρ).mem_nhds hx)).isSymmSndFDerivAt (by norm_num) |>.eq _ _

/-- Elementary normal Hessian recovery from the actual pointwise equation.
The tangential row controls all remaining Hessian entries by ellipticity. -/
theorem native_normal_hessian_bound
    (a : Matrix (Fin 2) (Fin 2) ℝ) (H : Matrix (Fin 2) (Fin 2) ℝ)
    (F κ M S T : ℝ) (hκ : 0 < κ) (hM : 0 ≤ M) (hS : 0 ≤ S)
    (hT : 0 ≤ T) (ha : κ ≤ a 0 0) (hentries : ∀ i j, |a i j| ≤ M)
    (hsym : H 0 1 = H 1 0) (h01 : |H 0 1| ≤ T) (h11 : |H 1 1| ≤ T)
    (hF : |F| ≤ S) (heq : ∑ i : Fin 2, ∑ j : Fin 2, a i j * H i j = F) :
    |H 0 0| ≤ κ⁻¹ * (S + 3 * M * T) := by
  have haa : 0 < a 0 0 := hκ.trans_le ha
  have hp : |a 0 0 * H 0 0| ≤ S + 3 * M * T := by
    have he : a 0 0 * H 0 0 = F - (a 0 1 * H 0 1 + a 1 0 * H 1 0 + a 1 1 * H 1 1) := by
      simp only [Fin.sum_univ_two] at heq
      linarith
    rw [he]
    calc
      _ ≤ |F| + |a 0 1 * H 0 1 + a 1 0 * H 1 0 + a 1 1 * H 1 1| := abs_sub _ _
      _ ≤ S + (|a 0 1 * H 0 1| + |a 1 0 * H 1 0| + |a 1 1 * H 1 1|) :=
        add_le_add hF ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl))
      _ ≤ S + (M * T + M * T + M * T) := by
        simp only [abs_mul]
        have hh := add_le_add (add_le_add
          (mul_le_mul (hentries 0 1) h01 (abs_nonneg _) hM)
          (mul_le_mul (hentries 1 0) (hsym ▸ h01) (abs_nonneg _) hM))
          (mul_le_mul (hentries 1 1) h11 (abs_nonneg _) hM)
        linarith
      _ = _ := by ring
  rw [abs_mul, abs_of_pos haa] at hp
  calc
    _ ≤ (S + 3 * M * T) / (a 0 0) := (le_div_iff₀ haa).mpr (by nlinarith)
    _ ≤ (S + 3 * M * T) / κ := div_le_div_of_nonneg_left (by positivity) hκ ha
    _ = _ := by rw [div_eq_mul_inv, mul_comm]

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
