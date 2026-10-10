import NativeBoundaryNormalFluxConjugacy
import NativeBoundaryNeumannReflection

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization QuasilinearBootstrap

def nativePrincipalWithin (ρ : ℝ) {J : Set Jet} (Q : SmoothQuasilinearOperator J)
    (u : E2 → ℝ) (x : E2) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => fluxDp Q (firstJetWithin ρ u x) (coordinateVector 2 j) i

def nativeNormalFluxError (ρ : ℝ) {J : Set Jet} (Q : SmoothQuasilinearOperator J)
    (u : E2 → ℝ) (x : E2) : E2 :=
  (-Q.lowerOrder (firstJetWithin ρ u x) -
    fluxDx Q (firstJetWithin ρ u x) (coordinateVector 2 1) 1 -
    fluxDz Q (firstJetWithin ρ u x) 1 * planarGradientWithin u (closedHalfDisc ρ) x 1) •
      coordinateVector 2 0 +
  (fluxDx Q (firstJetWithin ρ u x) (coordinateVector 2 1) 0 +
    fluxDz Q (firstJetWithin ρ u x) 0 * planarGradientWithin u (closedHalfDisc ρ) x 1) •
      coordinateVector 2 1

def nativeNormalFluxCoefficients (ρ : ℝ) {J : Set Jet} (Q : SmoothQuasilinearOperator J)
    (g : SmoothDirichletDatum ρ) (u : E2 → ℝ) : LinearizedCoefficients where
  a x := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2)
    (nativeDualMatrix (nativePrincipalWithin ρ Q u x))
  c := 0
  d x := -(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2)
    (nativeDualMatrix (nativePrincipalWithin ρ Q u x)) (nativeNormalFluxError ρ Q u x)) +
      deriv (deriv g.value) (x 1) • coordinateVector 2 0
  b := 0
  q := 0
  f := 0

theorem native_principalWithin_eq_raw {ρ : ℝ} {J : Set Jet}
    (Q : SmoothQuasilinearOperator J) (u : E2 → ℝ) (x : E2)
    (hx : x ∈ openHalfDisc ρ) :
    nativePrincipalWithin ρ Q u x = rawPrincipalMatrix Q u x := by
  unfold nativePrincipalWithin rawPrincipalMatrix
  rw [firstJetWithin_eq_firstJet u hx]

theorem native_gradient_tangent_composition (h : ℝ → ℝ) (x : E2)
    (hd : DifferentiableAt ℝ h (x 1)) :
    planarGradient (fun y : E2 => h (y 1)) x = deriv h (x 1) • coordinateVector 2 1 := by
  have hder := hd.hasFDerivAt.comp x
    (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).hasFDerivAt
  have hfd : fderiv ℝ h (x 1) 1 = deriv h (x 1) := rfl
  ext i
  rw [Helpers.gradient_apply]
  change (fderiv ℝ (h ∘ (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2))) x)
    (coordinateVector 2 i) = _
  rw [hder.fderiv]
  fin_cases i <;> simp [coordinateVector, hfd]

theorem SmoothDirichletDatum.gradient_deriv_extension
    {ρ : ℝ} (g : SmoothDirichletDatum ρ) (x : E2) (hx : x ∈ Metric.ball 0 ρ) :
    planarGradient (fun y : E2 => deriv g.value (y 1)) x =
      deriv (deriv g.value) (x 1) • coordinateVector 2 1 := by
  apply native_gradient_tangent_composition
  have hn : ‖x‖ < ρ := by simpa only [Metric.mem_ball, dist_zero_right] using hx
  have hb : |x 1| ≤ ‖x‖ := PiLp.norm_apply_le x 1 (p := 2)
  have hgd : ContDiffOn ℝ ∞ (deriv g.value) (Ioo (-ρ) ρ) :=
    g.smooth.deriv_of_isOpen isOpen_Ioo (by simp)
  have hxi : x 1 ∈ Ioo (-ρ) ρ := abs_lt.mp (hb.trans_lt hn)
  exact (hgd.contDiffAt (isOpen_Ioo.mem_nhds hxi)).differentiableAt (by simp)

theorem C1QuasilinearDirichletSolution.native_normal_flux_conjugate_relation
    {ρ : ℝ} {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (x : E2) (hx : x ∈ openHalfDisc ρ) :
    (nativeNormalFluxCoefficients ρ Q g u).a x
        (planarGradient (fun y => Q.flux (firstJetWithin ρ u y) 0) x) +
      (nativeNormalFluxCoefficients ρ Q g u).d x =
    nativeQuarterTurn (planarGradient (fun y =>
      fderivWithin ℝ u (closedHalfDisc ρ) y (coordinateVector 2 1) - deriv g.value (y 1)) x) := by
  let D : E2 → ℝ := fun y => fderivWithin ℝ u (closedHalfDisc ρ) y (coordinateVector 2 1)
  let G : E2 → ℝ := fun y => deriv g.value (y 1)
  have hDd : DifferentiableAt ℝ D x :=
    ((hsolution.smooth_partial_on_openHalfDisc 1).contDiffAt
      ((openHalfDisc_isOpen ρ).mem_nhds hx)).differentiableAt (by simp)
  have hGd : DifferentiableAt ℝ G x :=
    (g.smooth_deriv_extension_on_ball.contDiffAt (Metric.isOpen_ball.mem_nhds hx.1)).differentiableAt
      (by simp)
  have hgrad : planarGradient (fun y => D y - G y) x = planarGradient D x - planarGradient G x := by
    unfold planarGradient
    rw [fderiv_fun_sub hDd hGd]
    simp only [ContinuousLinearMap.sub_apply, sub_smul, Finset.sum_sub_distrib]
  rw [show (fun y => fderivWithin ℝ u (closedHalfDisc ρ) y (coordinateVector 2 1) -
    deriv g.value (y 1)) = (fun y => D y - G y) from rfl, hgrad, map_sub]
  have hdatum : nativeQuarterTurn (planarGradient G x) =
      -(deriv (deriv g.value) (x 1) • coordinateVector 2 0) := by
    rw [show planarGradient G x = _ from g.gradient_deriv_extension x hx.1]
    ext i
    fin_cases i <;> simp [nativeQuarterTurn_zero, nativeQuarterTurn_one, coordinateVector]
  rw [hdatum]
  have hp := hsolution.native_normal_flux_dual_relation x hx
  dsimp only at hp
  dsimp only [nativeNormalFluxCoefficients]
  rw [native_principalWithin_eq_raw Q u x hx]
  have he : nativeNormalFluxError ρ Q u x =
      (-Q.lowerOrder (firstJet u x) - fluxDx Q (firstJet u x) (coordinateVector 2 1) 1 -
        fluxDz Q (firstJet u x) 1 * planarGradient u x 1) • coordinateVector 2 0 +
      (fluxDx Q (firstJet u x) (coordinateVector 2 1) 0 +
        fluxDz Q (firstJet u x) 0 * planarGradient u x 1) • coordinateVector 2 1 := by
    simp only [nativeNormalFluxError, firstJetWithin_eq_firstJet u hx,
      planarGradientWithin_closedHalfDisc_eq u hx]
  rw [he]
  change _ + (-_ + _) = nativeQuarterTurn (planarGradient D x) - -_
  rw [sub_neg_eq_add, ← hp]
  abel

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
