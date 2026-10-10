import NativeBoundaryPrincipalSourceHolder

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization QuasilinearBootstrap

/-- Tangential differentiation of the lower-order scalar term is kept in
divergence form, so this forcing involves only the actual first jet. -/
def nativeTangentialForcingJet {J : Set Jet} (Q : SmoothQuasilinearOperator J) (j : Jet) : E2 :=
  fluxDx Q j (coordinateVector 2 1) + j.2.2 1 • fluxDz Q j + Q.lowerOrder j • coordinateVector 2 1

def nativeTangentialSchauderCoefficients (ρ : ℝ) {J : Set Jet} (Q : SmoothQuasilinearOperator J)
    (g : SmoothDirichletDatum ρ) (u : E2 → ℝ) : LinearizedCoefficients where
  a x := fluxDp Q (firstJetWithin ρ u x)
  c := 0
  d x := nativeTangentialForcingJet Q (firstJetWithin ρ u x) +
    fluxDp Q (firstJetWithin ρ u x) (deriv (deriv g.value) (x 1) • coordinateVector 2 1)
  b := 0
  q := 0
  f := 0

theorem native_tangential_forcing_jet_smooth (J : Set Jet) (hJ : IsOpen J)
    (Q : SmoothQuasilinearOperator J) : ContDiffOn ℝ ∞ (nativeTangentialForcingJet Q) J := by
  have hx : ContDiffOn ℝ ∞ (fluxDx Q) J := native_jet_x_partial_smooth J hJ Q.flux Q.flux_smooth
  have hz : ContDiffOn ℝ ∞ (fluxDz Q) J := native_jet_z_partial_smooth J hJ Q.flux Q.flux_smooth
  have hp : ContDiffOn ℝ ∞ (fun j : Jet => j.2.2 1) J := by
    have hp0 : ContDiffOn ℝ ∞ (fun j : Jet => j.2.2) J := by fun_prop
    simpa only [Function.comp_def, EuclideanSpace.proj, PiLp.proj_apply] using
      (EuclideanSpace.proj (1 : Fin 2)).contDiff.comp_contDiffOn hp0
  exact ((hx.clm_apply contDiffOn_const).add (hp.smul hz)).add
    (Q.lowerOrder_smooth.smul_const _)

theorem native_tangential_principal_forcing_jet_smooth (J : Set Jet) (hJ : IsOpen J)
    (Q : SmoothQuasilinearOperator J) :
    ContDiffOn ℝ ∞ (fun j : Jet => (fluxDp Q j, nativeTangentialForcingJet Q j)) J :=
  (native_jet_p_partial_smooth J hJ Q.flux Q.flux_smooth).prodMk
    (native_tangential_forcing_jet_smooth J hJ Q)

/-- The actual zero-trace tangential derivative satisfies the conjugate flux
relation with the actual normal flux; its scalar source is exactly zero. -/
theorem C1QuasilinearDirichletSolution.native_tangential_schauder_conjugate_relation
    {ρ : ℝ} {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (x : E2) (hx : x ∈ openHalfDisc ρ) :
    (nativeTangentialSchauderCoefficients ρ Q g u).a x
      (planarGradient (fun y => fderivWithin ℝ u (closedHalfDisc ρ) y (coordinateVector 2 1) -
        deriv g.value (y 1)) x) + (nativeTangentialSchauderCoefficients ρ Q g u).d x =
      -nativeQuarterTurn (planarGradient (fun y => Q.flux (firstJetWithin ρ u y) 0) x) := by
  let D : E2 → ℝ := fun y => fderivWithin ℝ u (closedHalfDisc ρ) y (coordinateVector 2 1)
  let G : E2 → ℝ := fun y => deriv g.value (y 1)
  have hDd : DifferentiableAt ℝ D x :=
    ((hsolution.smooth_partial_on_openHalfDisc 1).contDiffAt
      ((openHalfDisc_isOpen ρ).mem_nhds hx)).differentiableAt (by simp)
  have hGd : DifferentiableAt ℝ G x :=
    (g.smooth_deriv_extension_on_ball.contDiffAt (Metric.isOpen_ball.mem_nhds hx.1)).differentiableAt (by simp)
  have hgrad : planarGradient (fun y => D y - G y) x = planarGradient D x - planarGradient G x := by
    unfold planarGradient
    rw [fderiv_fun_sub hDd hGd]
    simp only [sub_apply, sub_smul, Finset.sum_sub_distrib]
  have hdatum := g.gradient_deriv_extension x hx.1
  change (fluxDp Q (firstJetWithin ρ u x)) (planarGradient (fun y => D y - G y) x) +
    (nativeTangentialForcingJet Q (firstJetWithin ρ u x) +
      fluxDp Q (firstJetWithin ρ u x) (deriv (deriv g.value) (x 1) • coordinateVector 2 1)) = _
  rw [hgrad, show planarGradient G x = _ from hdatum, map_sub]
  have hcancel : (fluxDp Q (firstJetWithin ρ u x)) (planarGradient D x) -
      (fluxDp Q (firstJetWithin ρ u x)) (deriv (deriv g.value) (x 1) • coordinateVector 2 1) +
      (nativeTangentialForcingJet Q (firstJetWithin ρ u x) +
       (fluxDp Q (firstJetWithin ρ u x)) (deriv (deriv g.value) (x 1) • coordinateVector 2 1)) =
      (fluxDp Q (firstJetWithin ρ u x)) (planarGradient D x) +
        nativeTangentialForcingJet Q (firstJetWithin ρ u x) := by abel
  rw [hcancel, firstJetWithin_eq_firstJet u hx]
  have hcon := hsolution.native_flux_conjugacy x hx
  let V := planarGradient D x
  have hV : V = V 0 • coordinateVector 2 0 + V 1 • coordinateVector 2 1 := by
    ext i
    fin_cases i <;> simp [coordinateVector]
  ext i
  simp only [PiLp.add_apply, PiLp.neg_apply]
  rw [show (fluxDp Q (firstJet u x) V) i =
      rawPrincipalMatrix Q u x i 0 * V 0 + rawPrincipalMatrix Q u x i 1 * V 1 by
    conv_lhs => rw [hV]
    simp only [map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, rawPrincipalMatrix]
    ring]
  fin_cases i
  · change rawPrincipalMatrix Q u x 0 0 * V 0 + rawPrincipalMatrix Q u x 0 1 * V 1 +
      nativeTangentialForcingJet Q (firstJet u x) 0 =
        -nativeQuarterTurn (planarGradient (fun y => Q.flux (firstJetWithin ρ u y) 0) x) 0
    rw [nativeQuarterTurn_zero]
    simp only [nativeTangentialForcingJet, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    simp [coordinateVector]
    dsimp only [V, D, firstJet, coordinateVector] at hcon ⊢
    nlinarith only [hcon.2]
  · change rawPrincipalMatrix Q u x 1 0 * V 0 + rawPrincipalMatrix Q u x 1 1 * V 1 +
      nativeTangentialForcingJet Q (firstJet u x) 1 =
        -nativeQuarterTurn (planarGradient (fun y => Q.flux (firstJetWithin ρ u y) 0) x) 1
    rw [nativeQuarterTurn_one]
    simp only [nativeTangentialForcingJet, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    simp [coordinateVector]
    dsimp only [V, D, firstJet, coordinateVector] at hcon ⊢
    nlinarith only [hcon.1]

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
