import NativeBoundaryDualCoefficientBounds

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization

theorem SmoothDirichletDatum.smooth_second_deriv_extension_on_ball
    {ρ : ℝ} (g : SmoothDirichletDatum ρ) :
    ContDiffOn ℝ ∞ (fun x : E2 => deriv (deriv g.value) (x 1)) (Metric.ball 0 ρ) := by
  let g' : SmoothDirichletDatum ρ :=
    ⟨deriv g.value, g.smooth.deriv_of_isOpen isOpen_Ioo (by simp)⟩
  exact g'.smooth_deriv_extension_on_ball

theorem C1QuasilinearDirichletSolution.continuous_native_flux_slices
    {ρ : ℝ} (hρ : 0 < ρ) {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u) :
    ContinuousOn (fun x => fluxDx Q (firstJetWithin ρ u x)) (closedHalfDisc ρ) ∧
    ContinuousOn (fun x => fluxDz Q (firstJetWithin ρ u x)) (closedHalfDisc ρ) ∧
    ContinuousOn (fun x => fluxDp Q (firstJetWithin ρ u x)) (closedHalfDisc ρ) := by
  have hj := continuousOn_firstJetWithin hρ hsolution.c1
  exact ⟨(QuotientHelpers.x_partial_continuousOn J hsolution.jet_domain_open Q.flux
      Q.flux_smooth).comp hj hsolution.attained_jets,
    (QuotientHelpers.z_partial_continuousOn J hsolution.jet_domain_open Q.flux
      Q.flux_smooth).comp hj hsolution.attained_jets,
    (QuotientHelpers.p_partial_continuousOn J hsolution.jet_domain_open Q.flux
      Q.flux_smooth).comp hj hsolution.attained_jets⟩

theorem C1QuasilinearDirichletSolution.native_principal_determinant_nonzero
    {ρ : ℝ} {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (x : E2) (hx : x ∈ closedHalfDisc ρ) :
    nativePrincipalWithin ρ Q u x 0 0 * nativePrincipalWithin ρ Q u x 1 1 -
      nativePrincipalWithin ρ Q u x 0 1 * nativePrincipalWithin ρ Q u x 1 0 ≠ 0 := by
  obtain ⟨κ, hκ, hell⟩ := hsolution.uniformly_elliptic
  have hquad : ∀ ξ : E2, κ * ‖ξ‖ ^ 2 ≤
      ∑ i : Fin 2, ∑ j : Fin 2, nativePrincipalWithin ρ Q u x i j * ξ j * ξ i := by
    intro ξ
    rw [← native_matrix_inner_quadratic, native_principalWithin_toEuclideanCLM]
    exact hell x (u x) (planarGradientWithin u (closedHalfDisc ρ) x) ξ
      (hsolution.attained_jets x hx)
  have hd := native_coercive_matrix_determinant_lower (nativePrincipalWithin ρ Q u x) κ hκ hquad
  exact (lt_of_lt_of_le (sq_pos_of_pos (by linarith : 0 < κ / 2)) hd).ne'

theorem C1QuasilinearDirichletSolution.continuous_native_normal_flux_coefficients
    {ρ : ℝ} (hρ : 0 < ρ) {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u) :
    coefficientsContinuousOn (closedHalfDisc ρ ∩ Metric.ball 0 ρ)
      (nativeNormalFluxCoefficients ρ Q g u) := by
  let K := closedHalfDisc ρ
  let V := K ∩ Metric.ball (0 : E2) ρ
  obtain ⟨hDx, hDz, hDp⟩ := hsolution.continuous_native_flux_slices hρ
  have hAij (i j : Fin 2) : ContinuousOn (fun x => nativePrincipalWithin ρ Q u x i j) K :=
    (EuclideanSpace.proj i).continuous.comp_continuousOn (hDp.clm_apply continuousOn_const)
  have hdet : ContinuousOn (fun x => nativePrincipalWithin ρ Q u x 0 0 * nativePrincipalWithin ρ Q u x 1 1 -
      nativePrincipalWithin ρ Q u x 0 1 * nativePrincipalWithin ρ Q u x 1 0) K :=
    ((hAij 0 0).mul (hAij 1 1)).sub ((hAij 0 1).mul (hAij 1 0))
  have hdual : ContinuousOn (fun x => nativeDualMatrix (nativePrincipalWithin ρ Q u x)) K := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    exact (hAij j i).div hdet (fun x hx => hsolution.native_principal_determinant_nonzero x hx)
  have hCLM : Continuous (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2)) :=
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2)).toAlgEquiv.toLinearMap.continuous_of_finiteDimensional
  have ha : ContinuousOn (nativeNormalFluxCoefficients ρ Q g u).a K :=
    hCLM.comp_continuousOn hdual
  have hxD (i : Fin 2) : ContinuousOn
      (fun x => fluxDx Q (firstJetWithin ρ u x) (coordinateVector 2 1) i) K :=
    (EuclideanSpace.proj i).continuous.comp_continuousOn (hDx.clm_apply continuousOn_const)
  have hzD (i : Fin 2) : ContinuousOn (fun x => fluxDz Q (firstJetWithin ρ u x) i) K :=
    (EuclideanSpace.proj i).continuous.comp_continuousOn hDz
  have hgD : ContinuousOn (fun x => planarGradientWithin u (closedHalfDisc ρ) x 1) K :=
    (EuclideanSpace.proj (1 : Fin 2)).continuous.comp_continuousOn
      (continuousOn_planarGradientWithin_closedHalfDisc hρ hsolution.c1)
  have he : ContinuousOn (nativeNormalFluxError ρ Q u) K :=
    ((((hsolution.continuous_boundary_coefficients hρ).2.1.neg.sub (hxD 1)).sub
      ((hzD 1).mul hgD)).smul continuousOn_const).add
        (((hxD 0).add ((hzD 0).mul hgD)).smul continuousOn_const)
  have hd : ContinuousOn (nativeNormalFluxCoefficients ρ Q g u).d V :=
    ((ha.clm_apply he).neg.mono (fun x hx => hx.1)).add
      ((g.smooth_second_deriv_extension_on_ball.continuousOn.mono (fun x hx => hx.2)).smul continuousOn_const)
  exact ⟨ha.mono (fun x hx => hx.1), continuousOn_const, hd,
    continuousOn_const, continuousOn_const, continuousOn_const⟩

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
