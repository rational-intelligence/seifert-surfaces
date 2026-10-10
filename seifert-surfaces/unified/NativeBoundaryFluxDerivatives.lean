import NativeBoundaryFullGradientSobolev

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization QuasilinearBootstrap

theorem C1QuasilinearDirichletSolution.native_flux_partial_derivative
    {ρ : ℝ} {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (x : E2) (hx : x ∈ openHalfDisc ρ) (i k : Fin 2) :
    planarGradient (fun y => Q.flux (firstJetWithin ρ u y) i) x k =
      fluxDx Q (firstJet u x) (coordinateVector 2 k) i +
      fluxDz Q (firstJet u x) i * planarGradient u x k +
      ∑ j : Fin 2, rawPrincipalMatrix Q u x i j * planarHessian u x k j := by
  have hΩ := openHalfDisc_isOpen ρ
  have hC2 : ContDiffOn ℝ 2 u (openHalfDisc ρ) := hsolution.smooth_on_openHalfDisc.of_le (by simp)
  have hdu : ContDiffOn ℝ 1 (fderiv ℝ u) (openHalfDisc ρ) :=
    hC2.fderiv_of_isOpen hΩ (by norm_num)
  have hgrad : ContDiffOn ℝ 1 (planarGradient u) (openHalfDisc ρ) := by
    unfold planarGradient
    exact ContDiffOn.sum (fun j _ => (hdu.clm_apply contDiffOn_const).smul_const _)
  have hgradder (ξ : E2) : fderiv ℝ (planarGradient u) x ξ =
      ∑ j : Fin 2, (fderiv ℝ (fderiv ℝ u) x ξ (coordinateVector 2 j)) • coordinateVector 2 j := by
    have hdx := (hdu.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by norm_num)
    unfold planarGradient
    rw [fderiv_fun_sum (fun j _ => (hdx.clm_apply (differentiableAt_const _)).smul_const _)]
    simp only [ContinuousLinearMap.sum_apply, fderiv_smul_const
      (hdx.clm_apply (differentiableAt_const _)), ContinuousLinearMap.smulRight_apply,
      fderiv_clm_apply hdx (differentiableAt_const _), fderiv_fun_const,
      Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply]
  have he : (fun y => Q.flux (firstJetWithin ρ u y) i) =ᶠ[𝓝 x]
      (fun y => Q.flux (firstJet u y) i) := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    rw [firstJetWithin_eq_firstJet u hy]
  rw [QuasilinearLocalization.Helpers.gradient_apply, he.fderiv_eq]
  have huat := (hC2.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by norm_num)
  have hgat := (hgrad.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by norm_num)
  have hj : firstJet u x ∈ J := by
    simpa only [← firstJetWithin_eq_firstJet u hx] using
      hsolution.attained_jets x (openHalfDisc_subset_closedHalfDisc ρ hx)
  have hQ := (Q.flux_smooth.contDiffAt (hsolution.jet_domain_open.mem_nhds hj)).differentiableAt (by simp)
  have hjetD : HasFDerivAt (firstJet u)
      ((ContinuousLinearMap.id ℝ E2).prod
        ((fderiv ℝ u x).prod (fderiv ℝ (planarGradient u) x))) x :=
    (hasFDerivAt_id x).prodMk (huat.hasFDerivAt.prodMk hgat.hasFDerivAt)
  have hAiD := (EuclideanSpace.proj i).hasFDerivAt.comp x (hQ.hasFDerivAt.comp x hjetD)
  have hAiDeq : fderiv ℝ (fun y => Q.flux (firstJet u y) i) x =
      (EuclideanSpace.proj i).comp ((fderiv ℝ Q.flux (firstJet u x)).comp
        ((ContinuousLinearMap.id ℝ E2).prod
          ((fderiv ℝ u x).prod (fderiv ℝ (planarGradient u) x)))) := by
    simpa only [Function.comp_def, EuclideanSpace.proj, PiLp.proj_apply] using hAiD.fderiv
  rw [hAiDeq]
  change (fderiv ℝ Q.flux (firstJet u x)
    (coordinateVector 2 k, (fderiv ℝ u x (coordinateVector 2 k),
      fderiv ℝ (planarGradient u) x (coordinateVector 2 k)))) i = _
  rw [hgradder, ← Helpers.gradient_apply]
  have hv : (coordinateVector 2 k, (planarGradient u x k,
      ∑ j : Fin 2, planarHessian u x k j • coordinateVector 2 j)) =
      (coordinateVector 2 k, (0, 0)) +
      (planarGradient u x k) • (0, (1, 0)) +
      ∑ j : Fin 2, planarHessian u x k j • (0, (0, coordinateVector 2 j)) := by
    simp only [planarHessian, Fin.sum_univ_two, Prod.fst_add, Prod.snd_add,
      Prod.fst_smul, Prod.snd_smul, smul_zero, zero_add, add_zero, smul_eq_mul, mul_one]
    ext <;> simp [Fin.sum_univ_two]
  change ((fderiv ℝ Q.flux (firstJet u x))
    (coordinateVector 2 k, (planarGradient u x k,
      ∑ j : Fin 2, planarHessian u x k j • coordinateVector 2 j))) i = _
  rw [hv]
  simp only [map_add, map_smul, map_sum, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  unfold rawPrincipalMatrix fluxDp fluxDx fluxDz
  rw [Helpers.fderiv_x_slice Q.flux (firstJet u x) hQ,
    Helpers.fderiv_z_slice Q.flux (firstJet u x) hQ,
    Helpers.fderiv_p_slice Q.flux (firstJet u x) hQ]
  simp only [fluxDx, fluxDz, fluxDp, rawPrincipalMatrix,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.inr_apply]
  simp only [Fin.sum_univ_two, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rw [show (0 : ℝ × E2) = (0, 0) from rfl]
  ring

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
