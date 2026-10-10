import NativeBoundaryC1HolderOperations

set_option autoImplicit false
set_option maxHeartbeats 50000
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization

theorem native_cap_C2_derivative_holder
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (c : E2) (hcf : c 0 = 0) (r : ℝ) (hr : 0 < r) (f : E2 → F)
    (α : ℝ≥0) (hα1 : α ≤ 1) (hf : ContDiffOn ℝ 2 f (nativeClosedBoundaryCap c r)) :
    ∃ C, HolderOnWith C α (fderivWithin ℝ f (nativeClosedBoundaryCap c r))
      (nativeClosedBoundaryCap c r) :=
  native_contDiffOn_cap_holder c r hr _ α hα1
    (hf.fderivWithin (m := 1) (nativeClosedBoundaryCap_uniqueDiffOn c r hr hcf) (by norm_num))

/-- The first derivatives of both coefficients in the actual zero-source
linear tangent equation are Hölder, solely from the original solution. -/
theorem C1QuasilinearDirichletSolution.local_C1_holder_tangential_schauder_data
    {ρ : ℝ} (hρ : 0 < ρ) {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (c : E2) (hc : c ∈ flatBoundary ρ) :
    ∃ r : ℝ, ∃ α : ℝ≥0, 0 < r ∧ 0 < α ∧ α < 1 ∧
      Metric.closedBall c r ⊆ Metric.ball 0 ρ ∧
      ContDiffOn ℝ 2 u (nativeClosedBoundaryCap c r) ∧
      ContDiffOn ℝ 1 (nativeTangentialSchauderCoefficients ρ Q g u).a
        (nativeClosedBoundaryCap c r) ∧
      ContDiffOn ℝ 1 (nativeTangentialSchauderCoefficients ρ Q g u).d
        (nativeClosedBoundaryCap c r) ∧
      (∃ C, HolderOnWith C α
        (fderivWithin ℝ (nativeTangentialSchauderCoefficients ρ Q g u).a (nativeClosedBoundaryCap c r))
        (nativeClosedBoundaryCap c r)) ∧
      (∃ C, HolderOnWith C α
        (fderivWithin ℝ (nativeTangentialSchauderCoefficients ρ Q g u).d (nativeClosedBoundaryCap c r))
        (nativeClosedBoundaryCap c r)) := by
  obtain ⟨r, α, hr, hα, hα1, hball, hu, hp, hDp⟩ :=
    hsolution.local_C1_holder_jet_composition hρ c hc
      (fun j : Jet => (fluxDp Q j, nativeTangentialForcingJet Q j))
      (native_tangential_principal_forcing_jet_smooth J hsolution.jet_domain_open Q)
  let K := nativeClosedBoundaryCap c r
  let p := fun x => (fluxDp Q (firstJetWithin ρ u x), nativeTangentialForcingJet Q (firstJetWithin ρ u x))
  let a := (nativeTangentialSchauderCoefficients ρ Q g u).a
  let F := fun x => nativeTangentialForcingJet Q (firstJetWithin ρ u x)
  let v := fun x : E2 => deriv (deriv g.value) (x 1) • coordinateVector 2 1
  have hKD := nativeClosedBoundaryCap_uniqueDiffOn c r hr hc.2
  have ha : ContDiffOn ℝ 1 a K ∧ ∃ C, HolderOnWith C α (fderivWithin ℝ a K) K := by
    simpa only [p, a, nativeTangentialSchauderCoefficients, ContinuousLinearMap.coe_fst', Function.comp_def]
      using native_cap_C1_holder_comp_linear K hKD p α hp hDp
        (ContinuousLinearMap.fst ℝ (E2 →L[ℝ] E2) E2)
  have hF : ContDiffOn ℝ 1 F K ∧ ∃ C, HolderOnWith C α (fderivWithin ℝ F K) K := by
    simpa only [p, F, ContinuousLinearMap.coe_snd', Function.comp_def]
      using native_cap_C1_holder_comp_linear K hKD p α hp hDp
        (ContinuousLinearMap.snd ℝ (E2 →L[ℝ] E2) E2)
  have hv2 : ContDiffOn ℝ 2 v K :=
    ((g.smooth_second_deriv_extension_on_ball.mono (fun x hx => hball hx.1)).of_le (by simp)).smul_const _
  have hv : ContDiffOn ℝ 1 v K := hv2.of_le (by norm_num)
  have hDv : ∃ C, HolderOnWith C α (fderivWithin ℝ v K) K :=
    native_cap_C2_derivative_holder c hc.2 r hr v α hα1.le hv2
  have hav := native_cap_C1_holder_clm_apply c hc.2 r hr a v α hα hα1.le ha.1 hv ha.2 hDv
  have hd := native_cap_C1_holder_add K hKD F (fun x => a x (v x)) α hF.1 hav.1 hF.2 hav.2
  exact ⟨r, α, hr, hα, hα1, hball, hu, ha.1, hd.1, ha.2, hd.2⟩

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
