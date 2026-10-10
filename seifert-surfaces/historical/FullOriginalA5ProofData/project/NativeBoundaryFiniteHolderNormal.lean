import NativeBoundaryFiniteJetComposition

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization QuasilinearBootstrap
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak.BoundaryContinuation

/-- At each finite order, the original normal within derivative is recovered
from the gained tangential derivative and the actual elliptic equation. -/
theorem C1QuasilinearDirichletSolution.finite_holder_normal_derivative_from_tangential
    {ρ : ℝ} (hρ : 0 < ρ) {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (c : E2) (hc : c ∈ flatBoundary ρ) (r : ℝ) (hr : 0 < r)
    (hball : Metric.closedBall c r ⊆ Metric.ball 0 ρ)
    (α : ℝ≥0) (hα : 0 < α) (hα1 : α ≤ 1) (m : ℕ)
    (S : Set Jet) (hS : IsCompact S) (hSc : Convex ℝ S) (hSJ : S ⊆ J)
    (hmap : MapsTo (firstJetWithin ρ u) (nativeClosedBoundaryCap c r) S)
    (hu : NativeCapHolder (nativeClosedBoundaryCap c r) α (m + 1) u)
    (hT : NativeCapHolder (nativeClosedBoundaryCap c r) α (m + 1)
      (fun x => fderivWithin ℝ u (closedHalfDisc ρ) x (coordinateVector 2 1))) :
    NativeCapHolder (nativeClosedBoundaryCap c (r / 2)) α (m + 1)
      (fun x => fderivWithin ℝ u (closedHalfDisc ρ) x (coordinateVector 2 0)) := by
  let K := nativeClosedBoundaryCap c r
  let U := Metric.ball c r ∩ {x : E2 | 0 < x 0}
  let t := fun x => fderivWithin ℝ u (closedHalfDisc ρ) x (coordinateVector 2 1)
  let n := fun x => fderivWithin ℝ u (closedHalfDisc ρ) x (coordinateVector 2 0)
  let a := nativePrincipalWithin ρ Q u
  let F := nativeClassicalSourceWithin ρ Q u
  let T (i : Fin 2) := fun x => fderivWithin ℝ t K x (coordinateVector 2 i)
  let N := fun x => (F x - a x 0 1 * T 0 x - a x 1 0 * T 0 x - a x 1 1 * T 1 x) / a x 0 0
  let G := fun x => N x • coordinateVector 2 0 + T 0 x • coordinateVector 2 1
  have hcf : c 0 = 0 := hc.2
  have hK : K ⊆ closedHalfDisc ρ := fun x hx =>
    ⟨Metric.ball_subset_closedBall (hball hx.1), hx.2⟩
  have hU : IsOpen U := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (0 : Fin 2)).continuous)
  have hUK : U ⊆ K := fun x hx =>
    ⟨Metric.ball_subset_closedBall hx.1, by change 0 ≤ x 0; exact le_of_lt hx.2⟩
  have hUρ : U ⊆ openHalfDisc ρ := fun x hx =>
    ⟨hball (Metric.ball_subset_closedBall hx.1), hx.2⟩
  have hnC : ContinuousOn n K :=
    ((hsolution.c1.continuousOn_fderivWithin (closedHalfDisc_uniqueDiffOn hρ) (by norm_num)).clm_apply
      (continuousOn_const (c := coordinateVector 2 0))).mono hK
  have hKD := nativeClosedBoundaryCap_uniqueDiffOn c r hr hcf
  have hTm : ∀ i, NativeCapHolder K α m (T i) := hT.2
  have hAm : NativeCapHolder K α m (fun x => fluxDp Q (firstJetWithin ρ u x)) :=
    hsolution.jet_composition_capHolder c hcf r hr hball α hα hα1 m hu S hS hSc hSJ hmap
      (fluxDp Q) (native_jet_p_partial_smooth J hsolution.jet_domain_open Q.flux Q.flux_smooth)
  have ham : ∀ i j, NativeCapHolder K α m (fun x => a x i j) := by
    intro i j
    simpa only [Function.comp_def, EuclideanSpace.proj, PiLp.proj_apply,
      ContinuousLinearMap.apply_apply, nativePrincipalWithin, a] using
      ((hAm.comp_linear hKD (ContinuousLinearMap.apply ℝ E2 (coordinateVector 2 j))).comp_linear
        hKD (EuclideanSpace.proj i))
  have hFm : NativeCapHolder K α m F :=
    hsolution.jet_composition_capHolder c hcf r hr hball α hα hα1 m hu S hS hSc hSJ hmap
      (nativeClassicalSourceJet Q) (native_classical_source_jet_smooth J hsolution.jet_domain_open Q)
  obtain ⟨κ, hκ, hnormal⟩ := hsolution.boundary_normal_flux_coercive
  have ha0 : ∀ x ∈ K, a x 0 0 ≠ 0 := fun x hx =>
    (hκ.trans_le (hnormal x (hK hx))).ne'
  have hNm : NativeCapHolder K α m N := by
    have hp01 := (ham 0 1).mul c r hr hcf hα hα1 (hTm 0)
    have hp10 := (ham 1 0).mul c r hr hcf hα hα1 (hTm 0)
    have hp11 := (ham 1 1).mul c r hr hcf hα hα1 (hTm 1)
    exact (((hFm.sub hKD hp01).sub hKD hp10).sub hKD hp11).div_positive
      c r κ hr hcf hκ hα hα1 (ham 0 0) (fun x hx => hnormal x (hK hx))
  have hGm : NativeCapHolder K α m G := (hNm.smul_const hKD (coordinateVector 2 0)).add
    hKD ((hTm 0).smul_const hKD (coordinateVector 2 1))
  have hder : ∀ x ∈ U, HasFDerivAt n (innerSL ℝ (G x)) x := by
    intro x hx
    have hxρ := hUρ hx
    have hd : DifferentiableAt ℝ n x :=
      ((hsolution.smooth_partial_on_openHalfDisc 0).contDiffAt
        ((openHalfDisc_isOpen ρ).mem_nhds hxρ)).differentiableAt (by simp)
    have htEq (i : Fin 2) : T i x = planarHessian u x i 1 := by
      change fderivWithin ℝ t K x (coordinateVector 2 i) = _
      rw [fderivWithin_of_mem_nhds (mem_of_superset (hU.mem_nhds hx) hUK)]
      simpa only [QuasilinearLocalization.Helpers.gradient_apply] using
        hsolution.native_partial_gradient_hessian x hxρ i 1
    have heq := hsolution.native_classical_equation_on_openHalfDisc x hxρ
    change (∑ i : Fin 2, ∑ j : Fin 2, rawPrincipalMatrix Q u x i j * planarHessian u x i j) = _ at heq
    have haEq := native_principalWithin_eq_raw Q u x hxρ
    have hFEq := native_classicalSourceWithin_eq Q u hxρ
    rw [← haEq, ← hFEq] at heq
    have hsym := hsolution.native_hessian_symmetry x hxρ 0 1
    have hN : N x = planarHessian u x 0 0 := by
      dsimp only [N]
      rw [htEq 0, htEq 1]
      exact (native_normal_hessian_formula (a x) (planarHessian u x) (F x)
        (ha0 x (hUK hx)) hsym heq).symm
    have hG : G x = planarGradient n x := by
      ext i
      fin_cases i
      · simpa [G, hN, coordinateVector, n] using
          (hsolution.native_partial_gradient_hessian x hxρ 0 0).symm
      · simpa [G, coordinateVector, htEq 0, hsym, n] using
          (hsolution.native_partial_gradient_hessian x hxρ 1 0).symm
    rw [hG, ← native_fderiv_eq_innerSL_planarGradient]
    exact hd.hasFDerivAt
  exact native_capHolder_smaller_cap_of_derivative c hcf r (r / 2)
    (by positivity) (by linarith) α hα m n (fun x => innerSL ℝ (G x)) hnC
    (hGm.comp_linear hKD (innerSL ℝ)) hder

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
