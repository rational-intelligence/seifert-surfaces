import NativeBoundaryTangentialHessianHolder
import NativeBoundaryHolderCompactAlgebra

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization QuasilinearBootstrap
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak.BoundaryContinuation

/-- The original normal within derivative is C1 on a smaller closed cap:
its missing derivative is recovered from the actual elliptic equation. -/
theorem C1QuasilinearDirichletSolution.local_C2_holder_closed_boundary_cap
    {ρ : ℝ} (hρ : 0 < ρ) {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (c : E2) (hc : c ∈ flatBoundary ρ) :
    ∃ δ : ℝ, ∃ α : ℝ≥0, 0 < δ ∧ 0 < α ∧ α < 1 ∧
      Metric.closedBall c δ ⊆ Metric.ball 0 ρ ∧
      ContDiffOn ℝ 2 u (nativeClosedBoundaryCap c δ) ∧
      ∀ i j : Fin 2, ∃ C : ℝ≥0, HolderOnWith C α
        (fun x => fderivWithin ℝ
          (fun y => fderivWithin ℝ u (closedHalfDisc ρ) y (coordinateVector 2 j))
          (nativeClosedBoundaryCap c δ) x (coordinateVector 2 i))
        (nativeClosedBoundaryCap c δ) := by
  obtain ⟨tR, α, htR, hα, hα1, htball, htC, htH⟩ :=
    hsolution.local_C1_holder_tangential_derivative hρ c hc
  obtain ⟨sR, hsR, hsball, huC⟩ := hsolution.local_C2_closed_boundary_cap hρ c hc
  let r := min tR sR
  have hr : 0 < r := lt_min htR hsR
  have hrt : r ≤ tR := min_le_left _ _
  have hrs : r ≤ sR := min_le_right _ _
  have hball : Metric.closedBall c r ⊆ Metric.ball 0 ρ :=
    (Metric.closedBall_subset_closedBall hrt).trans htball
  have hsubT : nativeClosedBoundaryCap c r ⊆ nativeClosedBoundaryCap c tR := fun x hx =>
    ⟨Metric.closedBall_subset_closedBall hrt hx.1, hx.2⟩
  have hsubS : nativeClosedBoundaryCap c r ⊆ nativeClosedBoundaryCap c sR := fun x hx =>
    ⟨Metric.closedBall_subset_closedBall hrs hx.1, hx.2⟩
  have hT := htC.mono hsubT
  have hTH := native_derivative_holder_cap_restrict c hc.2 tR r hr hrt _ htC α htH
  have hu2 := huC.mono hsubS
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
  have hcompact : IsCompact K := (isCompact_closedBall c r).inter_right
    (isClosed_le continuous_const (EuclideanSpace.proj (0 : Fin 2)).continuous)
  have hA1 : ContDiffOn ℝ 1 (fun x => fluxDp Q (firstJetWithin ρ u x)) K :=
    hsolution.jet_composition_contDiffOn_cap c hcf r hr hball 1 hu2
      (fluxDp Q) (native_jet_p_partial_smooth J hsolution.jet_domain_open Q.flux Q.flux_smooth)
  have ha1 : ∀ i j, ContDiffOn ℝ 1 (fun x => a x i j) K := by
    intro i j
    simpa only [Function.comp_def, EuclideanSpace.proj, PiLp.proj_apply, nativePrincipalWithin, a] using
      (EuclideanSpace.proj i).contDiff.comp_contDiffOn (hA1.clm_apply (contDiffOn_const (c := coordinateVector 2 j)))
  have hF1 : ContDiffOn ℝ 1 F K :=
    hsolution.jet_composition_contDiffOn_cap c hcf r hr hball 1 hu2
      (nativeClassicalSourceJet Q) (native_classical_source_jet_smooth J hsolution.jet_domain_open Q)
  have haH : ∀ i j, ∃ C, HolderOnWith C α (fun x => a x i j) K := fun i j =>
    native_contDiffOn_cap_holder c r hr _ α hα1.le (ha1 i j)
  have hFH : ∃ C, HolderOnWith C α F K :=
    native_contDiffOn_cap_holder c r hr _ α hα1.le hF1
  have hTC : ∀ i, ContinuousOn (T i) K := fun i =>
    (hT.continuousOn_fderivWithin (nativeClosedBoundaryCap_uniqueDiffOn c r hr hcf)
      (by norm_num)).clm_apply (continuousOn_const (c := coordinateVector 2 i))
  have haC : ∀ i j, ContinuousOn (fun x => a x i j) K := by
    intro i j
    exact (EuclideanSpace.proj i).continuous.comp_continuousOn
      (((hsolution.continuous_native_flux_slices hρ).2.2.clm_apply
        (continuousOn_const (c := coordinateVector 2 j))).mono hK)
  have hFC : ContinuousOn F K :=
    ((native_classical_source_jet_smooth J hsolution.jet_domain_open Q).continuousOn.comp
      (continuousOn_firstJetWithin hρ hsolution.c1) hsolution.attained_jets).mono hK
  obtain ⟨κ, hκ, hnormal⟩ := hsolution.boundary_normal_flux_coercive
  have ha0 : ∀ x ∈ K, a x 0 0 ≠ 0 := fun x hx =>
    (hκ.trans_le (hnormal x (hK hx))).ne'
  have hNH : ∃ C, HolderOnWith C α N K := by
    have hp01 := native_compact_holder_mul_exists K hcompact _ _ α hα (haH 0 1) (hTH 0)
    have hp10 := native_compact_holder_mul_exists K hcompact _ _ α hα (haH 1 0) (hTH 0)
    have hp11 := native_compact_holder_mul_exists K hcompact _ _ α hα (haH 1 1) (hTH 1)
    have hs01 := native_compact_holder_sub_exists K _ _ α hFH hp01
    have hs10 := native_compact_holder_sub_exists K _ _ α hs01 hp10
    have hs11 := native_compact_holder_sub_exists K _ _ α hs10 hp11
    exact native_compact_holder_div_exists K hcompact _ _ α hα κ hκ
      (fun x hx => hnormal x (hK hx)) hs11 (haH 0 0)
  have hNC : ContinuousOn N K :=
    (((hFC.sub ((haC 0 1).mul (hTC 0))).sub ((haC 1 0).mul (hTC 0))).sub
      ((haC 1 1).mul (hTC 1))).div (haC 0 0) ha0
  have hGC : ContinuousOn G K := (hNC.smul continuousOn_const).add
    ((hTC 0).smul continuousOn_const)
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
  have hDC : ContinuousOn (fun x => innerSL ℝ (G x)) K :=
    (innerSL ℝ).continuous.comp_continuousOn hGC
  have hgain := native_C1_smaller_cap_of_continuous_derivative c hcf r (r / 2)
    (by positivity) (by linarith) n (fun x => innerSL ℝ (G x)) hnC hDC hder
  have hsmall : nativeClosedBoundaryCap c (r / 2) ⊆ K := fun x hx =>
    ⟨Metric.closedBall_subset_closedBall (by linarith) hx.1, hx.2⟩
  have hnormalH : ∀ i, ∃ C, HolderOnWith C α
      (fun x => fderivWithin ℝ n (nativeClosedBoundaryCap c (r / 2)) x (coordinateVector 2 i))
      (nativeClosedBoundaryCap c (r / 2)) := by
    intro i
    fin_cases i
    · obtain ⟨C, hC⟩ := hNH
      refine ⟨C, ?_⟩
      intro x hx y hy
      change edist ((fderivWithin ℝ n (nativeClosedBoundaryCap c (r / 2)) x) (coordinateVector 2 0))
          ((fderivWithin ℝ n (nativeClosedBoundaryCap c (r / 2)) y) (coordinateVector 2 0)) ≤ _
      rw [hgain.2 hx, hgain.2 hy]
      simpa [G, T, t, K, innerSL_apply_apply, PiLp.inner_apply, coordinateVector] using
        hC x (hsmall hx) y (hsmall hy)
    · obtain ⟨C, hC⟩ := hTH 0
      refine ⟨C, ?_⟩
      intro x hx y hy
      change edist ((fderivWithin ℝ n (nativeClosedBoundaryCap c (r / 2)) x) (coordinateVector 2 1))
          ((fderivWithin ℝ n (nativeClosedBoundaryCap c (r / 2)) y) (coordinateVector 2 1)) ≤ _
      rw [hgain.2 hx, hgain.2 hy]
      simpa [G, T, t, K, innerSL_apply_apply, PiLp.inner_apply, coordinateVector] using
        hC x (hsmall hx) y (hsmall hy)
  have htSmallH := native_derivative_holder_cap_restrict c hcf r (r / 2) (by positivity)
    (by linarith) t hT α hTH
  refine ⟨r / 2, α, by positivity, hα, hα1,
    (Metric.closedBall_subset_closedBall (by linarith)).trans hball, hu2.mono hsmall, ?_⟩
  intro i j
  fin_cases j
  · exact hnormalH i
  · exact htSmallH i

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
