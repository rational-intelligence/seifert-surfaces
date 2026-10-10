import NativeBoundaryLinearTangentialSchauder
import NativeBoundaryLinearHessianEquation
import NativeBoundaryFiniteOrderReconstruction

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization QuasilinearBootstrap

/-- Normal recovery for the actual linear divergence equation. The source
contains exactly the derivatives of its original principal field and forcing. -/
theorem native_linear_normal_C1_holder_reconstruction
    (R r κ : ℝ) (hr : 0 < r) (hrR : r < R) (hκ : 0 < κ)
    (C : LinearizedCoefficients) (v : E2 → ℝ) (α : ℝ≥0)
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hv : ContDiffOn ℝ 1 v (closedHalfDisc R))
    (ha : ContDiffOn ℝ 1 C.a (closedHalfDisc R))
    (hd : ContDiffOn ℝ 1 C.d (closedHalfDisc R))
    (hDa : ∃ A, HolderOnWith A α (fderivWithin ℝ C.a (closedHalfDisc R)) (closedHalfDisc R))
    (hDd : ∃ A, HolderOnWith A α (fderivWithin ℝ C.d (closedHalfDisc R)) (closedHalfDisc R))
    (hDv : ∃ A, HolderOnWith A α (fderivWithin ℝ v (closedHalfDisc R)) (closedHalfDisc R))
    (hvi : ContDiffOn ℝ 2 v (openHalfDisc R))
    (hc : C.c = 0) (hb : C.b = 0) (hq : C.q = 0) (hf : C.f = 0)
    (hprincipal : ∀ x ∈ closedHalfDisc R, ∀ ξ : E2,
      κ * ‖ξ‖ ^ 2 ≤ inner ℝ (C.a x ξ) ξ)
    (hw : LinearWeakEquation (openHalfDisc R) C v (planarGradient v))
    (hT : ContDiffOn ℝ 1
      (fun x => fderivWithin ℝ v (closedHalfDisc R) x (coordinateVector 2 1)) (closedHalfDisc r))
    (hTH : ∃ A, HolderOnWith A α
      (fderivWithin ℝ (fun x => fderivWithin ℝ v (closedHalfDisc R) x (coordinateVector 2 1))
        (closedHalfDisc r)) (closedHalfDisc r)) :
    ContDiffOn ℝ 2 v (closedHalfDisc (r / 2)) ∧
      ∀ j : Fin 2,
        ContDiffOn ℝ 1 (fun x => fderivWithin ℝ v (closedHalfDisc R) x (coordinateVector 2 j))
          (closedHalfDisc (r / 2)) ∧
        ∃ A, HolderOnWith A α
          (fderivWithin ℝ (fun x => fderivWithin ℝ v (closedHalfDisc R) x (coordinateVector 2 j))
            (closedHalfDisc (r / 2))) (closedHalfDisc (r / 2)) := by
  let K0 := closedHalfDisc R
  let K := closedHalfDisc r
  let U := openHalfDisc r
  let t := fun x => fderivWithin ℝ v K0 x (coordinateVector 2 1)
  let n := fun x => fderivWithin ℝ v K0 x (coordinateVector 2 0)
  let a := fun x => nativeMatrixOfCLM (C.a x)
  let F := fun x => -(∑ i : Fin 2, (
    (fderivWithin ℝ C.a K0 x (coordinateVector 2 i) (planarGradientWithin v K0 x)) i +
      (fderivWithin ℝ C.d K0 x (coordinateVector 2 i)) i))
  let T (i : Fin 2) := fun x => fderivWithin ℝ t K x (coordinateVector 2 i)
  let N := fun x => (F x - a x 0 1 * T 0 x - a x 1 0 * T 0 x - a x 1 1 * T 1 x) / a x 0 0
  let G := fun x => N x • coordinateVector 2 0 + T 0 x • coordinateVector 2 1
  have hR : 0 < R := hr.trans hrR
  have hKsub : K ⊆ K0 := closedHalfDisc_mono hrR.le
  have hUsub : U ⊆ openHalfDisc R := fun x hx =>
    ⟨Metric.ball_subset_ball hrR.le hx.1, hx.2⟩
  have hUK : U ⊆ K := openHalfDisc_subset_closedHalfDisc _
  have hKc : IsCompact K := (isCompact_closedBall (0 : E2) r).inter_right
    (isClosed_le continuous_const (EuclideanSpace.proj (0 : Fin 2)).continuous)
  have hnC : ContinuousOn n K :=
    ((hv.continuousOn_fderivWithin (closedHalfDisc_uniqueDiffOn hR) (by norm_num)).clm_apply
      (continuousOn_const (c := coordinateVector 2 0))).mono hKsub
  have hTC (i : Fin 2) : ContinuousOn (T i) K :=
    (hT.continuousOn_fderivWithin (closedHalfDisc_uniqueDiffOn hr) (by norm_num)).clm_apply continuousOn_const
  have hTHi (i : Fin 2) : ∃ A, HolderOnWith A α (T i) K :=
    native_holder_derivative_apply_const K t α hTH (coordinateVector 2 i)
  have hAa : ∃ A, HolderOnWith A α C.a K := by
    obtain ⟨A, hA⟩ := native_contDiffOn_cap_holder 0 R hR C.a α hα1 ha
    exact ⟨A, hA.mono hKsub⟩
  obtain ⟨HA, hHA⟩ := native_holder_matrix_of_clm K C.a α hAa
  have haH (i j : Fin 2) : ∃ A, HolderOnWith A α (fun x => a x i j) K := ⟨HA, hHA i j⟩
  obtain ⟨HG, hHG⟩ := native_holder_planarGradientWithin K0 v α hDv
  have hterm (i : Fin 2) : ∃ A, HolderOnWith A α
      (fun x => (fderivWithin ℝ C.a K0 x (coordinateVector 2 i) (planarGradientWithin v K0 x)) i +
        (fderivWithin ℝ C.d K0 x (coordinateVector 2 i)) i) K := by
    obtain ⟨Ai, hAi⟩ := native_holder_derivative_apply_const K0 C.a α hDa (coordinateVector 2 i)
    obtain ⟨Di, hDi⟩ := native_holder_derivative_apply_const K0 C.d α hDd (coordinateVector 2 i)
    obtain ⟨Pi, hPi⟩ := native_compact_holder_clm_apply_exists K hKc _ _ α hα
      ⟨Ai, hAi.mono hKsub⟩ ⟨HG, hHG.mono hKsub⟩
    have hPs := native_holder_comp_linear K _ Pi α hPi (EuclideanSpace.proj i)
    have hDs := native_holder_comp_linear K _ Di α (hDi.mono hKsub) (EuclideanSpace.proj i)
    exact ⟨_, native_holder_add K _ _ _ _ α hPs hDs⟩
  have hFH : ∃ A, HolderOnWith A α F K := by
    obtain ⟨A0, h0⟩ := hterm 0
    obtain ⟨A1, h1⟩ := hterm 1
    simpa only [F, Fin.sum_univ_two] using
      ⟨A0 + A1, native_holder_neg K _ (A0 + A1) α (native_holder_add K _ _ A0 A1 α h0 h1)⟩
  have haa : ∀ x ∈ K, κ ≤ a x 0 0 := by
    intro x hx
    have he := hprincipal x (hKsub hx) (coordinateVector 2 0)
    simpa [a, nativeMatrixOfCLM, PiLp.inner_apply, Fin.sum_univ_two, coordinateVector, PiLp.norm_single] using he
  have ha0 (x : E2) (hx : x ∈ K) : a x 0 0 ≠ 0 := (hκ.trans_le (haa x hx)).ne'
  have hNH : ∃ A, HolderOnWith A α N K := by
    have hp01 := native_compact_holder_mul_exists K hKc _ _ α hα (haH 0 1) (hTHi 0)
    have hp10 := native_compact_holder_mul_exists K hKc _ _ α hα (haH 1 0) (hTHi 0)
    have hp11 := native_compact_holder_mul_exists K hKc _ _ α hα (haH 1 1) (hTHi 1)
    exact native_compact_holder_div_exists K hKc _ _ α hα κ hκ haa
      (native_compact_holder_sub_exists K _ _ α
        (native_compact_holder_sub_exists K _ _ α
          (native_compact_holder_sub_exists K _ _ α hFH hp01) hp10) hp11) (haH 0 0)
  obtain ⟨HN, hHN⟩ := hNH
  have hGC : ContinuousOn G K := ((hHN.continuousOn hα).smul continuousOn_const).add
    ((hTC 0).smul continuousOn_const)
  have hEq := native_linear_classical_hessian_equation (openHalfDisc R) K0 (openHalfDisc_isOpen R)
    (fun x hx => mem_of_superset ((openHalfDisc_isOpen R).mem_nhds hx)
      (openHalfDisc_subset_closedHalfDisc R)) C v
    (ha.mono (openHalfDisc_subset_closedHalfDisc R)) (hd.mono (openHalfDisc_subset_closedHalfDisc R))
    hvi hc hb hq hf hw
  have hder : ∀ x ∈ U, HasFDerivAt n (innerSL ℝ (G x)) x := by
    intro x hx
    have hxi := hUsub hx
    have htEq (i : Fin 2) : T i x = planarHessian v x i 1 := by
      change fderivWithin ℝ t K x (coordinateVector 2 i) = _
      rw [fderivWithin_of_mem_nhds (mem_of_superset ((openHalfDisc_isOpen r).mem_nhds hx) hUK)]
      simpa only [QuasilinearLocalization.Helpers.gradient_apply] using
        native_generic_partial_gradient_hessian (openHalfDisc R) K0 (openHalfDisc_isOpen R)
          (fun y hy => mem_of_superset ((openHalfDisc_isOpen R).mem_nhds hy)
            (openHalfDisc_subset_closedHalfDisc R)) v hvi x hxi i 1
    have hsym : planarHessian v x 0 1 = planarHessian v x 1 0 :=
      ((hvi.contDiffAt ((openHalfDisc_isOpen R).mem_nhds hxi)).isSymmSndFDerivAt (by norm_num)).eq _ _
    have hN : N x = planarHessian v x 0 0 := by
      dsimp only [N]
      rw [htEq 0, htEq 1]
      exact (native_normal_hessian_formula (a x) (planarHessian v x) (F x)
        (ha0 x (hUK hx)) hsym (hEq x hxi)).symm
    have hpartial (i : Fin 2) : planarGradient n x i = planarHessian v x i 0 :=
      native_generic_partial_gradient_hessian (openHalfDisc R) K0 (openHalfDisc_isOpen R)
        (fun y hy => mem_of_superset ((openHalfDisc_isOpen R).mem_nhds hy)
          (openHalfDisc_subset_closedHalfDisc R)) v hvi x hxi i 0
    have hG : G x = planarGradient n x := by
      ext i
      fin_cases i
      · simpa [G, hN, coordinateVector] using (hpartial 0).symm
      · simpa [G, coordinateVector, htEq 0, hsym] using (hpartial 1).symm
    have hnc : ContDiffOn ℝ 1 n (openHalfDisc R) := by
      apply ((hvi.fderiv_of_isOpen (openHalfDisc_isOpen R) (m := 1) (by norm_num)).clm_apply
        contDiffOn_const).congr
      intro y hy
      change fderivWithin ℝ v K0 y (coordinateVector 2 0) =
        fderiv ℝ v y (coordinateVector 2 0)
      rw [fderivWithin_of_mem_nhds (mem_of_superset ((openHalfDisc_isOpen R).mem_nhds hy)
        (openHalfDisc_subset_closedHalfDisc R))]
    rw [hG, ← native_fderiv_eq_innerSL_planarGradient]
    exact ((hnc.contDiffAt ((openHalfDisc_isOpen R).mem_nhds hxi)).differentiableAt (by norm_num)).hasFDerivAt
  have hgain := native_C1_smaller_cap_of_continuous_derivative 0 (by simp) r (r / 2)
    (by positivity) (by linarith) n (fun x => innerSL ℝ (G x)) hnC
    ((innerSL ℝ).continuous.comp_continuousOn hGC) hder
  change ContDiffOn ℝ 1 n (closedHalfDisc (r / 2)) ∧
    EqOn (fderivWithin ℝ n (closedHalfDisc (r / 2)))
      (fun x => innerSL ℝ (G x)) (closedHalfDisc (r / 2)) at hgain
  have hsub : closedHalfDisc (r / 2) ⊆ K := closedHalfDisc_mono (by linarith)
  have hnH : ∃ A, HolderOnWith A α (fderivWithin ℝ n (closedHalfDisc (r / 2)))
      (closedHalfDisc (r / 2)) := by
    apply native_clm_holder_of_coordinate_evaluations
    intro i
    fin_cases i
    · refine ⟨HN, ?_⟩
      intro x hx y hy
      change edist ((fderivWithin ℝ n (closedHalfDisc (r / 2)) x) (coordinateVector 2 0))
        ((fderivWithin ℝ n (closedHalfDisc (r / 2)) y) (coordinateVector 2 0)) ≤ _
      rw [hgain.2 hx, hgain.2 hy]
      simpa [G, innerSL_apply_apply, PiLp.inner_apply, coordinateVector] using hHN x (hsub hx) y (hsub hy)
    · obtain ⟨A, hA⟩ := hTHi 0
      refine ⟨A, ?_⟩
      intro x hx y hy
      change edist ((fderivWithin ℝ n (closedHalfDisc (r / 2)) x) (coordinateVector 2 1))
        ((fderivWithin ℝ n (closedHalfDisc (r / 2)) y) (coordinateVector 2 1)) ≤ _
      rw [hgain.2 hx, hgain.2 hy]
      simpa [G, innerSL_apply_apply, PiLp.inner_apply, coordinateVector] using hA x (hsub hx) y (hsub hy)
  have htH := native_derivative_holder_cap_restrict 0 (by simp) r (r / 2) (by positivity)
    (by linarith) t hT α (fun i => native_holder_derivative_apply_const K t α hTH (coordinateVector 2 i))
  have hparts : ∀ j : Fin 2, ContDiffOn ℝ 1
      (fun x => fderivWithin ℝ v K0 x (coordinateVector 2 j)) (closedHalfDisc (r / 2)) ∧
      ∃ A, HolderOnWith A α
        (fderivWithin ℝ (fun x => fderivWithin ℝ v K0 x (coordinateVector 2 j))
          (closedHalfDisc (r / 2))) (closedHalfDisc (r / 2)) := by
    intro j
    fin_cases j
    · exact ⟨hgain.1, hnH⟩
    · exact ⟨hT.mono hsub, native_clm_holder_of_coordinate_evaluations _ _ α htH⟩
  have hGrad : ContDiffOn ℝ 1 (planarGradientWithin v K0) (closedHalfDisc (r / 2)) :=
    ContDiffOn.sum (fun j _ => (hparts j).1.smul contDiffOn_const)
  have hDf : ContDiffOn ℝ 1 (fderivWithin ℝ v (closedHalfDisc (r / 2))) (closedHalfDisc (r / 2)) := by
    apply ((innerSL ℝ).contDiff.comp_contDiffOn hGrad).congr
    intro x hx
    rw [fderivWithin_subset (hsub.trans hKsub) (closedHalfDisc_uniqueDiffOn (by positivity) x hx)
      (hv.differentiableOn (by norm_num) x ((hsub.trans hKsub) hx))]
    simpa only [Function.comp_def] using (native_fderivWithin_eq_innerSL_planarGradientWithin v K0 x)
  exact ⟨contDiffOn_succ_of_fderivWithin
    ((hv.differentiableOn (by norm_num)).mono (hsub.trans hKsub)) (by norm_num) hDf, hparts⟩

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
