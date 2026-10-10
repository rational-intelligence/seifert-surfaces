import NativeBoundaryLinearNormalReconstruction
import NativeBoundaryFiniteHolderAlgebra

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization QuasilinearBootstrap

theorem native_linear_higher_normal_derivative
    (R r κ : ℝ) (hr : 0 < r) (hrR : r < R) (hκ : 0 < κ)
    (C : LinearizedCoefficients) (v : E2 → ℝ) (α : ℝ≥0)
    (hα : 0 < α) (hα1 : α ≤ 1) (m : ℕ)
    (hv : NativeCapHolder (closedHalfDisc R) α (m + 1) v)
    (ha : NativeCapHolder (closedHalfDisc R) α (m + 1) C.a)
    (hd : NativeCapHolder (closedHalfDisc R) α (m + 1) C.d)
    (hvi : ContDiffOn ℝ 2 v (openHalfDisc R))
    (hc : C.c = 0) (hb : C.b = 0) (hq : C.q = 0) (hf : C.f = 0)
    (hprincipal : ∀ x ∈ closedHalfDisc R, ∀ ξ : E2,
      κ * ‖ξ‖ ^ 2 ≤ inner ℝ (C.a x ξ) ξ)
    (hw : LinearWeakEquation (openHalfDisc R) C v (planarGradient v))
    (hT : NativeCapHolder (closedHalfDisc r) α (m + 1)
      (fun x => fderivWithin ℝ v (closedHalfDisc R) x (coordinateVector 2 1))) :
    NativeCapHolder (closedHalfDisc (r / 2)) α (m + 1)
      (fun x => fderivWithin ℝ v (closedHalfDisc R) x (coordinateVector 2 0)) := by
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
  have hKD := closedHalfDisc_uniqueDiffOn hr
  have hK0D := closedHalfDisc_uniqueDiffOn hR
  have ha1 : ContDiffOn ℝ 1 C.a K0 := ha.1.of_le (by simp)
  have hd1 : ContDiffOn ℝ 1 C.d K0 := hd.1.of_le (by simp)
  have hv1 : ContDiffOn ℝ 1 v K0 := hv.1.of_le (by simp)
  have ht1 : ContDiffOn ℝ 1 t K := hT.1.of_le (by simp)
  have hnC : ContinuousOn n K :=
    ((hv1.continuousOn_fderivWithin hK0D (by norm_num)).clm_apply
      (continuousOn_const (c := coordinateVector 2 0))).mono hKsub
  have haLow : NativeCapHolder K α m C.a :=
    (ha.lower 0 R hR hα1).restrict hKsub hKD
  have haEntry (i j : Fin 2) : NativeCapHolder K α m (fun x => a x i j) := by
    exact (haLow.comp_linear hKD (ContinuousLinearMap.apply ℝ E2 (coordinateVector 2 j))).comp_linear
      hKD (EuclideanSpace.proj i)
  have hTm (i : Fin 2) : NativeCapHolder K α m (T i) := hT.2 i
  have hGm : NativeCapHolder K α m (planarGradientWithin v K0) :=
    (hv.gradient_field hK0D).restrict hKsub hKD
  have hterm (i : Fin 2) : NativeCapHolder K α m
      (fun x => (fderivWithin ℝ C.a K0 x (coordinateVector 2 i) (planarGradientWithin v K0 x)) i +
        (fderivWithin ℝ C.d K0 x (coordinateVector 2 i)) i) := by
    have hp := ((ha.2 i).restrict hKsub hKD).clm_apply 0 r hr (by simp) hα hα1 hGm
    have hs := hp.comp_linear hKD (EuclideanSpace.proj i)
    have hd' := ((hd.2 i).restrict hKsub hKD).comp_linear hKD (EuclideanSpace.proj i)
    exact hs.add hKD hd'
  have hFm : NativeCapHolder K α m F := by
    simpa only [F, Fin.sum_univ_two] using ((hterm 0).add hKD (hterm 1)).neg hKD
  have haa : ∀ x ∈ K, κ ≤ a x 0 0 := by
    intro x hx
    have he := hprincipal x (hKsub hx) (coordinateVector 2 0)
    simpa [a, nativeMatrixOfCLM, PiLp.inner_apply, Fin.sum_univ_two, coordinateVector, PiLp.norm_single] using he
  have ha0 (x : E2) (hx : x ∈ K) : a x 0 0 ≠ 0 := (hκ.trans_le (haa x hx)).ne'
  have hNm : NativeCapHolder K α m N := by
    have hp01 := (haEntry 0 1).mul 0 r hr (by simp) hα hα1 (hTm 0)
    have hp10 := (haEntry 1 0).mul 0 r hr (by simp) hα hα1 (hTm 0)
    have hp11 := (haEntry 1 1).mul 0 r hr (by simp) hα hα1 (hTm 1)
    exact (((hFm.sub hKD hp01).sub hKD hp10).sub hKD hp11).div_positive
      0 r κ hr (by simp) hκ hα hα1 (haEntry 0 0) haa
  have hGGm : NativeCapHolder K α m G :=
    (hNm.smul_const hKD (coordinateVector 2 0)).add hKD ((hTm 0).smul_const hKD (coordinateVector 2 1))
  have hEq := native_linear_classical_hessian_equation (openHalfDisc R) K0 (openHalfDisc_isOpen R)
    (fun x hx => mem_of_superset ((openHalfDisc_isOpen R).mem_nhds hx)
      (openHalfDisc_subset_closedHalfDisc R)) C v
    (ha1.mono (openHalfDisc_subset_closedHalfDisc R)) (hd1.mono (openHalfDisc_subset_closedHalfDisc R))
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
      change fderivWithin ℝ v K0 y (coordinateVector 2 0) = fderiv ℝ v y (coordinateVector 2 0)
      rw [fderivWithin_of_mem_nhds (mem_of_superset ((openHalfDisc_isOpen R).mem_nhds hy)
        (openHalfDisc_subset_closedHalfDisc R))]
    rw [hG, ← native_fderiv_eq_innerSL_planarGradient]
    exact ((hnc.contDiffAt ((openHalfDisc_isOpen R).mem_nhds hxi)).differentiableAt (by norm_num)).hasFDerivAt
  exact native_capHolder_smaller_cap_of_derivative 0 (by simp) r (r / 2) (by positivity)
    (by linarith) α hα m n (fun x => innerSL ℝ (G x)) hnC (hGGm.comp_linear hKD (innerSL ℝ)) hder

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
