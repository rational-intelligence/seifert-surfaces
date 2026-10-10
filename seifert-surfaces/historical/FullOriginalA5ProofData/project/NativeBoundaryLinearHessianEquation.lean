import NativeBoundaryClassicalDivergence
import NativeBoundaryLinearTangentialEquation
import NativeBoundaryGenericCoefficientFields

set_option autoImplicit false
set_option maxHeartbeats 100000
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization QuasilinearBootstrap

theorem native_generic_partial_gradient_hessian
    (U K : Set E2) (hU : IsOpen U) (hUK : ∀ x ∈ U, K ∈ 𝓝 x)
    (v : E2 → ℝ) (hv : ContDiffOn ℝ 2 v U)
    (x : E2) (hx : x ∈ U) (i j : Fin 2) :
    planarGradient (fun y => fderivWithin ℝ v K y (coordinateVector 2 j)) x i =
      planarHessian v x i j := by
  have he : (fun y => fderivWithin ℝ v K y (coordinateVector 2 j)) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ v y (coordinateVector 2 j)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    rw [fderivWithin_of_mem_nhds (hUK y hy)]
  rw [QuasilinearLocalization.Helpers.gradient_apply, he.fderiv_eq]
  have hd : DifferentiableAt ℝ (fderiv ℝ v) x :=
    ((hv.fderiv_of_isOpen hU (m := 1) (by norm_num)).contDiffAt
      (hU.mem_nhds hx)).differentiableAt (by norm_num)
  simp only [fderiv_clm_apply hd (differentiableAt_const _), fderiv_fun_const,
    add_apply, ContinuousLinearMap.comp_apply, zero_apply, Pi.zero_apply, map_zero, zero_add,
    ContinuousLinearMap.flip_apply, planarHessian]

theorem native_generic_gradient_derivative
    (U : Set E2) (hU : IsOpen U) (v : E2 → ℝ) (hv : ContDiffOn ℝ 2 v U)
    (x : E2) (hx : x ∈ U) (i : Fin 2) :
    fderiv ℝ (planarGradient v) x (coordinateVector 2 i) =
      ∑ j : Fin 2, planarHessian v x i j • coordinateVector 2 j := by
  have hd : DifferentiableAt ℝ (fderiv ℝ v) x :=
    ((hv.fderiv_of_isOpen hU (m := 1) (by norm_num)).contDiffAt
      (hU.mem_nhds hx)).differentiableAt (by norm_num)
  unfold planarGradient
  rw [fderiv_fun_sum (fun j _ => (hd.clm_apply (differentiableAt_const _)).smul_const _)]
  simp only [sum_apply, fderiv_smul_const (hd.clm_apply (differentiableAt_const _)),
    ContinuousLinearMap.smulRight_apply, fderiv_clm_apply hd (differentiableAt_const _),
    fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply, planarHessian]

/-- Expansion of the actual divergence equation. No symmetry of the
principal operator is assumed. -/
theorem native_linear_classical_hessian_equation
    (U K : Set E2) (hU : IsOpen U) (hUK : ∀ x ∈ U, K ∈ 𝓝 x)
    (C : LinearizedCoefficients) (v : E2 → ℝ)
    (ha : ContDiffOn ℝ 1 C.a U) (hd : ContDiffOn ℝ 1 C.d U)
    (hv : ContDiffOn ℝ 2 v U)
    (hc : C.c = 0) (hb : C.b = 0) (hq : C.q = 0) (hf : C.f = 0)
    (hw : LinearWeakEquation U C v (planarGradient v)) :
    ∀ x ∈ U, ∑ i : Fin 2, ∑ j : Fin 2,
      nativeMatrixOfCLM (C.a x) i j * planarHessian v x i j =
      -(∑ i : Fin 2, (
        (fderivWithin ℝ C.a K x (coordinateVector 2 i) (planarGradientWithin v K x)) i +
          (fderivWithin ℝ C.d K x (coordinateVector 2 i)) i)) := by
  let G := planarGradient v
  let F := fun x => C.a x (G x) + C.d x
  have hG : ContDiffOn ℝ 1 G U := by
    unfold G planarGradient
    exact ContDiffOn.sum (fun i _ =>
      ((hv.fderiv_of_isOpen hU (m := 1) (by norm_num)).clm_apply contDiffOn_const).smul_const _)
  have hF : ContDiffOn ℝ 1 F U := (ha.clm_apply hG).add hd
  have hweak : ∀ φ : E2 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ x in U, inner ℝ (F x) (planarGradient φ x)) = 0 := by
    intro φ hs hcompact ht
    simpa only [linearizedFlux, linearizedSource, hc, hb, hq, hf, Pi.zero_apply,
      zero_apply, smul_zero, add_zero, zero_mul, sub_zero, F, G] using (hw φ hs hcompact ht).2.2
  have hpoint := native_classical_divergence_zero_of_weak U hU F hF hweak
  intro x hx
  have had := (ha.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
  have hgd := (hG.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
  have hdd := (hd.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
  have hcomp (i : Fin 2) :
      (fderiv ℝ F x (coordinateVector 2 i)) i =
        (fderiv ℝ C.a x (coordinateVector 2 i) (G x)) i +
        (∑ j : Fin 2, nativeMatrixOfCLM (C.a x) i j * planarHessian v x i j) +
        (fderiv ℝ C.d x (coordinateVector 2 i)) i := by
    dsimp only [F]
    rw [fderiv_fun_add (had.clm_apply hgd) hdd, add_apply, fderiv_clm_apply had hgd,
      add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
    rw [show fderiv ℝ G x (coordinateVector 2 i) =
      ∑ j : Fin 2, planarHessian v x i j • coordinateVector 2 j from
      native_generic_gradient_derivative U hU v hv x hx i]
    simp only [Fin.sum_univ_two, map_add, map_smul, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul, nativeMatrixOfCLM]
    ring
  have he := hpoint x hx
  simp_rw [hcomp] at he
  have hwithinG : planarGradientWithin v K x = G x := by
    unfold planarGradientWithin G planarGradient
    rw [fderivWithin_of_mem_nhds (hUK x hx)]
  rw [hwithinG]
  simp only [fderivWithin_of_mem_nhds (hUK x hx), Fin.sum_univ_two] at he ⊢
  linarith

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
