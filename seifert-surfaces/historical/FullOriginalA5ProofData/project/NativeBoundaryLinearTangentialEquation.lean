import NativeBoundaryDifferentiateDivergence
import NativeBoundaryGenericTangentialDerivative

set_option autoImplicit false
set_option maxHeartbeats 50000
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization

def nativeClosedDifferentiatedLinearCoefficients (K : Set E2)
    (C : LinearizedCoefficients) (v : E2 → ℝ) : LinearizedCoefficients where
  a := C.a
  c := 0
  d x := fderivWithin ℝ C.a K x (coordinateVector 2 1) (planarGradientWithin v K x) +
    fderivWithin ℝ C.d K x (coordinateVector 2 1)
  b := 0
  q := 0
  f := 0

theorem native_gradient_derivative_tangent_commutes
    (U : Set E2) (hU : IsOpen U) (v : E2 → ℝ) (hv : ContDiffOn ℝ 2 v U)
    (x : E2) (hx : x ∈ U) :
    fderiv ℝ (planarGradient v) x (coordinateVector 2 1) =
      planarGradient (fun y => fderiv ℝ v y (coordinateVector 2 1)) x := by
  have hD : ContDiffOn ℝ 1 (fderiv ℝ v) U := hv.fderiv_of_isOpen hU (by norm_num)
  have hd : DifferentiableAt ℝ (fderiv ℝ v) x :=
    (hD.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
  have hparts (i : Fin 2) : DifferentiableAt ℝ (fun y => fderiv ℝ v y (coordinateVector 2 i)) x :=
    hd.clm_apply (differentiableAt_const _)
  have hcomm (i : Fin 2) :
      fderiv ℝ (fun y => fderiv ℝ v y (coordinateVector 2 i)) x (coordinateVector 2 1) =
      fderiv ℝ (fun y => fderiv ℝ v y (coordinateVector 2 1)) x (coordinateVector 2 i) := by
    simp only [fderiv_clm_apply hd (differentiableAt_const _), fderiv_fun_const,
      add_apply, ContinuousLinearMap.comp_apply, zero_apply, Pi.zero_apply, map_zero, zero_add,
      ContinuousLinearMap.flip_apply]
    exact ((hv.contDiffAt (hU.mem_nhds hx)).isSymmSndFDerivAt (by norm_num)).eq _ _
  unfold planarGradient
  rw [fderiv_fun_sum (fun i _ => (hparts i).smul_const (coordinateVector 2 i))]
  simp only [ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [fderiv_smul_const (hparts i), ContinuousLinearMap.smulRight_apply, hcomm i]

/-- The actual within tangent derivative satisfies the differentiated
linear equation on the same one-sided open region. -/
theorem native_closed_tangential_derivative_linear_weak
    (U K : Set E2) (hU : IsOpen U) (hUK : ∀ x ∈ U, K ∈ 𝓝 x)
    (C : LinearizedCoefficients) (v : E2 → ℝ)
    (ha : ContDiffOn ℝ 1 C.a U) (hd : ContDiffOn ℝ 1 C.d U)
    (hv : ContDiffOn ℝ 2 v U)
    (hc : C.c = 0) (hb : C.b = 0) (hq : C.q = 0) (hf : C.f = 0)
    (hw : LinearWeakEquation U C v (planarGradient v)) :
    let t := fun x => fderivWithin ℝ v K x (coordinateVector 2 1)
    ContDiffOn ℝ 1 t U ∧
      LinearWeakEquation U (nativeClosedDifferentiatedLinearCoefficients K C v) t (planarGradient t) := by
  let t := fun x => fderivWithin ℝ v K x (coordinateVector 2 1)
  let t0 := fun x => fderiv ℝ v x (coordinateVector 2 1)
  let F := fun x => C.a x (planarGradient v x) + C.d x
  have hD : ContDiffOn ℝ 1 (fderiv ℝ v) U := hv.fderiv_of_isOpen hU (by norm_num)
  have hG : ContDiffOn ℝ 1 (planarGradient v) U := by
    unfold planarGradient
    exact ContDiffOn.sum (fun i _ => (hD.clm_apply contDiffOn_const).smul_const _)
  have hFc : ContDiffOn ℝ 1 F U := (ha.clm_apply hG).add hd
  have ht0 : ContDiffOn ℝ 1 t0 U := hD.clm_apply contDiffOn_const
  have htEq : EqOn t t0 U := by
    intro x hx
    dsimp only [t, t0]
    rw [fderivWithin_of_mem_nhds (hUK x hx)]
  have htc : ContDiffOn ℝ 1 t U := ht0.congr htEq
  have hGteq (x : E2) (hx : x ∈ U) : planarGradient t x = planarGradient t0 x := by
    have he : t =ᶠ[𝓝 x] t0 := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact htEq hy
    unfold planarGradient
    rw [he.fderiv_eq]
  have hFeq (x : E2) (hx : x ∈ U) :
      linearizedFlux (nativeClosedDifferentiatedLinearCoefficients K C v) t (planarGradient t) x =
        fderiv ℝ F x (coordinateVector 2 1) := by
    have had := (ha.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
    have hgd := (hG.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
    have hdd := (hd.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
    have hgWithin : planarGradientWithin v K x = planarGradient v x := by
      unfold planarGradientWithin planarGradient
      rw [fderivWithin_of_mem_nhds (hUK x hx)]
    simp only [linearizedFlux, nativeClosedDifferentiatedLinearCoefficients, Pi.zero_apply,
      smul_zero, add_zero, fderivWithin_of_mem_nhds (hUK x hx), hgWithin, hGteq x hx]
    change C.a x (planarGradient t0 x) +
      ((fderiv ℝ C.a x (coordinateVector 2 1)) (planarGradient v x) +
        fderiv ℝ C.d x (coordinateVector 2 1)) = fderiv ℝ F x (coordinateVector 2 1)
    dsimp only [F]
    rw [fderiv_fun_add (had.clm_apply hgd) hdd, add_apply,
      fderiv_clm_apply had hgd, add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, native_gradient_derivative_tangent_commutes U hU v hv x hx]
    abel
  have hdiv : ∀ φ : E2 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ x in U, inner ℝ (F x) (planarGradient φ x)) = 0 := by
    intro φ hs hcompact ht
    have hh := (hw φ hs hcompact ht).2.2
    simpa only [linearizedFlux, linearizedSource, hc, hb, hq, hf, Pi.zero_apply,
      ContinuousLinearMap.zero_apply, smul_zero, add_zero, zero_mul, sub_zero, F] using hh
  refine ⟨htc, ?_⟩
  intro φ hs hcompact ht
  obtain ⟨hi, hz⟩ := native_tangential_derivative_divergence_zero U hU F hFc hdiv φ hs hcompact ht
  have hEq : (fun x => inner ℝ
      (linearizedFlux (nativeClosedDifferentiatedLinearCoefficients K C v) t (planarGradient t) x)
      (planarGradient φ x)) =ᵐ[volume.restrict U]
      (fun x => inner ℝ (fderiv ℝ F x (coordinateVector 2 1)) (planarGradient φ x)) := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    rw [hFeq x hx]
  have hsource (x : E2) :
      linearizedSource (nativeClosedDifferentiatedLinearCoefficients K C v) t (planarGradient t) x = 0 := by
    simp [linearizedSource, nativeClosedDifferentiatedLinearCoefficients]
  refine ⟨hi.congr hEq.symm, ?_, ?_⟩
  · simp only [linearizedSource, nativeClosedDifferentiatedLinearCoefficients,
      zero_apply, Pi.zero_apply, zero_mul, zero_add]
    exact integrable_zero _ _ _
  · simpa only [linearizedSource, nativeClosedDifferentiatedLinearCoefficients,
      zero_apply, Pi.zero_apply, zero_mul, zero_add, sub_zero] using
      (integral_congr_ae hEq).trans hz

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
