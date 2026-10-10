import NativeBoundaryClosedLinearDifference

set_option autoImplicit false
set_option maxHeartbeats 50000
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization
open SeifertSurfaces.QuasilinearProviderBridge

/-- Tangential differentiation preserves the actual smooth-test divergence
identity. This uses integration by parts on the original one-sided open set. -/
theorem native_tangential_derivative_divergence_zero
    (U : Set E2) (hU : IsOpen U) (F : E2 → E2) (hF : ContDiffOn ℝ 1 F U)
    (hweak : ∀ φ : E2 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ x in U, inner ℝ (F x) (planarGradient φ x)) = 0)
    (φ : E2 → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (ht : tsupport φ ⊆ U) :
    IntegrableOn (fun x => inner ℝ (fderiv ℝ F x (coordinateVector 2 1)) (planarGradient φ x)) U ∧
      (∫ x in U, inner ℝ (fderiv ℝ F x (coordinateVector 2 1)) (planarGradient φ x)) = 0 := by
  let d (i : Fin 2) := fun x => fderiv ℝ φ x (coordinateVector 2 i)
  let f (i : Fin 2) := fun x => F x i
  have hd (i : Fin 2) : ContDiff ℝ ∞ (d i) :=
    (hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hdc (i : Fin 2) : HasCompactSupport (d i) := hc.fderiv_apply (𝕜 := ℝ) _
  have hdt (i : Fin 2) : tsupport (d i) ⊆ U := (tsupport_fderiv_apply_subset ℝ _).trans ht
  have hf (i : Fin 2) : ContDiffOn ℝ 1 (f i) U := by
    simpa only [f, Function.comp_def, EuclideanSpace.proj, PiLp.proj_apply] using
      (EuclideanSpace.proj i).contDiff.comp_contDiffOn hF
  have hpartial (i : Fin 2) (x : E2) (hx : x ∈ U) :
      fderiv ℝ (f i) x (coordinateVector 2 1) = (fderiv ℝ F x (coordinateVector 2 1)) i := by
    have hp := (EuclideanSpace.proj i).hasFDerivAt.comp x
      ((hF.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)).hasFDerivAt
    exact congrArg (fun A : E2 →L[ℝ] ℝ => A (coordinateVector 2 1)) hp.fderiv
  have hmixed (i : Fin 2) (x : E2) :
      fderiv ℝ (d i) x (coordinateVector 2 1) = fderiv ℝ (d 1) x (coordinateVector 2 i) := by
    have hdx : DifferentiableAt ℝ (fderiv ℝ φ) x :=
      (hφ.fderiv_right (m := 1) (by simp)).differentiable (by norm_num) x
    simp only [d, fderiv_clm_apply hdx (differentiableAt_const _), fderiv_fun_const]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.zero_apply, Pi.zero_apply, map_zero, zero_add, ContinuousLinearMap.flip_apply]
    exact ((hφ.of_le (by simp : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω))).contDiffAt.isSymmSndFDerivAt
      (by norm_num)).eq _ _
  let A (i : Fin 2) := fun x => fderiv ℝ (f i) x (coordinateVector 2 1) * d i x
  let B (i : Fin 2) := fun x => f i x * fderiv ℝ (d 1) x (coordinateVector 2 i)
  have hAi (i : Fin 2) : IntegrableOn (A i) U := by
    apply (QuasilinearLocalization.Helpers.continuousOn_supported_integrable U (tsupport (d i))
      (A i) (hdc i) (hdt i) ?_ ?_).integrableOn
    · exact (((hf i).continuousOn_fderiv_of_isOpen hU (by norm_num)).clm_apply continuousOn_const).mul
        (hd i).continuous.continuousOn
    · intro x hx
      exact subset_tsupport (d i) ((mul_ne_zero_iff.mp hx).2)
  have hBi (i : Fin 2) : IntegrableOn (B i) U := by
    apply (QuasilinearLocalization.Helpers.continuousOn_supported_integrable U (tsupport (d 1))
      (B i) (hdc 1) (hdt 1) ?_ ?_).integrableOn
    · exact (hf i).continuousOn.mul (((hd 1).continuous_fderiv (by simp)).clm_apply continuous_const).continuousOn
    · intro x hx
      have hh : x ∈ support (fun y => fderiv ℝ (d 1) y (coordinateVector 2 i)) :=
        (mul_ne_zero_iff.mp hx).2
      exact (tsupport_fderiv_apply_subset ℝ (coordinateVector 2 i)) (subset_tsupport _ hh)
  have hIBP (i : Fin 2) : (∫ x in U, B i x) = -(∫ x in U, A i x) := by
    have hh := Helpers.C1_hasWeakGrad U hU (f i) (hf i) 1 (d i) (hd i) (hdc i) (hdt i)
    simp only [QuasilinearLocalization.Helpers.gradient_apply] at hh
    change (∫ x in U, f i x * fderiv ℝ (d i) x (coordinateVector 2 1)) =
      -(∫ x in U, fderiv ℝ (f i) x (coordinateVector 2 1) * d i x) at hh
    simp_rw [hmixed i] at hh
    exact hh
  have hEq : (fun x => inner ℝ (fderiv ℝ F x (coordinateVector 2 1)) (planarGradient φ x))
      =ᵐ[volume.restrict U] (fun x => A 0 x + A 1 x) := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    simp only [PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_two, Helpers.gradient_apply,
      ← hpartial 0 x hx, ← hpartial 1 x hx, A, d]
  have hEqB : (fun x => inner ℝ (F x) (planarGradient (d 1) x)) =
      (fun x => B 0 x + B 1 x) := by
    funext x
    simp only [PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_two, Helpers.gradient_apply, B, f]
  have hz := hweak (d 1) (hd 1) (hdc 1) (hdt 1)
  rw [hEqB, integral_add (hBi 0) (hBi 1), hIBP 0, hIBP 1] at hz
  refine ⟨((hAi 0).add (hAi 1)).congr hEq.symm, ?_⟩
  rw [integral_congr_ae hEq, integral_add (hAi 0) (hAi 1)]
  linarith

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
