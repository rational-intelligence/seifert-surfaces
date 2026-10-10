import NativeBoundaryDifferentiateDivergence

set_option autoImplicit false
set_option maxHeartbeats 100000
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization
open SeifertSurfaces.QuasilinearProviderBridge

/-- A C1 flux with the actual smooth-test divergence identity has zero
classical divergence at every point of the original open region. -/
theorem native_classical_divergence_zero_of_weak
    (U : Set E2) (hU : IsOpen U) (F : E2 → E2) (hF : ContDiffOn ℝ 1 F U)
    (hw : ∀ φ : E2 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ x in U, inner ℝ (F x) (planarGradient φ x)) = 0) :
    ∀ x ∈ U, ∑ i : Fin 2, (fderiv ℝ F x (coordinateVector 2 i)) i = 0 := by
  let fi (i : Fin 2) := fun x => F x i
  let di (i : Fin 2) := fun x => fderiv ℝ (fi i) x (coordinateVector 2 i)
  let div := fun x => ∑ i : Fin 2, di i x
  have hfi (i : Fin 2) : ContDiffOn ℝ 1 (fi i) U := by
    simpa only [fi, Function.comp_def, EuclideanSpace.proj, PiLp.proj_apply] using
      (EuclideanSpace.proj i).contDiff.comp_contDiffOn hF
  have hdi (i : Fin 2) : ContinuousOn (di i) U :=
    ((hfi i).continuousOn_fderiv_of_isOpen hU (by norm_num)).clm_apply continuousOn_const
  have hdiv : ContinuousOn div U := continuousOn_finsetSum _ (fun i _ => hdi i)
  have hz : div =ᵐ[volume.restrict U] 0 := by
    change ∀ᵐ x ∂(volume.restrict U), div x = 0
    rw [ae_restrict_iff' hU.measurableSet]
    apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hdiv.locallyIntegrableOn hU.measurableSet)
    intro φ hs hc ht
    have hdiInt (i : Fin 2) : IntegrableOn (fun x => di i x * φ x) U :=
      (QuasilinearLocalization.Helpers.continuousOn_supported_integrable U (tsupport φ) _ hc ht
        ((hdi i).mul hs.continuous.continuousOn)
        (QuasilinearLocalization.Helpers.mul_test_support_subset _ φ)).integrableOn
    have hFiInt (i : Fin 2) : IntegrableOn (fun x => fi i x * planarGradient φ x i) U := by
      apply Integrable.integrableOn
      apply QuasilinearLocalization.Helpers.continuousOn_supported_integrable U (tsupport φ) _ hc ht
        ((hfi i).continuousOn.mul ?_) ?_
      · simpa only [Function.comp_def, EuclideanSpace.proj, PiLp.proj_apply] using
          (EuclideanSpace.proj i).continuous.comp_continuousOn (continuous_planarGradient hs).continuousOn
      · intro x hx
        apply (tsupport_fderiv_apply_subset ℝ (coordinateVector 2 i))
        apply subset_tsupport
        simpa only [Function.mem_support, QuasilinearLocalization.Helpers.gradient_apply] using
          (mul_ne_zero_iff.mp hx).2
    have hIBP (i : Fin 2) : (∫ x in U, fi i x * planarGradient φ x i) =
        -(∫ x in U, di i x * φ x) := by
      simpa only [QuasilinearLocalization.Helpers.gradient_apply, coordinateVector, di] using
        (Helpers.C1_hasWeakGrad U hU (fi i) (hfi i) i φ hs hc ht)
    have hEq := hw φ hs hc ht
    have hinner : (fun x => inner ℝ (F x) (planarGradient φ x)) =
        (fun x => ∑ i : Fin 2, fi i x * planarGradient φ x i) := by
      funext x
      simp [fi, PiLp.inner_apply, mul_comm]
    rw [hinner, integral_finsetSum _ (fun i _ => hFiInt i)] at hEq
    simp_rw [hIBP] at hEq
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := U) (fun x hx => by
      simp [image_eq_zero_of_notMem_tsupport (fun h => hx (ht h))])]
    simp only [smul_eq_mul]
    have hfun : (fun x => φ x * div x) = (fun x => ∑ i : Fin 2, di i x * φ x) := by
      funext x
      simp only [div, Fin.sum_univ_two]
      ring
    rw [hfun, integral_finsetSum _ (fun i _ => hdiInt i)]
    simp only [Fin.sum_univ_two] at hEq ⊢
    linarith
  have hpoint := Measure.eqOn_open_of_ae_eq hz hU hdiv continuousOn_const
  intro x hx
  have hpartial (i : Fin 2) : di i x = (fderiv ℝ F x (coordinateVector 2 i)) i := by
    have hh := (EuclideanSpace.proj i).hasFDerivAt.comp x
      ((hF.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)).hasFDerivAt
    exact congrArg (fun L : E2 →L[ℝ] ℝ => L (coordinateVector 2 i)) hh.fderiv
  simpa only [div, hpartial, Pi.zero_apply] using hpoint hx

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
