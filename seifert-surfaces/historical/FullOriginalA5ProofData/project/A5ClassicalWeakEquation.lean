import A5NativeMetricGraphRegularity
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

set_option autoImplicit false
open scoped ContDiff BigOperators
open Set Topology Filter MeasureTheory
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.AppendixACoordinates CurvedDivergence

private theorem integrable_mul_local_test
    {U : Set E2} (hU : IsOpen U) {f φ : E2 → ℝ}
    (hf : ContinuousOn f U) (hφ : Continuous φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U) :
    Integrable (fun x => f x * φ x) := by
  exact ((hf.mul hφ.continuousOn).continuous_of_tsupport_subset hU
    (tsupport_mul_subset_right.trans hs)).integrable_of_hasCompactSupport hc.mul_left

/-- A classical divergence equation on an arbitrary open set gives the
full compact-test weak identity. No global extension of the flux is used. -/
theorem weak_flux_identity_of_classical_equation
    (U : Set E2) (hU : IsOpen U) (A : E2 → E2) (B : E2 → ℝ)
    (hA : ContDiffOn ℝ 1 A U) (hB : ContinuousOn B U)
    (heq : ∀ x ∈ U, planarDivergence A x + B x = 0)
    (φ : E2 → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U) :
    weakFluxIdentity U A B φ := by
  have hAc (i : Fin 2) : ContDiffOn ℝ 1 (fun x => A x i) U :=
    (EuclideanSpace.proj i : E2 →L[ℝ] ℝ).contDiff.comp_contDiffOn hA
  have hAdc (i : Fin 2) : ContinuousOn
      (fun x => fderiv ℝ (fun y => A y i) x (coordinateVector 2 i)) U :=
    ((hAc i).continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  have hpd (i : Fin 2) : Continuous
      (fun x => fderiv ℝ φ x (coordinateVector 2 i)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hiA (i : Fin 2) : Integrable
      (fun x => A x i * fderiv ℝ φ x (coordinateVector 2 i)) :=
    integrable_mul_local_test hU (hAc i).continuousOn (hpd i)
      (hc.fderiv_apply (𝕜 := ℝ) (coordinateVector 2 i))
      ((tsupport_fderiv_apply_subset ℝ _).trans hs)
  have hiD (i : Fin 2) : Integrable
      (fun x => fderiv ℝ (fun y => A y i) x (coordinateVector 2 i) * φ x) :=
    integrable_mul_local_test hU (hAdc i) hφ.continuous hc hs
  have hiB : Integrable (fun x => B x * φ x) :=
    integrable_mul_local_test hU hB hφ.continuous hc hs
  have hibp (i : Fin 2) :
      (∫ x, A x i * fderiv ℝ φ x (coordinateVector 2 i)) =
        -(∫ x, fderiv ℝ (fun y => A y i) x (coordinateVector 2 i) * φ x) := by
    apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (hiD i) (hiA i)
      (integrable_mul_local_test hU (hAc i).continuousOn hφ.continuous hc hs)
    · intro x hx
      exact ((hAc i).contDiffAt (hU.mem_nhds (hs hx))).differentiableAt one_ne_zero
    · intro x hx
      exact hφ.differentiable (by simp) x
  have hinner (x : E2) : inner ℝ (A x) (planarGradient φ x) =
      ∑ i : Fin 2, A x i * fderiv ℝ φ x (coordinateVector 2 i) := by
    simp [planarGradient, PiLp.inner_apply, Fin.sum_univ_succ, coordinateVector,
      EuclideanSpace.single]
    ; ring
  unfold weakFluxIdentity
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · simp_rw [hinner]
    rw [integral_sub (integrable_finsetSum _ (fun i _ => hiA i)) hiB,
      integral_finsetSum _ (fun i _ => hiA i)]
    simp_rw [hibp]
    rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ => hiD i),
      sub_eq_add_neg, ← neg_add, ← integral_add (integrable_finsetSum _ (fun i _ => hiD i)) hiB]
    have hz : (fun x => (∑ i : Fin 2,
        fderiv ℝ (fun y => A y i) x (coordinateVector 2 i) * φ x) + B x * φ x) = 0 := by
      funext x
      by_cases hx : x ∈ U
      · rw [← Finset.sum_mul, ← add_mul]
        change (planarDivergence A x + B x) * φ x = 0
        rw [heq x hx, zero_mul]
      · have hzero : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun hm => hx (hs hm))
        simp [hzero]
    rw [hz]
    simp
  · intro x hx
    have hn : x ∉ tsupport φ := fun hm => hx (hs hm)
    have hz := image_eq_zero_of_notMem_tsupport hn
    have hd := fderiv_of_notMem_tsupport ℝ hn
    simp [planarGradient, hd, hz]

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
