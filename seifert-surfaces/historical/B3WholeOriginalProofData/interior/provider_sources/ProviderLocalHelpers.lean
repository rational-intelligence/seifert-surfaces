import LocalizationBasic
import DifferentialGeometry.External.DeGiorgi.SobolevSpace.Witnesses

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology BigOperators ContDiff
namespace SeifertSurfaces.QuasilinearProviderBridge.Helpers
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.QuasilinearLocalization.Helpers

lemma C1_hasWeakGrad (Ω : Set E2) (hΩ : IsOpen Ω) (u : E2 → ℝ)
    (hu : ContDiffOn ℝ 1 u Ω) : DeGiorgi.HasWeakGrad (planarGradient u) u Ω := by
  intro i φ hφ hsupp hsub
  let v := coordinateVector 2 i
  have hu' : ContinuousOn (fun x => fderiv ℝ u x v) Ω :=
    (hu.continuousOn_fderiv_of_isOpen hΩ le_rfl).clm_apply continuousOn_const
  have hφ' : Continuous (fun x => fderiv ℝ φ x v) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφsupp : support (fun x => fderiv ℝ φ x v) ⊆ tsupport φ :=
    (subset_tsupport _).trans (tsupport_fderiv_apply_subset ℝ v)
  have hint1 : Integrable (fun x => fderiv ℝ u x v * φ x) :=
    continuousOn_supported_integrable Ω (tsupport φ) _ hsupp hsub
      (hu'.mul hφ.continuous.continuousOn) (mul_test_support_subset _ _)
  have hint2 : Integrable (fun x => u x * fderiv ℝ φ x v) :=
    continuousOn_supported_integrable Ω (tsupport φ) _ hsupp hsub
      (hu.continuousOn.mul hφ'.continuousOn) (by
        intro x hx
        apply hφsupp
        exact (mul_ne_zero_iff.mp hx).2)
  have hint3 : Integrable (fun x => u x * φ x) :=
    continuousOn_supported_integrable Ω (tsupport φ) _ hsupp hsub
      (hu.continuousOn.mul hφ.continuous.continuousOn) (mul_test_support_subset _ _)
  simp_rw [gradient_apply]
  change (∫ x in Ω, u x * fderiv ℝ φ x v) = -(∫ x in Ω, fderiv ℝ u x v * φ x)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero,
    setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hint1 hint2 hint3
      (fun x hx => (hu.contDiffAt (hΩ.mem_nhds (hsub hx))).differentiableAt one_ne_zero)
      (fun x hx => hφ.differentiable (by simp) x)
  · intro x hx
    simp [image_eq_zero_of_notMem_tsupport (fun h => hx (hsub h))]
  · intro x hx
    have hder : fderiv ℝ φ x = 0 := fderiv_of_notMem_tsupport ℝ (fun h => hx (hsub h))
    simp [hder]

lemma continuousOn_closedBall_memLp (u : E2 → ℝ) (x₀ : E2) (r : ℝ)
    (hu : ContinuousOn u (Metric.closedBall x₀ r)) :
    MemLp u 2 (volume.restrict (Metric.ball x₀ r)) := by
  have hK : IsCompact (Metric.closedBall x₀ r) := isCompact_closedBall x₀ r
  haveI : IsFiniteMeasure (volume.restrict (Metric.ball x₀ r)) :=
    isFiniteMeasure_restrict.mpr (ne_of_lt (lt_of_le_of_lt
      (measure_mono Metric.ball_subset_closedBall) hK.measure_lt_top))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hu
  apply MemLp.of_bound
    (hu.aestronglyMeasurable_of_subset_isCompact hK Metric.isOpen_ball.measurableSet
      Metric.ball_subset_closedBall) C
  filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
  exact hC x (Metric.ball_subset_closedBall hx)

end SeifertSurfaces.QuasilinearProviderBridge.Helpers
