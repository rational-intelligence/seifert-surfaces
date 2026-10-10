import CoefficientBounds

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology BigOperators ContDiff
namespace SeifertSurfaces.QuasilinearLocalization
open SeifertSurfaces.AppendixACoordinates

namespace QuotientHelpers

lemma gradient_translate (φ : E2 → ℝ) (hφ : ContDiff ℝ ∞ φ) (v x : E2) :
    planarGradient (fun y => φ (y + v)) x = planarGradient φ (x + v) := by
  apply (InnerProductSpace.toDual ℝ E2).injective
  simp only [Helpers.gradient_dual]
  have hd := (hφ.differentiable (by simp) (x + v)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).add_const v)
  simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id] using hd.fderiv

lemma weak_global (Ω : Set E2) (J : Set Jet) (Q : SmoothQuasilinearOperator J)
    (u : E2 → ℝ) (hweak : IsWeakDivergenceSolutionOn Ω Q.flux Q.lowerOrder u)
    (φ : E2 → ℝ) (hφ : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ)
    (hsub : tsupport φ ⊆ Ω) :
    (∫ x, inner ℝ (Q.flux (firstJet u x)) (planarGradient φ x) -
      Q.lowerOrder (firstJet u x) * φ x) = 0 := by
  have hw := hweak φ hφ hsupp hsub
  unfold weakFluxIdentity at hw
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero] at hw
  · exact hw
  · intro x hx
    have ht : x ∉ tsupport φ := fun hxφ => hx (hsub hxφ)
    simp [Helpers.gradient_zero_off_tsupport φ ht, image_eq_zero_of_notMem_tsupport ht]

lemma translated_weak_global (Ω : Set E2) (J : Set Jet) (Q : SmoothQuasilinearOperator J)
    (u : E2 → ℝ) (hweak : IsWeakDivergenceSolutionOn Ω Q.flux Q.lowerOrder u)
    (x₀ : E2) (r : ℝ) (hr : 0 < r) (hball : Metric.closedBall x₀ (4 * r) ⊆ Ω)
    (k : Fin 2) (h : ℝ) (hhr : |h| < r)
    (φ : E2 → ℝ) (hφ : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ)
    (hsub : tsupport φ ⊆ Metric.ball x₀ (2 * r)) :
    (∫ x, inner ℝ (Q.flux (firstJet u (shift k h x))) (planarGradient φ x) -
      Q.lowerOrder (firstJet u (shift k h x)) * φ x) = 0 := by
  let v := h • coordinateVector 2 k
  let ψ : E2 → ℝ := fun y => φ (y + -v)
  have hψ : ContDiff ℝ ∞ ψ := hφ.comp (contDiff_id.add contDiff_const)
  have hψsupp : HasCompactSupport ψ := hsupp.comp_homeomorph (Homeomorph.addRight (-v))
  have hψsub : tsupport ψ ⊆ Ω := by
    rw [show ψ = φ ∘ Homeomorph.addRight (-v) by rfl, tsupport_comp_eq_preimage]
    intro y hy
    have hyB := hsub hy
    have hy4 := shift_mem_closedBall x₀ (y + -v) r hr
      (ball_two_subset_closed_three x₀ r hr hyB) k h hhr
    have heq : shift k h (y + -v) = y := by simp [shift, v]
    exact hball (heq ▸ hy4)
  have hw := weak_global Ω J Q u hweak ψ hψ hψsupp hψsub
  have heq := (@integral_add_right_eq_self E2 ℝ _ _ _ volume _ _)
    (fun y => inner ℝ (Q.flux (firstJet u y)) (planarGradient ψ y) -
      Q.lowerOrder (firstJet u y) * ψ y) v
  rw [← heq] at hw
  simpa [ψ, shift, v, gradient_translate φ hφ] using hw

lemma quotient_fields_integrable (Ω : Set E2) (hΩ : IsOpen Ω) (J : Set Jet) (hJ : IsOpen J)
    (Q : SmoothQuasilinearOperator J) (u : E2 → ℝ) (hC1 : ContDiffOn ℝ 1 u Ω)
    (hjets : ∀ x ∈ Ω, firstJet u x ∈ J) (x₀ : E2) (r : ℝ) (hr : 0 < r)
    (hball : Metric.closedBall x₀ (4 * r) ⊆ Ω) (k : Fin 2) (h : ℝ) (hhr : |h| < r)
    (φ : E2 → ℝ) (hφ : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ)
    (hsub : tsupport φ ⊆ Metric.ball x₀ (2 * r)) :
    Integrable (fun x => inner ℝ (Q.flux (firstJet u (shift k h x))) (planarGradient φ x)) ∧
    Integrable (fun x => Q.lowerOrder (firstJet u (shift k h x)) * φ x) ∧
    Integrable (fun x => inner ℝ (Q.flux (firstJet u x)) (planarGradient φ x)) ∧
    Integrable (fun x => Q.lowerOrder (firstJet u x) * φ x) := by
  let B := Metric.ball x₀ (2 * r)
  have hBΩ : B ⊆ Ω := (Metric.ball_subset_closedBall.trans
    (Metric.closedBall_subset_closedBall (by linarith))).trans hball
  have hj : ContinuousOn (firstJet u) Ω :=
    continuousOn_id.prodMk (hC1.continuousOn.prodMk (Helpers.gradient_continuousOn Ω hΩ u hC1))
  have hs : Continuous (shift k h) := by unfold shift; fun_prop
  have hshiftΩ : MapsTo (shift k h) B Ω := by
    intro x hx
    exact hball (shift_mem_closedBall x₀ x r hr (ball_two_subset_closed_three x₀ r hr hx) k h hhr)
  have hjs := hj.comp hs.continuousOn hshiftΩ
  have hAS : ContinuousOn (fun x => Q.flux (firstJet u (shift k h x))) B :=
    Q.flux_smooth.continuousOn.comp hjs (fun x hx => hjets _ (hshiftΩ hx))
  have hBS : ContinuousOn (fun x => Q.lowerOrder (firstJet u (shift k h x))) B :=
    Q.lowerOrder_smooth.continuousOn.comp hjs (fun x hx => hjets _ (hshiftΩ hx))
  have hA : ContinuousOn (fun x => Q.flux (firstJet u x)) B :=
    (Q.flux_smooth.continuousOn.comp hj hjets).mono hBΩ
  have hB : ContinuousOn (fun x => Q.lowerOrder (firstJet u x)) B :=
    (Q.lowerOrder_smooth.continuousOn.comp hj hjets).mono hBΩ
  have hgrad := (Helpers.gradient_continuous φ hφ).continuousOn (s := B)
  exact ⟨Helpers.continuousOn_supported_integrable B _ _ hsupp hsub (hAS.inner hgrad)
      (Helpers.inner_gradient_support_subset _ φ),
    Helpers.continuousOn_supported_integrable B _ _ hsupp hsub (hBS.mul hφ.continuous.continuousOn)
      (Helpers.mul_test_support_subset _ φ),
    Helpers.continuousOn_supported_integrable B _ _ hsupp hsub (hA.inner hgrad)
      (Helpers.inner_gradient_support_subset _ φ),
    Helpers.continuousOn_supported_integrable B _ _ hsupp hsub (hB.mul hφ.continuous.continuousOn)
      (Helpers.mul_test_support_subset _ φ)⟩

end QuotientHelpers

theorem R2_differenceQuotient_weak_equation
    (Ω : Set E2) (hΩ : IsOpen Ω) (J : Set Jet) (hJ : IsOpen J)
    (Q : SmoothQuasilinearOperator J) (u : E2 → ℝ) (hC1 : ContDiffOn ℝ 1 u Ω)
    (hjets : ∀ x ∈ Ω, firstJet u x ∈ J)
    (hweak : IsWeakDivergenceSolutionOn Ω Q.flux Q.lowerOrder u)
    (x₀ : E2) (r : ℝ) (hr : 0 < r) (T : Set Jet)
    (hball : Metric.closedBall x₀ (4 * r) ⊆ Ω)
    (hT : Convex ℝ T) (hTJ : T ⊆ J)
    (hjetsT : ∀ x ∈ Metric.closedBall x₀ (4 * r), firstJet u x ∈ T)
    (k : Fin 2) (h : ℝ) (hh : 0 < |h|) (hhr : |h| < r) :
    ContDiffOn ℝ 1 (differenceQuotient u k h) (Metric.ball x₀ (2 * r)) ∧
      LinearWeakEquation (Metric.ball x₀ (2 * r)) (averagedCoefficients Q u k h)
        (differenceQuotient u k h) (planarGradient (differenceQuotient u k h)) := by
  have hne : h ≠ 0 := (abs_pos.mp hh)
  let B := Metric.ball x₀ (2 * r)
  have hBΩ : B ⊆ Ω := (Metric.ball_subset_closedBall.trans
    (Metric.closedBall_subset_closedBall (by linarith))).trans hball
  have hsΩ : ∀ x ∈ B, shift k h x ∈ Ω := by
    intro x hx
    exact hball (QuotientHelpers.shift_mem_closedBall x₀ x r hr
      (QuotientHelpers.ball_two_subset_closed_three x₀ r hr hx) k h hhr)
  have hflux : ∀ x ∈ B,
      linearizedFlux (averagedCoefficients Q u k h) (differenceQuotient u k h)
        (planarGradient (differenceQuotient u k h)) x =
          h⁻¹ • (Q.flux (firstJet u (shift k h x)) - Q.flux (firstJet u x)) := by
    intro x hx
    have hs : ∀ t ∈ Icc (0 : ℝ) 1, jetSegment u k h x t ∈ J :=
      fun t ht => hTJ (QuotientHelpers.jetSegment_mem u x₀ r hr T hT hjetsT k h hhr x
        (QuotientHelpers.ball_two_subset_closed_three x₀ r hr hx) t ht)
    simpa [linearizedFlux, R2_differenceQuotient_gradient Ω hΩ u hC1 k h hne x
      (hBΩ hx) (hsΩ x hx)] using (R2_segment_flux_and_source_identity J hJ Q u k h hne x hs).1.symm
  have hsource : ∀ x ∈ B,
      linearizedSource (averagedCoefficients Q u k h) (differenceQuotient u k h)
        (planarGradient (differenceQuotient u k h)) x =
          (Q.lowerOrder (firstJet u (shift k h x)) - Q.lowerOrder (firstJet u x)) / h := by
    intro x hx
    have hs : ∀ t ∈ Icc (0 : ℝ) 1, jetSegment u k h x t ∈ J :=
      fun t ht => hTJ (QuotientHelpers.jetSegment_mem u x₀ r hr T hT hjetsT k h hhr x
        (QuotientHelpers.ball_two_subset_closed_three x₀ r hr hx) t ht)
    simpa [linearizedSource, R2_differenceQuotient_gradient Ω hΩ u hC1 k h hne x
      (hBΩ hx) (hsΩ x hx)] using (R2_segment_flux_and_source_identity J hJ Q u k h hne x hs).2.symm
  refine ⟨QuotientHelpers.quotient_contDiffOn Ω hΩ u hC1 x₀ r hr hball k h hhr, ?_⟩
  intro φ hφ hsupp hsub
  obtain ⟨hiAS, hiBS, hiA, hiB⟩ := QuotientHelpers.quotient_fields_integrable Ω hΩ J hJ Q u hC1
    hjets x₀ r hr hball k h hhr φ hφ hsupp hsub
  let AS := fun x => inner ℝ (Q.flux (firstJet u (shift k h x))) (planarGradient φ x)
  let BS := fun x => Q.lowerOrder (firstJet u (shift k h x)) * φ x
  let A := fun x => inner ℝ (Q.flux (firstJet u x)) (planarGradient φ x)
  let B₀ := fun x => Q.lowerOrder (firstJet u x) * φ x
  have heA : ∀ x ∈ B, inner ℝ
      (linearizedFlux (averagedCoefficients Q u k h) (differenceQuotient u k h)
        (planarGradient (differenceQuotient u k h)) x) (planarGradient φ x) =
      h⁻¹ * (AS x - A x) := by
    intro x hx
    rw [hflux x hx]
    simp [AS, A, inner_sub_left, real_inner_smul_left]
  have heB : ∀ x ∈ B, linearizedSource (averagedCoefficients Q u k h)
      (differenceQuotient u k h) (planarGradient (differenceQuotient u k h)) x * φ x =
      h⁻¹ * (BS x - B₀ x) := by
    intro x hx
    rw [hsource x hx]
    dsimp [BS, B₀]
    rw [div_eq_mul_inv]
    ring
  have hiFlux : IntegrableOn (fun x => inner ℝ
      (linearizedFlux (averagedCoefficients Q u k h) (differenceQuotient u k h)
        (planarGradient (differenceQuotient u k h)) x) (planarGradient φ x)) B := by
    exact ((hiAS.sub hiA).const_mul h⁻¹).integrableOn.congr_fun
      (fun x hx => (heA x hx).symm) measurableSet_ball
  have hiSource : IntegrableOn (fun x => linearizedSource (averagedCoefficients Q u k h)
      (differenceQuotient u k h) (planarGradient (differenceQuotient u k h)) x * φ x) B := by
    exact ((hiBS.sub hiB).const_mul h⁻¹).integrableOn.congr_fun
      (fun x hx => (heB x hx).symm) measurableSet_ball
  refine ⟨hiFlux, hiSource, ?_⟩
  have heq : (∫ x in B, inner ℝ
      (linearizedFlux (averagedCoefficients Q u k h) (differenceQuotient u k h)
        (planarGradient (differenceQuotient u k h)) x) (planarGradient φ x) -
      linearizedSource (averagedCoefficients Q u k h) (differenceQuotient u k h)
        (planarGradient (differenceQuotient u k h)) x * φ x) =
      ∫ x in B, h⁻¹ * ((AS x - BS x) - (A x - B₀ x)) := by
    apply setIntegral_congr_fun measurableSet_ball
    intro x hx
    dsimp only
    rw [heA x hx, heB x hx]
    ring
  rw [heq]
  have hz : ∀ x, x ∉ B → h⁻¹ * ((AS x - BS x) - (A x - B₀ x)) = 0 := by
    intro x hx
    have ht : x ∉ tsupport φ := fun hxφ => hx (hsub hxφ)
    simp [AS, BS, A, B₀, Helpers.gradient_zero_off_tsupport φ ht,
      image_eq_zero_of_notMem_tsupport ht]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz, integral_const_mul]
  have hiS : Integrable (fun x => AS x - BS x) := hiAS.sub hiBS
  have hiO : Integrable (fun x => A x - B₀ x) := hiA.sub hiB
  rw [integral_sub hiS hiO]
  have hw := QuotientHelpers.weak_global Ω J Q u hweak φ hφ hsupp (hsub.trans hBΩ)
  have hws := QuotientHelpers.translated_weak_global Ω J Q u hweak x₀ r hr hball
    k h hhr φ hφ hsupp hsub
  change h⁻¹ * ((∫ x, AS x - BS x) - ∫ x, A x - B₀ x) = 0
  rw [hws, hw]
  simp

end SeifertSurfaces.QuasilinearLocalization
