import NativeTangentialQuotients

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization

theorem native_translated_weak_global_on
    (Ω B : Set E2) (J : Set Jet) (Q : SmoothQuasilinearOperator J)
    (u : E2 → ℝ) (hweak : IsWeakDivergenceSolutionOn Ω Q.flux Q.lowerOrder u)
    (hBΩ : B ⊆ Ω) (k : Fin 2) (h : ℝ) (hshiftΩ : MapsTo (shift k h) B Ω)
    (φ : E2 → ℝ) (hφ : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ)
    (hsub : tsupport φ ⊆ B) :
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
    have heq : shift k h (y + -v) = y := by simp [shift, v]
    exact heq ▸ hshiftΩ hyB
  have hw := QuotientHelpers.weak_global Ω J Q u hweak ψ hψ hψsupp hψsub
  have heq := (@integral_add_right_eq_self E2 ℝ _ _ _ volume _ _)
    (fun y => inner ℝ (Q.flux (firstJet u y)) (planarGradient ψ y) -
      Q.lowerOrder (firstJet u y) * ψ y) v
  rw [← heq] at hw
  simpa [ψ, shift, v, QuotientHelpers.gradient_translate φ hφ] using hw

theorem native_quotient_test_fields_integrable_on
    (Ω B : Set E2) (hΩ : IsOpen Ω) (J : Set Jet) (Q : SmoothQuasilinearOperator J)
    (u : E2 → ℝ) (hC1 : ContDiffOn ℝ 1 u Ω)
    (hjets : ∀ x ∈ Ω, firstJet u x ∈ J)
    (hBΩ : B ⊆ Ω) (k : Fin 2) (h : ℝ) (hshiftΩ : MapsTo (shift k h) B Ω)
    (φ : E2 → ℝ) (hφ : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ)
    (hsub : tsupport φ ⊆ B) :
    Integrable (fun x => inner ℝ (Q.flux (firstJet u (shift k h x))) (planarGradient φ x)) ∧
    Integrable (fun x => Q.lowerOrder (firstJet u (shift k h x)) * φ x) ∧
    Integrable (fun x => inner ℝ (Q.flux (firstJet u x)) (planarGradient φ x)) ∧
    Integrable (fun x => Q.lowerOrder (firstJet u x) * φ x) := by
  have hj : ContinuousOn (firstJet u) Ω :=
    continuousOn_id.prodMk
      (hC1.continuousOn.prodMk (Helpers.gradient_continuousOn Ω hΩ u hC1))
  have hs : Continuous (shift k h) := by unfold shift; fun_prop
  have hjs := hj.comp hs.continuousOn hshiftΩ
  have hAS : ContinuousOn (fun x => Q.flux (firstJet u (shift k h x))) B :=
    Q.flux_smooth.continuousOn.comp hjs (fun x hx => hjets _ (hshiftΩ hx))
  have hBS : ContinuousOn (fun x => Q.lowerOrder (firstJet u (shift k h x))) B :=
    Q.lowerOrder_smooth.continuousOn.comp hjs (fun x hx => hjets _ (hshiftΩ hx))
  have hA : ContinuousOn (fun x => Q.flux (firstJet u x)) B :=
    (Q.flux_smooth.continuousOn.comp hj hjets).mono hBΩ
  have hB : ContinuousOn (fun x => Q.lowerOrder (firstJet u x)) B :=
    (Q.lowerOrder_smooth.continuousOn.comp hj hjets).mono hBΩ
  have hg : ContinuousOn (planarGradient φ) B := (Helpers.gradient_continuous φ hφ).continuousOn
  refine ⟨Helpers.continuousOn_supported_integrable B (tsupport φ) _ hsupp hsub
      (hAS.inner hg) (Helpers.inner_gradient_support_subset _ φ),
    Helpers.continuousOn_supported_integrable B (tsupport φ) _ hsupp hsub
      (hBS.mul hφ.continuous.continuousOn) (Helpers.mul_test_support_subset _ φ),
    Helpers.continuousOn_supported_integrable B (tsupport φ) _ hsupp hsub
      (hA.inner hg) (Helpers.inner_gradient_support_subset _ φ),
    Helpers.continuousOn_supported_integrable B (tsupport φ) _ hsupp hsub
      (hB.mul hφ.continuous.continuousOn) (Helpers.mul_test_support_subset _ φ)⟩

/-- Subtracting the translated and original native weak identities gives the
actual flux/source difference identity. The domain need not contain a full
ball across its flat edge; only the true tangential shift must stay in Ω. -/
theorem native_difference_weak_identity_on
    (Ω B : Set E2) (hΩ : IsOpen Ω) (J : Set Jet) (Q : SmoothQuasilinearOperator J)
    (u : E2 → ℝ) (hC1 : ContDiffOn ℝ 1 u Ω)
    (hjets : ∀ x ∈ Ω, firstJet u x ∈ J)
    (hweak : IsWeakDivergenceSolutionOn Ω Q.flux Q.lowerOrder u)
    (hBΩ : B ⊆ Ω) (k : Fin 2) (h : ℝ) (hshiftΩ : MapsTo (shift k h) B Ω)
    (φ : E2 → ℝ) (hφ : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ)
    (hsub : tsupport φ ⊆ B) :
    IntegrableOn (fun x => inner ℝ
      (h⁻¹ • (Q.flux (firstJet u (shift k h x)) - Q.flux (firstJet u x)))
      (planarGradient φ x)) B ∧
    IntegrableOn (fun x => ((Q.lowerOrder (firstJet u (shift k h x)) -
      Q.lowerOrder (firstJet u x)) / h) * φ x) B ∧
    (∫ x in B, inner ℝ
      (h⁻¹ • (Q.flux (firstJet u (shift k h x)) - Q.flux (firstJet u x)))
      (planarGradient φ x) -
      ((Q.lowerOrder (firstJet u (shift k h x)) - Q.lowerOrder (firstJet u x)) / h) * φ x) = 0 := by
  obtain ⟨hiAS, hiBS, hiA, hiB⟩ := native_quotient_test_fields_integrable_on
    Ω B hΩ J Q u hC1 hjets hBΩ k h hshiftΩ φ hφ hsupp hsub
  let AS := fun x => inner ℝ (Q.flux (firstJet u (shift k h x))) (planarGradient φ x)
  let BS := fun x => Q.lowerOrder (firstJet u (shift k h x)) * φ x
  let A := fun x => inner ℝ (Q.flux (firstJet u x)) (planarGradient φ x)
  let B₀ := fun x => Q.lowerOrder (firstJet u x) * φ x
  have heA : (fun x => inner ℝ
      (h⁻¹ • (Q.flux (firstJet u (shift k h x)) - Q.flux (firstJet u x)))
      (planarGradient φ x)) = (fun x => h⁻¹ * (AS x - A x)) := by
    funext x
    simp only [real_inner_smul_left, inner_sub_left, AS, A]
  have heB : (fun x => ((Q.lowerOrder (firstJet u (shift k h x)) -
      Q.lowerOrder (firstJet u x)) / h) * φ x) = (fun x => h⁻¹ * (BS x - B₀ x)) := by
    funext x
    dsimp only [BS, B₀]
    rw [div_eq_mul_inv]
    ring
  refine ⟨by rw [heA]; exact ((hiAS.sub hiA).const_mul h⁻¹).integrableOn,
    by rw [heB]; exact ((hiBS.sub hiB).const_mul h⁻¹).integrableOn, ?_⟩
  have heq : (fun x => inner ℝ
      (h⁻¹ • (Q.flux (firstJet u (shift k h x)) - Q.flux (firstJet u x)))
      (planarGradient φ x) -
      ((Q.lowerOrder (firstJet u (shift k h x)) - Q.lowerOrder (firstJet u x)) / h) * φ x) =
      (fun x => h⁻¹ * ((AS x - BS x) - (A x - B₀ x))) := by
    rw [show (fun x => inner ℝ
      (h⁻¹ • (Q.flux (firstJet u (shift k h x)) - Q.flux (firstJet u x)))
      (planarGradient φ x) -
      ((Q.lowerOrder (firstJet u (shift k h x)) - Q.lowerOrder (firstJet u x)) / h) * φ x) =
      (fun x => (fun y => inner ℝ
        (h⁻¹ • (Q.flux (firstJet u (shift k h y)) - Q.flux (firstJet u y)))
        (planarGradient φ y)) x - (fun y => ((Q.lowerOrder (firstJet u (shift k h y)) -
          Q.lowerOrder (firstJet u y)) / h) * φ y) x) from rfl]
    rw [heA, heB]
    funext x
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
  have hws := native_translated_weak_global_on Ω B J Q u hweak hBΩ k h hshiftΩ
    φ hφ hsupp hsub
  change h⁻¹ * ((∫ x, AS x - BS x) - ∫ x, A x - B₀ x) = 0
  rw [hws, hw]
  simp

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
