import B1InteriorNormalizedClassical_v475
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem native_local_smooth_weak_gradient_v475 (U : Set E2) (hU : IsOpen U) (u : E2 → ℝ)
    (hu : ∀ x ∈ U, ContDiffAt ℝ ∞ u x) : WeakGradientOn U u (planarGradient u) := by
  have huc : ContinuousOn u U := fun x hx => (hu x hx).continuousAt.continuousWithinAt
  have hdu : ContinuousOn (fderiv ℝ u) U :=
    fun x hx => ((hu x hx).fderiv_right (m := 0) (by simp)).continuousAt.continuousWithinAt
  have hgrad : ContinuousOn (planarGradient u) U := by
    unfold planarGradient
    apply continuousOn_finset_sum
    intro i hi
    exact (hdu.clm_apply continuousOn_const).smul continuousOn_const
  refine ⟨huc.locallyIntegrableOn hU.measurableSet, hgrad.locallyIntegrableOn hU.measurableSet, ?_⟩
  intro φ hφ hc hs i
  have integral_product (F ψ : E2 → ℝ) (hF : ContinuousOn F U)
      (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ U) :
      Integrable (fun x => F x * ψ x) := by
    apply (integrableOn_iff_integrable_of_support_subset ?_).mp
      (((hF.mono hψs).mul hψ.continuousOn).integrableOn_compact hψc)
    intro x hx
    exact subset_tsupport ψ ((mul_ne_zero_iff.mp hx).2)
  have hi1 : Integrable (fun x => fderiv ℝ u x (coordinateVector 2 i) * φ x) :=
    integral_product _ _ (hdu.clm_apply continuousOn_const) hφ.continuous hc hs
  have hi2 : Integrable (fun x => u x * fderiv ℝ φ x (coordinateVector 2 i)) :=
    integral_product _ _ huc ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hc.fderiv_apply ℝ _) ((tsupport_fderiv_apply_subset ℝ _).trans hs)
  have hi3 : Integrable (fun x => u x * φ x) :=
    integral_product _ _ huc hφ.continuous hc hs
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hi1 hi2 hi3
    (fun x hx => (hu x (hs hx)).differentiableAt (by simp))
    (fun x _ => hφ.differentiable (by simp) x)
  have hgcoord : ∀ x, planarGradient u x i = fderiv ℝ u x (coordinateVector 2 i) := by
    intro x
    fin_cases i <;> simp [planarGradient, coordinateVector, Fin.sum_univ_two]
  simp_rw [hgcoord]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero,
    setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact hibp
  · intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), mul_zero]
  · intro x hx
    rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (hs h))]
    simp

/-- A literal smooth classical equation supplies its actual native weak form
on any open planar domain, with compact supported tests. -/
theorem native_local_classical_linear_weak_v475
    (O : Set E2) (hO : IsOpen O)
    (a : E2 → Mat2) (b : E2 → E2) (c u : E2 → ℝ)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) O)
    (hb : ContDiffOn ℝ ∞ b O) (hc : ContDiffOn ℝ ∞ c O)
    (hu : ContDiffOn ℝ ∞ u O)
    (heq : ∀ x ∈ O, classicalL a b c u x = 0) :
    WeakLinearEquationOn O a b c u (planarGradient u) := by
  have hgrad : ContDiffOn ℝ ∞ (planarGradient u) O := by
    unfold planarGradient
    apply ContDiffOn.sum
    intro i hi
    exact ((hu.fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const).smul_const _
  have hP (i : Fin 2) : ContDiffOn ℝ 1
      (fun x => matrixAction (a x) (planarGradient u x) i) O := by
    change ContDiffOn ℝ 1 (fun x => ∑ j : Fin 2, a x i j * planarGradient u x j) O
    apply ContDiffOn.sum
    intro j hj
    exact ((ha i j).of_le (by simp)).mul
      ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp_contDiffOn (hgrad.of_le (by simp)))
  have hQ : ContinuousOn (fun x => inner ℝ (b x) (planarGradient u x)+c x*u x) O :=
    (hb.continuousOn.inner hgrad.continuousOn).add (hc.continuousOn.mul hu.continuousOn)
  refine ⟨native_local_smooth_weak_gradient_v475 O hO u
    (fun x hx => (hu x hx).contDiffAt (hO.mem_nhds hx)),?_⟩
  intro φ hφ hφc ht
  obtain ⟨hint,-,hid⟩ := native_local_flux_form_identity_v475 O hO
    (fun x => matrixAction (a x) (planarGradient u x))
    (fun x => inner ℝ (b x) (planarGradient u x)+c x*u x) hP hQ φ hφ hφc ht
  refine ⟨hint,?_⟩
  rw [hid]
  have hz : (∫ x in O, ((∑ i : Fin 2,
      fderiv ℝ (fun y => matrixAction (a y) (planarGradient u y) i) x
        (coordinateVector 2 i))+ (inner ℝ (b x) (planarGradient u x)+c x*u x))*φ x) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
    have hh := heq x hx
    unfold classicalL at hh
    rw [← add_assoc,hh,zero_mul]
    rfl
  rw [hz,neg_zero]

#print axioms native_local_classical_linear_weak_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
