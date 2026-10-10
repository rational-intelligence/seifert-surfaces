import B1HalfDiscNativeClassical_v468

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem native_compact_flux_weight_integrable_v475 (U : Set E2) (F ψ : E2 → ℝ)
    (hF : ContinuousOn F U) (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (ht : tsupport ψ ⊆ U) : Integrable (fun x => F x * ψ x) := by
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp
    (((hF.mono ht).mul hψ.continuousOn).integrableOn_compact hc)
  intro x hx
  exact subset_tsupport ψ ((mul_ne_zero_iff.mp hx).2)

/-- Local integration by parts for a nonlinear flux, using its literal
classical divergence.  Smoothness is needed only on the open test domain. -/
theorem native_local_flux_form_identity_v475
    (O : Set E2) (hO : IsOpen O) (P : E2 → E2) (Q : E2 → ℝ)
    (hP : ∀ i : Fin 2, ContDiffOn ℝ 1 (fun x => P x i) O)
    (hQ : ContinuousOn Q O)
    (φ : E2 → ℝ) (hs : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (ht : tsupport φ ⊆ O) :
    IntegrableOn (fun x => inner ℝ (P x) (planarGradient φ x) - Q x * φ x) O ∧
    IntegrableOn (fun x =>
      ((∑ i : Fin 2, fderiv ℝ (fun y => P y i) x (coordinateVector 2 i)) + Q x) * φ x) O ∧
    (∫ x in O, inner ℝ (P x) (planarGradient φ x) - Q x * φ x) =
      -(∫ x in O,
        ((∑ i : Fin 2, fderiv ℝ (fun y => P y i) x (coordinateVector 2 i)) + Q x) * φ x) := by
  have hdf (i : Fin 2) : ContinuousOn
      (fun x => fderiv ℝ (fun y => P y i) x (coordinateVector 2 i)) O :=
    ((hP i).continuousOn_fderiv_of_isOpen hO (by simp)).clm_apply continuousOn_const
  have hcoord (x : E2) (i : Fin 2) :
      planarGradient φ x i = fderiv ℝ φ x (coordinateVector 2 i) := by
    fin_cases i <;> simp [planarGradient,Fin.sum_univ_two,coordinateVector]
  have hpartial (i : Fin 2) :
      (∫ x in O, P x i * planarGradient φ x i) =
        -(∫ x in O, fderiv ℝ (fun y => P y i) x (coordinateVector 2 i) * φ x) := by
    let dφ := fun x => fderiv ℝ φ x (coordinateVector 2 i)
    have hdc : HasCompactSupport dφ := hφc.fderiv_apply ℝ (coordinateVector 2 i)
    have hdt : tsupport dφ ⊆ O := (tsupport_fderiv_apply_subset ℝ (coordinateVector 2 i)).trans ht
    have hi1 := native_compact_flux_weight_integrable_v475 O _ φ (hdf i) hs.continuous hφc ht
    have hi2 := native_compact_flux_weight_integrable_v475 O _ dφ (hP i).continuousOn
      ((hs.continuous_fderiv (by simp)).clm_apply continuous_const) hdc hdt
    have hi3 := native_compact_flux_weight_integrable_v475 O _ φ (hP i).continuousOn hs.continuous hφc ht
    have he := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
      hi1 hi2 hi3
      (fun x hx => ((hP i x (ht hx)).contDiffAt (hO.mem_nhds (ht hx))).differentiableAt (by simp))
      (fun x _ => hs.differentiable (by simp) x)
    simp_rw [hcoord]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero,
      setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact he
    · intro x hx
      rw [show φ x = 0 from image_eq_zero_of_notMem_tsupport (fun h => hx (ht h)),mul_zero]
    · intro x hx
      rw [show fderiv ℝ φ x (coordinateVector 2 i) = 0 from
        image_eq_zero_of_notMem_tsupport (f := dφ) (fun h => hx (hdt h)),mul_zero]
  have hiP (i : Fin 2) : IntegrableOn (fun x => P x i * planarGradient φ x i) O := by
    simp_rw [hcoord]
    exact (native_compact_flux_weight_integrable_v475 O _ _ (hP i).continuousOn
      ((hs.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hφc.fderiv_apply ℝ (coordinateVector 2 i))
      ((tsupport_fderiv_apply_subset ℝ (coordinateVector 2 i)).trans ht)).restrict
  have hiD (i : Fin 2) : IntegrableOn
      (fun x => fderiv ℝ (fun y => P y i) x (coordinateVector 2 i) * φ x) O :=
    (native_compact_flux_weight_integrable_v475 O _ φ (hdf i) hs.continuous hφc ht).restrict
  have hiQ : IntegrableOn (fun x => Q x * φ x) O :=
    (native_compact_flux_weight_integrable_v475 O _ φ hQ hs.continuous hφc ht).restrict
  have hinner (x : E2) : inner ℝ (P x) (planarGradient φ x) =
      P x 0 * planarGradient φ x 0 + P x 1 * planarGradient φ x 1 := by
    simp [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_two]
    ring
  let L := fun x => (∑ i : Fin 2,
    fderiv ℝ (fun y => P y i) x (coordinateVector 2 i)) + Q x
  have hfun : (fun x => L x * φ x) =
      (fun x => fderiv ℝ (fun y => P y 0) x (coordinateVector 2 0) * φ x) +
      (fun x => fderiv ℝ (fun y => P y 1) x (coordinateVector 2 1) * φ x) +
      (fun x => Q x * φ x) := by
    funext x
    simp [L,Fin.sum_univ_two]
    ring
  refine ⟨?_,?_,?_⟩
  · simp_rw [hinner]
    exact ((hiP 0).add (hiP 1)).sub hiQ
  · change IntegrableOn (fun x => L x * φ x) O
    rw [hfun]
    exact ((hiD 0).add (hiD 1)).add hiQ
  · have hleft : (∫ x in O, inner ℝ (P x) (planarGradient φ x) - Q x * φ x) =
      ∫ x in O, P x 0 * planarGradient φ x 0 + P x 1 * planarGradient φ x 1 - Q x * φ x := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [hinner]
    rw [hleft]
    have hsplit := integral_sub ((hiP 0).add (hiP 1)) hiQ
    simp only [Pi.add_apply] at hsplit
    rw [hsplit]
    have hsplitP := integral_add (hiP 0) (hiP 1)
    simp only [Pi.add_apply] at hsplitP
    rw [hsplitP,hpartial 0,hpartial 1]
    have hsplitD := integral_add (hiD 0) (hiD 1)
    have hsplitQ := integral_add ((hiD 0).add (hiD 1)) hiQ
    simp only [Pi.add_apply] at hsplitD hsplitQ
    have hright : (∫ x in O, L x * φ x) =
        (∫ x in O, fderiv ℝ (fun y => P y 0) x (coordinateVector 2 0) * φ x) +
        (∫ x in O, fderiv ℝ (fun y => P y 1) x (coordinateVector 2 1) * φ x) +
        (∫ x in O, Q x * φ x) := by
      simp_rw [congrFun hfun,Pi.add_apply]
      rw [hsplitQ,hsplitD]
    change _ = -(∫ x in O, L x * φ x)
    rw [hright]
    ring

/-- All compactly supported test variations give the exact classical equation,
including the sign of the height derivative in the B1 area residual. -/
theorem native_local_flux_classical_of_tests_v475
    (O : Set E2) (hO : IsOpen O) (P : E2 → E2) (Q : E2 → ℝ)
    (hP : ∀ i : Fin 2, ContDiffOn ℝ 1 (fun x => P x i) O)
    (hQ : ContinuousOn Q O)
    (hweak : ∀ φ : E2 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ O →
      (∫ x in O, inner ℝ (P x) (planarGradient φ x) - Q x * φ x) = 0) :
    ∀ x ∈ O,
      (∑ i : Fin 2, fderiv ℝ (fun y => P y i) x (coordinateVector 2 i)) + Q x = 0 := by
  let L := fun x => (∑ i : Fin 2,
    fderiv ℝ (fun y => P y i) x (coordinateVector 2 i)) + Q x
  have hdf (i : Fin 2) : ContinuousOn
      (fun x => fderiv ℝ (fun y => P y i) x (coordinateVector 2 i)) O :=
    ((hP i).continuousOn_fderiv_of_isOpen hO (by simp)).clm_apply continuousOn_const
  have hL : ContinuousOn L O :=
    (continuousOn_finsetSum Finset.univ (fun i _ => hdf i)).add hQ
  have hae : L =ᵐ[volume.restrict O] 0 := by
    change ∀ᵐ x ∂volume.restrict O, L x = 0
    rw [ae_restrict_iff' hO.measurableSet]
    apply hO.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hL.locallyIntegrableOn hO.measurableSet)
    intro φ hs hφc ht
    have hf := native_local_flux_form_identity_v475 O hO P Q hP hQ φ hs hφc ht
    have hz := hweak φ hs hφc ht
    have hn := hf.2.2
    rw [hz] at hn
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := O)
      (fun x hx => show φ x • L x = 0 by
        rw [image_eq_zero_of_notMem_tsupport (fun hh => hx (ht hh)),zero_smul])]
    simp only [smul_eq_mul]
    simp_rw [mul_comm (φ _)]
    change 0 = -(∫ x in O, L x * φ x) at hn
    linarith
  exact MeasureTheory.Measure.eqOn_open_of_ae_eq hae hO hL continuousOn_const

#print axioms native_local_flux_form_identity_v475
#print axioms native_local_flux_classical_of_tests_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
