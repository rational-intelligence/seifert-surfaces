import B1HalfDiscNativeSmoothInterior_v468
noncomputable section
open Set Topology Function MeasureTheory
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1GraphCoefficients
open ChartMetricProvider.Variational.IsothermalPDELower.NativeDirichlet
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem compact_weight_integrable_v468 (U : Set E2) (F ψ : E2 → ℝ)
    (hF : ContinuousOn F U) (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (ht : tsupport ψ ⊆ U) : Integrable (fun x => F x * ψ x) := by
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp
    (((hF.mono ht).mul hψ.continuousOn).integrableOn_compact hc)
  intro x hx
  exact subset_tsupport ψ ((mul_ne_zero_iff.mp hx).2)

/-- Integration by parts for a representative smooth only on the original open domain. -/
theorem halfdisc_local_classical_form_identity_v468
    (R : ℝ) (O : Set E2) (hO : IsOpen O) (hUO : halfDisc R ⊆ O)
    (a : E2 → Mat2) (b : E2 → E2) (c v : E2 → ℝ)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) O)
    (hb : ContDiffOn ℝ ∞ b O) (hc : ContDiffOn ℝ ∞ c O)
    (hv : ContDiffOn ℝ ∞ v O)
    (φ : E2 → ℝ) (hs : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (ht : tsupport φ ⊆ halfDisc R) :
    IntegrableOn (fun x => inner ℝ (matrixAction (a x) (planarGradient v x))
      (planarGradient φ x) -
      (inner ℝ (b x) (planarGradient v x) + c x * v x) * φ x) (halfDisc R) ∧
    IntegrableOn (fun x => classicalL a b c v x * φ x) (halfDisc R) ∧
    (∫ x in halfDisc R, inner ℝ (matrixAction (a x) (planarGradient v x))
      (planarGradient φ x) -
      (inner ℝ (b x) (planarGradient v x) + c x * v x) * φ x) =
      -(∫ x in halfDisc R, classicalL a b c v x * φ x) := by
  let U := halfDisc R
  let flux := fun x => matrixAction (a x) (planarGradient v x)
  have hgrad : ContDiffOn ℝ 1 (planarGradient v) O := by
    unfold planarGradient
    apply ContDiffOn.sum
    intro i hi
    exact (hv.fderiv_of_isOpen hO (m := 1) (by simp)).clm_apply contDiffOn_const |>.smul contDiffOn_const
  have hf (i : Fin 2) : ContDiffOn ℝ 1 (fun x => flux x i) O := by
    change ContDiffOn ℝ 1 (fun x => ∑ j : Fin 2, a x i j * planarGradient v x j) O
    apply ContDiffOn.sum
    intro j hj
    exact ((ha i j).of_le (by simp)).mul
      ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp_contDiffOn hgrad)
  have hdf (i : Fin 2) : ContinuousOn
      (fun x => fderiv ℝ (fun y => flux y i) x (coordinateVector 2 i)) O :=
    ((hf i).continuousOn_fderiv_of_isOpen hO (by simp)).clm_apply continuousOn_const
  have hcoord (x : E2) (i : Fin 2) :
      planarGradient φ x i = fderiv ℝ φ x (coordinateVector 2 i) := by
    fin_cases i <;> simp [planarGradient,Fin.sum_univ_two,coordinateVector]
  have hpartial (i : Fin 2) :
      (∫ x in U, flux x i * planarGradient φ x i) =
        -(∫ x in U, fderiv ℝ (fun y => flux y i) x (coordinateVector 2 i) * φ x) := by
    let dφ := fun x => fderiv ℝ φ x (coordinateVector 2 i)
    have hdc : HasCompactSupport dφ := hφc.fderiv_apply ℝ (coordinateVector 2 i)
    have hdt : tsupport dφ ⊆ U := (tsupport_fderiv_apply_subset ℝ (coordinateVector 2 i)).trans ht
    have hi1 := compact_weight_integrable_v468 O _ φ (hdf i) hs.continuous hφc (ht.trans hUO)
    have hi2 := compact_weight_integrable_v468 O _ dφ (hf i).continuousOn
      ((hs.continuous_fderiv (by simp)).clm_apply continuous_const) hdc (hdt.trans hUO)
    have hi3 := compact_weight_integrable_v468 O _ φ (hf i).continuousOn hs.continuous hφc (ht.trans hUO)
    have he := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
      hi1 hi2 hi3
      (fun x hx => ((hf i x (hUO (ht hx))).contDiffAt (hO.mem_nhds (hUO (ht hx)))).differentiableAt (by simp))
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
  have hiP (i : Fin 2) : IntegrableOn (fun x => flux x i * planarGradient φ x i) U := by
    simp_rw [hcoord]
    exact (compact_weight_integrable_v468 O _ _ (hf i).continuousOn
      ((hs.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hφc.fderiv_apply ℝ (coordinateVector 2 i))
      (((tsupport_fderiv_apply_subset ℝ (coordinateVector 2 i)).trans ht).trans hUO)).restrict
  have hiD (i : Fin 2) : IntegrableOn
      (fun x => fderiv ℝ (fun y => flux y i) x (coordinateVector 2 i) * φ x) U :=
    (compact_weight_integrable_v468 O _ φ (hdf i) hs.continuous hφc (ht.trans hUO)).restrict
  let lower := fun x => inner ℝ (b x) (planarGradient v x) + c x * v x
  have hlower : ContinuousOn lower O :=
    (hb.continuousOn.inner hgrad.continuousOn).add
      (hc.continuousOn.mul hv.continuousOn)
  have hiL : IntegrableOn (fun x => lower x * φ x) U :=
    (compact_weight_integrable_v468 O _ φ hlower hs.continuous hφc (ht.trans hUO)).restrict
  have hinner (x : E2) : inner ℝ (flux x) (planarGradient φ x) =
      flux x 0 * planarGradient φ x 0 + flux x 1 * planarGradient φ x 1 := by
    simp [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_two]
    ring
  have hfun : (fun x => classicalL a b c v x * φ x) =
      (fun x => fderiv ℝ (fun y => flux y 0) x (coordinateVector 2 0) * φ x) +
      (fun x => fderiv ℝ (fun y => flux y 1) x (coordinateVector 2 1) * φ x) +
      (fun x => lower x * φ x) := by
    funext x
    simp [classicalL,flux,lower,Fin.sum_univ_two]
    ring
  refine ⟨?_,?_,?_⟩
  · simp_rw [show ∀x, matrixAction (a x) (planarGradient v x) = flux x from fun _ => rfl,hinner]
    exact ((hiP 0).add (hiP 1)).sub hiL
  · rw [hfun]
    exact ((hiD 0).add (hiD 1)).add hiL
  · have hleft : (∫ x in U, inner ℝ (flux x) (planarGradient φ x) -
        lower x * φ x) =
      ∫ x in U, flux x 0 * planarGradient φ x 0 +
        flux x 1 * planarGradient φ x 1 - lower x * φ x := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [hinner]
    change (∫ x in U, inner ℝ (flux x) (planarGradient φ x) - lower x * φ x) = _
    rw [hleft]
    have hsplit := integral_sub ((hiP 0).add (hiP 1)) hiL
    simp only [Pi.add_apply] at hsplit
    rw [hsplit]
    have hsplitP := integral_add (hiP 0) (hiP 1)
    simp only [Pi.add_apply] at hsplitP
    rw [hsplitP,hpartial 0,hpartial 1]
    have hsplitD := integral_add (hiD 0) (hiD 1)
    have hsplitL := integral_add ((hiD 0).add (hiD 1)) hiL
    simp only [Pi.add_apply] at hsplitD hsplitL
    have hright : (∫ x in U, classicalL a b c v x * φ x) =
        (∫ x in U, fderiv ℝ (fun y => flux y 0) x (coordinateVector 2 0) * φ x) +
        (∫ x in U, fderiv ℝ (fun y => flux y 1) x (coordinateVector 2 1) * φ x) +
        (∫ x in U, lower x * φ x) := by
      simp_rw [congrFun hfun,Pi.add_apply]
      rw [hsplitL,hsplitD]
    rw [hright]
    ring


end SeifertSurfaces.OriginalEndpoints.B1Tangency
