import NativeBoundaryTangentialFlatTesting

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization

theorem native_weak_partial_as_flux_equation
    (U : Set E2) (f G : E2 → ℝ) (i : Fin 2)
    (hf : MemLp f 2 (volume.restrict U)) (hG : MemLp G 2 (volume.restrict U))
    (ψ : E2 → ℝ) (hs : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (he : (∫ x in U, f x * fderiv ℝ ψ x (coordinateVector 2 i)) =
      -(∫ x in U, G x * ψ x)) :
    (∫ x in U, inner ℝ (f x • coordinateVector 2 i) (planarGradient ψ x) - (-G x) * ψ x) = 0 := by
  have hd : Continuous (fun x => fderiv ℝ ψ x (coordinateVector 2 i)) :=
    (hs.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdL : MemLp (fun x => fderiv ℝ ψ x (coordinateVector 2 i)) 2 (volume.restrict U) :=
    (hd.memLp_of_hasCompactSupport (hc.fderiv_apply (𝕜 := ℝ) _)).restrict U
  have hψL : MemLp ψ 2 (volume.restrict U) :=
    (hs.continuous.memLp_of_hasCompactSupport hc).restrict U
  have hiF : Integrable (fun x => f x * fderiv ℝ ψ x (coordinateVector 2 i))
      (volume.restrict U) := hf.integrable_mul hdL
  have hiG : Integrable (fun x => G x * ψ x) (volume.restrict U) := hG.integrable_mul hψL
  have hinner (x : E2) : inner ℝ (f x • coordinateVector 2 i) (planarGradient ψ x) =
      f x * fderiv ℝ ψ x (coordinateVector 2 i) := by
    fin_cases i <;> simp [PiLp.inner_apply, coordinateVector, Fin.sum_univ_two, Helpers.gradient_apply] <;> ring
  simp_rw [hinner, neg_mul, sub_neg_eq_add]
  rw [integral_add hiF hiG]
  rw [he]
  ring

theorem native_even_reflected_scalar_memLp
    (ρ : ℝ) (f : E2 → ℝ) (hf : MemLp f 2 (volume.restrict (openHalfDisc ρ))) :
    MemLp (nativeEvenReflectedSource ρ f) 2 volume := by
  have hm := (openHalfDisc_isOpen ρ).measurableSet
  have hi : MemLp ((openHalfDisc ρ).indicator f) 2 volume :=
    (memLp_indicator_iff_restrict hm.nullMeasurableSet).mpr hf
  exact hi.add (hi.comp_measurePreserving normalReflection.measurePreserving)

/-- Actual even reflection preserves native H1. This first part pays its
normal weak partial using the zero-flat test extension; no classical
derivative of the even extension on the flat edge is assumed. -/
theorem native_even_reflected_normal_weak_partial
    (ρ : ℝ) (f G : E2 → ℝ)
    (hf : MemLp f 2 (volume.restrict (openHalfDisc ρ)))
    (hG : MemLp G 2 (volume.restrict (openHalfDisc ρ)))
    (hw : DeGiorgi.HasWeakPartialDeriv 0 G f (openHalfDisc ρ)) :
    DeGiorgi.HasWeakPartialDeriv 0 (nativeReflectedSource ρ G)
      (nativeEvenReflectedSource ρ f) (Metric.ball 0 ρ) := by
  let F : E2 → E2 := fun x => f x • coordinateVector 2 0
  have hF : MemLp F 2 (volume.restrict (openHalfDisc ρ)) := by
    exact hf.continuousLinearMap_comp ((ContinuousLinearMap.id ℝ ℝ).smulRight (coordinateVector 2 0))
  have hweak : ∀ ψ : E2 → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ openHalfDisc ρ →
        (∫ x in openHalfDisc ρ, inner ℝ (F x) (planarGradient ψ x) - (-G x) * ψ x) = 0 := by
    intro ψ hs hc ht
    exact native_weak_partial_as_flux_equation _ f G 0 hf hG ψ hs hc (hw ψ hs hc ht)
  obtain ⟨hFR, hGR, hR⟩ := native_flux_source_reflected_weak_identity ρ F (fun x => -G x) hF hG.neg hweak
  have hflux (x : E2) : nativeReflectedFlux ρ F x =
      nativeEvenReflectedSource ρ f x • coordinateVector 2 0 := by
    by_cases hx : x ∈ openHalfDisc ρ <;> by_cases hr : normalReflection x ∈ openHalfDisc ρ <;>
      simp [nativeReflectedFlux, nativeEvenReflectedSource, F, hx, hr,
        normalReflection_basis_zero, normalReflection.map_smul, add_smul, sub_eq_add_neg]
  have hsource (x : E2) : nativeReflectedSource ρ (fun x => -G x) x = -nativeReflectedSource ρ G x := by
    by_cases hx : x ∈ openHalfDisc ρ <;> by_cases hr : normalReflection x ∈ openHalfDisc ρ <;>
      simp [nativeReflectedSource, hx, hr] <;> ring
  intro ψ hs hc ht
  obtain ⟨hiF, hiG, he⟩ := hR ψ hs hc ht
  have hinner (x : E2) : inner ℝ (nativeReflectedFlux ρ F x) (planarGradient ψ x) =
      nativeEvenReflectedSource ρ f x * fderiv ℝ ψ x (coordinateVector 2 0) := by
    rw [hflux]
    simp [PiLp.inner_apply, coordinateVector, Fin.sum_univ_two, Helpers.gradient_apply] <;> ring
  simp_rw [hinner] at hiF he
  simp_rw [hsource, neg_mul] at hiG he
  rw [integral_sub hiF hiG, integral_neg] at he
  have hballF : (∫ x in Metric.ball (0 : E2) ρ,
      nativeEvenReflectedSource ρ f x * fderiv ℝ ψ x (coordinateVector 2 0)) =
      ∫ x, nativeEvenReflectedSource ρ f x * fderiv ℝ ψ x (coordinateVector 2 0) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (ht h))]
    simp
  have hballG : (∫ x in Metric.ball (0 : E2) ρ, nativeReflectedSource ρ G x * ψ x) =
      ∫ x, nativeReflectedSource ρ G x * ψ x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (ht h)), mul_zero]
  change (∫ x in Metric.ball (0 : E2) ρ,
    nativeEvenReflectedSource ρ f x * fderiv ℝ ψ x (coordinateVector 2 0)) =
      -(∫ x in Metric.ball (0 : E2) ρ, nativeReflectedSource ρ G x * ψ x)
  rw [hballF, hballG]
  linarith

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
