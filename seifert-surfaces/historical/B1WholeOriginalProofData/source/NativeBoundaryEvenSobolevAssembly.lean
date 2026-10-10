import NativeBoundaryEvenSobolev

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal
namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization

theorem native_even_reflected_tangential_weak_partial
    (ρ : ℝ) (f G : E2 → ℝ)
    (hf : MemLp f 2 (volume.restrict (openHalfDisc ρ)))
    (hG : MemLp G 2 (volume.restrict (openHalfDisc ρ)))
    (hw : DeGiorgi.HasWeakPartialDeriv 1 G f (openHalfDisc ρ)) :
    DeGiorgi.HasWeakPartialDeriv 1 (nativeEvenReflectedSource ρ G)
      (nativeEvenReflectedSource ρ f) (Metric.ball 0 ρ) := by
  let F : E2 → E2 := fun x => f x • coordinateVector 2 1
  have hF : MemLp F 2 (volume.restrict (openHalfDisc ρ)) := by
    exact hf.continuousLinearMap_comp ((ContinuousLinearMap.id ℝ ℝ).smulRight (coordinateVector 2 1))
  have hweak : ∀ ψ : E2 → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Metric.ball 0 ρ →
        (∫ x in openHalfDisc ρ, inner ℝ (F x) (planarGradient ψ x) - (-G x) * ψ x) = 0 := by
    intro ψ hs hc ht
    exact native_weak_partial_as_flux_equation _ f G 1 hf hG ψ hs hc
      (native_tangential_weak_partial_testing_to_flat ρ f G hf hG hw ψ hs hc ht)
  obtain ⟨hFR, hGR, hR⟩ := native_even_flux_source_reflected_weak_identity ρ F (fun x => -G x) hF hG.neg hweak
  have hflux (x : E2) : nativeEvenReflectedFlux ρ F x =
      nativeEvenReflectedSource ρ f x • coordinateVector 2 1 := by
    by_cases hx : x ∈ openHalfDisc ρ <;> by_cases hr : normalReflection x ∈ openHalfDisc ρ <;>
      simp [nativeEvenReflectedFlux, nativeEvenReflectedSource, F, hx, hr,
        normalReflection_basis_one, normalReflection.map_smul, add_smul, sub_eq_add_neg]
  have hsource (x : E2) : nativeEvenReflectedSource ρ (fun x => -G x) x = -nativeEvenReflectedSource ρ G x := by
    by_cases hx : x ∈ openHalfDisc ρ <;> by_cases hr : normalReflection x ∈ openHalfDisc ρ <;>
      simp [nativeEvenReflectedSource, hx, hr] <;> ring
  intro ψ hs hc ht
  obtain ⟨hiF, hiG, he⟩ := hR ψ hs hc ht
  have hinner (x : E2) : inner ℝ (nativeEvenReflectedFlux ρ F x) (planarGradient ψ x) =
      nativeEvenReflectedSource ρ f x * fderiv ℝ ψ x (coordinateVector 2 1) := by
    rw [hflux]
    simp [PiLp.inner_apply, coordinateVector, Fin.sum_univ_two, Helpers.gradient_apply] <;> ring
  simp_rw [hinner] at hiF he
  simp_rw [hsource, neg_mul] at hiG he
  rw [integral_sub hiF hiG, integral_neg] at he
  have hballF : (∫ x in Metric.ball (0 : E2) ρ,
      nativeEvenReflectedSource ρ f x * fderiv ℝ ψ x (coordinateVector 2 1)) =
      ∫ x, nativeEvenReflectedSource ρ f x * fderiv ℝ ψ x (coordinateVector 2 1) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (ht h))]
    simp
  have hballG : (∫ x in Metric.ball (0 : E2) ρ, nativeEvenReflectedSource ρ G x * ψ x) =
      ∫ x, nativeEvenReflectedSource ρ G x * ψ x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (ht h)), mul_zero]
  change (∫ x in Metric.ball (0 : E2) ρ,
    nativeEvenReflectedSource ρ f x * fderiv ℝ ψ x (coordinateVector 2 1)) =
      -(∫ x in Metric.ball (0 : E2) ρ, nativeEvenReflectedSource ρ G x * ψ x)
  rw [hballF, hballG]
  linarith

theorem native_even_reflected_memW1p
    (ρ : ℝ) (f : E2 → ℝ) (hw : DeGiorgi.MemW1p 2 f (openHalfDisc ρ)) :
    DeGiorgi.MemW1p 2 (nativeEvenReflectedSource ρ f) (Metric.ball 0 ρ) := by
  refine ⟨(native_even_reflected_scalar_memLp ρ f hw.1).restrict _, ?_⟩
  intro i
  fin_cases i
  · obtain ⟨G, hG, hweak⟩ := hw.2 0
    have hm := (openHalfDisc_isOpen ρ).measurableSet
    have hi : MemLp ((openHalfDisc ρ).indicator G) 2 volume :=
      (memLp_indicator_iff_restrict hm.nullMeasurableSet).mpr hG
    have hodd : MemLp (nativeReflectedSource ρ G) 2 volume :=
      hi.sub (hi.comp_measurePreserving normalReflection.measurePreserving)
    exact ⟨nativeReflectedSource ρ G, hodd.restrict _,
      native_even_reflected_normal_weak_partial ρ f G hw.1 hG hweak⟩
  · obtain ⟨G, hG, hweak⟩ := hw.2 1
    exact ⟨nativeEvenReflectedSource ρ G, (native_even_reflected_scalar_memLp ρ G hG).restrict _,
      native_even_reflected_tangential_weak_partial ρ f G hw.1 hG hweak⟩

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
