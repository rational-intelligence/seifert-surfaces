import NativeBoundaryNeumannCoefficientPackage

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization

theorem native_even_flux_radius_congr (r s : ℝ) (hrs : r ≤ s) (F : E2 → E2)
    (x : E2) (hx : x ∈ Metric.ball 0 r) :
    nativeEvenReflectedFlux r F x = nativeEvenReflectedFlux s F x := by
  have hxS := Metric.ball_subset_ball hrs hx
  have hRx := normalReflection_maps_ball r hx
  have hRxS := normalReflection_maps_ball s hxS
  have hIx : (openHalfDisc r).indicator F x = (openHalfDisc s).indicator F x := by
    by_cases hp : 0 < x 0
    · simp only [indicator_of_mem (show x ∈ openHalfDisc r from ⟨hx, hp⟩),
        indicator_of_mem (show x ∈ openHalfDisc s from ⟨hxS, hp⟩)]
    · simp only [indicator_of_notMem (show x ∉ openHalfDisc r from fun hh => hp hh.2),
        indicator_of_notMem (show x ∉ openHalfDisc s from fun hh => hp hh.2)]
  have hIR : (openHalfDisc r).indicator F (normalReflection x) =
      (openHalfDisc s).indicator F (normalReflection x) := by
    by_cases hp : 0 < normalReflection x 0
    · simp only [indicator_of_mem (show normalReflection x ∈ openHalfDisc r from ⟨hRx, hp⟩),
        indicator_of_mem (show normalReflection x ∈ openHalfDisc s from ⟨hRxS, hp⟩)]
    · simp only [indicator_of_notMem (show normalReflection x ∉ openHalfDisc r from fun hh => hp hh.2),
        indicator_of_notMem (show normalReflection x ∉ openHalfDisc s from fun hh => hp hh.2)]
  simp only [nativeEvenReflectedFlux, hIx, hIR]

theorem native_neumann_linear_weak_restrict (r s κ : ℝ) (hrs : r ≤ s)
    (C : LinearizedCoefficients) (v : E2 → ℝ) (G : E2 → E2)
    (hw : LinearWeakEquation (Metric.ball 0 s) (nativeNeumannCoefficients s κ C) v G) :
    LinearWeakEquation (Metric.ball 0 r) (nativeNeumannCoefficients r κ C) v G := by
  have he := native_linear_weak_restrict (Metric.ball 0 s) (Metric.ball 0 r) Metric.isOpen_ball
    (Metric.ball_subset_ball hrs) _ v G hw
  have hF (x : E2) (hx : x ∈ Metric.ball 0 r) :
      linearizedFlux (nativeNeumannCoefficients r κ C) v G x =
        linearizedFlux (nativeNeumannCoefficients s κ C) v G x := by
    simp only [linearizedFlux, nativeNeumannCoefficients, native_even_flux_radius_congr r s hrs C.d x hx]
  have hS (x : E2) : linearizedSource (nativeNeumannCoefficients r κ C) v G x =
      linearizedSource (nativeNeumannCoefficients s κ C) v G x := rfl
  intro ψ hs hc ht
  obtain ⟨hiF, hiS, hzero⟩ := he ψ hs hc ht
  refine ⟨hiF.congr_fun (fun x hx => by rw [hF x hx]) Metric.isOpen_ball.measurableSet,
    hiS.congr_fun (fun x hx => by rw [hS]) Metric.isOpen_ball.measurableSet, ?_⟩
  rw [← hzero]
  apply setIntegral_congr_fun Metric.isOpen_ball.measurableSet
  intro x hx
  dsimp
  rw [hF x hx, hS]

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
