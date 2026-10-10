import NativeBoundaryLocalDualPackage

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization

theorem native_neumann_coefficient_bounds (ρ κ M : ℝ) (C : LinearizedCoefficients)
    (hb : CoefficientBounds (openHalfDisc ρ) C κ M) :
    CoefficientBounds (Metric.ball 0 ρ) (nativeNeumannCoefficients ρ κ C) κ (M + κ) := by
  have hrb := native_reflected_coefficient_bounds 0 (by simp) ρ κ M C hb
  have hM : 0 ≤ M := by linarith [hb.2.1]
  have hMK : 0 ≤ M + κ := by linarith [hb.1]
  refine ⟨hrb.1, hrb.2.1, hrb.2.2.1, ?_⟩
  intro x hx
  have ha := (hrb.2.2.2 x hx).1
  have hD : ‖nativeEvenReflectedFlux ρ C.d x‖ ≤ M := by
    have hRx := normalReflection_maps_ball ρ hx
    rcases lt_trichotomy 0 (x 0) with hp | hz | hn
    · have hxU : x ∈ openHalfDisc ρ := ⟨hx, hp⟩
      have hRU : normalReflection x ∉ openHalfDisc ρ := by
        intro hh
        have h := hh.2
        change 0 < normalReflection x 0 at h
        rw [normalReflection_zero] at h
        linarith
      simpa only [nativeEvenReflectedFlux, indicator_of_mem hxU, indicator_of_notMem hRU,
        map_zero, add_zero] using (hb.2.2.2 x hxU).2.2.1
    · have hxU : x ∉ openHalfDisc ρ := by
        intro hh
        have hp : 0 < x 0 := hh.2
        linarith
      have hRU : normalReflection x ∉ openHalfDisc ρ := by
        intro hh
        have h := hh.2
        change 0 < normalReflection x 0 at h
        rw [normalReflection_zero] at h
        linarith
      simpa only [nativeEvenReflectedFlux, indicator_of_notMem hxU, indicator_of_notMem hRU,
        map_zero, add_zero, norm_zero] using hM
    · have hxU : x ∉ openHalfDisc ρ := fun hh => (not_lt_of_ge hn.le) hh.2
      have hRU : normalReflection x ∈ openHalfDisc ρ :=
        ⟨hRx, by change 0 < normalReflection x 0; rw [normalReflection_zero]; linarith⟩
      simpa only [nativeEvenReflectedFlux, indicator_of_notMem hxU, indicator_of_mem hRU,
        zero_add, normalReflection.norm_map] using (hb.2.2.2 _ hRU).2.2.1
  exact ⟨ha, by simpa [nativeNeumannCoefficients] using hMK,
    hD.trans (le_add_of_nonneg_right hb.1.le),
    by simpa [nativeNeumannCoefficients] using hMK,
    by simpa [nativeNeumannCoefficients] using hMK,
    by simpa [nativeNeumannCoefficients] using hMK⟩

theorem native_neumann_coefficients_measurable (ρ κ : ℝ) (C : LinearizedCoefficients)
    (hm : CoefficientMeasurableOn (openHalfDisc ρ) C) :
    CoefficientMeasurableOn (Metric.ball 0 ρ) (nativeNeumannCoefficients ρ κ C) := by
  have hr := native_reflected_coefficients_measurable 0 (by simp) ρ κ C hm
  have hd : AEStronglyMeasurable (nativeEvenReflectedFlux ρ C.d) (volume.restrict (Metric.ball 0 ρ)) := by
    have hU := (openHalfDisc_isOpen ρ).measurableSet
    have hD : AEStronglyMeasurable ((openHalfDisc ρ).indicator C.d) volume :=
      (aestronglyMeasurable_indicator_iff hU).mpr hm.2.2.1
    exact (hD.add (normalReflection.continuous.comp_aestronglyMeasurable
      (hD.comp_quasiMeasurePreserving normalReflection.measurePreserving.quasiMeasurePreserving))).restrict
  exact ⟨hr.1, aestronglyMeasurable_const, hd, aestronglyMeasurable_const,
    aestronglyMeasurable_const, aestronglyMeasurable_const⟩

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
