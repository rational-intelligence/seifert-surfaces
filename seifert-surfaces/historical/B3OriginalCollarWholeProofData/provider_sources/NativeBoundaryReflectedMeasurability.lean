import NativeBoundaryC1ReflectedEquation

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization

theorem native_reflected_field_measurable
    {F : Type*} [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F]
    (c : E2) (hc : c 0 = 0) (ρ : ℝ) (f : E2 → F)
    (hf : AEStronglyMeasurable f (volume.restrict (Metric.ball c ρ ∩ {x : E2 | 0 < x 0})))
    (T : F → F) (hT : Continuous T) (hT0 : T 0 = 0) (z : F) :
    AEStronglyMeasurable (fun x => if 0 < x 0 then f x else
      if x 0 < 0 then T (f (normalReflection x)) else z) (volume.restrict (Metric.ball c ρ)) := by
  classical
  let B := Metric.ball c ρ ∩ {x : E2 | 0 < x 0}
  let D := B.indicator f
  have hB : MeasurableSet B := (Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (0 : Fin 2)).continuous)).measurableSet
  have hD : AEStronglyMeasurable D volume := (aestronglyMeasurable_indicator_iff hB).mpr hf
  have hDR : AEStronglyMeasurable (fun x => T (D (normalReflection x))) volume :=
    hT.comp_aestronglyMeasurable
      (hD.comp_quasiMeasurePreserving normalReflection.measurePreserving.quasiMeasurePreserving)
  have hsum : AEStronglyMeasurable (fun x => D x + T (D (normalReflection x)))
      (volume.restrict (Metric.ball c ρ)) := (hD.add hDR).restrict
  have hne : ∀ᵐ x : E2 ∂volume, x 0 ≠ 0 := by
    simpa only [ae_iff, not_not] using native_flat_plane_null
  apply hsum.congr
  filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet,
    hne.filter_mono (ae_mono Measure.restrict_le_self)] with x hx hn
  have hRx := normalReflection_maps_centered_ball hc ρ hx
  rcases lt_or_gt_of_ne hn with hneg | hpos
  · have hxB : x ∉ B := fun hh => (not_lt_of_ge hneg.le) hh.2
    have hRxB : normalReflection x ∈ B := by
      refine ⟨hRx, ?_⟩
      change 0 < normalReflection x 0
      rw [normalReflection_zero]
      linarith
    simp [D, indicator_of_notMem hxB, indicator_of_mem hRxB, hneg, not_lt.mpr hneg.le]
  · have hxB : x ∈ B := ⟨hx, hpos⟩
    have hRxB : normalReflection x ∉ B := by
      intro hh
      have h : 0 < normalReflection x 0 := hh.2
      rw [normalReflection_zero] at h
      linarith
    simp [D, indicator_of_mem hxB, indicator_of_notMem hRxB, hpos, hT0]

theorem native_reflected_coefficients_measurable
    (c : E2) (hc : c 0 = 0) (ρ κ : ℝ) (C : LinearizedCoefficients)
    (hm : CoefficientMeasurableOn (Metric.ball c ρ ∩ {x : E2 | 0 < x 0}) C) :
    CoefficientMeasurableOn (Metric.ball c ρ) (reflectLinearizedCoefficients C κ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact native_reflected_field_measurable c hc ρ C.a hm.1
      (fun A => normalReflectionCLM.comp (A.comp normalReflectionCLM))
      (continuous_const.clm_comp (continuous_id.clm_comp continuous_const)) (by ext x; simp)
      (κ • ContinuousLinearMap.id ℝ E2)
  · exact native_reflected_field_measurable c hc ρ C.c hm.2.1
      normalReflection normalReflection.continuous (map_zero _) 0
  · exact native_reflected_field_measurable c hc ρ C.d hm.2.2.1
      (fun v => -normalReflection v) normalReflection.continuous.neg (by simp) 0
  · exact native_reflected_field_measurable c hc ρ C.b hm.2.2.2.1
      (fun b => b.comp normalReflectionCLM) (continuous_id.clm_comp continuous_const)
      (by ext x; simp) 0
  · exact native_reflected_field_measurable c hc ρ C.q hm.2.2.2.2.1
      id continuous_id rfl 0
  · exact native_reflected_field_measurable c hc ρ C.f hm.2.2.2.2.2
      (fun z => -z) continuous_neg neg_zero 0

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
