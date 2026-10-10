import Section5CommonLeafUnitClockV488

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology Function Filter MeasureTheory
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}

def longitudeUnitParameter (g : SmoothMetric E.Carrier)
    (J : LongitudeFoliation.{0} E) (a : Circle) : Circle → E.Carrier :=
  (longitude_unit_clock_periodic g J a).lift ∘
    (AddCircle.homeomorphCircle (longitude_length_positive g J a).ne').symm

theorem longitude_unit_parameter_exp (g : SmoothMetric E.Carrier)
    (J : LongitudeFoliation.{0} E) (a : Circle) (s : ℝ) :
    longitudeUnitParameter g J a (Circle.exp (2 * Real.pi * s / longitudeLength g J a)) =
      longitudeUnitClock g J a s := by
  have h : Circle.exp (2 * Real.pi * s / longitudeLength g J a) =
      AddCircle.homeomorphCircle (longitude_length_positive g J a).ne'
        (s : AddCircle (longitudeLength g J a)) := by
    rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk]
    congr 1
    ring
  rw [h]
  simp [longitudeUnitParameter, Function.Periodic.lift_coe]

theorem longitude_unit_parameter_continuous (g : SmoothMetric E.Carrier)
    (J : LongitudeFoliation.{0} E) (a : Circle) :
    Continuous (longitudeUnitParameter g J a) := by
  apply Continuous.comp _ (AddCircle.homeomorphCircle (longitude_length_positive g J a).ne').symm.continuous
  apply continuous_coinduced_dom.mpr
  exact (longitude_clock_smooth J a).continuous.comp (longitudeArclengthIso g J a).symm.continuous

theorem longitude_unit_parameter_image (g : SmoothMetric E.Carrier)
    (J : LongitudeFoliation.{0} E) (a : Circle) :
    range (longitudeUnitParameter g J a) = J.leaf a := by
  ext p
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨s, hs⟩ := QuotientAddGroup.mk_surjective
      ((AddCircle.homeomorphCircle (longitude_length_positive g J a).ne').symm z)
    unfold longitudeUnitParameter
    dsimp only [Function.comp_apply]
    rw [← hs]
    change J.torus (a, Circle.exp ((longitudeArclengthIso g J a).symm s)) ∈ J.leaf a
    exact ⟨_, rfl⟩
  · rintro ⟨z, rfl⟩
    obtain ⟨t, rfl⟩ := Circle.exp_surjective z
    refine ⟨Circle.exp (2 * Real.pi * longitudeArclength g J a t / longitudeLength g J a), ?_⟩
    rw [longitude_unit_parameter_exp]
    unfold longitudeUnitClock
    change longitudeClock J a ((longitudeArclengthIso g J a).symm
      ((longitudeArclengthIso g J a) t)) = _
    rw [OrderIso.symm_apply_apply]
    rfl

theorem longitude_unit_parameter_arclength (g : SmoothMetric E.Carrier)
    (J : LongitudeFoliation.{0} E) (a : Circle) (t : ℝ) :
    let gamma := fun s : ℝ => longitudeUnitParameter g J a
      (Circle.exp (2 * Real.pi * s / longitudeLength g J a))
    let velocity := mfderiv 𝓘(ℝ) (𝓡∂ 3) gamma t
      ((NormedSpace.fromTangentSpace t).symm 1)
    g.inner (gamma t) velocity velocity = 1 := by
  have h : (fun s : ℝ => longitudeUnitParameter g J a
      (Circle.exp (2 * Real.pi * s / longitudeLength g J a))) =
      longitudeUnitClock g J a := funext (longitude_unit_parameter_exp g J a)
  dsimp only
  rw [h]
  rw [longitude_unit_parameter_exp]
  exact longitude_unit_clock_unit_speed g J a t

#print axioms longitude_unit_parameter_arclength
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
