import Section5CommonLeafArcInverseV488

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology Function Filter MeasureTheory
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}

theorem longitude_arclength_inverse_hasDerivAt (g : SmoothMetric E.Carrier)
    (J : LongitudeFoliation.{0} E) (a : Circle) (s : ℝ) :
    HasDerivAt (longitudeArclengthIso g J a).symm
      (longitudeSpeed g J a ((longitudeArclengthIso g J a).symm s))⁻¹ s := by
  apply HasDerivAt.of_local_left_inverse
    (longitudeArclengthIso g J a).symm.continuous.continuousAt
    (longitude_arclength_hasDerivAt g J a _)
    (longitude_speed_positive g J a _).ne'
  exact Filter.Eventually.of_forall (fun y => (longitudeArclengthIso g J a).apply_symm_apply y)

def longitudeUnitClock (g : SmoothMetric E.Carrier) (J : LongitudeFoliation.{0} E)
    (a : Circle) (s : ℝ) : E.Carrier :=
  longitudeClock J a ((longitudeArclengthIso g J a).symm s)

theorem longitude_unit_clock_periodic (g : SmoothMetric E.Carrier)
    (J : LongitudeFoliation.{0} E) (a : Circle) :
    Function.Periodic (longitudeUnitClock g J a) (longitudeLength g J a) := by
  intro s
  unfold longitudeUnitClock
  rw [longitude_arclength_inverse_shift]
  simp [longitudeClock,Circle.exp_add,Circle.exp_two_pi]

theorem longitude_unit_clock_unit_speed (g : SmoothMetric E.Carrier)
    (J : LongitudeFoliation.{0} E) (a : Circle) (s : ℝ) :
    g.inner (longitudeUnitClock g J a s)
      (mfderiv 𝓘(ℝ) (𝓡∂ 3) (longitudeUnitClock g J a) s 1)
      (mfderiv 𝓘(ℝ) (𝓡∂ 3) (longitudeUnitClock g J a) s 1) = 1 := by
  let q := (longitudeArclengthIso g J a).symm
  let speed := longitudeSpeed g J a (q s)
  have hspeed : 0 < speed := longitude_speed_positive g J a _
  have hq : HasDerivAt q speed⁻¹ s := longitude_arclength_inverse_hasDerivAt g J a s
  have hqd : mfderiv 𝓘(ℝ) 𝓘(ℝ) q s 1 = speed⁻¹ := by
    rw [mfderiv_eq_fderiv]
    change fderiv ℝ q s 1 = speed⁻¹
    rw [hq.hasFDerivAt.fderiv]
    simp
  have hcomp := mfderiv_comp s
    ((longitude_clock_smooth J a).mdifferentiableAt (by simp)) hq.differentiableAt.mdifferentiableAt
  change g.inner (longitudeClock J a (q s))
    (mfderiv 𝓘(ℝ) (𝓡∂ 3) (longitudeClock J a ∘ q) s 1)
    (mfderiv 𝓘(ℝ) (𝓡∂ 3) (longitudeClock J a ∘ q) s 1) = 1
  rw [hcomp]
  change g.inner (longitudeClock J a (q s))
    (mfderiv 𝓘(ℝ) (𝓡∂ 3) (longitudeClock J a) (q s) (mfderiv 𝓘(ℝ) 𝓘(ℝ) q s 1))
    (mfderiv 𝓘(ℝ) (𝓡∂ 3) (longitudeClock J a) (q s) (mfderiv 𝓘(ℝ) 𝓘(ℝ) q s 1)) = 1
  rw [hqd]
  have hvel : mfderiv 𝓘(ℝ) (𝓡∂ 3) (longitudeClock J a) (q s) (speed⁻¹ : ℝ) =
      speed⁻¹ • mfderiv 𝓘(ℝ) (𝓡∂ 3) (longitudeClock J a) (q s) 1 := by
    simpa using (mfderiv 𝓘(ℝ) (𝓡∂ 3) (longitudeClock J a) (q s)).map_smul speed⁻¹ 1
  rw [hvel]
  simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
  have hsquare : speed^2 = g.inner (longitudeClock J a (q s))
      (mfderiv 𝓘(ℝ) (𝓡∂ 3) (longitudeClock J a) (q s) 1)
      (mfderiv 𝓘(ℝ) (𝓡∂ 3) (longitudeClock J a) (q s) 1) :=
    Real.sq_sqrt (g.pos _ _ (longitude_clock_velocity_ne_zero J a _)).le
  rw [← hsquare]
  field_simp

#print axioms longitude_unit_clock_unit_speed
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
