import Section5CommonLeafParameterV488

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology Function Filter MeasureTheory
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}

theorem longitude_arclength_int_shift (g : SmoothMetric E.Carrier)
    (J : LongitudeFoliation.{0} E) (a : Circle) (t : ℝ) (m : ℤ) :
    longitudeArclength g J a (t + m * (2 * Real.pi)) =
      longitudeArclength g J a t + m * longitudeLength g J a := by
  have hsucc (m : ℤ) (hm : longitudeArclength g J a (t + m * (2 * Real.pi)) =
      longitudeArclength g J a t + m * longitudeLength g J a) :
      longitudeArclength g J a (t + (m + 1 : ℤ) * (2 * Real.pi)) =
        longitudeArclength g J a t + (m + 1 : ℤ) * longitudeLength g J a := by
      rw [Int.cast_add, Int.cast_one]
      have h : t + ((m : ℝ) + 1) * (2 * Real.pi) =
          (t + m * (2 * Real.pi)) + 2 * Real.pi := by ring
      rw [h, longitude_arclength_shift, hm]
      ring
  have hpred (m : ℤ) (hm : longitudeArclength g J a (t + m * (2 * Real.pi)) =
      longitudeArclength g J a t + m * longitudeLength g J a) :
      longitudeArclength g J a (t + (m - 1 : ℤ) * (2 * Real.pi)) =
        longitudeArclength g J a t + (m - 1 : ℤ) * longitudeLength g J a := by
      rw [Int.cast_sub, Int.cast_one]
      have h : (t + ((m : ℝ) - 1) * (2 * Real.pi)) + 2 * Real.pi =
          t + m * (2 * Real.pi) := by ring
      have he := longitude_arclength_shift g J a (t + ((m : ℝ) - 1) * (2 * Real.pi))
      rw [h, hm] at he
      linarith
  induction m using Int.induction_on with
  | zero => simp
  | succ m hm => exact hsucc _ hm
  | pred m hm => exact hpred _ hm

theorem longitude_unit_parameter_injective (g : SmoothMetric E.Carrier)
    (J : LongitudeFoliation.{0} E) (a : Circle) :
    Injective (longitudeUnitParameter g J a) := by
  intro z w h
  let e := AddCircle.homeomorphCircle (longitude_length_positive g J a).ne'
  obtain ⟨s, hs⟩ := QuotientAddGroup.mk_surjective (e.symm z)
  obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective (e.symm w)
  apply e.symm.injective
  rw [← hs, ← ht]
  have hclock : longitudeUnitClock g J a s = longitudeUnitClock g J a t := by
    change (longitude_unit_clock_periodic g J a).lift (e.symm z) =
      (longitude_unit_clock_periodic g J a).lift (e.symm w) at h
    simpa only [← hs, ← ht, Function.Periodic.lift_coe] using h
  have hexp := congrArg Prod.snd (J.smoothEmbedding.isEmbedding.injective hclock)
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hexp
  have harc := congrArg (longitudeArclengthIso g J a) hm
  change (longitudeArclengthIso g J a) ((longitudeArclengthIso g J a).symm s) =
    longitudeArclength g J a ((longitudeArclengthIso g J a).symm t + m * (2 * Real.pi)) at harc
  rw [OrderIso.apply_symm_apply, longitude_arclength_int_shift] at harc
  change s = (longitudeArclengthIso g J a) ((longitudeArclengthIso g J a).symm t) +
    m * longitudeLength g J a at harc
  rw [OrderIso.apply_symm_apply] at harc
  rw [QuotientAddGroup.eq]
  apply AddSubgroup.mem_zmultiples_iff.mpr
  refine ⟨-m, ?_⟩
  simp only [zsmul_eq_mul, Int.cast_neg]
  linarith

theorem longitude_unit_parameter_embedding (g : SmoothMetric E.Carrier)
    (J : LongitudeFoliation.{0} E) (a : Circle) :
    IsEmbedding (longitudeUnitParameter g J a) :=
  ((longitude_unit_parameter_continuous g J a).isClosedEmbedding
    (longitude_unit_parameter_injective g J a)).isEmbedding

#print axioms longitude_unit_parameter_embedding
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
