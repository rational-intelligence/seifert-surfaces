import Section5CommonLeafPeriodicV488
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology Function Filter MeasureTheory
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}

theorem longitude_arclength_surjective (g : SmoothMetric E.Carrier)
    (J : LongitudeFoliation.{0} E) (a : Circle) :
    Surjective (longitudeArclength g J a) := by
  apply (longitude_arclength_continuous g J a).surjective
  · exact (longitude_speed_periodic g J a).tendsto_atTop_intervalIntegral_of_pos'
      ((longitude_speed_continuous g J a).intervalIntegrable _ _)
      (longitude_speed_positive g J a) (by positivity)
  · exact (longitude_speed_periodic g J a).tendsto_atBot_intervalIntegral_of_pos'
      ((longitude_speed_continuous g J a).intervalIntegrable _ _)
      (longitude_speed_positive g J a) (by positivity)

def longitudeArclengthIso (g : SmoothMetric E.Carrier)
    (J : LongitudeFoliation.{0} E) (a : Circle) : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective (longitudeArclength g J a)
    (longitude_arclength_strictMono g J a) (longitude_arclength_surjective g J a)

theorem longitude_arclength_shift (g : SmoothMetric E.Carrier)
    (J : LongitudeFoliation.{0} E) (a : Circle) (t : ℝ) :
    longitudeArclength g J a (t+2*Real.pi) =
      longitudeArclength g J a t + longitudeLength g J a := by
  simpa only [longitudeArclength,longitudeLength,zero_add] using
    (longitude_speed_periodic g J a).intervalIntegral_add_eq_add 0 t
      (fun x y => (longitude_speed_continuous g J a).intervalIntegrable x y)

theorem longitude_arclength_inverse_shift (g : SmoothMetric E.Carrier)
    (J : LongitudeFoliation.{0} E) (a : Circle) (s : ℝ) :
    (longitudeArclengthIso g J a).symm (s+longitudeLength g J a) =
      (longitudeArclengthIso g J a).symm s + 2*Real.pi := by
  apply (longitudeArclengthIso g J a).injective
  rw [OrderIso.apply_symm_apply]
  change s + longitudeLength g J a =
    longitudeArclength g J a ((longitudeArclengthIso g J a).symm s + 2*Real.pi)
  rw [longitude_arclength_shift]
  change s + longitudeLength g J a =
    (longitudeArclengthIso g J a) ((longitudeArclengthIso g J a).symm s) + longitudeLength g J a
  rw [OrderIso.apply_symm_apply]

#print axioms longitude_arclength_inverse_shift
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
