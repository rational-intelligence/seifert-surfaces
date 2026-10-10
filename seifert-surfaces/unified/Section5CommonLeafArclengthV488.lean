import Section5CommonLeafLabelFlowV488

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology Function Filter MeasureTheory
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}

/-- The actual accumulated metric arclength of the longitude clock. -/
def longitudeArclength (g : SmoothMetric E.Carrier) (J : LongitudeFoliation.{0} E)
    (a : Circle) (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, longitudeSpeed g J a s

theorem longitude_arclength_hasDerivAt (g : SmoothMetric E.Carrier)
    (J : LongitudeFoliation.{0} E) (a : Circle) (t : ℝ) :
    HasDerivAt (longitudeArclength g J a) (longitudeSpeed g J a t) t := by
  apply intervalIntegral.integral_hasDerivAt_right
    ((longitude_speed_continuous g J a).intervalIntegrable 0 t)
  · exact (longitude_speed_continuous g J a).stronglyMeasurableAtFilter volume (𝓝 t)
  · exact (longitude_speed_continuous g J a).continuousAt

theorem longitude_arclength_strictMono (g : SmoothMetric E.Carrier)
    (J : LongitudeFoliation.{0} E) (a : Circle) :
    StrictMono (longitudeArclength g J a) := by
  apply strictMono_of_deriv_pos
  intro t
  rw [(longitude_arclength_hasDerivAt g J a t).deriv]
  exact longitude_speed_positive g J a t

theorem longitude_arclength_continuous (g : SmoothMetric E.Carrier)
    (J : LongitudeFoliation.{0} E) (a : Circle) :
    Continuous (longitudeArclength g J a) :=
  continuous_iff_continuousAt.mpr (fun t => (longitude_arclength_hasDerivAt g J a t).continuousAt)

theorem longitude_arclength_endpoints (g : SmoothMetric E.Carrier)
    (J : LongitudeFoliation.{0} E) (a : Circle) :
    longitudeArclength g J a 0 = 0 ∧
      longitudeArclength g J a (2*Real.pi) = longitudeLength g J a := by
  exact ⟨by simp [longitudeArclength],rfl⟩

#print axioms longitude_arclength_strictMono
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
