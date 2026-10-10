import Section5CommonLeafSmoothClockV488

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology Function Filter MeasureTheory Bundle
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}

theorem longitude_unit_parameter_smooth (g : SmoothMetric E.Carrier)
    (J : LongitudeFoliation.{0} E) (a : Circle) :
    ContMDiff (𝓡 1) (𝓡∂ 3) ∞ (longitudeUnitParameter g J a) := by
  intro z₀
  let c := (z₀ : ℂ).arg
  let rot : Circle → Circle := fun z => Circle.exp (-c) * z
  let angle : Circle → ℝ := fun z => c + (Complex.log (rot z : ℂ)).im
  have hexp (z : Circle) : Circle.exp (angle z) = z := by
    dsimp only [angle]
    rw [Complex.log_im, Circle.exp_add, Circle.exp_arg (rot z)]
    dsimp only [rot]
    rw [Circle.exp_neg, ← mul_assoc, mul_inv_cancel, one_mul]
  have hrot : rot z₀ = 1 := by
    dsimp only [rot, c]
    rw [Circle.exp_neg, Circle.exp_arg, inv_mul_cancel]
  have hslit : (rot z₀ : ℂ) ∈ Complex.slitPlane := by
    rw [hrot]
    simp
  haveI : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨by simp⟩
  have hcoe : ContMDiff (𝓡 1) 𝓘(ℝ,ℂ) ∞ (fun z : Circle => (z : ℂ)) :=
    contMDiff_coe_sphere
  have hr : ContMDiff (𝓡 1) (𝓡 1) ∞ rot := contMDiff_const.mul contMDiff_id
  have hl := (Complex.contDiffAt_log hslit (n := ∞)).restrict_scalars ℝ
  have hi := Complex.imCLM.contDiff.contMDiff.contMDiffAt.comp z₀
    (hl.contMDiffAt.comp z₀ (hcoe.comp hr).contMDiffAt)
  have ha : ContMDiffAt (𝓡 1) 𝓘(ℝ) ∞ angle z₀ := contMDiffAt_const.add hi
  have hp : longitudeUnitParameter g J a =
      (fun z => longitudeUnitClock g J a (longitudeLength g J a / (2 * Real.pi) * angle z)) := by
    funext z
    have hs : 2 * Real.pi * (longitudeLength g J a / (2 * Real.pi) * angle z) /
        longitudeLength g J a = angle z := by
      field_simp [(longitude_length_positive g J a).ne', Real.pi_ne_zero]
    have h := longitude_unit_parameter_exp g J a
      (longitudeLength g J a / (2 * Real.pi) * angle z)
    rwa [hs, hexp] at h
  rw [hp]
  exact (longitude_unit_clock_smooth g J a).contMDiffAt.comp z₀
    (contMDiffAt_const.mul ha)

#print axioms longitude_unit_parameter_smooth
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
