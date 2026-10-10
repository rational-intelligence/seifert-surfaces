import Section5CommonLeafArclengthV488

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology Function Filter MeasureTheory
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}

private def curveMetricSpeed (g : SmoothMetric E.Carrier) (c : ℝ → E.Carrier)
    (t : ℝ) : ℝ :=
  Real.sqrt (g.inner (c t) (mfderiv 𝓘(ℝ) (𝓡∂ 3) c t 1)
    (mfderiv 𝓘(ℝ) (𝓡∂ 3) c t 1))

private theorem curveMetricSpeed_add (g : SmoothMetric E.Carrier)
    (c : ℝ → E.Carrier) (hc : ContMDiff 𝓘(ℝ) (𝓡∂ 3) ∞ c) (u t : ℝ) :
    curveMetricSpeed g (fun s => c (s+u)) t = curveMetricSpeed g c (t+u) := by
  have hshift : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ) (fun s : ℝ => s+u) t := ((hasDerivAt_id t).add_const u).differentiableAt.mdifferentiableAt
  have hd : mfderiv 𝓘(ℝ) 𝓘(ℝ) (fun s : ℝ => s+u) t 1 = 1 := by
    rw [mfderiv_eq_fderiv]
    change fderiv ℝ (fun s : ℝ => s+u) t 1 = 1
    simpa only [id_eq,ContinuousLinearMap.toSpanSingleton_apply,smul_eq_mul,mul_one,one_mul] using
      congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) ((hasDerivAt_id t).add_const u).hasFDerivAt.fderiv
  unfold curveMetricSpeed
  change Real.sqrt (g.inner (c (t+u))
    (mfderiv 𝓘(ℝ) (𝓡∂ 3) (c ∘ fun s : ℝ => s+u) t 1)
    (mfderiv 𝓘(ℝ) (𝓡∂ 3) (c ∘ fun s : ℝ => s+u) t 1)) = _
  rw [mfderiv_comp t (hc.mdifferentiableAt (by simp)) hshift]
  change Real.sqrt (g.inner (c (t+u))
    (mfderiv 𝓘(ℝ) (𝓡∂ 3) c (t+u) (mfderiv 𝓘(ℝ) 𝓘(ℝ) (fun s : ℝ => s+u) t 1))
    (mfderiv 𝓘(ℝ) (𝓡∂ 3) c (t+u) (mfderiv 𝓘(ℝ) 𝓘(ℝ) (fun s : ℝ => s+u) t 1))) = _
  rw [hd]

theorem longitude_speed_periodic (g : SmoothMetric E.Carrier)
    (J : LongitudeFoliation.{0} E) (a : Circle) :
    Function.Periodic (longitudeSpeed g J a) (2*Real.pi) := by
  intro t
  have hclock : (fun s => longitudeClock J a (s+2*Real.pi)) = longitudeClock J a := by
    funext s
    simp [longitudeClock,Circle.exp_add,Circle.exp_two_pi]
  have h := curveMetricSpeed_add g (longitudeClock J a) (longitude_clock_smooth J a)
    (2*Real.pi) t
  rw [hclock] at h
  exact h.symm

#print axioms longitude_speed_periodic
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
