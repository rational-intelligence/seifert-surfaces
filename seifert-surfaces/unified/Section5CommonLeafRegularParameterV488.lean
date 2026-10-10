import Section5CommonLeafSmoothParameterV488

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology Function Filter MeasureTheory
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}

theorem longitude_unit_clock_differential_injective (g : SmoothMetric E.Carrier)
    (J : LongitudeFoliation.{0} E) (a : Circle) (t : ℝ) :
    Injective (mfderiv 𝓘(ℝ) (𝓡∂ 3) (longitudeUnitClock g J a) t) := by
  let D := mfderiv 𝓘(ℝ) (𝓡∂ 3) (longitudeUnitClock g J a) t
  have hD : D 1 ≠ 0 := by
    intro h
    have hu := longitude_unit_clock_unit_speed g J a t
    change g.inner _ (D 1) (D 1) = 1 at hu
    simp [h] at hu
  intro x y hxy
  have hx : D x = (show ℝ from x) • D 1 := by simpa using D.map_smul (show ℝ from x) 1
  have hy : D y = (show ℝ from y) • D 1 := by simpa using D.map_smul (show ℝ from y) 1
  change D x = D y at hxy
  rw [hx,hy] at hxy
  exact (smul_left_injective ℝ hD) hxy

theorem longitude_unit_parameter_differential_injective (g : SmoothMetric E.Carrier)
    (J : LongitudeFoliation.{0} E) (a z : Circle) :
    Injective (mfderiv (𝓡 1) (𝓡∂ 3) (longitudeUnitParameter g J a) z) := by
  let L := longitudeLength g J a
  let k := 2 * Real.pi / L
  have hk : k ≠ 0 := div_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
    (longitude_length_positive g J a).ne'
  let scale : ℝ → ℝ := fun t => k * t
  let clock : ℝ → Circle := Circle.exp ∘ scale
  have hs : ContDiff ℝ ∞ scale := contDiff_const.mul contDiff_id
  have hc : ContMDiff 𝓘(ℝ) (𝓡 1) ∞ clock := contMDiff_circleExp.comp hs.contMDiff
  have hscale (t : ℝ) : Injective (mfderiv 𝓘(ℝ) 𝓘(ℝ) scale t) := by
    have hd : HasDerivAt scale k t := by simpa [scale] using (hasDerivAt_id t).const_mul k
    rw [mfderiv_eq_fderiv]
    change Injective (fderiv ℝ scale t)
    rw [hd.hasFDerivAt.fderiv]
    intro x y h
    simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at h
    exact mul_right_cancel₀ hk h
  have hclock (t : ℝ) : Injective (mfderiv 𝓘(ℝ) (𝓡 1) clock t) := by
    rw [mfderiv_comp t ((contMDiff_circleExp (m := ∞)).mdifferentiableAt (by simp))
      (hs.differentiable (by simp) t).mdifferentiableAt]
    exact (circle_clock_differential_injective _).comp (hscale t)
  obtain ⟨θ, hθ⟩ := Circle.exp_surjective z
  let t := θ / k
  have ht : clock t = z := by
    dsimp only [clock,Function.comp_apply,scale,t]
    rw [mul_div_cancel₀ _ hk,hθ]
  have hsurj : Surjective (mfderiv 𝓘(ℝ) (𝓡 1) clock t) := by
    apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f :=
      (mfderiv 𝓘(ℝ) (𝓡 1) clock t).toLinearMap) ?_).mp (hclock t)
    change Module.finrank ℝ ℝ = Module.finrank ℝ (Euc 1)
    simp
  have heq : longitudeUnitParameter g J a ∘ clock = longitudeUnitClock g J a := by
    funext s
    have hnum : k * s = 2 * Real.pi * s / L := by dsimp only [k]; ring
    simpa only [Function.comp_apply,clock,scale,hnum,L] using longitude_unit_parameter_exp g J a s
  have hcomp := mfderiv_comp t
    ((longitude_unit_parameter_smooth g J a).mdifferentiableAt (by simp))
    (hc.mdifferentiableAt (by simp))
  rw [heq] at hcomp
  rw [← ht]
  intro v w h
  obtain ⟨x,rfl⟩ := hsurj v
  obtain ⟨y,rfl⟩ := hsurj w
  have hxy : mfderiv 𝓘(ℝ) (𝓡∂ 3) (longitudeUnitClock g J a) t x =
      mfderiv 𝓘(ℝ) (𝓡∂ 3) (longitudeUnitClock g J a) t y := by
    rw [hcomp]
    exact h
  exact congrArg _ ((longitude_unit_clock_differential_injective g J a t) hxy)

#print axioms longitude_unit_parameter_differential_injective
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
