import CurveComplexGenusTwo.Topology.ActualModelHomology.ActualBoundaryCapRayGeometry

namespace CurveComplex.Hyperbolic.OneBoundaryRay

theorem visible_cap_arg_bound (θ : ℝ) (hθ : 0<θ) (hθpi : θ≤Real.pi)
    (w : ℂ) (hw : ‖w‖=1) (hcap : Real.cos θ≤w.re) : |w.arg|≤θ := by
  have hc : Real.cos w.arg=w.re := by
    simpa [hw] using Complex.norm_mul_cos_arg w
  by_contra hn
  have hs := Real.cos_lt_cos_of_nonneg_of_le_pi hθ.le
    (Complex.abs_arg_le_pi w) (lt_of_not_ge hn)
  rw [Real.cos_abs,hc] at hs
  linarith

theorem visible_cap_parameter (θ : ℝ) (hθ : 0<θ) (hθpi : θ≤Real.pi)
    (w : ℂ) (hw : ‖w‖=1) (hcap : Real.cos θ≤w.re) :
    ∃ t : unitInterval, w=Complex.exp (((1-2*(t:ℝ))*θ : ℝ)*Complex.I) := by
  have hb := visible_cap_arg_bound θ hθ hθpi w hw hcap
  have hlo := (abs_le.mp hb).1
  have hhi := (abs_le.mp hb).2
  let u : ℝ := (1-w.arg/θ)/2
  have hu0 : 0≤u := by
    dsimp [u]
    have h := (div_le_one hθ).mpr hhi
    linarith
  have hu1 : u≤1 := by
    dsimp [u]
    have h : -1≤w.arg/θ := (le_div_iff₀ hθ).mpr (by simpa using hlo)
    linarith
  refine ⟨⟨u,hu0,hu1⟩,?_⟩
  have he : (1-2*u)*θ=w.arg := by
    dsimp [u]
    field_simp [hθ.ne']
    <;> ring
  change w=Complex.exp (((1-2*u)*θ : ℝ)*Complex.I)
  rw [he]
  simpa [hw] using (Complex.norm_mul_exp_arg_mul_I w).symm

end CurveComplex.Hyperbolic.OneBoundaryRay
