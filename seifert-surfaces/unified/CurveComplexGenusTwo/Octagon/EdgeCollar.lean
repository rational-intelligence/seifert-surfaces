import CurveComplexGenusTwo.Foundations.Octagon

namespace CurveComplex.Octagon

/-! Radial collars on the open parts of the eight circular sides. -/

abbrev CollarRadius := Set.Ioc (1 / 2 : ℝ) 1
abbrev CollarAngle := Set.Ioo (0 : ℝ) 1

private theorem collarRadius_nonneg (r : CollarRadius) : 0 ≤ (r : ℝ) := by
  have hr := r.property.1
  linarith

private theorem collarRadius_le_one (r : CollarRadius) : (r : ℝ) ≤ 1 := r.property.2

noncomputable def collarPoint (i : Side) (r : CollarRadius) (t : CollarAngle) : Disk :=
  ⟨(r : ℝ) * (Circle.exp (2 * Real.pi * ((i.val : ℝ) + (t : ℝ)) / 8) : ℂ), by
    rw [Metric.mem_closedBall, dist_zero_right, norm_mul]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (collarRadius_nonneg r), Circle.norm_coe]
    simpa using collarRadius_le_one r⟩

theorem collarPoint_norm (i : Side) (r : CollarRadius) (t : CollarAngle) :
    ‖(collarPoint i r t : ℂ)‖ = (r : ℝ) := by
  change ‖(r : ℝ) * (Circle.exp (2 * Real.pi * ((i.val : ℝ) + (t : ℝ)) / 8) : ℂ)‖ = (r : ℝ)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (collarRadius_nonneg r), Circle.norm_coe, mul_one]

theorem collarPoint_continuous (i : Side) :
    Continuous (fun p : CollarRadius × CollarAngle => collarPoint i p.1 p.2) := by
  apply Continuous.subtype_mk
  have ha : Continuous (fun p : CollarRadius × CollarAngle =>
      2 * Real.pi * ((i.val : ℝ) + (p.2 : ℝ)) / 8) := by fun_prop
  have hc : Continuous (fun p : CollarRadius × CollarAngle =>
      (Circle.exp (2 * Real.pi * ((i.val : ℝ) + (p.2 : ℝ)) / 8) : ℂ)) :=
    continuous_subtype_val.comp (Circle.exp.continuous.comp ha)
  have hr : Continuous (fun p : CollarRadius × CollarAngle => ((p.1 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)
  exact hr.mul hc

noncomputable def collarToInterval (t : CollarAngle) : unitInterval :=
  ⟨(t : ℝ), le_of_lt t.property.1, le_of_lt t.property.2⟩

theorem collarPoint_boundary (i : Side) (t : CollarAngle) :
    collarPoint i ⟨1, by norm_num⟩ t = side i (collarToInterval t) := by
  apply Subtype.ext
  simp [collarPoint, side, collarToInterval]

theorem collarPoint_interior_iff (i : Side) (r : CollarRadius) (t : CollarAngle) :
    collarPoint i r t ∈ diskInterior ↔ (r : ℝ) < 1 := by
  simp [diskInterior, collarPoint_norm]

end CurveComplex.Octagon

namespace CurveComplex.Octagon

theorem collar_quotient_fiber_interior (i : Side) (r : CollarRadius) (t : CollarAngle)
    (hr : (r : ℝ) < 1) :
    mk ⁻¹' ({mk (collarPoint i r t)} : Set Surface) = {collarPoint i r t} := by
  have hi : collarPoint i r t ∈ diskInterior :=
    (collarPoint_interior_iff i r t).2 hr
  ext x
  constructor
  · intro hx
    have hmk : mk x = mk (collarPoint i r t) := hx
    have hxy := mem_diskInterior_of_mk_eq_mk hi hmk.symm
    exact Set.mem_singleton_iff.mpr hxy.symm
  · intro hx
    exact congrArg mk (Set.mem_singleton_iff.mp hx)

end CurveComplex.Octagon

namespace CurveComplex.Octagon

private noncomputable def angle (i : Side) (t : ℝ) : ℝ :=
  2 * Real.pi * ((i.val : ℝ) + t) / 8

private theorem angle_mem (i : Side) (t : CollarAngle) :
    angle i t ∈ Set.Icc (angle i 0) (angle i 1) := by
  constructor <;> dsimp [angle] <;> nlinarith [Real.pi_pos, t.property.1, t.property.2]

private theorem angle_width (i : Side) :
    angle i 1 - angle i 0 < 2 * Real.pi := by
  dsimp [angle]
  nlinarith [Real.pi_pos]

theorem collarPoint_injective (i : Side) :
    Function.Injective (fun p : CollarRadius × CollarAngle => collarPoint i p.1 p.2) := by
  rintro ⟨r, t⟩ ⟨s, u⟩ h
  have hr : r = s := Subtype.ext (by
    have := congrArg (fun x : Disk => ‖(x : ℂ)‖) h
    simpa [collarPoint_norm] using this)
  subst s
  have he : Circle.exp (angle i (t : ℝ)) = Circle.exp (angle i (u : ℝ)) := by
    apply Circle.ext
    have hh := congrArg (fun x : Disk => (x : ℂ)) h
    change ((r : ℝ) : ℂ) * (Circle.exp (angle i (t : ℝ)) : ℂ) =
      ((r : ℝ) : ℂ) * (Circle.exp (angle i (u : ℝ)) : ℂ) at hh
    exact mul_left_cancel₀ (by
      exact_mod_cast (ne_of_gt (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) r.property.1))) hh
  have ha := Circle.exp_injOn_Icc (angle_width i) (angle_mem i t) (angle_mem i u) he
  have htu : t = u := Subtype.ext (by
    dsimp [angle] at ha
    nlinarith [ha, Real.pi_pos])
  exact Prod.ext rfl htu

end CurveComplex.Octagon

namespace CurveComplex.Octagon

private theorem polarCoord_symm_eq_real_mul_exp (r θ : ℝ) :
    Complex.polarCoord.symm (r, θ) = (r : ℂ) * (Circle.exp θ : ℂ) := by
  simp [Complex.polarCoord_symm_apply, Circle.coe_exp, Complex.exp_mul_I,
    Complex.ofReal_cos, Complex.ofReal_sin]

private theorem collarPoint_polar (i : Side) (r : CollarRadius) (t : CollarAngle) :
    (collarPoint i r t : ℂ) =
      (Circle.exp (angle i 0) : ℂ) *
        Complex.polarCoord.symm ((r : ℝ), angle 0 (t : ℝ)) := by
  rw [polarCoord_symm_eq_real_mul_exp]
  change ((r : ℝ) : ℂ) * (Circle.exp (angle i (t : ℝ)) : ℂ) =
    (Circle.exp (angle i 0) : ℂ) *
      (((r : ℝ) : ℂ) * (Circle.exp (angle 0 (t : ℝ)) : ℂ))
  have ha : angle i (t : ℝ) = angle i 0 + angle 0 (t : ℝ) := by
    simp [angle]; ring
  rw [ha, Circle.exp_add]
  simp only [Circle.coe_mul]
  ring

end CurveComplex.Octagon
