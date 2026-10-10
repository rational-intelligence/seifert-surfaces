import CurveComplexGenusTwo.Topology.ActualModelHomology.ActualOneBoundaryCapParameters
import ClassificationOfSurfaces.LeanEval.ChallengeDeps

namespace CurveComplex.Hyperbolic.OneBoundaryRay

noncomputable def modelRotation (p : ℕ) : ℂ :=
  Real.fourierChar (3/(2*modelSideCount p))

 theorem rotated_boundary_real (p : ℕ) (r : ℝ) :
    (modelRotation p*(Complex.ClosedUnitDisc.bdyPtOfReal r : ℂ)).re=
      Real.cos (2*Real.pi*(3/(2*modelSideCount p)+r)) := by
  change ((Real.fourierChar (3/(2*modelSideCount p)) : ℂ)*
    (Real.fourierChar r : ℂ)).re=_
  rw [← Circle.coe_mul,← AddChar.map_add_eq_mul]
  rw [Real.fourierChar_apply]
  exact Complex.exp_ofReal_mul_I_re _

 theorem rotated_deleted_arc_real (p : ℕ) (t : ℝ) :
    (modelRotation p*(Complex.ClosedUnitDisc.bdyPtOfReal
      (-(1+t)/modelSideCount p) : ℂ)).re=
      Real.cos ((1-2*t)*modelCapAngle p) := by
  rw [rotated_boundary_real]
  congr 1
  unfold modelCapAngle
  field_simp [(modelSideCount_pos p).ne']
  ring

theorem deleted_arc_lies_in_visible_cap (p : ℕ) (t : ℝ) (ht : 0≤t) (ht1 : t≤1) :
    1 ≤ modelRayOrigin p*(modelRotation p*
      (Complex.ClosedUnitDisc.bdyPtOfReal (-(1+t)/modelSideCount p) : ℂ)).re := by
  rw [rotated_deleted_arc_real]
  have hangle := modelCapAngle_pos p
  have hab : |(1-2*t)*modelCapAngle p| ≤ modelCapAngle p := by
    apply abs_le.mpr
    constructor <;> nlinarith [mul_nonneg ht hangle.le,
      mul_nonneg (sub_nonneg.mpr ht1) hangle.le]
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi
    (abs_nonneg ((1-2*t)*modelCapAngle p))
    (show modelCapAngle p≤Real.pi by linarith [modelCapAngle_lt_half_pi p,Real.pi_pos]) hab
  rw [Real.cos_abs] at hc
  unfold modelRayOrigin
  rw [one_div_mul_eq_div]
  exact (le_div_iff₀ (modelCapCos_pos p)).mpr (by simpa using hc)

theorem rotated_deleted_arc_value (p : ℕ) (t : ℝ) :
    modelRotation p*(Complex.ClosedUnitDisc.bdyPtOfReal
      (-(1+t)/modelSideCount p) : ℂ)=
      Complex.exp (((1-2*t)*modelCapAngle p : ℝ)*Complex.I) := by
  change (Real.fourierChar (3/(2*modelSideCount p)) : ℂ)*
    (Real.fourierChar (-(1+t)/modelSideCount p) : ℂ)=_
  rw [← Circle.coe_mul,← AddChar.map_add_eq_mul,Real.fourierChar_apply]
  congr 2
  congr 1
  unfold modelCapAngle
  field_simp [(modelSideCount_pos p).ne']
  ring

end CurveComplex.Hyperbolic.OneBoundaryRay
