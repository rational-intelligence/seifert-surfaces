import CapGraphBoundaryBasics
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
open SeifertSurfaces.AppendixACoordinates L1Independent
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem cap_circle_frame (s t : ℝ) :
    unitCircleParameter t = Real.cos (t-s) • unitCircleParameter s +
      Real.sin (t-s) • rotateQuarter (unitCircleParameter s) := by
  apply PiLp.ext
  intro i
  fin_cases i
  · simp [unitCircleParameter,rotateQuarter,EuclideanSpace.equiv,Real.cos_sub,Real.sin_sub]
    linear_combination -Real.cos t * Real.cos_sq_add_sin_sq s
  · simp [unitCircleParameter,rotateQuarter,EuclideanSpace.equiv,Real.cos_sub,Real.sin_sub]
    linear_combination -Real.sin t * Real.cos_sq_add_sin_sq s

theorem cap_upper_curve (s q y : ℝ) (hq : 0<q) (hq1 : q≤1/2)
    (hy : y∈Icc (-capLensReach q) (capLensReach q)) :
    capCoordinateEquiv s (capLensUpper y,y)=unitCircleParameter (s+Real.arcsin y) := by
  have hb := (cap_transverse_interval_bounds q y hq hq1 hy).1
  rw [cap_circle_frame s (s+Real.arcsin y),show s+Real.arcsin y-s=Real.arcsin y by ring,
    Real.cos_arcsin,Real.sin_arcsin (abs_lt.mp hb).1.le (abs_lt.mp hb).2.le]
  rfl

theorem cap_artificial_cos_negative (s q t : ℝ) (hq : 0<q)
    (ht : t∈Icc (s+Real.pi/2+Real.arcsin (q/2)) (s+3*Real.pi/2-Real.arcsin (q/2))) :
    Real.cos (t-s)≤0 := by
  have he : 0≤Real.arcsin (q/2) := Real.arcsin_nonneg.mpr (by linarith)
  exact Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith [ht.1]) (by linarith [ht.2])

theorem cap_lower_curve (s q t : ℝ) (hq : 0<q)
    (ht : t∈Icc (s+Real.pi/2+Real.arcsin (q/2)) (s+3*Real.pi/2-Real.arcsin (q/2))) :
    capCoordinateEquiv s (capLensLower q (q*Real.sin (t-s)),q*Real.sin (t-s)) =
      unitCircleParameter s+q • unitCircleParameter t := by
  have hc := cap_artificial_cos_negative s q t hq ht
  have he : q^2-(q*Real.sin (t-s))^2=(q*Real.cos (t-s))^2 := by
    have hh := congrArg (fun x:ℝ => q^2*x) (Real.cos_sq_add_sin_sq (t-s))
    nlinarith
  have hs : Real.sqrt (q^2-(q*Real.sin (t-s))^2)= -q*Real.cos (t-s) := by
    rw [he,Real.sqrt_sq_eq_abs,abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hq.le hc)]
    ring
  rw [capCoordinateEquiv_apply,capLensLower,hs,cap_circle_frame s t,smul_add,smul_smul,smul_smul]
  module

theorem cap_upper_flux_coordinate (s q y : ℝ) (hq : 0<q) (hq1 : q≤1/2)
    (hy : y∈Icc (-capLensReach q) (capLensReach q)) (j : Fin 2) :
    (unitCircleParameter s j-deriv capLensUpper y * rotateQuarter (unitCircleParameter s) j)*
      Real.sqrt (1-y^2) = unitCircleParameter (s+Real.arcsin y) j := by
  rw [(cap_lens_upper_deriv q y hq hq1 hy).deriv,cap_circle_frame s (s+Real.arcsin y),
    show s+Real.arcsin y-s=Real.arcsin y by ring,Real.cos_arcsin,
    Real.sin_arcsin (abs_lt.mp (cap_transverse_interval_bounds q y hq hq1 hy).1).1.le
      (abs_lt.mp (cap_transverse_interval_bounds q y hq hq1 hy).1).2.le]
  have hs : Real.sqrt (1-y^2)≠0 := ne_of_gt (Real.sqrt_pos.mpr (cap_transverse_interval_bounds q y hq hq1 hy).2.1)
  simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
  field_simp
  ring

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
