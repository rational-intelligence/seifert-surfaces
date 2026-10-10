import CapBoundaryCoordinateCurves
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
open SeifertSurfaces.AppendixACoordinates L1Independent
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem cap_artificial_transverse_range (s q t : ℝ) (hq : 0<q) (hq1 : q≤1/2)
    (ht : t∈Icc (s+Real.pi/2+Real.arcsin (q/2)) (s+3*Real.pi/2-Real.arcsin (q/2))) :
    q*Real.sin (t-s)∈Icc (-capLensReach q) (capLensReach q) := by
  have he := cap_arcsin_bounds q hq hq1
  let x := t-s-Real.pi/2
  have hx0 : 0≤x := by dsimp [x];linarith [ht.1,he.1]
  have hxpi : x≤Real.pi := by dsimp [x];linarith [ht.2,he.1]
  have hxlo : Real.arcsin (q/2)≤x := by dsimp [x];linarith [ht.1]
  have hxhi : x≤Real.pi-Real.arcsin (q/2) := by dsimp [x];linarith [ht.2]
  have hlo := Real.cos_le_cos_of_nonneg_of_le_pi hx0 (show Real.pi-Real.arcsin (q/2)≤Real.pi by linarith [he.1]) hxhi
  rw [Real.cos_pi_sub] at hlo
  have hhi := Real.cos_le_cos_of_nonneg_of_le_pi he.1.le hxpi hxlo
  have hsin : Real.sin (t-s)=Real.cos x := by
    rw [← Real.sin_add_pi_div_two]
    congr 1
    dsimp [x]
    ring
  rw [hsin]
  constructor <;> dsimp [capLensReach]
  · nlinarith [mul_le_mul_of_nonneg_left hlo hq.le]
  · exact mul_le_mul_of_nonneg_left hhi hq.le

theorem cap_artificial_transverse_endpoints (s q : ℝ) (hq : 0<q) (hq1 : q≤1/2) :
    q*Real.sin ((s+Real.pi/2+Real.arcsin (q/2))-s)=capLensReach q ∧
    q*Real.sin ((s+3*Real.pi/2-Real.arcsin (q/2))-s)= -capLensReach q := by
  constructor
  · rw [show s+Real.pi/2+Real.arcsin (q/2)-s=Real.arcsin (q/2)+Real.pi/2 by ring,
      Real.sin_add_pi_div_two]
    rfl
  · have he : s+3*Real.pi/2-Real.arcsin (q/2)-s=(Real.pi-Real.arcsin (q/2))+Real.pi/2 := by ring
    rw [he,Real.sin_add_pi_div_two,Real.cos_pi_sub]
    dsimp [capLensReach]
    ring

theorem cap_lower_flux_coordinate (s q t : ℝ) (hq : 0<q) (hq1 : q≤1/2)
    (ht : t∈Icc (s+Real.pi/2+Real.arcsin (q/2)) (s+3*Real.pi/2-Real.arcsin (q/2))) (j : Fin 2) :
    (unitCircleParameter s j-deriv (capLensLower q) (q*Real.sin (t-s))*rotateQuarter (unitCircleParameter s) j)*
      (q*Real.cos (t-s)) = q*unitCircleParameter t j := by
  have hr := cap_artificial_transverse_range s q t hq hq1 ht
  have hd := (cap_lens_lower_deriv q (q*Real.sin (t-s)) hq hq1 hr).deriv
  have hc := cap_artificial_cos_negative s q t hq ht
  have hs : Real.sqrt (q^2-(q*Real.sin (t-s))^2) = -q*Real.cos (t-s) := by
    have he : q^2-(q*Real.sin (t-s))^2=(q*Real.cos (t-s))^2 := by
      have hh := congrArg (fun x:ℝ => q^2*x) (Real.cos_sq_add_sin_sq (t-s))
      nlinarith
    rw [he,Real.sqrt_sq_eq_abs,abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hq.le hc)]
    ring
  have hne : q*Real.cos (t-s)≠0 := by
    have hh := Real.sqrt_pos.mpr (cap_lens_lower_radicand_pos q (q*Real.sin (t-s)) hq hq1 hr)
    rw [hs] at hh
    linarith
  have hcosne : Real.cos (t-s)≠0 := by intro hh;apply hne;rw [hh,mul_zero]
  rw [hd,hs,cap_circle_frame s t]
  simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
  field_simp [hcosne]
  ring

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
