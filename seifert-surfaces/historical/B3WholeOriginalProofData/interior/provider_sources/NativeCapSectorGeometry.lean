import NativePlaneRotation
import NativeACZeroExtension

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
open SeifertSurfaces.AppendixACoordinates L1Independent
set_option maxRecDepth 10000
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

theorem polarAngle_mem (z : E2) : polarAngle z ∈ Icc (-Real.pi) Real.pi :=
  ⟨(Complex.neg_pi_lt_arg _).le, Complex.arg_le_pi _⟩

theorem polarAngle_reconstruct (z : E2) : ‖z‖ • unitCircleParameter (polarAngle z) = z := by
  let w : ℂ := (z 0 : ℂ) + (z 1 : ℂ) * Complex.I
  have hn : ‖w‖ = ‖z‖ := by
    have he : ‖w‖ ^ 2 = ‖z‖ ^ 2 := by
      rw [Complex.sq_norm, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
      simp [w, Complex.normSq_apply, pow_two]
    nlinarith [norm_nonneg w, norm_nonneg z]
  ext i
  fin_cases i
  · change ‖z‖ * Real.cos (Complex.arg w) = z 0
    rw [← hn, Complex.norm_mul_cos_arg]
    simp [w]
  · change ‖z‖ * Real.sin (Complex.arg w) = z 1
    rw [← hn, Complex.norm_mul_sin_arg]
    simp [w]

theorem cap_sector_angles (q : ℝ) (hq : 0 < q) (hqhalf : q ≤ 1 / 2) :
    let e : ℝ := Real.arcsin (q / 2)
    (-Real.pi < e - Real.pi / 2) ∧
    e - Real.pi / 2 < Real.pi / 2 - e ∧
    Real.pi / 2 - e < Real.pi ∧
    Real.pi - 2 * e ≤ Real.pi := by
  dsimp only
  have hep : 0 < Real.arcsin (q / 2) := Real.arcsin_pos.mpr (by positivity)
  have heb : Real.arcsin (q / 2) < Real.pi / 6 := by
    apply (Real.arcsin_lt_iff_lt_sin (by constructor <;> linarith)
      (by constructor <;> linarith [Real.pi_pos])).mpr
    rw [Real.sin_pi_div_six]
    linarith
  exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos],
    by linarith [Real.pi_pos], by linarith⟩

theorem cap_sector_inside (s q r t : ℝ) (hq : 0 < q) (hqhalf : q ≤ 1 / 2)
    (hr : 0 < r) (hrq : r < q)
    (ht : t ∈ Icc (Real.arcsin (q / 2) - Real.pi / 2)
      (Real.pi / 2 - Real.arcsin (q / 2))) :
    unitCircleParameter s + r • planeRotation (s + Real.pi) (unitCircleParameter t) ∈ disc 1 := by
  let e := Real.arcsin (q / 2)
  have he := cap_sector_angles q hq hqhalf
  dsimp only at he
  have hep : 0 < e := Real.arcsin_pos.mpr (by positivity)
  have hepi : e < Real.pi / 2 := by linarith [he.2.1]
  have hcos : q / 2 ≤ Real.cos t := by
    have habst : |t| ≤ Real.pi / 2 - e := by
      apply abs_le.mpr
      constructor <;> linarith [ht.1, ht.2]
    have hc := Real.antitoneOn_cos
      (show |t| ∈ Icc (0 : ℝ) Real.pi by constructor; exact abs_nonneg _; linarith [habst, hep])
      (show Real.pi / 2 - e ∈ Icc (0 : ℝ) Real.pi by constructor <;> linarith [Real.pi_pos])
      habst
    rw [Real.cos_abs, Real.cos_sub, Real.cos_pi_div_two, Real.sin_pi_div_two] at hc
    simp only [zero_mul, one_mul, zero_add] at hc
    rw [show Real.sin e = q / 2 from Real.sin_arcsin' (by constructor <;> linarith)] at hc
    exact hc
  have hn : ‖unitCircleParameter s + r • planeRotation (s + Real.pi) (unitCircleParameter t)‖ ^ 2 =
      1 + r ^ 2 - 2 * r * Real.cos t := by
    rw [planeRotation_circle, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    change (Real.cos s + r * Real.cos (s + Real.pi + t)) ^ 2 +
      (Real.sin s + r * Real.sin (s + Real.pi + t)) ^ 2 = _
    have ha : s + Real.pi + t = s + t + Real.pi := by ring
    rw [ha, Real.cos_add_pi, Real.sin_add_pi, Real.cos_add, Real.sin_add]
    nlinarith [Real.cos_sq_add_sin_sq s, Real.cos_sq_add_sin_sq t,
      congrArg (fun v : ℝ => v * (r * Real.cos t) ^ 2) (Real.cos_sq_add_sin_sq s),
      congrArg (fun v : ℝ => v * (r * Real.sin t) ^ 2) (Real.cos_sq_add_sin_sq s),
      congrArg (fun v : ℝ => v * r ^ 2) (Real.cos_sq_add_sin_sq t)]
  change dist _ 0 < 1
  rw [dist_zero_right]
  nlinarith [norm_nonneg (unitCircleParameter s + r • planeRotation (s + Real.pi) (unitCircleParameter t)),
    mul_pos hr (sub_pos.mpr hrq), mul_nonneg hr.le (sub_nonneg.mpr hcos)]

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
