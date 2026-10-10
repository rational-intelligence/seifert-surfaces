import InitialActualBoundaryLift_v411

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal

namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates

private theorem actual_boundary_cap_circle_geometry_v411
    (s q : ℝ) (hq : 0 < q) (hqhalf : q ≤ 1 / 2) :
    let e : ℝ := Real.arcsin (q / 2)
    let a : ℝ := s + Real.pi / 2 + e
    let b : ℝ := s + 3 * Real.pi / 2 - e
    a < b ∧ b - a ≤ Real.pi ∧ b < a + 2 * Real.pi ∧
      unitCircleParameter s + q • unitCircleParameter a = unitCircleParameter (s + 2 * e) ∧
      unitCircleParameter s + q • unitCircleParameter b = unitCircleParameter (s - 2 * e) ∧
      (∀ t ∈ Ioo a b, unitCircleParameter s + q • unitCircleParameter t ∈ disc 1) ∧
      (∀ t ∈ Icc b (a + 2 * Real.pi),
        unitCircleParameter s + q • unitCircleParameter t ∉ disc 1) := by
  classical
  dsimp only
  let e : ℝ := Real.arcsin (q / 2)
  let a : ℝ := s + Real.pi / 2 + e
  let b : ℝ := s + 3 * Real.pi / 2 - e
  have hepos : 0 < e := Real.arcsin_pos.mpr (by positivity)
  have hebound : e < Real.pi / 6 := by
    apply (Real.arcsin_lt_iff_lt_sin (by constructor <;> linarith)
      (by constructor <;> linarith [Real.pi_pos])).mpr
    rw [Real.sin_pi_div_six]
    linarith
  have hesin : Real.sin e = q / 2 :=
    Real.sin_arcsin' (by constructor <;> linarith)
  have hecos : Real.cos e ^ 2 = 1 - (q / 2) ^ 2 := by
    have hunit := Real.sin_sq_add_cos_sq e
    rw [hesin] at hunit
    linarith
  have hn (t : ℝ) : ‖unitCircleParameter s + q • unitCircleParameter t‖ ^ 2 =
      1 + q ^ 2 + 2 * q * Real.cos (t - s) := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    change (Real.cos s + q * Real.cos t) ^ 2 + (Real.sin s + q * Real.sin t) ^ 2 = _
    rw [Real.cos_sub]
    have hqt := congrArg (fun z : ℝ => q ^ 2 * z) (Real.cos_sq_add_sin_sq t)
    nlinarith [Real.cos_sq_add_sin_sq s, hqt]
  have htop : unitCircleParameter s + q • unitCircleParameter a =
      unitCircleParameter (s + 2 * e) := by
    ext i
    fin_cases i
    · change Real.cos s + q * Real.cos (s + Real.pi / 2 + e) = Real.cos (s + 2 * e)
      rw [Real.cos_add, Real.cos_add, Real.sin_add, Real.cos_pi_div_two, Real.sin_pi_div_two,
        Real.cos_add, Real.cos_two_mul, Real.sin_two_mul]
      simp only [mul_zero, mul_one, zero_add, zero_sub, add_zero]
      rw [hesin]
      rw [hecos]
      ring
    · change Real.sin s + q * Real.sin (s + Real.pi / 2 + e) = Real.sin (s + 2 * e)
      rw [Real.sin_add, Real.sin_add, Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two,
        Real.sin_add, Real.cos_two_mul, Real.sin_two_mul]
      simp only [mul_zero, mul_one, zero_add, zero_sub, add_zero]
      rw [hesin]
      rw [hecos]
      ring
  have hbottom : unitCircleParameter s + q • unitCircleParameter b =
      unitCircleParameter (s - 2 * e) := by
    have hc : unitCircleParameter b = unitCircleParameter (s - Real.pi / 2 - e) := by
      have hb : b = (s - Real.pi / 2 - e) + 2 * Real.pi := by dsimp [b]; ring
      rw [hb]
      ext i
      fin_cases i <;> simp [unitCircleParameter, Real.cos_add_two_pi, Real.sin_add_two_pi]
    rw [hc]
    ext i
    fin_cases i
    · change Real.cos s + q * Real.cos (s - Real.pi / 2 - e) = Real.cos (s - 2 * e)
      rw [Real.cos_sub, Real.cos_sub, Real.sin_sub, Real.cos_pi_div_two, Real.sin_pi_div_two,
        Real.cos_sub, Real.cos_two_mul, Real.sin_two_mul]
      simp only [mul_zero, mul_one, zero_add, zero_sub, sub_zero]
      rw [hesin]
      rw [hecos]
      ring
    · change Real.sin s + q * Real.sin (s - Real.pi / 2 - e) = Real.sin (s - 2 * e)
      rw [Real.sin_sub, Real.sin_sub, Real.cos_sub, Real.cos_pi_div_two, Real.sin_pi_div_two,
        Real.sin_sub, Real.cos_two_mul, Real.sin_two_mul]
      simp only [mul_zero, mul_one, zero_add, zero_sub, sub_zero]
      rw [hesin]
      rw [hecos]
      ring
  refine ⟨by change a < b; dsimp [a, b]; linarith [Real.pi_pos],
    by change b - a ≤ Real.pi; dsimp [a, b]; linarith,
    by change b < a + 2 * Real.pi; dsimp [a, b]; linarith [Real.pi_pos], htop, hbottom, ?_, ?_⟩
  · intro t ht
    let k : ℝ := t - s - Real.pi
    let h : ℝ := Real.pi / 2 - e
    have hhpos : 0 < h := by dsimp [h]; linarith [Real.pi_pos]
    have hhrange : h ∈ Icc (0 : ℝ) Real.pi := by dsimp [h]; constructor <;> linarith [Real.pi_pos]
    have hk : |k| < h := by
      apply abs_lt.mpr
      dsimp [k, h, a, b] at *
      constructor <;> linarith [ht.1, ht.2]
    have hcos := Real.strictAntiOn_cos
      (show |k| ∈ Icc (0 : ℝ) Real.pi from ⟨abs_nonneg _, hk.le.trans hhrange.2⟩)
      hhrange hk
    have hcosk : Real.cos k = Real.cos |k| := by rw [Real.cos_abs]
    have hcosh : Real.cos h = q / 2 := by
      dsimp [h]
      rw [Real.cos_sub, Real.cos_pi_div_two, Real.sin_pi_div_two]
      simpa using hesin
    rw [hcosh, ← hcosk] at hcos
    have hcosangle : Real.cos (t - s) = -Real.cos k := by
      have he : t - s = k + Real.pi := by dsimp [k]; ring
      rw [he, Real.cos_add_pi]
    have hnormsq : ‖unitCircleParameter s + q • unitCircleParameter t‖ ^ 2 < 1 := by
      rw [hn, hcosangle]
      nlinarith [mul_pos hq (show 0 < Real.cos k - q / 2 by linarith)]
    change dist (unitCircleParameter s + q • unitCircleParameter t) 0 < 1
    rw [dist_zero_right]
    nlinarith [norm_nonneg (unitCircleParameter s + q • unitCircleParameter t)]
  · intro t ht hmem
    let k : ℝ := t - s - 2 * Real.pi
    let h : ℝ := Real.pi / 2 + e
    have hhrange : h ∈ Icc (0 : ℝ) Real.pi := by dsimp [h]; constructor <;> linarith [Real.pi_pos]
    have hk : |k| ≤ h := by
      apply abs_le.mpr
      dsimp [k, h, a, b] at *
      constructor <;> linarith [ht.1, ht.2]
    have hcos := Real.antitoneOn_cos
      (show |k| ∈ Icc (0 : ℝ) Real.pi from ⟨abs_nonneg _, hk.trans hhrange.2⟩)
      hhrange hk
    have hcosh : Real.cos h = -(q / 2) := by
      dsimp [h]
      rw [Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]
      simp only [zero_mul, one_mul, zero_sub]
      rw [hesin]
    rw [hcosh, Real.cos_abs] at hcos
    have hcosangle : Real.cos (t - s) = Real.cos k := by
      have he : t - s = k + 2 * Real.pi := by dsimp [k]; ring
      rw [he, Real.cos_add_two_pi]
    have hnormsq : 1 ≤ ‖unitCircleParameter s + q • unitCircleParameter t‖ ^ 2 := by
      rw [hn, hcosangle]
      nlinarith [mul_nonneg hq.le (show 0 ≤ Real.cos k + q / 2 by linarith)]
    have hnorm : ‖unitCircleParameter s + q • unitCircleParameter t‖ < 1 := by
      change dist (unitCircleParameter s + q • unitCircleParameter t) 0 < 1 at hmem
      rwa [dist_zero_right] at hmem
    nlinarith [norm_nonneg (unitCircleParameter s + q • unitCircleParameter t)]

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
