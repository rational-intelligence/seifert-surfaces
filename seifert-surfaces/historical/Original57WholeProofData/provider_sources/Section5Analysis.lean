import Mathlib

/-!
# Section 5: genuine analytic and numerical prerequisites

Source: Lemmas 5.4--5.5, Proposition 5.7, Appendix B.1--B.3.
The measure below represents arclength only after a geometric producer supplies
that identification. Integrability is explicit: the Bochner integral has a junk
value for nonintegrable functions. No embedded-surface production is asserted.
-/

open MeasureTheory
open scoped Interval ContDiff

namespace SeifertSurfaces.Section5.Analysis.ProfileConstruction

noncomputable def slope (t : ℝ) : ℝ :=
  Real.smoothTransition t - Real.smoothTransition (-t)

lemma slope_smooth : ContDiff ℝ ∞ slope := by
  exact Real.smoothTransition.contDiff.sub
    (Real.smoothTransition.contDiff.comp contDiff_id.neg)

lemma slope_continuous : Continuous slope := slope_smooth.continuous

lemma slope_odd (t : ℝ) : slope (-t) = -slope t := by
  simp only [slope, neg_neg]
  ring

lemma slope_abs_le_one (t : ℝ) : |slope t| ≤ 1 := by
  rw [abs_le]
  have h1 := Real.smoothTransition.nonneg t
  have h2 := Real.smoothTransition.nonneg (-t)
  have h3 := Real.smoothTransition.le_one t
  have h4 := Real.smoothTransition.le_one (-t)
  unfold slope
  constructor <;> linarith

lemma slope_nonneg (t : ℝ) (ht : 0 ≤ t) : 0 ≤ slope t := by
  unfold slope
  rw [Real.smoothTransition.zero_of_nonpos (neg_nonpos.mpr ht), sub_zero]
  exact Real.smoothTransition.nonneg t

lemma slope_eq_one (t : ℝ) (ht : 1 ≤ t) : slope t = 1 := by
  unfold slope
  rw [Real.smoothTransition.one_of_one_le ht,
    Real.smoothTransition.zero_of_nonpos (by linarith), sub_zero]

noncomputable def profile (t : ℝ) : ℝ :=
  1 - (∫ x in (0 : ℝ)..1, slope x) + ∫ x in (0 : ℝ)..t, slope x

lemma profile_hasDerivAt (t : ℝ) : HasDerivAt profile (slope t) t := by
  change HasDerivAt (fun x : ℝ => (1 - (∫ x in (0 : ℝ)..1, slope x)) +
    (∫ x in (0 : ℝ)..x, slope x)) (slope t) t
  apply HasDerivAt.const_add
  exact intervalIntegral.integral_hasDerivAt_right
    (slope_continuous.intervalIntegrable 0 t)
    slope_continuous.stronglyMeasurable.stronglyMeasurableAtFilter
    slope_continuous.continuousAt

lemma profile_deriv (t : ℝ) : deriv profile t = slope t :=
  (profile_hasDerivAt t).deriv

lemma profile_smooth : ContDiff ℝ ∞ profile := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun t => (profile_hasDerivAt t).differentiableAt, ?_⟩
  simpa only [funext profile_deriv] using slope_smooth

lemma primitive_even (t : ℝ) :
    (∫ x in (0 : ℝ)..(-t), slope x) = ∫ x in (0 : ℝ)..t, slope x := by
  have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := t) slope
  simp only [neg_zero, slope_odd, intervalIntegral.integral_neg] at h
  rw [intervalIntegral.integral_symm 0 (-t)] at h
  linarith

lemma profile_even : Function.Even profile := by
  intro t
  unfold profile
  rw [primitive_even]

lemma profile_formula (t : ℝ) :
    profile t = 1 - ∫ x in t..(1 : ℝ), slope x := by
  have h := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (slope_continuous.intervalIntegrable 0 t)
    (slope_continuous.intervalIntegrable t 1)
  unfold profile
  linarith

lemma profile_matches_positive (t : ℝ) (ht : 1 ≤ t) : profile t = t := by
  have h := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (slope_continuous.intervalIntegrable 0 1)
    (slope_continuous.intervalIntegrable 1 t)
  have hc : (∫ x in (1 : ℝ)..t, slope x) = t - 1 := by
    have heq : (∫ x in (1 : ℝ)..t, slope x) = ∫ x in (1 : ℝ)..t, (1 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le ht] at hx
      exact slope_eq_one x hx.1
    simpa using heq
  unfold profile
  linarith

lemma profile_matches_abs (t : ℝ) (ht : 1 ≤ |t|) : profile t = |t| := by
  by_cases h : 0 ≤ t
  · rw [abs_of_nonneg h] at ht ⊢
    exact profile_matches_positive t ht
  · have hn : t ≤ 0 := (lt_of_not_ge h).le
    rw [abs_of_nonpos hn] at ht ⊢
    rw [← profile_even t]
    exact profile_matches_positive (-t) ht

lemma profile_bounds_positive (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    t ≤ profile t ∧ profile t ≤ 1 := by
  have hn : 0 ≤ ∫ x in t..(1 : ℝ), slope x :=
    intervalIntegral.integral_nonneg ht1 fun x hx =>
      slope_nonneg x (ht.trans hx.1)
  have hu : (∫ x in t..(1 : ℝ), slope x) ≤ 1 - t := by
    have h := intervalIntegral.integral_mono_on (μ := volume) ht1
      (slope_continuous.intervalIntegrable t 1) (intervalIntegrable_const)
      (fun x _ => (abs_le.mp (slope_abs_le_one x)).2)
    simpa using h
  rw [profile_formula]
  constructor <;> linarith

lemma profile_bounds (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    |t| ≤ profile t ∧ profile t ≤ 1 := by
  by_cases h : 0 ≤ t
  · rw [abs_of_nonneg h]
    exact profile_bounds_positive t h ht.2
  · have hn : t ≤ 0 := (lt_of_not_ge h).le
    rw [abs_of_nonpos hn, ← profile_even t]
    exact profile_bounds_positive (-t) (by linarith) (by linarith [ht.1])

lemma profile_deriv_zero : deriv profile 0 = 0 := by
  rw [profile_deriv]
  simp [slope]

end SeifertSurfaces.Section5.Analysis.ProfileConstruction


namespace SeifertSurfaces.Section5.Analysis

/-- Equation (9); the same value is obtained for either complementary sector. -/
noncomputable def twoSidedAngle (alpha : ℝ) : ℝ := min alpha (Real.pi - alpha)

theorem two_sided_angle_bounds
    (alpha : ℝ) (hpositive : 0 < alpha) (hlt : alpha < Real.pi) :
    0 < twoSidedAngle alpha ∧ twoSidedAngle alpha ≤ Real.pi / 2 := by
  constructor
  · exact lt_min hpositive (sub_pos.mpr hlt)
  · unfold twoSidedAngle
    rcases le_total alpha (Real.pi - alpha) with h | h
    · rw [min_eq_left h]
      linarith
    · rw [min_eq_right h]
      linarith

theorem complementary_sectors_have_same_angle (alpha : ℝ) :
    twoSidedAngle (Real.pi - alpha) = twoSidedAngle alpha := by
  unfold twoSidedAngle
  rw [sub_sub_cancel, min_comm]

/-- The smooth replacement profile used in Appendix B.1, extended by |t| outside [-1,1].
The matching condition and smoothness include all orders of seam matching.
The inequalities used by the quantitative proof are retained explicitly. -/
structure RoundingProfile where
  profile : ℝ → ℝ
  smooth : ContDiff ℝ ∞ profile
  even : Function.Even profile
  matches_abs : ∀ t : ℝ, 1 ≤ |t| → profile t = |t|
  above_abs : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |t| ≤ profile t
  at_most_one : ∀ t ∈ Set.Icc (-1 : ℝ) 1, profile t ≤ 1
  deriv_bound : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |deriv profile t| ≤ 1
  deriv_zero : deriv profile 0 = 0

/-- Appendix B.1 asserts existence of such a smooth profile; this is a separate producer. -/
theorem rounding_profile_exists : Nonempty RoundingProfile := by
  exact ⟨{
    profile := ProfileConstruction.profile
    smooth := ProfileConstruction.profile_smooth
    even := ProfileConstruction.profile_even
    matches_abs := ProfileConstruction.profile_matches_abs
    above_abs := fun t ht => (ProfileConstruction.profile_bounds t ht).1
    at_most_one := fun t ht => (ProfileConstruction.profile_bounds t ht).2
    deriv_bound := fun t _ => by
      rw [ProfileConstruction.profile_deriv]
      exact ProfileConstruction.slope_abs_le_one t
    deriv_zero := ProfileConstruction.profile_deriv_zero
  }⟩

/-- The actual interval integral defining g(m) in Appendix B.1. -/
noncomputable def profileGain (P : RoundingProfile) (m : ℝ) : ℝ :=
  ∫ t in (-1 : ℝ)..1,
    Real.sqrt (1 + m ^ 2) - Real.sqrt (1 + m ^ 2 * (deriv P.profile t) ^ 2)

/-- The source's g₀(θ) = 1/2 g(tan(θ/2)), after locating the minimum. -/
noncomputable def angleGain (P : RoundingProfile) (theta : ℝ) : ℝ :=
  profileGain P (Real.tan (theta / 2)) / 2

theorem profile_gain_positive (P : RoundingProfile) (m : ℝ) (hm : 0 < m) :
    0 < profileGain P m := by
  have hd : Continuous (deriv P.profile) := P.smooth.continuous_deriv (by simp)
  unfold profileGain
  apply intervalIntegral.integral_pos (by norm_num)
  · apply Continuous.continuousOn
    fun_prop
  · intro t ht
    have hb := (sq_le_one_iff_abs_le_one _).mpr
      (P.deriv_bound t ⟨ht.1.le, ht.2⟩)
    apply sub_nonneg.mpr
    apply Real.sqrt_le_sqrt
    nlinarith [mul_nonneg (sq_nonneg m) (sub_nonneg.mpr hb)]
  · refine ⟨0, by norm_num, ?_⟩
    rw [P.deriv_zero]
    simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero, Real.sqrt_one]
    apply sub_pos.mpr
    exact (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)).mpr (by nlinarith)

theorem profile_gain_continuous (P : RoundingProfile) :
    ContinuousOn (profileGain P) (Set.Ioi 0) := by
  have hd : Continuous (deriv P.profile) := P.smooth.continuous_deriv (by simp)
  have hc : Continuous (fun p : ℝ × ℝ =>
      Real.sqrt (1 + p.1 ^ 2) - Real.sqrt (1 + p.1 ^ 2 * (deriv P.profile p.2) ^ 2)) := by
    fun_prop
  exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    hc (-1) 1).continuousOn

lemma scaled_sqrt_bound (c t : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    c * Real.sqrt (1 + t ^ 2) ≤ Real.sqrt (1 + c * t ^ 2) := by
  apply Real.le_sqrt (by positivity) (by positivity) |>.mpr
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hsq : c ^ 2 ≤ c := by nlinarith
  have ht := mul_le_mul_of_nonneg_right hsq (sq_nonneg t)
  nlinarith

lemma sqrt_difference_monotone (a b c : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    Real.sqrt (1 + a ^ 2) - Real.sqrt (1 + c * a ^ 2) ≤
      Real.sqrt (1 + b ^ 2) - Real.sqrt (1 + c * b ^ 2) := by
  let A := Real.sqrt (1 + a ^ 2)
  let B := Real.sqrt (1 + b ^ 2)
  let C := Real.sqrt (1 + c * a ^ 2)
  let D := Real.sqrt (1 + c * b ^ 2)
  have hA : A ^ 2 = 1 + a ^ 2 := Real.sq_sqrt (by positivity)
  have hB : B ^ 2 = 1 + b ^ 2 := Real.sq_sqrt (by positivity)
  have hC : C ^ 2 = 1 + c * a ^ 2 := Real.sq_sqrt (by positivity)
  have hD : D ^ 2 = 1 + c * b ^ 2 := Real.sq_sqrt (by positivity)
  have hAB : A ≤ B := Real.sqrt_le_sqrt (by nlinarith)
  have hden : c * (B + A) ≤ D + C := by
    have h1 := scaled_sqrt_bound c a hc hc1
    have h2 := scaled_sqrt_bound c b hc hc1
    dsimp [A,B,C,D]
    linarith
  have hh := mul_le_mul_of_nonneg_left hden (sub_nonneg.mpr hAB)
  have heq : (B - A) * (c * (B + A)) = (D - C) * (D + C) := by
    calc
      _ = c * (B ^ 2 - A ^ 2) := by ring
      _ = D ^ 2 - C ^ 2 := by rw [hB,hA,hC,hD]; ring
      _ = (D - C) * (D + C) := by ring
  rw [heq] at hh
  have hDC : 0 < D + C := by dsimp [D,C]; positivity
  have h := (mul_le_mul_iff_left₀ hDC).mp hh
  change A - C ≤ B - D
  linarith

theorem profile_gain_monotone (P : RoundingProfile) :
    MonotoneOn (profileGain P) (Set.Ioi 0) := by
  intro a ha b hb hab
  have hd : Continuous (deriv P.profile) := P.smooth.continuous_deriv (by simp)
  have hca : Continuous (fun t : ℝ => Real.sqrt (1 + a ^ 2) -
      Real.sqrt (1 + a ^ 2 * (deriv P.profile t) ^ 2)) := by fun_prop
  have hcb : Continuous (fun t : ℝ => Real.sqrt (1 + b ^ 2) -
      Real.sqrt (1 + b ^ 2 * (deriv P.profile t) ^ 2)) := by fun_prop
  apply intervalIntegral.integral_mono_on (by norm_num) (hca.intervalIntegrable _ _)
    (hcb.intervalIntegrable _ _)
  intro t ht
  simpa only [mul_comm (a ^ 2), mul_comm (b ^ 2)] using
    sqrt_difference_monotone a b ((deriv P.profile t) ^ 2) ha.le hab (sq_nonneg _)
      ((sq_le_one_iff_abs_le_one _).mpr (P.deriv_bound t ht))

theorem angle_gain_positive (P : RoundingProfile) (theta : ℝ)
    (htheta : 0 < theta) (hupper : theta ≤ Real.pi / 2) :
    0 < angleGain P theta := by
  unfold angleGain
  exact div_pos (profile_gain_positive P _
    (Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith)
      (by linarith [Real.pi_pos]))) (by norm_num)

theorem angle_gain_continuous (P : RoundingProfile) :
    ContinuousOn (angleGain P) (Set.Ioc 0 (Real.pi / 2)) := by
  have ht : ContinuousOn (fun theta : ℝ => Real.tan (theta / 2))
      (Set.Ioc 0 (Real.pi / 2)) := by
    intro theta htheta
    apply ContinuousAt.continuousWithinAt
    apply (Real.continuousAt_tan.mpr ?_).comp (by fun_prop)
    exact (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, htheta.1],
      by linarith [Real.pi_pos, htheta.2]⟩).ne'
  have hm : Set.MapsTo (fun theta : ℝ => Real.tan (theta / 2))
      (Set.Ioc 0 (Real.pi / 2)) (Set.Ioi 0) := by
    intro theta htheta
    exact Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith [htheta.1])
      (by linarith [Real.pi_pos, htheta.2])
  exact ((profile_gain_continuous P).comp ht hm).div_const 2

theorem angle_gain_monotone (P : RoundingProfile) :
    MonotoneOn (angleGain P) (Set.Ioc 0 (Real.pi / 2)) := by
  intro a ha b hb hab
  have hta := Real.tan_pos_of_pos_of_lt_pi_div_two (show 0 < a / 2 by linarith [ha.1])
    (show a / 2 < Real.pi / 2 by linarith [ha.2, Real.pi_pos])
  have htb := Real.tan_pos_of_pos_of_lt_pi_div_two (show 0 < b / 2 by linarith [hb.1])
    (show b / 2 < Real.pi / 2 by linarith [hb.2, Real.pi_pos])
  have hm := Real.strictMonoOn_tan.monotoneOn
    (show a / 2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) by
      constructor <;> linarith [ha.1, ha.2, Real.pi_pos])
    (show b / 2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) by
      constructor <;> linarith [hb.1, hb.2, Real.pi_pos])
    (show a / 2 ≤ b / 2 by linarith)
  exact div_le_div_of_nonneg_right (profile_gain_monotone P hta htb hm) (by norm_num)

/-- The two-sided angle bound is needed, rather than only alpha ≥ theta. -/
theorem wedge_slope_bounds (alpha theta : ℝ)
    (htheta : 0 < theta) (hupper : theta ≤ Real.pi / 2)
    (hlower : theta ≤ alpha) (halphaUpper : alpha ≤ Real.pi - theta) :
    Real.tan (theta / 2) ≤ (Real.tan (alpha / 2))⁻¹ ∧
      (Real.tan (alpha / 2))⁻¹ ≤ (Real.tan (theta / 2))⁻¹ := by
  have hp := Real.pi_pos
  have ht : theta / 2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  have ha : alpha / 2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  have hc : Real.pi / 2 - alpha / 2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  constructor
  · rw [← Real.tan_pi_div_two_sub]
    exact Real.strictMonoOn_tan.monotoneOn ht hc (by linarith)
  · exact inv_le_inv₀ (Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith) ha.2)
      (Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith) ht.2) |>.mpr
      (Real.strictMonoOn_tan.monotoneOn ht ha (by linarith))

theorem profile_gain_dominates_twice_angle_gain
    (P : RoundingProfile) (alpha theta : ℝ)
    (htheta : 0 < theta) (hupper : theta ≤ Real.pi / 2)
    (hlower : theta ≤ alpha) (halphaUpper : alpha ≤ Real.pi - theta) :
    2 * angleGain P theta ≤ profileGain P ((Real.tan (alpha / 2))⁻¹) := by
  have ht := Real.tan_pos_of_pos_of_lt_pi_div_two (show 0 < theta / 2 by linarith)
    (show theta / 2 < Real.pi / 2 by linarith [Real.pi_pos])
  have hb := (wedge_slope_bounds alpha theta htheta hupper hlower halphaUpper).1
  have h := profile_gain_monotone P ht (lt_of_lt_of_le ht hb) hb
  unfold angleGain
  linarith

/-- Equation (32), with the actual expression for F_s in (31).
The profile and its derivative are evaluated at the same t. -/
theorem profile_longitudinal_derivative_bound
    (slope slopeDerivative eta etaDerivative t profileValue profileDerivative : ℝ)
    (ht : |t| ≤ 1) (hprofileLower : 0 ≤ profileValue)
    (hprofileUpper : profileValue ≤ 1) (hderivative : |profileDerivative| ≤ 1) :
    (eta * slopeDerivative * profileValue +
      slope * etaDerivative * (profileValue - t * profileDerivative)) ^ 2 ≤
      2 * eta ^ 2 * slopeDerivative ^ 2 + 8 * slope ^ 2 * etaDerivative ^ 2 := by
  have ht2 : t ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one t).2 ht
  have hd2 : profileDerivative ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one profileDerivative).2 hderivative
  have hp2 : profileValue ^ 2 ≤ 1 := by nlinarith
  have htd : |t * profileDerivative| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul ht hderivative (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have hdiff : |profileValue - t * profileDerivative| ≤ 2 := by
    calc
      _ ≤ |profileValue| + |t * profileDerivative| := abs_sub _ _
      _ ≤ 2 := by rw [abs_of_nonneg hprofileLower]; linarith
  have hdiff2 : (profileValue - t * profileDerivative) ^ 2 ≤ 4 := by
    have := (sq_le_sq₀ (abs_nonneg (profileValue - t * profileDerivative))
      (show (0 : ℝ) ≤ 2 by norm_num)).mpr hdiff
    norm_num only [sq_abs] at this ⊢
    exact this
  have h1 := mul_le_mul_of_nonneg_left hp2 (sq_nonneg (eta * slopeDerivative))
  have h2 := mul_le_mul_of_nonneg_left hdiff2 (sq_nonneg (slope * etaDerivative))
  nlinarith [sq_nonneg (eta * slopeDerivative * profileValue -
    slope * etaDerivative * (profileValue - t * profileDerivative))]

/-- The lower-bound density in (34), with every error term present. -/
def roundingDensity (gain slope slopeDerivative eta etaDerivative sheetBound metricBound : ℝ) : ℝ :=
  eta * (gain - 2 * eta ^ 2 * slopeDerivative ^ 2 - 8 * slope ^ 2 * etaDerivative ^ 2 -
    sheetBound * eta - 6 * metricBound * eta * (1 + slope ^ 2))

/-- Equation (35)'s width bound. At slopeDerivative = 0 its infinite entry can
be replaced by the reach entry, which is already part of the minimum.
Positive sheet/metric bounds can always be chosen by enlarging geometric bounds. -/
noncomputable def roundingWidthCeiling
    (g0 slope slopeDerivative reach boundaryDistance sheetBound metricBound : ℝ) : ℝ :=
  min (reach / (2 * Real.sqrt (1 + slope ^ 2)))
    (min (if slopeDerivative = 0 then reach / (2 * Real.sqrt (1 + slope ^ 2))
      else Real.sqrt (g0 / (8 * slopeDerivative ^ 2)))
      (min (g0 / (4 * sheetBound))
        (min (g0 / (24 * metricBound * (1 + slope ^ 2))) (boundaryDistance / 2))))

noncomputable def roundingDerivativeCeiling (g0 slope : ℝ) : ℝ :=
  Real.sqrt g0 / (6 * slope)

theorem rounding_ceilings_positive
    (g0 slope slopeDerivative reach boundaryDistance sheetBound metricBound : ℝ)
    (hg0 : 0 < g0) (hslope : 0 < slope) (hreach : 0 < reach)
    (hboundary : 0 < boundaryDistance) (hsheet : 0 < sheetBound) (hmetric : 0 < metricBound) :
    0 < roundingWidthCeiling g0 slope slopeDerivative reach boundaryDistance sheetBound metricBound ∧
      0 < roundingDerivativeCeiling g0 slope := by
  have hroot : 0 < Real.sqrt (1 + slope ^ 2) := Real.sqrt_pos.2 (by positivity)
  unfold roundingWidthCeiling roundingDerivativeCeiling
  constructor
  · apply lt_min
    · positivity
    · apply lt_min
      · split_ifs with h
        · positivity
        · exact Real.sqrt_pos.2 (div_pos hg0 (mul_pos (by norm_num)
            (sq_pos_of_ne_zero h)))
      · apply lt_min
        · positivity
        · apply lt_min <;> positivity
  · positivity

/-- Numerical content of (35): three errors cost g₀/4 each; the derivative error costs 2g₀/9. -/
theorem admissible_rounding_bounds_control_errors
    (g0 slope slopeDerivative reach boundaryDistance sheetBound metricBound eta etaDerivative : ℝ)
    (hg0 : 0 < g0) (hslope : 0 < slope) (hreach : 0 < reach)
    (hboundary : 0 < boundaryDistance) (hsheet : 0 < sheetBound) (hmetric : 0 < metricBound)
    (heta : 0 < eta)
    (hwidth : eta ≤ roundingWidthCeiling g0 slope slopeDerivative reach boundaryDistance sheetBound metricBound)
    (hderivative : |etaDerivative| ≤ roundingDerivativeCeiling g0 slope) :
    2 * eta ^ 2 * slopeDerivative ^ 2 ≤ g0 / 4 ∧
      8 * slope ^ 2 * etaDerivative ^ 2 ≤ 2 * g0 / 9 ∧
      sheetBound * eta ≤ g0 / 4 ∧
      6 * metricBound * eta * (1 + slope ^ 2) ≤ g0 / 4 := by
  unfold roundingWidthCeiling at hwidth
  have hw := (le_min_iff.mp (le_min_iff.mp hwidth).2).2
  have hsheetWidth := (le_min_iff.mp hw).1
  have hmetricWidth := (le_min_iff.mp (le_min_iff.mp hw).2).1
  have hs : sheetBound * eta ≤ g0 / 4 := by
    have := (le_div_iff₀ (show 0 < 4 * sheetBound by positivity)).mp hsheetWidth
    nlinarith
  have hm : 6 * metricBound * eta * (1 + slope ^ 2) ≤ g0 / 4 := by
    have := (le_div_iff₀ (show 0 < 24 * metricBound * (1 + slope ^ 2) by positivity)).mp
      hmetricWidth
    nlinarith
  have hf : 2 * eta ^ 2 * slopeDerivative ^ 2 ≤ g0 / 4 := by
    by_cases hsd : slopeDerivative = 0
    · simp only [hsd, zero_pow (by decide : 2 ≠ 0), mul_zero]
      positivity
    · have hw' := (le_min_iff.mp (le_min_iff.mp hwidth).2).1
      simp only [hsd, ↓reduceIte] at hw'
      have hden : 0 < 8 * slopeDerivative ^ 2 := by positivity
      have hsq := (sq_le_sq₀ heta.le (Real.sqrt_nonneg _)).mpr hw'
      rw [Real.sq_sqrt (div_nonneg hg0.le hden.le)] at hsq
      have := (le_div_iff₀ hden).mp hsq
      nlinarith
  have hd : 8 * slope ^ 2 * etaDerivative ^ 2 ≤ 2 * g0 / 9 := by
    unfold roundingDerivativeCeiling at hderivative
    have hh := (le_div_iff₀ (show 0 < 6 * slope by positivity)).mp hderivative
    have hsq := (sq_le_sq₀ (show 0 ≤ |etaDerivative| * (6 * slope) by positivity)
      (Real.sqrt_nonneg g0)).mpr hh
    rw [Real.sq_sqrt hg0.le, mul_pow, sq_abs] at hsq
    nlinarith
  exact ⟨hf, hd, hs, hm⟩

/-- The exact 35/36 error total in Appendix B.1 gives strictly more than g₀η. -/
theorem rounding_density_lower_bound
    (gain g0 slope slopeDerivative eta etaDerivative sheetBound metricBound : ℝ)
    (hg0 : 0 < g0) (heta : 0 < eta) (hgain : 2 * g0 ≤ gain)
    (hfirst : 2 * eta ^ 2 * slopeDerivative ^ 2 ≤ g0 / 4)
    (hsecond : 8 * slope ^ 2 * etaDerivative ^ 2 ≤ 2 * g0 / 9)
    (hthird : sheetBound * eta ≤ g0 / 4)
    (hfourth : 6 * metricBound * eta * (1 + slope ^ 2) ≤ g0 / 4) :
    g0 * eta < roundingDensity gain slope slopeDerivative eta etaDerivative sheetBound metricBound := by
  unfold roundingDensity
  have h : g0 < gain - 2 * eta ^ 2 * slopeDerivative ^ 2 -
      8 * slope ^ 2 * etaDerivative ^ 2 - sheetBound * eta -
      6 * metricBound * eta * (1 + slope ^ 2) := by linarith
  simpa [mul_comm] using mul_lt_mul_of_pos_left h heta

/-- Lemma 5.4(4)'s integral estimate restricted to a measurable good subset.
All variables remain pointwise functions; no constant-width specialization is made. -/
theorem restricted_rounding_integral_lower_bound
    {Curve : Type*} [MeasurableSpace Curve]
    (mu : Measure Curve) [IsFiniteMeasure mu]
    (theta eta : Curve → ℝ) (g0 : ℝ → ℝ) (good : Set Curve)
    (hgood : MeasurableSet good)
    (htheta : ∀ x, theta x ∈ Set.Ioc 0 (Real.pi / 2))
    (heta : ∀ x, 0 ≤ eta x)
    (hg0 : ∀ t ∈ Set.Ioc 0 (Real.pi / 2), 0 ≤ g0 t)
    (hmonotone : MonotoneOn g0 (Set.Ioc 0 (Real.pi / 2)))
    (hintegrable : Integrable (fun x => g0 (theta x) * eta x) mu)
    (thetaOne etaOne : ℝ)
    (hthetaOne : thetaOne ∈ Set.Ioc 0 (Real.pi / 2)) (hetaOne : 0 ≤ etaOne)
    (hlowerAngle : ∀ x ∈ good, thetaOne ≤ theta x)
    (hlowerWidth : ∀ x ∈ good, etaOne ≤ eta x) :
    g0 thetaOne * etaOne * (mu good).toReal ≤
      ∫ x in good, g0 (theta x) * eta x ∂mu ∧
    (∫ x in good, g0 (theta x) * eta x ∂mu) ≤ ∫ x, g0 (theta x) * eta x ∂mu := by
  have hn : ∀ x, 0 ≤ g0 (theta x) * eta x := fun x =>
    mul_nonneg (hg0 _ (htheta x)) (heta x)
  constructor
  · have hc : IntegrableOn (fun _ : Curve => g0 thetaOne * etaOne) good mu :=
      integrableOn_const (measure_ne_top _ _)
    have hi := setIntegral_mono_on hc hintegrable.integrableOn hgood
      (fun x hx => mul_le_mul (hmonotone hthetaOne (htheta x) (hlowerAngle x hx))
        (hlowerWidth x hx) hetaOne (hg0 _ (htheta x)))
    simpa [setIntegral_const, Measure.real, smul_eq_mul, mul_comm, mul_left_comm,
      mul_assoc] using hi
  · exact setIntegral_le_integral hintegrable (Filter.Eventually.of_forall hn)

/-- The purely analytic passage from (34)--(35) to (13). All densities are
integrable real functions; geometric area comparison with these densities is open. -/
theorem integrated_rounding_density_bound
    {Curve : Type*} [MeasurableSpace Curve] (mu : Measure Curve)
    (gain g0 slope slopeDerivative eta etaDerivative sheetBound metricBound : Curve → ℝ)
    (hgain : ∀ x, 2 * g0 x ≤ gain x)
    (hg0 : ∀ x, 0 < g0 x) (heta : ∀ x, 0 < eta x)
    (hfirst : ∀ x, 2 * (eta x) ^ 2 * (slopeDerivative x) ^ 2 ≤ g0 x / 4)
    (hsecond : ∀ x, 8 * (slope x) ^ 2 * (etaDerivative x) ^ 2 ≤ 2 * g0 x / 9)
    (hthird : ∀ x, sheetBound x * eta x ≤ g0 x / 4)
    (hfourth : ∀ x, 6 * metricBound x * eta x * (1 + (slope x) ^ 2) ≤ g0 x / 4)
    (hlowerIntegrable : Integrable (fun x => g0 x * eta x) mu)
    (hdensityIntegrable : Integrable (fun x => roundingDensity (gain x) (slope x)
      (slopeDerivative x) (eta x) (etaDerivative x) (sheetBound x) (metricBound x)) mu) :
    (∫ x, g0 x * eta x ∂mu) ≤
      ∫ x, roundingDensity (gain x) (slope x) (slopeDerivative x)
        (eta x) (etaDerivative x) (sheetBound x) (metricBound x) ∂mu := by
  exact integral_mono hlowerIntegrable hdensityIntegrable fun x =>
    (rounding_density_lower_bound _ _ _ _ _ _ _ _ (hg0 x) (heta x)
      (hgain x) (hfirst x) (hsecond x) (hthird x) (hfourth x)).le

/-- Lemma 5.5's cost can be chosen after every positive fixed gain, for any finite real C. -/
theorem exists_small_push_off_parameter
    (sigmaZero C epsilon : ℝ) (hsigmaZero : 0 < sigmaZero) (hepsilon : 0 < epsilon) :
    ∃ sigma : ℝ, 0 < sigma ∧ sigma ≤ sigmaZero ∧ C * sigma < epsilon := by
  refine ⟨min sigmaZero (epsilon / (|C| + 1)) / 2, ?_, ?_, ?_⟩
  · exact div_pos (lt_min hsigmaZero (div_pos hepsilon (by positivity))) (by norm_num)
  · have := min_le_left sigmaZero (epsilon / (|C| + 1))
    linarith [lt_min hsigmaZero (div_pos hepsilon (show 0 < |C| + 1 by positivity))]
  · have hs : 0 < min sigmaZero (epsilon / (|C| + 1)) :=
      lt_min hsigmaZero (div_pos hepsilon (by positivity))
    have hh := (le_div_iff₀ (show 0 < |C| + 1 by positivity)).mp
      (min_le_right sigmaZero (epsilon / (|C| + 1)))
    have hc := le_abs_self C
    nlinarith [mul_nonneg (sub_nonneg.mpr hc) hs.le]

/-- Combining genuine area functions with fixed rounding gain and a later push-off.
This only selects a parameter from the given cost estimate, and does not produce surfaces. -/
theorem choose_push_off_preserving_gain
    (pushedArea : ℝ → ℝ) (roundedArea originalArea gain C sigmaZero : ℝ)
    (hgain : 0 < gain) (hthreshold : 0 < sigmaZero)
    (hrounding : roundedArea ≤ originalArea - gain)
    (hcost : ∀ sigma : ℝ, 0 < sigma → sigma ≤ sigmaZero →
      pushedArea sigma - roundedArea ≤ C * sigma) :
    ∃ sigma : ℝ, 0 < sigma ∧ sigma ≤ sigmaZero ∧
      pushedArea sigma < originalArea - gain / 2 := by
  obtain ⟨sigma, hs, ht, hc⟩ := exists_small_push_off_parameter sigmaZero C (gain / 2)
    hthreshold (by positivity)
  refine ⟨sigma, hs, ht, ?_⟩
  have := hcost sigma hs ht
  linarith

/-- Two independently obtained Lemma 5.5 thresholds and constants permit one
common later parameter. The constants are quantified before sigma. -/
theorem exists_common_push_off_parameter
    (sigmaUp sigmaDown CUp CDown epsilon : ℝ)
    (hup : 0 < sigmaUp) (hdown : 0 < sigmaDown) (hepsilon : 0 < epsilon) :
    ∃ sigma : ℝ, 0 < sigma ∧ sigma ≤ sigmaUp ∧ sigma ≤ sigmaDown ∧
      (CUp + CDown) * sigma < epsilon := by
  obtain ⟨sigma, hs, ht, hc⟩ := exists_small_push_off_parameter (min sigmaUp sigmaDown)
    (CUp + CDown) epsilon (lt_min hup hdown) hepsilon
  exact ⟨sigma, hs, ht.trans (min_le_left _ _), ht.trans (min_le_right _ _), hc⟩

/-- Proposition 5.7(1)'s elementary finite-order consequence, once its analytic
gradient estimate has genuinely been produced from the elliptic equation. -/
theorem finite_order_gradient_bound_excludes_punctured_critical_points
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (p : E) (m : ℕ) (cOne cTwo radius : ℝ)
    (hm : 1 ≤ m) (hcOne : 0 < cOne) (hcTwo : 0 < cTwo) (hradius : 0 < radius)
    (hsmooth : DifferentiableOn ℝ f (Metric.ball p radius))
    (hbound : ∀ x, 0 < dist x p → dist x p < radius →
      cOne * (dist x p) ^ m - cTwo * (dist x p) ^ (m + 1) ≤ ‖fderiv ℝ f x‖) :
    ∃ smallerRadius : ℝ, 0 < smallerRadius ∧ smallerRadius ≤ radius ∧
      ∀ x, 0 < dist x p → dist x p < smallerRadius → fderiv ℝ f x ≠ 0 := by
  refine ⟨min radius (cOne / cTwo), lt_min hradius (div_pos hcOne hcTwo),
    min_le_left _ _, ?_⟩
  intro x hx hxr hz
  have hd : dist x p < cOne / cTwo := hxr.trans_le (min_le_right _ _)
  have hb := hbound x hx (hxr.trans_le (min_le_left _ _))
  rw [hz, norm_zero, pow_succ] at hb
  have hh : cTwo * dist x p < cOne := by
    simpa [mul_comm] using (lt_div_iff₀ hcTwo).mp hd
  have := mul_pos (pow_pos hx m) (sub_pos.mpr hh)
  nlinarith

/-- Proposition 5.7(3)'s compactness deduction. Closedness is indispensable:
isolated points can otherwise accumulate outside the tangency set. -/
theorem compact_closed_isolated_subset_finite
    {X : Type*} [MetricSpace X] (carrier tangencies : Set X)
    (hcompact : IsCompact carrier) (hclosed : IsClosed tangencies)
    (hsubset : tangencies ⊆ carrier)
    (hisolated : ∀ p ∈ tangencies, ∃ epsilon : ℝ, 0 < epsilon ∧
      Metric.ball p epsilon ∩ tangencies ⊆ {p}) :
    tangencies.Finite := by
  apply (hcompact.of_isClosed_subset hclosed hsubset).finite
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro p hp
  obtain ⟨e, he, hsub⟩ := hisolated p hp
  refine ⟨Metric.ball p e, Metric.isOpen_ball, Set.Subset.antisymm hsub ?_⟩
  intro x hx
  have : x = p := Set.mem_singleton_iff.mp hx
  subst x
  exact ⟨Metric.mem_ball_self he, hp⟩

end SeifertSurfaces.Section5.Analysis
