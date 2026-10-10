import Mathlib

/-!
# Analytic obligations extracted from Appendix B

Source: `/home/caoyichuan/test/seifert-surfaces/references/seifert-surfaces.txt`,
Appendix B, printed pages 28--39. These are analytic helper statements, not
substitutes for the geometric lemmas. The reviewed theorem statements are proved
in this scratch candidate for the approved C-infinity snapshot.
-/

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace SeifertSurfaces.AppendixB

/-- Independent topological support: preserving a frontier point outside a tube
precludes strict containment in an open region. The printed Lemma 5.4(2)
asserts containment in closure(U), which this helper does not refute. -/
theorem frontier_agreement_prevents_open_inclusion {X : Type*}
    [TopologicalSpace X] (U rounded tube : Set X) (hU : IsOpen U)
    (hagreement : ∀ x, x ∉ tube → (x ∈ rounded ↔ x ∈ frontier U))
    (houtside : ∃ x ∈ frontier U, x ∉ tube) :
    ¬ rounded ⊆ U := by
  intro h
  obtain ⟨x, hx, hxt⟩ := houtside
  have hxr := (hagreement x hxt).2 hx
  have hxu := h hxr
  have hxi : x ∈ interior U := by simpa [hU.interior_eq] using hxu
  exact hx.2 hxi

/-- The odd cutoff chosen in the first paragraph of B.1, extended smoothly to ℝ.
The plateau begins strictly before 1, as required by “χ ≡ 1 near 1”. -/
structure RoundingCutoff where
  χ : ℝ → ℝ
  smooth : ContDiff ℝ ∞ χ
  odd : ∀ t, χ (-t) = -χ t
  zero : χ 0 = 0
  positive_side : ∀ t, 0 ≤ t → 0 ≤ χ t ∧ χ t ≤ 1
  plateau : ∃ b ∈ Ioo (0 : ℝ) 1, ∀ t, b ≤ t → χ t = 1

/-- The actual primitive formula in B.1; it is not an unspecified profile. -/
noncomputable def roundingProfile (c : RoundingCutoff) (t : ℝ) : ℝ :=
  (1 - ∫ u in (0 : ℝ)..1, c.χ u) + ∫ u in (0 : ℝ)..t, c.χ u

/-- B.1, Θ′ = χ. -/
theorem roundingProfile_hasDerivAt (c : RoundingCutoff) (t : ℝ) :
    HasDerivAt (roundingProfile c) (c.χ t) t := by
  have hc := c.smooth.continuous
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add _

/-- B.1, smoothness of the primitive. -/
theorem roundingProfile_smooth (c : RoundingCutoff) :
    ContDiff ℝ ∞ (roundingProfile c) := by
  apply contDiff_infty_iff_deriv.mpr
  constructor
  · intro t
    exact (roundingProfile_hasDerivAt c t).differentiableAt
  · have hd : deriv (roundingProfile c) = c.χ := funext fun t =>
      (roundingProfile_hasDerivAt c t).deriv
    rw [hd]
    exact c.smooth

/-- B.1, Θ is even. -/
theorem roundingProfile_even (c : RoundingCutoff) (t : ℝ) :
    roundingProfile c (-t) = roundingProfile c t := by
  have h := intervalIntegral.integral_comp_neg (f := c.χ) (a := 0) (b := t)
  simp only [c.odd, intervalIntegral.integral_neg, neg_zero] at h
  have h₁ := intervalIntegral.integral_symm (μ := volume) (f := c.χ) (a := -t) (b := 0)
  unfold roundingProfile
  linarith

/-- B.1, Θ ≥ |·|, including both sides of the interval. -/
theorem roundingProfile_majorizes_abs (c : RoundingCutoff) (t : ℝ) :
    |t| ≤ roundingProfile c t := by
  have hp : ∀ u : ℝ, 0 ≤ u → u ≤ roundingProfile c u := by
    intro u hu
    obtain ⟨b, hb, hplateau⟩ := c.plateau
    by_cases hu1 : u ≤ 1
    · have hc := c.smooth.continuous
      have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        (hc.intervalIntegrable 0 u) (hc.intervalIntegrable u 1)
      have hle := intervalIntegral.integral_mono_on (μ := volume) hu1 (hc.intervalIntegrable u 1)
        ((continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).intervalIntegrable u 1)
        (fun z hz => (c.positive_side z (hu.trans hz.1)).2)
      simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one] at hle
      unfold roundingProfile
      linarith
    · have hu1' : 1 ≤ u := by linarith
      have hc := c.smooth.continuous
      have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        (hc.intervalIntegrable 0 1) (hc.intervalIntegrable 1 u)
      have hi : (∫ z in (1 : ℝ)..u, c.χ z) = u - 1 := by
        calc
          (∫ z in (1 : ℝ)..u, c.χ z) = ∫ z in (1 : ℝ)..u, (1 : ℝ) := by
            apply intervalIntegral.integral_congr
            intro z hz
            exact hplateau z (hb.2.le.trans ((uIcc_of_le hu1') ▸ hz).1)
          _ = _ := by simp
      unfold roundingProfile
      linarith
  by_cases ht : 0 ≤ t
  · simpa [abs_of_nonneg ht] using hp t ht
  · have h := hp (-t) (by linarith)
    rw [roundingProfile_even] at h
    simpa [abs_of_neg (lt_of_not_ge ht)] using h

/-- B.1, 0 ≤ Θ ≤ 1 on the replacement interval. -/
theorem roundingProfile_bounds (c : RoundingCutoff) (t : ℝ)
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    0 ≤ roundingProfile c t ∧ roundingProfile c t ≤ 1 := by
  have hp := roundingProfile_majorizes_abs c t
  refine ⟨(abs_nonneg t).trans hp, ?_⟩
  have hu : |t| ≤ 1 := abs_le.mpr ht
  have hc := c.smooth.continuous
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 |t|) (hc.intervalIntegrable |t| 1)
  have hnon := intervalIntegral.integral_nonneg (μ := volume) hu
    (fun z hz => (c.positive_side z ((abs_nonneg t).trans hz.1)).1)
  have he : roundingProfile c |t| = roundingProfile c t := by
    rcases le_or_gt 0 t with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, roundingProfile_even]
  unfold roundingProfile at he ⊢
  linarith

/-- B.1, matching to |·| actually holds on a neighborhood of each seam.
This also records why strict separation on the entire open tube is not a
property of the source's explicit profile. -/
theorem roundingProfile_matches_abs_near_seams (c : RoundingCutoff) :
    ∃ b ∈ Ioo (0 : ℝ) 1, ∀ t, b ≤ |t| → roundingProfile c t = |t| := by
  obtain ⟨b, hb, hplateau⟩ := c.plateau
  refine ⟨b, hb, ?_⟩
  intro t ht
  have hc := c.smooth.continuous
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 1) (hc.intervalIntegrable 1 |t|)
  have hi : (∫ z in (1 : ℝ)..|t|, c.χ z) = |t| - 1 := by
    calc
      (∫ z in (1 : ℝ)..|t|, c.χ z) = ∫ z in (1 : ℝ)..|t|, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro z hz
        exact hplateau z ((le_min hb.2.le ht).trans hz.1)
      _ = _ := by simp
  have he : roundingProfile c |t| = |t| := by
    unfold roundingProfile
    linarith
  rcases le_or_gt 0 t with h | h
  · simpa [abs_of_nonneg h] using he
  · simpa [abs_of_neg h, roundingProfile_even] using he

/-- B.1, the cutoff has absolute value at most 1, including negative t. -/
theorem roundingCutoff_abs_le_one (c : RoundingCutoff) (t : ℝ) :
    |c.χ t| ≤ 1 := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg (c.positive_side t ht).1]
    exact (c.positive_side t ht).2
  · have hp := c.positive_side (-t) (by linarith)
    rw [c.odd] at hp
    rw [abs_of_nonpos (by linarith : c.χ t ≤ 0)]
    linarith

/-- B.1, the flat-slice gain g(m), with Θ′ replaced by its exact value χ. -/
noncomputable def profileGain (c : RoundingCutoff) (m : ℝ) : ℝ :=
  ∫ t in (-1 : ℝ)..1,
    Real.sqrt (1 + m ^ 2) - Real.sqrt (1 + m ^ 2 * (c.χ t) ^ 2)

/-- Continuity of the exact density difference at one fixed slope. -/
lemma gainIntegrand_continuous (c : RoundingCutoff) (m : ℝ) :
    Continuous (fun t => Real.sqrt (1 + m ^ 2) - Real.sqrt (1 + m ^ 2 * (c.χ t) ^ 2)) := by
  exact continuous_const.sub ((continuous_const.add
    (continuous_const.mul (c.smooth.continuous.pow 2))).sqrt)

/-- The cutoff bound makes the density difference nonnegative on every slice. -/
lemma gainIntegrand_nonnegative (c : RoundingCutoff) (m t : ℝ) :
    0 ≤ Real.sqrt (1 + m ^ 2) - Real.sqrt (1 + m ^ 2 * (c.χ t) ^ 2) := by
  apply sub_nonneg.mpr
  apply Real.sqrt_le_sqrt
  have hχ : (c.χ t) ^ 2 ≤ 1 := by
    simpa using (sq_le_sq.mpr (show |c.χ t| ≤ |(1 : ℝ)| by simpa using roundingCutoff_abs_le_one c t))
  nlinarith [mul_nonneg (sq_nonneg m) (sub_nonneg.mpr hχ)]

/-- A global integral bound used to prove both normalized endpoint limits. -/
lemma profileGain_bounds (c : RoundingCutoff) (m : ℝ) :
    0 ≤ profileGain c m ∧ profileGain c m ≤ 2 * Real.sqrt (1 + m ^ 2) := by
  constructor
  · exact intervalIntegral.integral_nonneg_of_forall (by norm_num) (gainIntegrand_nonnegative c m)
  · have h := intervalIntegral.integral_mono_on (μ := volume) (a := (-1 : ℝ)) (b := 1)
      (by norm_num) ((gainIntegrand_continuous c m).intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _)
      (fun t _ => sub_le_self _ (Real.sqrt_nonneg _))
    norm_num [profileGain] at h ⊢
    exact h

/-- Increasing the nonnegative slope increases the gain when the squared cutoff
value lies in the unit interval. -/
lemma sqrt_difference_monotone (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    MonotoneOn (fun m : ℝ => Real.sqrt (1 + m ^ 2) - Real.sqrt (1 + m ^ 2 * q)) (Ici 0) := by
  let d := fun m : ℝ => m / Real.sqrt (1 + m ^ 2) - m * q / Real.sqrt (1 + m ^ 2 * q)
  have hd : ∀ m : ℝ, HasDerivAt
      (fun m : ℝ => Real.sqrt (1 + m ^ 2) - Real.sqrt (1 + m ^ 2 * q)) (d m) m := by
    intro m
    have hA : 0 < 1 + m ^ 2 := by positivity
    have hB : 0 < 1 + m ^ 2 * q := by positivity
    convert (((hasDerivAt_id m).pow 2).const_add 1).sqrt hA.ne' |>.sub
      (((((hasDerivAt_id m).pow 2).mul_const q).const_add 1).sqrt hB.ne') using 1
    · funext y; simp only [Pi.sub_apply]; congr 1
    · dsimp [d]; ring
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    (by fun_prop) (fun m _ => (hd m).hasDerivWithinAt)
  intro m hm
  have hm0 : 0 ≤ m := (interior_subset hm : m ∈ Ici (0 : ℝ))
  have hA : 0 < Real.sqrt (1 + m ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hB : 0 < Real.sqrt (1 + m ^ 2 * q) := Real.sqrt_pos.mpr (by positivity)
  have hsA := Real.sq_sqrt (show 0 ≤ 1 + m ^ 2 by positivity)
  have hsB := Real.sq_sqrt (show 0 ≤ 1 + m ^ 2 * q by positivity)
  have hq2 : q ^ 2 ≤ q := by nlinarith
  have hrad : q * Real.sqrt (1 + m ^ 2) ≤ Real.sqrt (1 + m ^ 2 * q) := by
    apply (sq_le_sq₀ (by positivity) hB.le).mp
    have hp := mul_le_mul_of_nonneg_right hq2 (show 0 ≤ 1 + m ^ 2 by positivity)
    nlinarith
  dsimp [d]
  apply sub_nonneg.mpr
  apply (div_le_div_iff₀ hB hA).mpr
  nlinarith [mul_nonneg hm0 (sub_nonneg.mpr hrad)]

/-- B.1, strict positivity uses χ(0) = 0, not strict positivity at every t. -/
theorem profileGain_pos (c : RoundingCutoff) (m : ℝ) (hm : 0 < m) :
    0 < profileGain c m := by
  apply intervalIntegral.integral_pos (by norm_num) (gainIntegrand_continuous c m).continuousOn
    (fun t _ => gainIntegrand_nonnegative c m t)
  refine ⟨0, by norm_num, ?_⟩
  simp only [c.zero, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero, Real.sqrt_one]
  have h : 1 < Real.sqrt (1 + m ^ 2) := by
    have : Real.sqrt 1 < Real.sqrt (1 + m ^ 2) :=
      (Real.sqrt_lt_sqrt_iff (by norm_num : (0 : ℝ) ≤ 1)).2 (by nlinarith)
    simpa using this
  linarith

/-- B.1, parameter continuity of the integral. -/
theorem profileGain_continuous (c : RoundingCutoff) :
    Continuous (profileGain c) := by
  apply continuous_iff_continuousAt.mpr
  intro m₀
  let B := |m₀| + 1
  have hB : 0 ≤ B := by dsimp [B]; positivity
  apply intervalIntegral.continuousAt_of_dominated_interval
    (bound := fun _ => Real.sqrt (1 + B ^ 2))
  · exact Eventually.of_forall fun m => (gainIntegrand_continuous c m).aestronglyMeasurable
  · have hev : ∀ᶠ m in 𝓝 m₀, |m| < B :=
      continuous_abs.continuousAt.eventually (gt_mem_nhds (by dsimp [B]; linarith))
    filter_upwards [hev] with m hm
    exact ae_of_all _ fun t _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (gainIntegrand_nonnegative c m t)]
      apply (sub_le_self _ (Real.sqrt_nonneg _)).trans
      apply Real.sqrt_le_sqrt
      have hsq : m ^ 2 ≤ B ^ 2 := sq_le_sq.mpr (by simpa [abs_of_nonneg hB] using hm.le)
      linarith
  · exact continuous_const.intervalIntegrable _ _
  · exact ae_of_all _ fun t _ => by fun_prop

/-- B.1, g is non-decreasing for nonnegative slopes. -/
theorem profileGain_monotoneOn (c : RoundingCutoff) :
    MonotoneOn (profileGain c) (Ici (0 : ℝ)) := by
  intro a ha b hb hab
  apply intervalIntegral.integral_mono_on (by norm_num)
    ((gainIntegrand_continuous c a).intervalIntegrable _ _)
    ((gainIntegrand_continuous c b).intervalIntegrable _ _)
  intro t _
  apply sqrt_difference_monotone ((c.χ t) ^ 2) (sq_nonneg _) _ ha hb hab
  simpa using sq_le_sq.mpr (show |c.χ t| ≤ |(1 : ℝ)| by simpa using roundingCutoff_abs_le_one c t)

/-- B.1, endpoint normalization needed for g₀(θ) → 0. -/
theorem profileGain_zero (c : RoundingCutoff) :
    profileGain c 0 = 0 := by
  simp [profileGain]

/-- B.1, g₀ is the half-gain at the left endpoint of the slope interval. -/
noncomputable def angleGain (c : RoundingCutoff) (θ : ℝ) : ℝ :=
  profileGain c (Real.tan (θ / 2)) / 2

/-- B.1, the exact two-sided angle-to-slope implication. -/
theorem slope_mem_interval (θ α : ℝ) (hθ : θ ∈ Ioc (0 : ℝ) (Real.pi / 2))
    (hα : α ∈ Icc θ (Real.pi - θ)) :
    Real.cot (α / 2) ∈ Icc (Real.tan (θ / 2)) (Real.cot (θ / 2)) := by
  have hc : ∀ x : ℝ, Real.cot x = Real.tan (Real.pi / 2 - x) := by
    intro x
    rw [Real.tan_pi_div_two_sub, Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos, inv_div]
  rw [hc, hc]
  have ha : Real.pi / 2 - α / 2 ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [hα.1, hα.2, hθ.1, hθ.2, Real.pi_pos]
  constructor
  · apply Real.strictMonoOn_tan.monotoneOn
      (show θ / 2 ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) by
        constructor <;> linarith [hθ.1, hθ.2, Real.pi_pos]) ha
    linarith [hα.2]
  · apply Real.strictMonoOn_tan.monotoneOn ha
    · constructor <;> linarith [hθ.1, hθ.2, Real.pi_pos]
    · linarith [hα.1]

/-- B.1, positivity, continuity and monotonicity on the same angle domain. -/
theorem angleGain_properties (c : RoundingCutoff) :
    ContinuousOn (angleGain c) (Ioc (0 : ℝ) (Real.pi / 2)) ∧
    MonotoneOn (angleGain c) (Ioc (0 : ℝ) (Real.pi / 2)) ∧
    (∀ θ ∈ Ioc (0 : ℝ) (Real.pi / 2), 0 < angleGain c θ) ∧
    Tendsto (angleGain c) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have htan : ∀ θ ∈ Ioc (0 : ℝ) (Real.pi / 2), 0 < Real.tan (θ / 2) := by
    intro θ hθ
    apply Real.tan_pos_of_pos_of_lt_pi_div_two <;> linarith [hθ.1, hθ.2, Real.pi_pos]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro θ hθ
    have hcos : Real.cos (θ / 2) ≠ 0 := (Real.cos_pos_of_mem_Ioo (by
      constructor <;> linarith [hθ.1, hθ.2, Real.pi_pos])).ne'
    have htc : ContinuousAt (fun z : ℝ => Real.tan (z / 2)) θ :=
      (Real.continuousAt_tan.mpr hcos).comp (f := fun z : ℝ => z / 2) (by fun_prop)
    exact (((profileGain_continuous c).continuousAt.comp htc).div_const 2).continuousWithinAt
  · intro θ hθ φ hφ hθφ
    have ht := Real.strictMonoOn_tan.monotoneOn
      (show θ / 2 ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) by
        constructor <;> linarith [hθ.1, hθ.2, Real.pi_pos])
      (show φ / 2 ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) by
        constructor <;> linarith [hφ.1, hφ.2, Real.pi_pos]) (by linarith : θ / 2 ≤ φ / 2)
    exact div_le_div_of_nonneg_right (profileGain_monotoneOn c (htan θ hθ).le (htan φ hφ).le ht) (by norm_num)
  · intro θ hθ
    exact div_pos (profileGain_pos c _ (htan θ hθ)) (by norm_num)
  · have hc : ContinuousAt (angleGain c) 0 := by
      exact ((profileGain_continuous c).continuousAt.comp
        ((Real.continuousAt_tan.mpr (by simp)).comp (f := fun z : ℝ => z / 2)
          (continuousAt_id.div_const 2))).div_const 2
    have hz : angleGain c 0 = 0 := by simp [angleGain, profileGain_zero]
    simpa only [hz] using hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))

/-- B.1, the minimum formula, expressed without an unchecked real-valued infimum. -/
theorem angleGain_is_half_minimum (c : RoundingCutoff) (θ : ℝ)
    (hθ : θ ∈ Ioc (0 : ℝ) (Real.pi / 2)) :
    IsLeast ((profileGain c) ''
      Icc (Real.tan (θ / 2)) (Real.cot (θ / 2))) (2 * angleGain c θ) := by
  have hp : 0 < Real.tan (θ / 2) := Real.tan_pos_of_pos_of_lt_pi_div_two
    (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hI := slope_mem_interval θ θ hθ ⟨le_rfl, by linarith [hθ.2]⟩
  have he : 2 * angleGain c θ = profileGain c (Real.tan (θ / 2)) := by unfold angleGain; ring
  rw [he]
  refine ⟨⟨Real.tan (θ / 2), ⟨le_rfl, hI.1⟩, rfl⟩, ?_⟩
  rintro y ⟨m, hm, rfl⟩
  exact profileGain_monotoneOn c hp.le (hp.le.trans hm.1) hm.1

/-- B.1, both endpoint degenerations of the normalized gain. -/
theorem normalized_profileGain_limits (c : RoundingCutoff) :
    Tendsto (fun m => profileGain c m / (1 + m ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
    Tendsto (fun m => profileGain c m / (1 + m ^ 2)) atTop (𝓝 0) := by
  constructor
  · have hcont : ContinuousAt (fun m : ℝ => profileGain c m / (1 + m ^ 2)) 0 :=
      (profileGain_continuous c).continuousAt.div (by fun_prop) (by norm_num)
    simpa [profileGain_zero] using hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  · have htop : Tendsto (fun m : ℝ => Real.sqrt (1 + m ^ 2)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp (by
        simpa [add_comm] using tendsto_atTop_add_const_right atTop (1 : ℝ)
          (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)))
    apply squeeze_zero (fun m => div_nonneg (profileGain_bounds c m).1 (by positivity))
      (g := fun m : ℝ => 2 / Real.sqrt (1 + m ^ 2))
    · intro m
      have hs : 0 < Real.sqrt (1 + m ^ 2) := Real.sqrt_pos.mpr (by positivity)
      have hd : 0 < 1 + m ^ 2 := by positivity
      have hsq := Real.sq_sqrt hd.le
      apply (div_le_div_iff₀ hd hs).mpr
      have hp := mul_le_mul_of_nonneg_right (profileGain_bounds c m).2 hs.le
      nlinarith
    · exact tendsto_const_nhds.div_atTop htop

/-- The exact s-derivative expression in (31), with t = ξ₂/η(s). -/
noncomputable def longitudinalDerivative (c : RoundingCutoff)
    (m m' η η' t : ℝ) : ℝ :=
  η * m' * roundingProfile c t +
    m * η' * (roundingProfile c t - t * c.χ t)

/-- B.1, (31), retaining the width derivative term. -/
theorem varyingWidth_profile_derivative (c : RoundingCutoff)
    (m η : ℝ → ℝ) (s ξ m' η' : ℝ)
    (hm : HasDerivAt m m' s) (hη : HasDerivAt η η' s) (hη0 : η s ≠ 0) :
    HasDerivAt (fun z => m z * η z * roundingProfile c (ξ / η z))
      (longitudinalDerivative c (m s) m' (η s) η' (ξ / η s)) s := by
  have hd := (hm.mul hη).mul ((roundingProfile_hasDerivAt c (ξ / η s)).comp s
    ((hasDerivAt_const s ξ).div hη hη0))
  convert hd using 1
  · funext z; rfl
  · unfold longitudinalDerivative
    simp only [Function.comp_apply, Pi.mul_apply, Pi.div_apply]
    field_simp
    ring

/-- B.1, (32), the exact uniform numerical estimate on the whole normal slice. -/
theorem longitudinalDerivative_sq_le (c : RoundingCutoff)
    (m m' η η' t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
    (longitudinalDerivative c m m' η η' t) ^ 2 ≤
      2 * η ^ 2 * m' ^ 2 + 8 * m ^ 2 * η' ^ 2 := by
  obtain ⟨hΘ0, hΘ1⟩ := roundingProfile_bounds c t ht
  have ht1 : |t| ≤ 1 := abs_le.mpr ht
  have hχ1 := roundingCutoff_abs_le_one c t
  have hΘsq : roundingProfile c t ^ 2 ≤ 1 := by nlinarith
  have htc : |t * c.χ t| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul ht1 hχ1 (abs_nonneg _) (by norm_num)).trans_eq (by ring)
  have hdiff : |roundingProfile c t - t * c.χ t| ≤ 2 := by
    have := abs_sub (roundingProfile c t) (t * c.χ t)
    rw [abs_of_nonneg hΘ0] at this
    linarith
  have hdiffsq : (roundingProfile c t - t * c.χ t) ^ 2 ≤ 4 := by
    have := sq_le_sq.mpr (show |roundingProfile c t - t * c.χ t| ≤ |(2 : ℝ)| by simpa using hdiff)
    norm_num at this
    exact this
  have h1 : (η * m' * roundingProfile c t) ^ 2 ≤ η ^ 2 * m' ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg (η * m')) (sub_nonneg.mpr hΘsq)]
  have h2 : (m * η' * (roundingProfile c t - t * c.χ t)) ^ 2 ≤ 4 * m ^ 2 * η' ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg (m * η')) (sub_nonneg.mpr hdiffsq)]
  unfold longitudinalDerivative
  nlinarith [sq_nonneg (η * m' * roundingProfile c t -
    m * η' * (roundingProfile c t - t * c.χ t))]

/-- The square-root inequality used for both old and new area densities. -/
theorem sqrt_add_upper_bound (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + b / (2 * Real.sqrt a) := by
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hsq := Real.sq_sqrt ha.le
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · have hn : 0 ≤ (b / (2 * Real.sqrt a)) ^ 2 := sq_nonneg _
    have hc : Real.sqrt a * (b / (2 * Real.sqrt a)) = b / 2 := by
      field_simp
    nlinarith

/-- Old Euclidean graph area per ds; this is not curve length. -/
noncomputable def oldSliceArea (m m' η : ℝ) : ℝ :=
  ∫ ξ in (-η)..η, Real.sqrt (1 + m ^ 2 + m' ^ 2 * ξ ^ 2)

/-- New Euclidean graph area per ds, after ξ₂ = ηt. -/
noncomputable def newSliceArea (c : RoundingCutoff) (m m' η η' : ℝ) : ℝ :=
  η * ∫ t in (-1 : ℝ)..1,
    Real.sqrt (1 + m ^ 2 * (c.χ t) ^ 2 +
      (longitudinalDerivative c m m' η η' t) ^ 2)

/-- B.1, the nonnegative old-density remainder and the exact stated upper bound. -/
theorem oldSliceArea_remainder (m m' η : ℝ) (hη : 0 ≤ η) :
    0 ≤ oldSliceArea m m' η - 2 * η * Real.sqrt (1 + m ^ 2) ∧
    oldSliceArea m m' η - 2 * η * Real.sqrt (1 + m ^ 2) ≤ m' ^ 2 * η ^ 3 := by
  have hab : -η ≤ η := by linarith
  have hf : Continuous (fun ξ : ℝ => Real.sqrt (1 + m ^ 2 + m' ^ 2 * ξ ^ 2)) := by fun_prop
  have hl := intervalIntegral.integral_mono_on (μ := volume)
    (f := fun _ : ℝ => Real.sqrt (1 + m ^ 2)) hab
    (continuous_const.intervalIntegrable _ _) (hf.intervalIntegrable _ _)
    (fun ξ _ => Real.sqrt_le_sqrt (by nlinarith [mul_nonneg (sq_nonneg m') (sq_nonneg ξ)]))
  have hs0 : 0 ≤ Real.sqrt (1 + m ^ 2) := Real.sqrt_nonneg _
  have hs1 : 1 ≤ Real.sqrt (1 + m ^ 2) := by
    simpa using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + m ^ 2 by nlinarith [sq_nonneg m])
  have hs2 := Real.sq_sqrt (show 0 ≤ 1 + m ^ 2 by positivity)
  have hp : ∀ ξ ∈ Icc (-η) η, Real.sqrt (1 + m ^ 2 + m' ^ 2 * ξ ^ 2) ≤
      Real.sqrt (1 + m ^ 2) + m' ^ 2 * η ^ 2 / 2 := by
    intro ξ hξ
    have hξ2 : ξ ^ 2 ≤ η ^ 2 := sq_le_sq.mpr (by simpa [abs_of_nonneg hη] using abs_le.mpr hξ)
    have hb : 0 ≤ m' ^ 2 * η ^ 2 := by positivity
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · have hm := mul_le_mul_of_nonneg_left hξ2 (sq_nonneg m')
      have hcross := mul_le_mul_of_nonneg_right hs1 hb
      nlinarith [sq_nonneg (m' ^ 2 * η ^ 2)]
  have hu := intervalIntegral.integral_mono_on (μ := volume) hab (hf.intervalIntegrable _ _)
    (continuous_const.intervalIntegrable _ _) hp
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hl hu
  unfold oldSliceArea
  constructor <;> nlinarith

/-- B.1, Euclidean slice gain before the metric and C²-straightening errors. -/
theorem euclidean_slice_gain (c : RoundingCutoff) (m m' η η' : ℝ)
    (hη : 0 ≤ η) :
    η * (profileGain c m - 2 * η ^ 2 * m' ^ 2 - 8 * m ^ 2 * η' ^ 2) ≤
      oldSliceArea m m' η - newSliceArea c m m' η η' := by
  let E := 2 * η ^ 2 * m' ^ 2 + 8 * m ^ 2 * η' ^ 2
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hχ : Continuous (fun t : ℝ => Real.sqrt (1 + m ^ 2 * (c.χ t) ^ 2)) := by
    exact (continuous_const.add (continuous_const.mul (c.smooth.continuous.pow 2))).sqrt
  have hD : Continuous (longitudinalDerivative c m m' η η') := by
    unfold longitudinalDerivative
    exact continuous_const.mul (roundingProfile_smooth c).continuous |>.add
      (continuous_const.mul ((roundingProfile_smooth c).continuous.sub
        (continuous_id.mul c.smooth.continuous)))
  have hnew : Continuous (fun t : ℝ => Real.sqrt
      (1 + m ^ 2 * (c.χ t) ^ 2 + longitudinalDerivative c m m' η η' t ^ 2)) := by
    exact ((continuous_const.add (continuous_const.mul (c.smooth.continuous.pow 2))).add (hD.pow 2)).sqrt
  have hpoint : ∀ t ∈ Icc (-1 : ℝ) 1,
      Real.sqrt (1 + m ^ 2 * (c.χ t) ^ 2 + longitudinalDerivative c m m' η η' t ^ 2) ≤
      Real.sqrt (1 + m ^ 2 * (c.χ t) ^ 2) + E / 2 := by
    intro t ht
    have hdsq := longitudinalDerivative_sq_le c m m' η η' t ht
    have hs1 : 1 ≤ Real.sqrt (1 + m ^ 2 * (c.χ t) ^ 2) := by
      simpa using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + m ^ 2 * (c.χ t) ^ 2 by
        nlinarith [mul_nonneg (sq_nonneg m) (sq_nonneg (c.χ t))])
    have hs2 := Real.sq_sqrt (show 0 ≤ 1 + m ^ 2 * (c.χ t) ^ 2 by positivity)
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have hc := mul_le_mul_of_nonneg_right hs1 hE
    dsimp [E] at hE hc ⊢
    nlinarith [sq_nonneg E]
  have hi := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (-1 : ℝ) ≤ 1)
    (hnew.intervalIntegrable _ _) ((hχ.add continuous_const).intervalIntegrable _ _) hpoint
  simp only [Pi.add_apply] at hi
  rw [intervalIntegral.integral_add (hχ.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _),
    intervalIntegral.integral_const] at hi
  have hg : profileGain c m = 2 * Real.sqrt (1 + m ^ 2) -
      ∫ t in (-1 : ℝ)..1, Real.sqrt (1 + m ^ 2 * (c.χ t) ^ 2) := by
    unfold profileGain
    rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _) (hχ.intervalIntegrable _ _),
      intervalIntegral.integral_const]
    norm_num
  have hl := (oldSliceArea_remainder m m' η hη).1
  have hmul := mul_le_mul_of_nonneg_left hi hη
  simp only [smul_eq_mul] at hmul
  unfold newSliceArea
  dsimp [E] at hmul
  nlinarith

/-- B.1, (34)--(35). The hypotheses are exactly the four error caps
implied by (35); neither reach bound is silently used as an area estimate. -/
theorem slice_gain_from_error_caps (g g₀ m m' η η' C₁ Cmet : ℝ)
    (hg₀ : 0 ≤ g₀) (hη : 0 ≤ η) (hg : 2 * g₀ ≤ g)
    (hcurvature : 8 * η ^ 2 * m' ^ 2 ≤ g₀)
    (hwidthDerivative : 36 * m ^ 2 * η' ^ 2 ≤ g₀)
    (hstraightening : 4 * C₁ * η ≤ g₀)
    (hmetric : 24 * Cmet * η * (1 + m ^ 2) ≤ g₀) :
    g₀ * η ≤ η * (g - 2 * η ^ 2 * m' ^ 2 - 8 * m ^ 2 * η' ^ 2 -
      C₁ * η - 6 * Cmet * η * (1 + m ^ 2)) := by
  have h : g₀ ≤ g - 2 * η ^ 2 * m' ^ 2 - 8 * m ^ 2 * η' ^ 2 -
      C₁ * η - 6 * Cmet * η * (1 + m ^ 2) := by linarith
  nlinarith [mul_nonneg hη (sub_nonneg.mpr h)]

/-- B.1, κ = √g₀/(6m) produces the absolute derivative cap in (35). -/
theorem width_derivative_error_cap (g₀ m η' : ℝ) (hg₀ : 0 ≤ g₀)
    (hm : 0 < m) (hη' : |η'| ≤ Real.sqrt g₀ / (6 * m)) :
    36 * m ^ 2 * η' ^ 2 ≤ g₀ := by
  have hd : 0 < 6 * m := by positivity
  have hmul : |η'| * (6 * m) ≤ Real.sqrt g₀ := (le_div_iff₀ hd).mp hη'
  have hsq := Real.sq_sqrt hg₀
  have habs : |η'| ^ 2 = η' ^ 2 := sq_abs η'
  have hh : (|η'| * (6 * m)) ^ 2 ≤ (Real.sqrt g₀) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hmul 2
  nlinarith [hh]

/-- B.1, (11), and Corollary B.4(3)/Lemma B.5(3): common positive lower bounds
on gain and the two reaches, and common upper bounds on slopes/derivatives,
produce common width and absolute derivative caps. The index can contain both
the perturbation parameter and a point on the good part of an intersection curve.
The conclusion is ∃ η₀ κ₀, ∀ i, never ∀ i, ∃ η₀ κ₀. -/
theorem uniform_slice_caps {I : Type*}
    (g m m' reach boundaryReach : I → ℝ)
    (gmin M M' reachmin boundaryReachmin C₁ Cmet : ℝ)
    (hgmin : 0 < gmin) (hM : 0 ≤ M) (hM' : 0 ≤ M')
    (hreachmin : 0 < reachmin) (hboundaryReachmin : 0 < boundaryReachmin)
    (hC₁ : 0 ≤ C₁) (hCmet : 0 ≤ Cmet)
    (hg : ∀ i, gmin ≤ g i) (hm : ∀ i, |m i| ≤ M)
    (hm' : ∀ i, |m' i| ≤ M') (hreach : ∀ i, reachmin ≤ reach i)
    (hboundaryReach : ∀ i, boundaryReachmin ≤ boundaryReach i) :
    ∃ η₀ > 0, ∃ κ₀ > 0, ∀ i,
      η₀ ≤ reach i / (2 * Real.sqrt (1 + (m i) ^ 2)) ∧
      η₀ ≤ boundaryReach i / 2 ∧
      8 * η₀ ^ 2 * (m' i) ^ 2 ≤ g i ∧
      4 * C₁ * η₀ ≤ g i ∧
      24 * Cmet * η₀ * (1 + (m i) ^ 2) ≤ g i ∧
      36 * (m i) ^ 2 * κ₀ ^ 2 ≤ g i := by
  have h1 : ∀ᶠ a : ℝ in 𝓝 0, a < reachmin / (2 * Real.sqrt (1 + M ^ 2)) :=
    gt_mem_nhds (by positivity)
  have h2 : ∀ᶠ a : ℝ in 𝓝 0, a < boundaryReachmin / 2 := gt_mem_nhds (by positivity)
  have h3 : ∀ᶠ a : ℝ in 𝓝 0, 8 * a ^ 2 * M' ^ 2 < gmin :=
    (show ContinuousAt (fun a : ℝ => 8 * a ^ 2 * M' ^ 2) 0 by fun_prop).eventually
      (gt_mem_nhds (by simpa using hgmin))
  have h4 : ∀ᶠ a : ℝ in 𝓝 0, 4 * C₁ * a < gmin :=
    (show ContinuousAt (fun a : ℝ => 4 * C₁ * a) 0 by fun_prop).eventually
      (gt_mem_nhds (by simpa using hgmin))
  have h5 : ∀ᶠ a : ℝ in 𝓝 0, 24 * Cmet * a * (1 + M ^ 2) < gmin :=
    (show ContinuousAt (fun a : ℝ => 24 * Cmet * a * (1 + M ^ 2)) 0 by fun_prop).eventually
      (gt_mem_nhds (by simpa using hgmin))
  have h6 : ∀ᶠ a : ℝ in 𝓝 0, 36 * M ^ 2 * a ^ 2 < gmin :=
    (show ContinuousAt (fun a : ℝ => 36 * M ^ 2 * a ^ 2) 0 by fun_prop).eventually
      (gt_mem_nhds (by simpa using hgmin))
  have hall := h1.and (h2.and (h3.and (h4.and (h5.and h6))))
  obtain ⟨δ, hδ, hδcaps⟩ := Metric.mem_nhds_iff.mp hall
  let a := δ / 2
  have ha : 0 < a := by dsimp [a]; positivity
  have hmem : a ∈ Metric.ball 0 δ := by
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ha]
    dsimp [a]
    linarith
  obtain ⟨ha1, ha2, ha3, ha4, ha5, ha6⟩ := hδcaps hmem
  refine ⟨a, ha, a, ha, ?_⟩
  intro i
  have hm2 : (m i) ^ 2 ≤ M ^ 2 := sq_le_sq.mpr (by simpa [abs_of_nonneg hM] using hm i)
  have hm'2 : (m' i) ^ 2 ≤ M' ^ 2 := sq_le_sq.mpr (by simpa [abs_of_nonneg hM'] using hm' i)
  have hs : Real.sqrt (1 + (m i) ^ 2) ≤ Real.sqrt (1 + M ^ 2) := Real.sqrt_le_sqrt (by linarith)
  have hspos : 0 < Real.sqrt (1 + (m i) ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hcap : a * (2 * Real.sqrt (1 + M ^ 2)) ≤ reachmin :=
    ((lt_div_iff₀ (by positivity : 0 < 2 * Real.sqrt (1 + M ^ 2))).mp ha1).le
  refine ⟨(le_div_iff₀ (by positivity)).mpr ?_, ?_, ?_, ha4.le.trans (hg i), ?_, ?_⟩
  · have hprod := mul_le_mul_of_nonneg_left hs ha.le
    linarith [hreach i]
  · linarith [hboundaryReach i]
  · exact (mul_le_mul_of_nonneg_left hm'2 (by positivity : 0 ≤ 8 * a ^ 2)).trans
      (ha3.le.trans (hg i))
  · have hprod := mul_le_mul_of_nonneg_left (show 1 + (m i) ^ 2 ≤ 1 + M ^ 2 by linarith)
      (by positivity : 0 ≤ 24 * Cmet * a)
    exact hprod.trans (ha5.le.trans (hg i))
  · have hprod := mul_le_mul_of_nonneg_right hm2 (by positivity : 0 ≤ 36 * a ^ 2)
    nlinarith [hg i]

/-- B.1, restriction to a measurable subset keeps one and the same gain integrand.
It applies to the finite arclength measure on Γ once that measure is constructed. -/
theorem gain_on_measurable_subset {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (Z : Set X) (hZ : MeasurableSet Z)
    (g η : X → ℝ) (g₁ η₁ : ℝ) (hg₁ : 0 ≤ g₁) (hη₁ : 0 ≤ η₁)
    (hgain : Integrable (fun x => g x * η x) μ)
    (hnonnegative : ∀ x, 0 ≤ g x * η x)
    (hg : ∀ x ∈ Z, g₁ ≤ g x) (hη : ∀ x ∈ Z, η x = η₁) :
    g₁ * η₁ * (μ Z).toReal ≤ ∫ x, g x * η x ∂μ := by
  have hleft : IntegrableOn (fun _ : X => g₁ * η₁) Z μ := integrable_const _
  have hmono : (∫ x in Z, g₁ * η₁ ∂μ) ≤ ∫ x in Z, g x * η x ∂μ := by
    apply integral_mono_ae hleft hgain.integrableOn
    filter_upwards [ae_restrict_mem hZ] with x hx
    rw [hη x hx]
    exact mul_le_mul_of_nonneg_right (hg x hx) hη₁
  have hfull := setIntegral_le_integral (s := Z) hgain (ae_of_all _ hnonnegative)
  simpa [MeasureTheory.setIntegral_const, Measure.real, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
    hmono.trans hfull

/-- B.2, eˣ−1 ≤ xeˣ. -/
theorem exp_sub_one_le_mul_exp (x : ℝ) (hx : 0 ≤ x) :
    Real.exp x - 1 ≤ x * Real.exp x := by
  have h := Real.add_one_le_exp (-x)
  have hp := Real.exp_pos x
  have he : Real.exp (-x) * Real.exp x = 1 := by
    rw [← Real.exp_add]
    simp
  nlinarith [mul_nonneg (sub_nonneg.mpr h) hp.le]

/-- B.2, the push-off constant is fixed before σ, uniformly on [0, σ₀]. -/
theorem uniform_exponential_pushOff_bound (K₁ σ₀ A : ℝ)
    (hK₁ : 0 ≤ K₁) (hσ₀ : 0 ≤ σ₀) (hA : 0 ≤ A) :
    ∀ σ ∈ Icc (0 : ℝ) σ₀,
      (Real.exp (2 * K₁ * σ) - 1) * A ≤
        (2 * K₁ * Real.exp (2 * K₁ * σ₀) * A) * σ := by
  intro σ hσ
  have hs : 0 ≤ 2 * K₁ * σ := mul_nonneg (by positivity) hσ.1
  have h1 := exp_sub_one_le_mul_exp (2 * K₁ * σ) hs
  have h2 : Real.exp (2 * K₁ * σ) ≤ Real.exp (2 * K₁ * σ₀) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hσ.2 (by positivity))
  calc
    (Real.exp (2 * K₁ * σ) - 1) * A ≤
        (2 * K₁ * σ * Real.exp (2 * K₁ * σ)) * A := mul_le_mul_of_nonneg_right h1 hA
    _ ≤ (2 * K₁ * σ * Real.exp (2 * K₁ * σ₀)) * A :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hs) hA
    _ = _ := by ring

/-- B.2, integration of the logarithmic Jacobian bound. The radius σ₀ and
K are common to every x; the resulting estimate is uniform in x and σ. -/
theorem uniform_jacobian_from_log_derivative {X : Type*}
    (J : X → ℝ → ℝ) (K σ₀ : ℝ) (hK : 0 ≤ K) (hσ₀ : 0 < σ₀)
    (hJ : ∀ x, ContDiff ℝ 1 (J x))
    (hpositive : ∀ x, ∀ σ ∈ Icc (0 : ℝ) σ₀, 0 < J x σ)
    (hzero : ∀ x, J x 0 = 1)
    (hderiv : ∀ x, ∀ σ ∈ Icc (0 : ℝ) σ₀,
      |deriv (fun s => Real.log (J x s)) σ| ≤ K) :
    ∀ x, ∀ σ ∈ Icc (0 : ℝ) σ₀,
      |J x σ - 1| ≤ Real.exp (K * σ) - 1 := by
  intro x σ hσ
  have hd : ∀ s ∈ Icc (0 : ℝ) σ, HasDerivWithinAt (fun z => Real.log (J x z))
      (deriv (fun z => Real.log (J x z)) s) (Icc 0 σ) s := by
    intro s hs
    have hp := hpositive x s ⟨hs.1, hs.2.trans hσ.2⟩
    exact (((hJ x).differentiable (by norm_num)).differentiableAt.log hp.ne').hasDerivAt.hasDerivWithinAt
  have hb : ∀ s ∈ Ico (0 : ℝ) σ, ‖deriv (fun z => Real.log (J x z)) s‖ ≤ K := by
    intro s hs
    simpa [Real.norm_eq_abs] using hderiv x s ⟨hs.1, hs.2.le.trans hσ.2⟩
  have hlog := norm_image_sub_le_of_norm_deriv_le_segment' hd hb σ ⟨hσ.1, le_rfl⟩
  simp only [Real.norm_eq_abs, hzero, Real.log_one, sub_zero] at hlog
  obtain ⟨hl, hu⟩ := abs_le.mp hlog
  have hj := hpositive x σ hσ
  have hupper : J x σ ≤ Real.exp (K * σ) := by
    simpa only [Real.exp_log hj] using Real.exp_le_exp.mpr hu
  have hlower : Real.exp (-(K * σ)) ≤ J x σ := by
    simpa only [Real.exp_log hj] using Real.exp_le_exp.mpr hl
  have hexp : 1 ≤ Real.exp (K * σ) := Real.one_le_exp_iff.mpr (mul_nonneg hK hσ.1)
  have hinv : Real.exp (-(K * σ)) * Real.exp (K * σ) = 1 := by
    rw [← Real.exp_add]; simp
  have hsum : 2 ≤ Real.exp (K * σ) + Real.exp (-(K * σ)) := by
    nlinarith [sq_nonneg (Real.exp (K * σ) - 1), Real.exp_pos (K * σ)]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- B.3, a uniform small radius makes the bilinear-form coefficient coercive.
The analytic PDE existence theorem remains a separate obligation. -/
theorem small_radius_coercivity (ellipticity C b c : ℝ) (hellipticity : 0 < ellipticity)
    (hC : 0 ≤ C) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    ∃ R₀ > 0, ∀ R ∈ Ioc (0 : ℝ) R₀,
      ellipticity / 2 ≤ ellipticity - C * b * R - C ^ 2 * c * R ^ 2 := by
  have he : ∀ᶠ R : ℝ in 𝓝 0,
      ellipticity / 2 < ellipticity - C * b * R - C ^ 2 * c * R ^ 2 :=
    (show ContinuousAt (fun R : ℝ => ellipticity - C * b * R - C ^ 2 * c * R ^ 2) 0 by
      fun_prop).eventually (lt_mem_nhds (by simpa using (by linarith : ellipticity / 2 < ellipticity)))
  obtain ⟨δ, hδ, hbδ⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨δ / 2, by positivity, ?_⟩
  intro R hR
  have hmem : R ∈ Metric.ball 0 δ := by
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hR.1]
    linarith [hR.2]
  exact (hbδ hmem).le

/-- B.3, the finite-order lower estimate stays positive on one punctured
neighborhood, including its outer endpoint. -/
theorem finite_order_lower_bound (m : ℕ) (c₁ c₂ : ℝ)
    (hc₁ : 0 < c₁) (hc₂ : 0 ≤ c₂) :
    ∃ ρ₀ > 0, ∀ ρ ∈ Ioc (0 : ℝ) ρ₀,
      0 < (c₁ / 2) * ρ ^ m ∧
      (c₁ / 2) * ρ ^ m ≤ c₁ * ρ ^ m - c₂ * ρ ^ (m + 1) := by
  let ρ₀ := c₁ / (2 * (c₂ + 1))
  have hρ₀ : 0 < ρ₀ := by dsimp [ρ₀]; positivity
  refine ⟨ρ₀, hρ₀, ?_⟩
  intro ρ hρ
  have hpow : 0 < ρ ^ m := pow_pos hρ.1 _
  have hcap : c₂ * ρ ≤ c₁ / 2 := by
    have h := (le_div_iff₀ (by positivity : 0 < 2 * (c₂ + 1))).mp hρ.2
    nlinarith
  constructor
  · positivity
  · rw [pow_succ]
    nlinarith [mul_nonneg (sub_nonneg.mpr hcap) hpow.le]

/-- B.3, the product rule estimate for f = hv, before the finite-order argument. -/
theorem product_gradient_lower_bound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v' h' : E) (h v c₁ c₂ M ρ : ℝ) (m : ℕ)
    (hh : 1 / 2 ≤ h) (hρ : 0 ≤ ρ) (hc₁ : 0 ≤ c₁)
    (hc₂ : 0 ≤ c₂) (hM : 0 ≤ M)
    (hv' : c₁ * ρ ^ m ≤ ‖v'‖)
    (hv : |v| ≤ c₂ * ρ ^ (m + 1)) (hh' : ‖h'‖ ≤ M) :
    (c₁ / 2) * ρ ^ m - M * c₂ * ρ ^ (m + 1) ≤ ‖h • v' + v • h'‖ := by
  have hh0 : 0 ≤ h := by linarith
  have hb : ‖v • h'‖ ≤ M * c₂ * ρ ^ (m + 1) := by
    rw [norm_smul, Real.norm_eq_abs]
    have h1 := mul_le_mul_of_nonneg_right hv (norm_nonneg h')
    have h2 := mul_le_mul_of_nonneg_left hh' (by positivity : 0 ≤ c₂ * ρ ^ (m + 1))
    nlinarith
  have ha : (c₁ / 2) * ρ ^ m ≤ ‖h • v'‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh0]
    have h1 := mul_le_mul_of_nonneg_left hv' hh0
    have h2 := mul_le_mul_of_nonneg_right hh (by positivity : 0 ≤ c₁ * ρ ^ m)
    nlinarith
  have hn := norm_sub_norm_le (h • v') (-v • h')
  simp only [neg_smul, norm_neg, sub_neg_eq_add] at hn
  linarith

/-- B.1 in the named-lemma numbering: the radial data of the collar graph.
All derivatives exist on the same closed interval, with one Λ for the family.
The function has been smoothly extended across r = 0 for HasDerivAt. -/
structure RadialC2Family (X : Type*) where
  f : X → ℝ → ℝ
  df : X → ℝ → ℝ
  ddf : X → ℝ → ℝ
  r₀ : ℝ
  r₀_pos : 0 < r₀
  Λ : ℝ
  Λ_nonneg : 0 ≤ Λ
  zero : ∀ x, f x 0 = 0
  derivative : ∀ x, ∀ r ∈ Icc (0 : ℝ) r₀, HasDerivAt (f x) (df x r) r
  second_derivative : ∀ x, ∀ r ∈ Icc (0 : ℝ) r₀, HasDerivAt (df x) (ddf x r) r
  second_bound : ∀ x, ∀ r ∈ Icc (0 : ℝ) r₀, |ddf x r| ≤ Λ

/-- Lemma B.1, the uniform radial derivative estimate used before integration. -/
theorem radial_derivative_deviation {X : Type*} (F : RadialC2Family X)
    (x : X) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) F.r₀) :
    |F.df x r - F.df x 0| ≤ F.Λ * r := by
  have hd : ∀ z ∈ Icc 0 r, HasDerivWithinAt (F.df x) (F.ddf x z) (Icc 0 r) z := by
    intro z hz
    exact (F.second_derivative x z ⟨hz.1, hz.2.trans hr.2⟩).hasDerivWithinAt
  have hb : ∀ z ∈ Ico 0 r, ‖F.ddf x z‖ ≤ F.Λ := by
    intro z hz
    simpa [Real.norm_eq_abs] using F.second_bound x z ⟨hz.1, hz.2.le.trans hr.2⟩
  simpa [Real.norm_eq_abs] using norm_image_sub_le_of_norm_deriv_le_segment' hd hb r ⟨hr.1, le_rfl⟩

/-- Lemma B.1, choose one sign and one open neighborhood before choosing r.
The closed-arc extraction on L is a geometric step, recorded in the source map. -/
theorem uniform_radial_sign_on_neighborhood {X : Type*} [TopologicalSpace X]
    (F : RadialC2Family X) (ha : Continuous (fun x => F.df x 0))
    (x₀ : X) (hx₀ : F.df x₀ 0 ≠ 0) :
    ∃ ς : ℝ, (ς = 1 ∨ ς = -1) ∧
      ∃ U : Set X, IsOpen U ∧ x₀ ∈ U ∧
        ∃ a₀ > 0, ∃ r₁ > 0, r₁ ≤ F.r₀ / 4 ∧
          ∀ x ∈ U, ∀ r ∈ Ioc (0 : ℝ) r₁,
            (a₀ / 2) * r ≤ ς * F.f x r ∧ 0 < ς * F.f x r := by
  have hsign : ∃ ς : ℝ, (ς = 1 ∨ ς = -1) ∧ 0 < ς * F.df x₀ 0 := by
    rcases lt_or_gt_of_ne hx₀ with hn | hp
    · exact ⟨-1, Or.inr rfl, by nlinarith⟩
    · exact ⟨1, Or.inl rfl, by simpa using hp⟩
  obtain ⟨ς, hς, hpos⟩ := hsign
  let a₀ := ς * F.df x₀ 0 / 2
  have ha₀ : 0 < a₀ := by dsimp [a₀]; positivity
  let U := {x | a₀ < ς * F.df x 0}
  have hU : IsOpen U := isOpen_lt continuous_const (continuous_const.mul ha)
  have hxU : x₀ ∈ U := by dsimp [U, a₀]; linarith
  let r₁ := min (F.r₀ / 4) (a₀ / (2 * (F.Λ + 1)))
  have hr₁ : 0 < r₁ := lt_min (by have := F.r₀_pos; positivity)
    (by have := F.Λ_nonneg; positivity)
  have hr₁r : r₁ ≤ F.r₀ / 4 := min_le_left _ _
  refine ⟨ς, hς, U, hU, hxU, a₀, ha₀, r₁, hr₁, hr₁r, ?_⟩
  intro x hx r hr
  have hrr : r ≤ F.r₀ := by have := F.r₀_pos; linarith [hr.2]
  have hcap : F.Λ * r ≤ a₀ / 2 := by
    have hh := (le_div_iff₀ (by have := F.Λ_nonneg; positivity : 0 < 2 * (F.Λ + 1))).mp
      (hr.2.trans (min_le_right (F.r₀ / 4) (a₀ / (2 * (F.Λ + 1)))))
    nlinarith [F.Λ_nonneg]
  have hdf : ∀ z ∈ Icc (0 : ℝ) r, a₀ / 2 ≤ ς * F.df x z := by
    intro z hz
    have hdev := radial_derivative_deviation F x z ⟨hz.1, hz.2.trans hrr⟩
    obtain ⟨hl, hu⟩ := abs_le.mp hdev
    have hzc : F.Λ * z ≤ a₀ / 2 :=
      (mul_le_mul_of_nonneg_left hz.2 F.Λ_nonneg).trans hcap
    have hx' : a₀ < ς * F.df x 0 := hx
    rcases hς with hς | hς <;> rw [hς] at hx' ⊢ <;> nlinarith
  let q := fun z => ς * F.f x z - (a₀ / 2) * z
  have hq : ∀ z ∈ Icc (0 : ℝ) r,
      HasDerivAt q (ς * F.df x z - a₀ / 2) z := by
    intro z hz
    convert ((F.derivative x z ⟨hz.1, hz.2.trans hrr⟩).const_mul ς).sub
      ((hasDerivAt_id z).const_mul (a₀ / 2)) using 1
    · funext y; rfl
    · simp
  have hm : MonotoneOn q (Icc 0 r) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 r)
      (fun z hz => (hq z hz).continuousAt.continuousWithinAt)
      (fun z hz => (hq z (interior_subset hz)).hasDerivWithinAt)
    intro z hz
    exact sub_nonneg.mpr (hdf z (interior_subset hz))
  have hqr := hm ⟨le_rfl, hr.1.le⟩ ⟨hr.1.le, le_rfl⟩ hr.1.le
  have hlo : (a₀ / 2) * r ≤ ς * F.f x r := by simpa [q, F.zero] using hqr
  exact ⟨hlo, (mul_pos (by positivity : 0 < a₀ / 2) hr.1).trans_le hlo⟩

/-- Lemma B.1, finite boundary critical points cannot exhaust the circle.
Infinite X exposes the exact set-theoretic premise independently of the PDE. -/
theorem finite_zeros_not_identically_zero {X : Type*} [Infinite X]
    (a : X → ℝ) (ha : Set.Finite {x | a x = 0}) :
    ∃ x, a x ≠ 0 := by
  simpa only [mem_setOf_eq] using ha.exists_notMem

/-- Lemma B.3(i), the sign excludes the perturbed level in the cleared collar. -/
theorem positive_sign_excludes_opposite_level (ς f t : ℝ)
    (hς : ς = 1 ∨ ς = -1) (hf : 0 < ς * f) (ht : 0 < t) :
    f ≠ -ς * t := by
  intro heq
  rcases hς with rfl | rfl <;> subst f <;> nlinarith

/-- Corollary B.4(1), the numerical consequence of the quotient path estimate.
The quotient pseudometric and length comparison are not assumed to be built. -/
theorem collapsed_length_bound (ρ₀ ρ₂ length : ℝ) (N : ℕ)
    (hdiameter : ρ₀ / 2 ≤ length + 4 * (N : ℝ) * ρ₂)
    (hballs : 4 * (N : ℝ) * ρ₂ < ρ₀ / 8) :
    3 * ρ₀ / 8 < length := by
  linarith

/-- Corollary B.4(2), a fixed compact transverse set admits a uniform two-sided
angle bound on one fixed neighborhood. It may then be applied to moving γₜ;
proving γₜ enters this neighborhood remains a geometric obligation. -/
theorem uniform_angle_near_compact {X : Type*} [MetricSpace X]
    (K : Set X) (hK : IsCompact K) (hne : K.Nonempty)
    (α : X → ℝ) (hα : Continuous α)
    (htransverse : ∀ x ∈ K, α x ∈ Ioo (0 : ℝ) Real.pi) :
    ∃ θ ∈ Ioc (0 : ℝ) (Real.pi / 2), ∃ ζ > 0,
      ∀ x, Metric.infDist x K < ζ →
        ∀ β : ℝ, |β - α x| ≤ θ → θ ≤ min β (Real.pi - β) := by
  let f := fun x => min (α x) (Real.pi - α x)
  have hf : Continuous f := hα.min (continuous_const.sub hα)
  obtain ⟨p, hp, hmin⟩ := hK.exists_isMinOn hne hf.continuousOn
  have hpos : 0 < f p := lt_min (htransverse p hp).1 (by linarith [(htransverse p hp).2])
  let θ := min (f p / 4) (Real.pi / 2)
  have hθ : 0 < θ := lt_min (by positivity) (by positivity)
  have hθc : 4 * θ ≤ f p := by have := min_le_left (f p / 4) (Real.pi / 2); dsimp [θ]; linarith
  let U := {x | 2 * θ < f x}
  have hU : IsOpen U := isOpen_lt continuous_const hf
  have hKU : K ⊆ U := by
    intro x hx
    have hh : f p ≤ f x := hmin hx
    dsimp [U]
    linarith
  obtain ⟨ζ, hζ, hζU⟩ := hK.exists_thickening_subset_open hU hKU
  refine ⟨θ, ⟨hθ, min_le_right _ _⟩, ζ, hζ, ?_⟩
  intro x hx β hβ
  obtain ⟨y, hy, hxy⟩ := (Metric.infDist_lt_iff hne).mp hx
  have hxf := hζU (Metric.mem_thickening_iff.mpr ⟨y, hy, hxy⟩)
  have hxf1 : 2 * θ < α x := lt_of_lt_of_le hxf (min_le_left _ _)
  have hxf2 : 2 * θ < Real.pi - α x := lt_of_lt_of_le hxf (min_le_right _ _)
  obtain ⟨hβ1, hβ2⟩ := abs_le.mp hβ
  exact le_min (by linarith) (by linarith)

/-- Corollary B.4(3), the compactness ingredient behind a common positive
reach/width/derivative bound. This does not infer reach from curvature alone. -/
theorem uniform_positive_on_compact {X : Type*} [TopologicalSpace X]
    (K : Set X) (hK : IsCompact K) (f : X → ℝ)
    (hf : ContinuousOn f K) (hpositive : ∀ x ∈ K, 0 < f x) :
    ∃ c > 0, ∀ x ∈ K, c ≤ f x := by
  by_cases hn : K.Nonempty
  · obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hn hf
    exact ⟨f x, hpositive x hx, fun y hy => hmin hy⟩
  · exact ⟨1, by norm_num, fun x hx => (hn ⟨x, hx⟩).elim⟩

/-- B.1, local reach is only asserted lower semicontinuous. This compactness
helper covers that exact regularity without replacing it by continuity. -/
theorem uniform_positive_lowerSemicontinuous_on_compact {X : Type*}
    [TopologicalSpace X] (K : Set X) (hK : IsCompact K) (f : X → ℝ)
    (hf : LowerSemicontinuousOn f K) (hpositive : ∀ x ∈ K, 0 < f x) :
    ∃ c > 0, ∀ x ∈ K, c ≤ f x := by
  by_cases hn : K.Nonempty
  · obtain ⟨x, hx, hmin⟩ := hf.exists_isMinOn hn hK
    exact ⟨f x, hpositive x hx, fun y hy => hmin hy⟩
  · exact ⟨1, by norm_num, fun x hx => (hn ⟨x, hx⟩).elim⟩

/-- Equation (44). Empty bad sets contribute no restriction rather than zero;
Mathlib's real infDist to the empty set equals zero. -/
noncomputable def distanceRamp {X : Type*} [PseudoMetricSpace X]
    (ρ₂ : ℝ) (bad : Set X) (x : X) : ℝ :=
  @ite ℝ bad.Nonempty (Classical.propDecidable _)
    (min ρ₂ (Metric.infDist x bad)) ρ₂

/-- The T2 ramp uses both the same bad balls and the same forbidden collar. -/
noncomputable def collarDistanceRamp {X : Type*} [PseudoMetricSpace X]
    (ρ₂ : ℝ) (bad collar : Set X) (x : X) : ℝ :=
  min (distanceRamp ρ₂ bad x) (distanceRamp ρ₂ collar x)

/-- The unsmoothed width formula in (44); smoothing is an additional obligation. -/
noncomputable def widthRamp (η₁ η₂ κ₁ w : ℝ) : ℝ :=
  min η₁ (η₂ + κ₁ * w / 2)

/-- Equation (44), the same ramp has Lipschitz constant 1. -/
theorem distanceRamp_lipschitz {X : Type*} [PseudoMetricSpace X]
    (ρ₂ : ℝ) (bad : Set X) : LipschitzWith 1 (distanceRamp ρ₂ bad) := by
  classical
  unfold distanceRamp
  by_cases hn : bad.Nonempty
  · simp only [if_pos hn]
    exact (Metric.lipschitz_infDist_pt bad).const_min ρ₂
  · simp only [if_neg hn]
    exact (LipschitzWith.const ρ₂).weaken (by norm_num)

/-- Equation (44), adding the collar restriction keeps the same constant. -/
theorem collarDistanceRamp_lipschitz {X : Type*} [PseudoMetricSpace X]
    (ρ₂ : ℝ) (bad collar : Set X) :
    LipschitzWith 1 (collarDistanceRamp ρ₂ bad collar) := by
  unfold collarDistanceRamp
  simpa using (distanceRamp_lipschitz ρ₂ bad).min (distanceRamp_lipschitz ρ₂ collar)

/-- Equation (44), absolute slope control does not depend on η₂. -/
theorem widthRamp_lipschitz {X : Type*} [PseudoMetricSpace X]
    (w : X → ℝ) (hw : LipschitzWith 1 w)
    (η₁ η₂ κ₁ : ℝ) (hκ₁ : 0 ≤ κ₁) :
    LipschitzWith (Real.toNNReal (κ₁ / 2))
      (fun x => widthRamp η₁ η₂ κ₁ (w x)) := by
  have hk : 0 ≤ κ₁ / 2 := by positivity
  have he : (Real.toNNReal (κ₁ / 2) : ℝ) = κ₁ / 2 := Real.coe_toNNReal _ hk
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [he]
  have h := hw.dist_le_mul x y
  simp only [NNReal.coe_one, one_mul, Real.dist_eq] at h
  have hm : |κ₁ * w x / 2 - κ₁ * w y / 2| ≤ κ₁ / 2 * dist x y := by
    rw [show κ₁ * w x / 2 - κ₁ * w y / 2 = (κ₁ / 2) * (w x - w y) by ring,
      abs_mul, abs_of_nonneg hk]
    exact mul_le_mul_of_nonneg_left h hk
  have hmin := ((LipschitzWith.id.const_min η₁) : LipschitzWith 1 (fun z : ℝ => min η₁ z)).dist_le_mul
    (η₂ + κ₁ * w x / 2) (η₂ + κ₁ * w y / 2)
  simpa [widthRamp, Real.dist_eq] using hmin.trans (by simpa [Real.dist_eq] using hm)

/-- Equation (44), value and plateau checks before smoothing. -/
theorem widthRamp_values (η₁ η₂ κ₁ ρ₂ w : ℝ)
    (hη₁ : 0 < η₁) (hη₂ : 0 < η₂) (hη₂₁ : η₂ ≤ η₁)
    (hκ₁ : 0 ≤ κ₁) (hw : 0 ≤ w)
    (htransition : η₁ ≤ κ₁ * ρ₂ / 4) :
    0 < widthRamp η₁ η₂ κ₁ w ∧ widthRamp η₁ η₂ κ₁ w ≤ η₁ ∧
    (w = 0 → widthRamp η₁ η₂ κ₁ w = η₂) ∧
    (w = ρ₂ → widthRamp η₁ η₂ κ₁ w = η₁) := by
  unfold widthRamp
  refine ⟨lt_min hη₁ (by positivity), min_le_left _ _, ?_, ?_⟩
  · intro hw0
    simp [hw0, min_eq_right hη₂₁]
  · intro hwρ
    rw [hwρ, min_eq_left]
    nlinarith

/-- The T1/T2 choice η₁ = min(η₁geo, κ₁ρ₂/4), made before t. -/
theorem fixed_width_and_gain_positive (g₀ η₁geo κ₁ ρ₂ length : ℝ)
    (hg₀ : 0 < g₀) (hη₁geo : 0 < η₁geo) (hκ₁ : 0 < κ₁)
    (hρ₂ : 0 < ρ₂) (hlength : 0 < length) :
    0 < min η₁geo (κ₁ * ρ₂ / 4) ∧
    0 < g₀ * min η₁geo (κ₁ * ρ₂ / 4) * length := by
  have hw : 0 < min η₁geo (κ₁ * ρ₂ / 4) := lt_min hη₁geo (by positivity)
  exact ⟨hw, mul_pos (mul_pos hg₀ hw) hlength⟩

/-- B.4/B.5, e(t) → 0 supplies one δ excluding the disc-patch inequality for
every subsequent t. The gain ε is an argument, fixed before δ and t. -/
theorem small_error_excludes_disc_gain (e : ℝ → ℝ)
    (he : Tendsto e (𝓝[>] (0 : ℝ)) (𝓝 0)) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ t ∈ Ioc (0 : ℝ) δ,
      e t < ε ∧ ¬ ∃ Ga Gb : ℝ, ε ≤ Ga ∧ ε ≤ Gb ∧ Ga + Gb ≤ e t := by
  have hevent : ∀ᶠ t in 𝓝[>] (0 : ℝ), e t < ε := he.eventually (gt_mem_nhds hε)
  obtain ⟨δ, hδ, hbound⟩ := Metric.mem_nhdsWithin_iff.mp hevent
  refine ⟨δ / 2, by positivity, ?_⟩
  intro t ht
  have hb : e t < ε := hbound ⟨by simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos ht.1] using (by linarith [ht.2] : t < δ), ht.1⟩
  refine ⟨hb, ?_⟩
  rintro ⟨Ga, Gb, hGa, hGb, hsum⟩
  linarith

/-- B.4/B.5, the final strict area estimate with exactly the stated allowances. -/
theorem final_area_gap (A B At P ε Cσ : ℝ) (hε : 0 < ε)
    (hperturbation : At < A + ε / 2) (hpushOff : Cσ < ε / 4)
    (hfrontier : P ≤ At + B - ε + Cσ) :
    P < A + B - ε / 4 := by
  linarith

end SeifertSurfaces.AppendixB
