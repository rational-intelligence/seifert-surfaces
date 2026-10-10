import NativeCutoffMinimum
import LocalizationBasic

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.QuasilinearLocalization.Helpers
set_option autoImplicit false
set_option maxHeartbeats 0

private theorem native_annular_cutoff_uniform :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (a : E2) (s t : ℝ), 0 < s → s < t →
      ∃ chi : E2 → ℝ, ContDiff ℝ ∞ chi ∧ HasCompactSupport chi ∧
        tsupport chi ⊆ Metric.ball a t ∧
        (∀ z, 0 ≤ chi z ∧ chi z ≤ 1) ∧
        (∀ z ∈ Metric.ball a s, chi z = 1 ∧ planarGradient chi z = 0) ∧
        (∀ z, ‖planarGradient chi z‖ ≤ D / (t - s)) := by
  let b : ℝ → ℝ := Real.smoothTransition
  have hb : ContDiff ℝ ∞ b := Real.smoothTransition.contDiff
  have hdout (x : ℝ) (hx : x ∉ Icc (0 : ℝ) 1) : deriv b x = 0 := by
    have he : b =ᶠ[𝓝 x] (fun _ => if x < 0 then 0 else 1) := by
      by_cases h : x < 0
      · filter_upwards [eventually_lt_nhds h] with y hy
        simp only [if_pos h]
        exact Real.smoothTransition.zero_of_nonpos hy.le
      · have hx' : 1 < x := lt_of_not_ge (fun hx1 => hx ⟨le_of_not_gt h, hx1⟩)
        filter_upwards [eventually_gt_nhds hx'] with y hy
        simp only [if_neg h]
        exact Real.smoothTransition.one_of_one_le hy.le
    rw [he.deriv_eq, deriv_const]
  have hdc : HasCompactSupport (deriv b) :=
    HasCompactSupport.intro' isCompact_Icc isClosed_Icc hdout
  obtain ⟨C, hC⟩ := (hb.continuous_deriv (by simp)).bounded_above_of_compact_support hdc
  have hC0 : 0 ≤ C := (norm_nonneg (deriv b 0)).trans (hC 0)
  refine ⟨4 * C, by positivity, ?_⟩
  intro a s t hs hst
  let rho : ℝ := (s + t) / 2
  let den : ℝ := rho ^ 2 - s ^ 2
  have hsr : s < rho := by dsimp [rho]; linarith
  have hrt : rho < t := by dsimp [rho]; linarith
  have hr : 0 < rho := hs.trans hsr
  have hd : 0 < den := by dsimp [den]; nlinarith
  let q : E2 → ℝ := fun z => (rho ^ 2 - ‖z - a‖ ^ 2) / den
  let chi : E2 → ℝ := fun z => b (q z)
  have hq : ContDiff ℝ ∞ q :=
    (contDiff_const.sub ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))).div_const den
  have hc : ContDiff ℝ ∞ chi := hb.comp hq
  have hzero (z : E2) (hz : z ∉ Metric.closedBall a rho) : chi z = 0 := by
    have hz' : rho < ‖z - a‖ := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    apply Real.smoothTransition.zero_of_nonpos
    dsimp [q]
    apply div_nonpos_of_nonpos_of_nonneg _ hd.le
    nlinarith [norm_nonneg (z - a)]
  have hkc : HasCompactSupport chi :=
    HasCompactSupport.intro' (isCompact_closedBall a rho) Metric.isClosed_closedBall hzero
  have hks : tsupport chi ⊆ Metric.ball a t := by
    have hsc : tsupport chi ⊆ Metric.closedBall a rho := by
      apply closure_minimal _ Metric.isClosed_closedBall
      intro z hz
      by_contra hn
      exact hz (hzero z hn)
    exact hsc.trans (Metric.closedBall_subset_ball hrt)
  have hgrad (z : E2) : fderiv ℝ chi z =
      (deriv b (q z) * (-2 / den)) • innerSL ℝ (z - a) := by
    have htrans := (hasFDerivAt_id (𝕜 := ℝ) z).sub_const a
    have hsq := (hasStrictFDerivAt_norm_sq (z - a)).hasFDerivAt.comp z htrans
    have hqq : HasFDerivAt q
        (den⁻¹ • (-(2 • innerSL ℝ (z - a)) ∘L ContinuousLinearMap.id ℝ E2)) z := by
      simpa [q, Function.comp_def, div_eq_mul_inv] using
        (hsq.const_sub (rho ^ 2)).mul_const den⁻¹
    have hcomp := (hb.differentiable (by simp) (q z)).hasDerivAt.comp_hasFDerivAt z hqq
    change fderiv ℝ (b ∘ q) z = _
    rw [hcomp.fderiv]
    ext v
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.zero_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul, innerSL_apply_apply,
      ContinuousLinearMap.compSL_apply, ContinuousLinearMap.neg_apply]
    ring
  refine ⟨chi, hc, hkc, hks, fun z => ⟨Real.smoothTransition.nonneg _,
    Real.smoothTransition.le_one _⟩, ?_, ?_⟩
  · intro z hz
    have hz' : ‖z - a‖ < s := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    have hq1 : 1 < q z := by
      dsimp [q]
      apply (lt_div_iff₀ hd).mpr
      dsimp [den]
      nlinarith [norm_nonneg (z - a)]
    have heq : chi =ᶠ[𝓝 z] (fun _ => (1 : ℝ)) := by
      filter_upwards [hq.continuous.continuousAt.eventually (eventually_gt_nhds hq1)] with y hy
      exact Real.smoothTransition.one_of_one_le hy.le
    refine ⟨heq.eq_of_nhds, ?_⟩
    unfold planarGradient
    rw [heq.fderiv_eq]
    simp
  · intro z
    have hnorm : ‖planarGradient chi z‖ = ‖fderiv ℝ chi z‖ := by
      rw [← gradient_dual chi z, (InnerProductSpace.toDual ℝ E2).norm_map]
    rw [hnorm, hgrad]
    by_cases hinside : q z ∈ Icc (0 : ℝ) 1
    · have hzr : ‖z - a‖ ≤ rho := by
        have hqq : 0 ≤ rho ^ 2 - ‖z - a‖ ^ 2 :=
          by simpa only [zero_mul] using (le_div_iff₀ hd).mp hinside.1
        nlinarith [norm_nonneg (z - a)]
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_div, abs_neg,
        abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hd, innerSL_apply_norm]
      have hd2 : den * 4 = 2 * (t - s) * (rho + s) := by dsimp [den, rho]; ring
      have htsp : 0 < t - s := sub_pos.mpr hst
      calc
        |deriv b (q z)| * (2 / den) * ‖z - a‖ ≤ C * (2 / den) * rho := by
          gcongr
          simpa only [Real.norm_eq_abs] using hC (q z)
        _ ≤ 4 * C / (t - s) := by
          apply (le_div_iff₀ htsp).mpr
          rw [show C * (2 / den) * rho * (t - s) =
            (2 * C * rho * (t - s)) / den by ring]
          apply (div_le_iff₀ hd).mpr
          have he : 4 * C * den = C * (2 * (t - s) * (rho + s)) := by nlinarith [hd2]
          rw [he]
          have hcs : 0 ≤ C * s := mul_nonneg hC0 hs.le
          nlinarith [mul_nonneg hcs htsp.le]
    · rw [hdout _ hinside]
      simp only [zero_mul, zero_smul, norm_zero]
      positivity

#print axioms native_annular_cutoff_uniform
