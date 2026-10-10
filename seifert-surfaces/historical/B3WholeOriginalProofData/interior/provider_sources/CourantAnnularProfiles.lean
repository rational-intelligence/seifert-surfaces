import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
set_option autoImplicit false
noncomputable section
open Set Topology Function MeasureTheory
open scoped ContDiff
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.CourantAnalyticB

theorem annular_square_radius_profile
    (a z : ℝ) (ha : 0 < a) (haz : a < z)
    (q : ℝ → ℝ) (hq : ContDiff ℝ ∞ q) (hqc : HasCompactSupport q)
    (hqs : tsupport q ⊆ Ioo a z) :
    let h : ℝ → ℝ := fun u => q (Real.sqrt u) / Real.sqrt u
    ContDiff ℝ ∞ h ∧ HasCompactSupport h ∧
      tsupport h ⊆ Ioo (a ^ 2) (z ^ 2) ∧
      ∀ r ∈ Ioo a z, r * h (r ^ 2) = q r := by run_tac do Lean.Elab.Tactic.evalTactic (← Lean.ofExcept (Lean.Parser.runParserCategory (← Lean.getEnv) `tactic "exact (by\n  classical\n  dsimp only\n  let h : ℝ → ℝ := fun u => q (Real.sqrt u) / Real.sqrt u\n  have hzero : ∀ u : ℝ, u < a ^ 2 → h u = 0 := by\n    intro u hu\n    have hsqrt : Real.sqrt u < a := by\n      by_cases hupos : 0 ≤ u\n      · exact (Real.sqrt_lt hupos ha.le).mpr hu\n      · rw [Real.sqrt_eq_zero_of_nonpos (le_of_lt (lt_of_not_ge hupos))]\n        exact ha\n    have hq0 : q (Real.sqrt u) = 0 := by\n      apply image_eq_zero_of_notMem_tsupport\n      intro hs\n      exact (not_lt_of_ge (hqs hs).1.le) hsqrt\n    simp only [h, hq0, zero_div]\n  have hdiff : ContDiff ℝ ∞ h := by\n    apply contDiff_iff_contDiffAt.mpr\n    intro u\n    by_cases hu : 0 < u\n    · exact (hq.contDiffAt.comp u (Real.contDiffAt_sqrt hu.ne')).div\n        (Real.contDiffAt_sqrt hu.ne') (Real.sqrt_pos.mpr hu).ne'\n    · have hlocal : Filter.EventuallyEq (𝓝 u) h (fun _ => 0) := by\n        have hua : u < a ^ 2 := lt_of_le_of_lt (le_of_not_gt hu) (sq_pos_of_pos ha)\n        filter_upwards [eventually_lt_nhds hua] with v hv\n        exact hzero v hv\n      exact contDiffAt_const.congr_of_eventuallyEq hlocal\n  let K : Set ℝ := (fun r : ℝ => r ^ 2) '' tsupport q\n  have hK : IsCompact K := hqc.image (continuous_id.pow 2)\n  have hsupp : support h ⊆ K := by\n    intro u hu\n    have hqne : q (Real.sqrt u) ≠ 0 := by\n      intro hq0\n      exact hu (by simp only [h, hq0, zero_div])\n    have hs : Real.sqrt u ∈ tsupport q := subset_tsupport q hqne\n    have hupos : 0 ≤ u := by\n      by_contra hnot\n      rw [Real.sqrt_eq_zero_of_nonpos (le_of_lt (lt_of_not_ge hnot))] at hs\n      exact (not_lt_of_ge ha.le) (hqs hs).1\n    exact ⟨Real.sqrt u, hs, Real.sq_sqrt hupos⟩\n  have htsupp : tsupport h ⊆ K := closure_minimal hsupp hK.isClosed\n  have hsub : K ⊆ Ioo (a ^ 2) (z ^ 2) := by\n    rintro u ⟨r, hr, rfl⟩\n    obtain ⟨har, hrz⟩ := hqs hr\n    have hrpos : 0 < r := lt_trans ha har\n    exact ⟨by nlinarith, by nlinarith⟩\n  refine ⟨hdiff, HasCompactSupport.of_support_subset_isCompact hK hsupp,\n    htsupp.trans hsub, ?_⟩\n  intro r hr\n  have hrpos : 0 < r := lt_trans ha hr.1\n  rw [Real.sqrt_sq hrpos.le]\n  exact mul_div_cancel₀ (q r) hrpos.ne'\n\n)"))

theorem annular_square_radius_tests_detect
    (a z : ℝ) (ha : 0 < a) (haz : a < z)
    (v : ℝ → ℝ) (hv : LocallyIntegrableOn v (Ioo a z) volume) :
    (∀ h : ℝ → ℝ, ContDiff ℝ ∞ h → HasCompactSupport h →
      tsupport h ⊆ Ioo (a ^ 2) (z ^ 2) →
      IntegrableOn (fun r => r * h (r ^ 2) * v r) (Ioo a z) volume) ∧
    ((∀ h : ℝ → ℝ, ContDiff ℝ ∞ h → HasCompactSupport h →
      tsupport h ⊆ Ioo (a ^ 2) (z ^ 2) →
      (∫ r in Ioo a z, r * h (r ^ 2) * v r) = 0) →
      ∀ᵐ r ∂volume.restrict (Ioo a z), v r = 0) := by
  classical
  constructor
  · intro h hh hhc hhs
    let K : Set ℝ := Real.sqrt '' tsupport h
    have hK : IsCompact K := hhc.image Real.continuous_sqrt
    have hKs : K ⊆ Ioo a z := by
      rintro r ⟨u, hu, rfl⟩
      have hu' := hhs hu
      have huz : 0 < z := lt_trans ha haz
      exact ⟨(Real.lt_sqrt ha.le).mpr hu'.1,
        (Real.sqrt_lt (le_trans (sq_nonneg a) hu'.1.le) huz.le).mpr hu'.2⟩
    have hc : Continuous (fun r : ℝ => r * h (r ^ 2)) :=
      continuous_id.mul (hh.continuous.comp (continuous_id.pow 2))
    have hi : IntegrableOn (fun r => r * h (r ^ 2) * v r) K volume :=
      IntegrableOn.continuousOn_mul hc.continuousOn
        (hv.integrableOn_compact_subset hKs hK) hK
    have hind : Integrable (K.indicator (fun r => r * h (r ^ 2) * v r)) volume :=
      (integrable_indicator_iff hK.measurableSet).mpr hi
    apply hind.integrableOn.congr_fun _ measurableSet_Ioo
    intro r hr
    by_cases hrK : r ∈ K
    · exact indicator_of_mem hrK _
    · rw [indicator_of_notMem hrK]
      have hh0 : h (r ^ 2) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hs
        apply hrK
        exact ⟨r ^ 2, hs, Real.sqrt_sq (le_of_lt (lt_trans ha hr.1))⟩
      change 0 = r * h (r ^ 2) * v r
      rw [hh0, mul_zero, zero_mul]
  · intro hvanish
    apply (ae_restrict_iff' measurableSet_Ioo).mpr
    apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hv
    intro q hq hqc hqs
    obtain ⟨hd, hdc, hds, he⟩ := annular_square_radius_profile a z ha haz q hq hqc hqs
    have hzero := hvanish (fun u => q (Real.sqrt u) / Real.sqrt u) hd hdc hds
    have heq : (∫ r in Ioo a z, r * (q (Real.sqrt (r ^ 2)) / Real.sqrt (r ^ 2)) * v r) =
        ∫ r in Ioo a z, q r • v r := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro r hr
      change r * (q (Real.sqrt (r ^ 2)) / Real.sqrt (r ^ 2)) * v r = q r * v r
      rw [he r hr]
    rw [heq] at hzero
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioo a z)]
    · exact hzero
    · intro r hr
      have hq0 : q r = 0 := image_eq_zero_of_notMem_tsupport (fun hs => hr (hqs hs))
      rw [hq0, zero_smul]

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.CourantAnalyticB
