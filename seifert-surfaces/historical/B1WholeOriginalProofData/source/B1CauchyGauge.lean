import B1TangencyFiniteOrder
set_option maxHeartbeats 0
noncomputable section
open Set Topology Function MeasureTheory
open scoped Manifold ContDiff BigOperators NNReal ENNReal

namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.CauchyGauge

def literalCauchyPotential (R : ℝ) (a : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1 / (Real.pi : ℂ)) * ∫ ζ in Metric.ball (0 : ℂ) R, a ζ / (z - ζ)

def cauchyExponent (p : ℝ) : ℝ≥0 := Real.toNNReal (1 - 2 / p)

def WeakDbarIdentityOn (U : Set ℂ) (omega a : ℂ → ℂ) : Prop :=
  ∀ φ : ℂ → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
    IntegrableOn (fun z => omega z * dbarTest φ z) U ∧
    IntegrableOn (fun z => a z * φ z) U ∧
    (∫ z in U, omega z * dbarTest φ z) = -(∫ z in U, a z * φ z)

theorem literal_Cauchy_potential_bounded_holder_weak_dbar (R : ℝ) (hR : 0 < R)
    (p : ℝ) (hp : 2 < p) (a : ℂ → ℂ)
    (ha : MemLp a (ENNReal.ofReal p) (volume.restrict (Metric.ball (0 : ℂ) R))) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ Metric.ball (0 : ℂ) R,
      ‖literalCauchyPotential R a z‖ ≤ C) ∧
    (0 < cauchyExponent p ∧ cauchyExponent p < 1 ∧
      (cauchyExponent p : ℝ) = 1 - 2 / p) ∧
    (∃ C : ℝ≥0, HolderOnWith C (cauchyExponent p)
      (literalCauchyPotential R a) (Metric.ball (0 : ℂ) R)) ∧
    WeakDbarIdentityOn (Metric.ball (0 : ℂ) R) (literalCauchyPotential R a) a := by run_tac do Lean.Elab.Tactic.evalTactic (← Lean.ofExcept (Lean.Parser.runParserCategory (← Lean.getEnv) `tactic "set_option linter.style.haveILetI false in\nset_option linter.unusedSimpArgs false in\nset_option linter.unnecessarySeqFocus false in\nset_option linter.unusedTactic false in\nexact (by\n  have compact_test_inverse_kernel_annulus : ∀ (φ : ℂ → ℂ)\n    (hφ : ContDiff ℝ ∞ φ) (hcompact : HasCompactSupport φ)\n    (ζ : ℂ) (L ε : ℝ) (hε : 0 < ε) (hεL : ε < L)\n    (hsupport : tsupport φ ⊆ Metric.ball ζ L),\n    IntegrableOn (fun z : ℂ => (z - ζ)⁻¹ * dbarTest φ z)\n      {z : ℂ | ε < ‖z - ζ‖ ∧ ‖z - ζ‖ < L} (volume : Measure ℂ) ∧\n    (∫ z in {z : ℂ | ε < ‖z - ζ‖ ∧ ‖z - ζ‖ < L},\n      (z - ζ)⁻¹ * dbarTest φ z ∂(volume : Measure ℂ)) =\n      -(1 / 2 : ℂ) * ∫ t in (-Real.pi)..Real.pi,\n        φ (ζ + (ε : ℂ) * ((Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I)) := by\n    intro φ hφ hcompact ζ L ε hε hεL hsupport\n    classical\n    have polar : ∀ (f : ℂ → ℂ) (ζ : ℂ) (L ε : ℝ) (hε : 0 < ε),\n        (∫ z in {z : ℂ | ε < ‖z - ζ‖ ∧ ‖z - ζ‖ < L}, f z) =\n        ∫ p in Set.Ioo ε L ×ˢ Set.Ioo (-Real.pi) Real.pi,\n          p.1 • f (ζ + Complex.polarCoord.symm p)\n        := by\n      intro f ζ L ε hε\n      let S : Set ℂ := {z | ε < ‖z - ζ‖ ∧ ‖z - ζ‖ < L}\n      let Q : Set (ℝ × ℝ) := Set.Ioo ε L ×ˢ Set.Ioo (-Real.pi) Real.pi\n      have hs : MeasurableSet S :=\n        (isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).measurableSet.inter\n          (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const).measurableSet\n      have hq : MeasurableSet Q := measurableSet_Ioo.prod measurableSet_Ioo\n      have hsub : Q ⊆ polarCoord.target := by\n        intro p hp\n        exact ⟨lt_trans hε hp.1.1,hp.2⟩\n      calc\n        (∫ z in S, f z) = ∫ z, S.indicator f z := (integral_indicator hs).symm\n        _ = ∫ z, S.indicator f (ζ + z) := (integral_add_left_eq_self _ ζ).symm\n        _ = ∫ p in polarCoord.target, p.1 • S.indicator f (ζ + Complex.polarCoord.symm p) :=\n          (Complex.integral_comp_polarCoord_symm _).symm\n        _ = ∫ p in polarCoord.target, Q.indicator\n            (fun p => p.1 • f (ζ + Complex.polarCoord.symm p)) p := by\n          apply setIntegral_congr_fun polarCoord.open_target.measurableSet\n          intro p hp\n          have he : ζ + Complex.polarCoord.symm p ∈ S ↔ p ∈ Q := by\n            change (ε < ‖ζ + Complex.polarCoord.symm p - ζ‖ ∧\n              ‖ζ + Complex.polarCoord.symm p - ζ‖ < L) ↔\n              ((ε < p.1 ∧ p.1 < L) ∧ (-Real.pi < p.2 ∧ p.2 < Real.pi))\n            rw [add_sub_cancel_left,Complex.norm_polarCoord_symm,abs_of_pos (show 0 < p.1 from hp.1)]\n            exact ⟨fun h => ⟨h,hp.2⟩,fun h => h.1⟩\n          change p.1 • S.indicator f (ζ + Complex.polarCoord.symm p) = _\n          by_cases h : p ∈ Q\n          · rw [indicator_of_mem h,indicator_of_mem (he.mpr h)]\n          · rw [indicator_of_notMem h,indicator_of_notMem (mt he.mp h),smul_zero]\n        _ = ∫ p in polarCoord.target ∩ Q, p.1 • f (ζ + Complex.polarCoord.symm p) := by\n          rw [setIntegral_indicator hq]\n        _ = ∫ p in Q, p.1 • f (ζ + Complex.polarCoord.symm p) := by\n          rw [inter_eq_right.mpr hsub]\n    have differentiate : ∀ (φ : ℂ → ℂ) (hφ : ContDiff ℝ ∞ φ) (ζ : ℂ),\n        let e : ℝ → ℂ := fun t => (Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I\n        let q : ℝ × ℝ → ℂ := fun p => φ (ζ + (p.1 : ℂ) * e p.2)\n        let Fr : ℝ × ℝ → ℂ := fun p => fderiv ℝ φ (ζ + (p.1 : ℂ) * e p.2) (e p.2)\n        let Ft : ℝ × ℝ → ℂ := fun p => fderiv ℝ φ (ζ + (p.1 : ℂ) * e p.2)\n          ((p.1 : ℂ) * (-(Real.sin p.2 : ℂ) + (Real.cos p.2 : ℂ) * Complex.I))\n        Continuous Fr ∧ Continuous Ft ∧\n        (∀ r t : ℝ, HasDerivAt (fun r => q (r,t)) (Fr (r,t)) r) ∧\n        (∀ r t : ℝ, HasDerivAt (fun t => q (r,t)) (Ft (r,t)) t) ∧\n        (∀ r t : ℝ, r ≠ 0 →\n          r • (((r : ℂ) * e t)⁻¹ * dbarTest φ (ζ + (r : ℂ) * e t)) =\n          (1/2 : ℂ) * (Fr (r,t) + (Complex.I / (r : ℂ)) * Ft (r,t)))\n        := by\n      intro φ hφ ζ\n      dsimp only\n      let e : ℝ → ℂ := fun t => (Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I\n      have he : Continuous e :=\n        (Complex.continuous_ofReal.comp Real.continuous_cos).add\n          ((Complex.continuous_ofReal.comp Real.continuous_sin).mul continuous_const)\n      have hc : Continuous (fun p : ℝ × ℝ => ζ + (p.1 : ℂ) * e p.2) :=\n        continuous_const.add ((Complex.continuous_ofReal.comp continuous_fst).mul (he.comp continuous_snd))\n      have hd := (hφ.continuous_fderiv (by simp)).comp hc\n      have hrot : Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) *\n          (-(Real.sin p.2 : ℂ) + (Real.cos p.2 : ℂ) * Complex.I)) := by fun_prop\n      refine ⟨hd.clm_apply (he.comp continuous_snd),hd.clm_apply hrot,?_,?_,?_⟩\n      · intro r t\n        have hr : HasDerivAt (fun r : ℝ => ζ + (r : ℂ) * e t) (e t) r := by\n          simpa using (((hasDerivAt_id r).ofReal_comp).mul_const (e t)).const_add ζ\n        exact (hφ.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt r hr\n      · intro r t\n        have ht : HasDerivAt (fun t : ℝ => ζ + (r : ℂ) * e t)\n            ((r : ℂ) * (-(Real.sin t : ℂ) + (Real.cos t : ℂ) * Complex.I)) t := by\n          simpa [e] using ((((Real.hasDerivAt_cos t).ofReal_comp).add\n            ((Real.hasDerivAt_sin t).ofReal_comp.mul_const Complex.I)).const_mul (r : ℂ)).const_add ζ\n        exact (hφ.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t ht\n      · intro r t hr\n        let D := fderiv ℝ φ (ζ + (r : ℂ) * e t)\n        have de : D (e t) = (Real.cos t : ℂ) * D 1 + (Real.sin t : ℂ) * D Complex.I := by\n          have hv : e t = (Real.cos t) • (1 : ℂ) + (Real.sin t) • Complex.I := by\n            simp [e,Complex.real_smul]\n          rw [hv,map_add,map_smul,map_smul]\n          simp only [Complex.real_smul]\n        have dr : D ((r : ℂ) * (-(Real.sin t : ℂ) + (Real.cos t : ℂ) * Complex.I)) =\n            (r : ℂ) * (-(Real.sin t : ℂ) * D 1 + (Real.cos t : ℂ) * D Complex.I) := by\n          have hv : (r : ℂ) * (-(Real.sin t : ℂ) + (Real.cos t : ℂ) * Complex.I) =\n              r • ((-Real.sin t) • (1 : ℂ) + (Real.cos t) • Complex.I) := by\n            simp only [Complex.real_smul, Complex.ofReal_neg, mul_one]\n          rw [hv,map_smul,map_add,map_smul,map_smul]\n          simp only [Complex.real_smul,Complex.ofReal_neg]\n        have hein : (e t)⁻¹ = (Real.cos t : ℂ) - (Real.sin t : ℂ) * Complex.I := by\n          apply inv_eq_of_mul_eq_one_left\n          have ht : (Real.cos t : ℂ)^2 + (Real.sin t : ℂ)^2 = 1 := by\n            exact_mod_cast Real.cos_sq_add_sin_sq t\n          dsimp [e]\n          calc\n            _ = (Real.cos t : ℂ)^2 + (Real.sin t : ℂ)^2 := by\n              linear_combination -(Real.sin t : ℂ)^2 * Complex.I_sq\n            _ = 1 := ht\n        change r • (((r : ℂ) * e t)⁻¹ * ((1/2 : ℂ) * (D 1 + Complex.I * D Complex.I))) = _\n        change _ = (1/2 : ℂ) * (D (e t) + (Complex.I / (r : ℂ)) *\n          D ((r : ℂ) * (-(Real.sin t : ℂ) + (Real.cos t : ℂ) * Complex.I)))\n        rw [de,dr,mul_inv_rev,hein,Complex.real_smul]\n        have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr\n        field_simp (disch := first | assumption | positivity | norm_num | (apply ne_of_gt; linarith) | (norm_cast; assumption) | (apply mul_ne_zero <;> assumption))\n        ring_nf\n        simp [Complex.I_sq]\n    have rectangle : ∀ (q Fr Ft : ℝ × ℝ → ℂ) (hFr : Continuous Fr) (hFt : Continuous Ft)\n      (hdR : ∀ r t, HasDerivAt (fun r => q (r,t)) (Fr (r,t)) r)\n      (hdT : ∀ r t, HasDerivAt (fun t => q (r,t)) (Ft (r,t)) t)\n      (L ε : ℝ) (hε : 0 < ε) (hεL : ε < L)\n      (hperiod : ∀ r, q (r,Real.pi) = q (r,-Real.pi))\n      (houter : ∀ t, q (L,t) = 0),\n        (∫ p in Ioo ε L ×ˢ Ioo (-Real.pi) Real.pi,\n          (1/2 : ℂ) * (Fr p + Complex.I / (p.1 : ℂ) * Ft p)) =\n          -(1/2 : ℂ) * ∫ t in (-Real.pi)..Real.pi, q (ε,t)\n        := by\n      intro q Fr Ft hFr hFt hdR hdT L ε hε hεL hperiod houter\n      let Q := Ioo ε L ×ˢ Ioo (-Real.pi) Real.pi\n      let K := Icc ε L ×ˢ Icc (-Real.pi) Real.pi\n      let H : ℝ × ℝ → ℂ := fun p => Complex.I / (p.1 : ℂ) * Ft p\n      have hQK : Q ⊆ K := prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self\n      have hp : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]\n      have hFrint : IntegrableOn Fr Q :=\n        (ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)\n          (hFr.continuousOn : ContinuousOn Fr K)).mono_set hQK\n      have hHint : IntegrableOn H Q := by\n        apply (ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)\n          (f := H) ?_).mono_set hQK\n        apply ContinuousOn.mul _ hFt.continuousOn\n        apply ContinuousOn.div continuousOn_const\n          (Complex.continuous_ofReal.comp continuous_fst).continuousOn\n        intro p hp\n        exact Complex.ofReal_ne_zero.mpr (ne_of_gt (hε.trans_le hp.1.1))\n      have hrad : (∫ p in Q, Fr p) = -(∫ t in (-Real.pi)..Real.pi, q (ε,t)) := by\n        have hswapint : IntegrableOn (fun p : ℝ × ℝ => Fr p.swap)\n            (Ioo (-Real.pi) Real.pi ×ˢ Ioo ε L) :=\n          (ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)\n            (hFr.comp continuous_swap).continuousOn).mono_set\n              (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)\n        calc\n          (∫ p in Q, Fr p) = ∫ p in Ioo (-Real.pi) Real.pi ×ˢ Ioo ε L, Fr p.swap := by\n            simpa only [Measure.volume_eq_prod] using\n              (setIntegral_prod_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))\n                (Ioo ε L) (Ioo (-Real.pi) Real.pi) Fr).symm\n          _ = ∫ t in Ioo (-Real.pi) Real.pi, ∫ r in Ioo ε L, Fr (r,t) :=\n            setIntegral_prod _ hswapint\n          _ = ∫ t in Ioo (-Real.pi) Real.pi, -(q (ε,t)) := by\n            apply setIntegral_congr_fun measurableSet_Ioo\n            intro t ht\n            change (∫ r in Ioo ε L, Fr (r,t)) = -q (ε,t)\n            rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le hεL.le]\n            rw [intervalIntegral.integral_eq_sub_of_hasDerivAt\n              (fun r hr => hdR r t) ((hFr.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _)]\n            rw [houter,zero_sub]\n          _ = -(∫ t in (-Real.pi)..Real.pi, q (ε,t)) := by\n            rw [integral_neg,intervalIntegral.integral_of_le hp,integral_Ioc_eq_integral_Ioo]\n      have hang : (∫ p in Q, H p) = 0 := by\n        have hfub := setIntegral_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)) H\n          (s := Ioo ε L) (t := Ioo (-Real.pi) Real.pi)\n          (by simpa only [Measure.volume_eq_prod] using hHint)\n        rw [← Measure.volume_eq_prod] at hfub\n        rw [show (∫ p in Q, H p) = _ from hfub]\n        have hz : ∀ r ∈ Ioo ε L, (∫ t in Ioo (-Real.pi) Real.pi, H (r,t)) = 0 := by\n          intro r hr\n          change (∫ t in Ioo (-Real.pi) Real.pi, (Complex.I / (r : ℂ)) * Ft (r,t)) = 0\n          rw [integral_const_mul,← integral_Ioc_eq_integral_Ioo,\n            ← intervalIntegral.integral_of_le hp]\n          rw [intervalIntegral.integral_eq_sub_of_hasDerivAt\n            (fun t ht => hdT r t) ((hFt.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)]\n          rw [hperiod,sub_self,mul_zero]\n        calc\n          _ = ∫ _r in Ioo ε L, (0 : ℂ) := setIntegral_congr_fun measurableSet_Ioo hz\n          _ = 0 := integral_zero _ _\n      change (∫ p in Q, (1/2 : ℂ) * (Fr p + H p)) = _\n      rw [integral_const_mul,integral_add hFrint hHint,hrad,hang,add_zero]\n      ring\n    let f : ℂ → ℂ := fun z => (z - ζ)⁻¹ * dbarTest φ z\n    let S : Set ℂ := {z | ε < ‖z - ζ‖ ∧ ‖z - ζ‖ < L}\n    let K : Set ℂ := Metric.closedBall ζ L \\ Metric.ball ζ ε\n    have hKd : IsCompact K := (isCompact_closedBall ζ L).diff Metric.isOpen_ball\n    have hnz (z : ℂ) (hz : z ∈ K) : z - ζ ≠ 0 := by\n      have hlow : ε ≤ ‖z - ζ‖ := by\n        have h := hz.2\n        apply le_of_not_gt\n        intro he\n        apply h\n        exact Metric.mem_ball.mpr (by rwa [dist_eq_norm])\n      intro he\n      rw [he,norm_zero] at hlow\n      exact (not_le_of_gt hε) hlow\n    have hdb : Continuous (dbarTest φ) := by\n      have hc := hφ.continuous_fderiv (by simp)\n      exact continuous_const.mul ((hc.clm_apply continuous_const).add\n        (continuous_const.mul (hc.clm_apply continuous_const)))\n    have hfK : ContinuousOn f K :=\n      ((continuous_id.sub continuous_const).continuousOn.inv₀ hnz).mul hdb.continuousOn\n    have hSK : S ⊆ K := by\n      intro z hz\n      refine ⟨Metric.mem_closedBall.mpr (by rw [dist_eq_norm]; exact hz.2.le),?_⟩\n      intro he\n      have ht := Metric.mem_ball.mp he\n      rw [dist_eq_norm] at ht\n      exact (not_lt_of_ge hz.1.le) ht\n    have hint : IntegrableOn f S := (ContinuousOn.integrableOn_compact hKd hfK).mono_set hSK\n    refine ⟨hint,?_⟩\n    let e : ℝ → ℂ := fun t => (Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I\n    let q : ℝ × ℝ → ℂ := fun p => φ (ζ + (p.1 : ℂ) * e p.2)\n    let Fr : ℝ × ℝ → ℂ := fun p => fderiv ℝ φ (ζ + (p.1 : ℂ) * e p.2) (e p.2)\n    let Ft : ℝ × ℝ → ℂ := fun p => fderiv ℝ φ (ζ + (p.1 : ℂ) * e p.2)\n      ((p.1 : ℂ) * (-(Real.sin p.2 : ℂ) + (Real.cos p.2 : ℂ) * Complex.I))\n    obtain ⟨hFr,hFt,hdR,hdT,halg⟩ := differentiate φ hφ ζ\n    have hperiod : ∀ r, q (r,Real.pi) = q (r,-Real.pi) := by\n      intro r\n      simp [q,e,Real.cos_neg,Real.sin_neg]\n    have houter : ∀ t, q (L,t) = 0 := by\n      intro t\n      change φ (ζ + (L : ℂ) * e t) = 0\n      apply image_eq_zero_of_notMem_tsupport\n      intro hz\n      have hzball := hsupport hz\n      have hL : 0 < L := hε.trans hεL\n      have hn : ‖ζ + (L : ℂ) * e t - ζ‖ = L := by\n        rw [add_sub_cancel_left,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]\n        have he : ‖e t‖ = 1 := by\n          simpa only [e,Complex.ofReal_cos,Complex.ofReal_sin] using Complex.norm_cos_add_sin_mul_I t\n        rw [he,mul_one]\n      have hlt : ‖ζ + (L : ℂ) * e t - ζ‖ < L := by\n        have ht := Metric.mem_ball.mp hzball\n        rwa [dist_eq_norm] at ht\n      rw [hn] at hlt\n      exact (lt_irrefl L) hlt\n    change (∫ z in S, f z) = -(1/2 : ℂ) * ∫ t in (-Real.pi)..Real.pi, q (ε,t)\n    calc\n      (∫ z in S, f z) = ∫ p in Ioo ε L ×ˢ Ioo (-Real.pi) Real.pi,\n          p.1 • f (ζ + Complex.polarCoord.symm p) := polar f ζ L ε hε\n      _ = ∫ p in Ioo ε L ×ˢ Ioo (-Real.pi) Real.pi,\n          (1/2 : ℂ) * (Fr p + Complex.I / (p.1 : ℂ) * Ft p) := by\n        apply setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo)\n        intro p hp\n        have hr : p.1 ≠ 0 := ne_of_gt (hε.trans hp.1.1)\n        simpa only [f,Complex.polarCoord_symm_apply,add_sub_cancel_left,Fr,Ft,e] using halg p.1 p.2 hr\n      _ = -(1/2 : ℂ) * ∫ t in (-Real.pi)..Real.pi, q (ε,t) :=\n        rectangle q Fr Ft hFr hFt hdR hdT L ε hε hεL hperiod houter\n  have compact_test_inverse_kernel_fundamental_solution : ∀ (φ : ℂ → ℂ)\n    (hφ : ContDiff ℝ ∞ φ) (hcompact : HasCompactSupport φ) (ζ : ℂ),\n    Integrable (fun z : ℂ => (z - ζ)⁻¹ * dbarTest φ z) (volume : Measure ℂ) ∧\n    (∫ z : ℂ, (z - ζ)⁻¹ * dbarTest φ z ∂(volume : Measure ℂ)) =\n      -(Real.pi : ℂ) * φ ζ := by\n    intro φ hφ hcompact ζ\n    have test_regular (φ : ℂ → ℂ) (hφ : ContDiff ℝ ∞ φ)\n        (hc : HasCompactSupport φ) : Continuous (dbarTest φ) ∧ HasCompactSupport (dbarTest φ) := by\n      have hf := hφ.continuous_fderiv (by simp)\n      have h1 : Continuous (fun z : ℂ => fderiv ℝ φ z 1) := hf.clm_apply continuous_const\n      have hI : Continuous (fun z : ℂ => fderiv ℝ φ z Complex.I) := hf.clm_apply continuous_const\n      constructor\n      · exact continuous_const.mul (h1.add (continuous_const.mul hI))\n      · exact (((hc.fderiv_apply (𝕜 := ℝ) 1).add\n          ((hc.fderiv_apply (𝕜 := ℝ) Complex.I).mul_left)).mul_left)\n    have inverse_integrable_ball (r : ℝ) :\n        IntegrableOn (fun z : ℂ => z⁻¹) (Metric.ball 0 r) volume := by\n      apply integrableOn_ball_of_norm_le_rpow (C := 1) (α := 1)\n        (by norm_num [Complex.finrank_real_complex]) (by norm_num [Complex.finrank_real_complex])\n      · exact Filter.Eventually.of_forall fun z => by\n          simp [norm_inv,Real.rpow_neg_one]\n      · exact aestronglyMeasurable_id.inv₀\n    have inverse_translated_ball (ζ : ℂ) (r : ℝ) :\n        IntegrableOn (fun z : ℂ => (z - ζ)⁻¹) (Metric.ball ζ r) volume := by\n      have hi := ((measurePreserving_sub_right (volume : Measure ℂ) ζ).restrict_preimage\n        Metric.isOpen_ball.measurableSet).integrable_comp_of_integrable\n          (inverse_integrable_ball r)\n      have he : (fun z : ℂ => z - ζ) ⁻¹' Metric.ball 0 r = Metric.ball ζ r := by\n        ext z\n        change dist (z - ζ) 0 < r ↔ dist z ζ < r\n        rw [dist_zero_right, dist_eq_norm]\n      simpa only [IntegrableOn, Function.comp_def, he] using hi\n    have product_integrable (φ : ℂ → ℂ) (hφ : ContDiff ℝ ∞ φ)\n        (hc : HasCompactSupport φ) (ζ : ℂ) :\n        Integrable (fun z => (z - ζ)⁻¹ * dbarTest φ z) volume := by\n      have hinv : LocallyIntegrable (fun z : ℂ => (z - ζ)⁻¹) volume := by\n        rw [locallyIntegrable_iff]\n        intro K hK\n        obtain ⟨r, hr⟩ := hK.isBounded.subset_ball ζ\n        exact (inverse_translated_ball ζ r).mono_set hr\n      have hd := test_regular φ hφ hc\n      simpa only [smul_eq_mul] using\n        hinv.integrable_smul_right_of_hasCompactSupport hd.1 hd.2\n    have product_support (φ : ℂ → ℂ) (ζ : ℂ) :\n        support (fun z => (z - ζ)⁻¹ * dbarTest φ z) ⊆ tsupport φ := by\n      intro z hz\n      by_contra hn\n      have hd : dbarTest φ z = 0 := by\n        change (1 / 2 : ℂ) * (fderiv ℝ φ z 1 + Complex.I * fderiv ℝ φ z Complex.I) = 0\n        rw [fderiv_of_notMem_tsupport ℝ hn]\n        simp\n      exact hz (by simp only [hd, mul_zero])\n    have puncture_convergence (f : ℂ → ℂ) (hf : Integrable f volume)\n        (ζ : ℂ) (L : ℝ) (hs : support f ⊆ Metric.ball ζ L) (hz : f ζ = 0) :\n        Filter.Tendsto (fun ε : ℝ => ∫ z in {z : ℂ | ε < ‖z - ζ‖ ∧ ‖z - ζ‖ < L}, f z)\n          (𝓝[>] 0) (𝓝 (∫ z : ℂ, f z)) := by\n      let A := fun ε : ℝ => {z : ℂ | ε < ‖z - ζ‖ ∧ ‖z - ζ‖ < L}\n      have hA (ε : ℝ) : MeasurableSet (A ε) := by\n        exact ((isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).inter\n          (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const)).measurableSet\n      have hzero : Filter.Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds\n      have hlim : ∀ᵐ z : ℂ ∂volume,\n          Filter.Tendsto (fun ε : ℝ => (A ε).indicator f z) (𝓝[>] 0) (𝓝 (f z)) := by\n        apply Filter.Eventually.of_forall\n        intro z\n        by_cases hL : ‖z - ζ‖ < L\n        · by_cases hζ : z = ζ\n          · subst z\n            have hε : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin\n            apply Filter.Tendsto.congr' _ tendsto_const_nhds\n            filter_upwards [hε] with ε hε\n            simp [A, hz, not_lt_of_ge hε.le]\n          · have hn : 0 < ‖z - ζ‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hζ)\n            apply Filter.Tendsto.congr' _ tendsto_const_nhds\n            filter_upwards [hzero.eventually (gt_mem_nhds hn)] with ε hε\n            exact (Set.indicator_of_mem (show z ∈ A ε from ⟨hε, hL⟩) f).symm\n        · have hfz : f z = 0 := by\n            apply notMem_support.mp\n            intro h\n            have hd : dist z ζ < L := hs h\n            exact hL (by rwa [dist_eq_norm] at hd)\n          simpa only [hfz] using\n            (show Filter.Tendsto (fun ε : ℝ => (A ε).indicator f z) (𝓝[>] 0) (𝓝 0) from by\n              have he : (fun ε : ℝ => (A ε).indicator f z) = fun _ => 0 := by\n                funext ε\n                exact Set.indicator_of_notMem (fun h => hL h.2) f\n              rw [he]\n              exact tendsto_const_nhds)\n      have ht := tendsto_integral_filter_of_dominated_convergence (μ := volume)\n        (F := fun ε z => (A ε).indicator f z) (fun z => ‖f z‖)\n        (Filter.Eventually.of_forall fun ε => hf.aestronglyMeasurable.indicator (hA ε))\n        (Filter.Eventually.of_forall fun ε => Filter.Eventually.of_forall fun z => norm_indicator_le_norm_self f z)\n        hf.norm hlim\n      simpa only [integral_indicator (hA _)] using ht\n    have boundary_convergence (φ : ℂ → ℂ) (hφ : Continuous φ)\n        (hc : HasCompactSupport φ) (ζ : ℂ) :\n        Filter.Tendsto (fun ε : ℝ => ∫ t in (-Real.pi)..Real.pi,\n          φ (ζ + (ε : ℂ) * ((Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I)))\n          (𝓝[>] 0) (𝓝 ((2 * Real.pi : ℝ) • φ ζ)) := by\n      obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hφ\n      let F := fun ε : ℝ => fun t : ℝ =>\n        φ (ζ + (ε : ℂ) * ((Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I))\n      have hF (ε : ℝ) : Continuous (F ε) := by\n        exact hφ.comp (continuous_const.add (continuous_const.mul\n          ((Complex.continuous_ofReal.comp Real.continuous_cos).add\n            ((Complex.continuous_ofReal.comp Real.continuous_sin).mul continuous_const))))\n      have hlim : ∀ᵐ t ∂volume.restrict (Ioc (-Real.pi) Real.pi),\n          Filter.Tendsto (fun ε => F ε t) (𝓝[>] 0) (𝓝 (φ ζ)) := by\n        apply Filter.Eventually.of_forall\n        intro t\n        have he : Filter.Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] 0) (𝓝 0) :=\n          (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds\n        have hz : Filter.Tendsto (fun _ : ℝ => ζ) (𝓝[>] 0) (𝓝 ζ) := tendsto_const_nhds\n        have hp := (hz.add\n          (he.mul_const ((Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I)))\n        simpa only [F, Function.comp_def, Complex.ofReal_zero, zero_mul, add_zero] using hφ.continuousAt.tendsto.comp hp\n      have ht := tendsto_integral_filter_of_dominated_convergence\n        (μ := volume.restrict (Ioc (-Real.pi) Real.pi)) (F := F) (fun _ => C)\n        (Filter.Eventually.of_forall fun ε => (hF ε).aestronglyMeasurable.restrict)\n        (Filter.Eventually.of_forall fun ε => Filter.Eventually.of_forall fun t => hC _)\n        (integrableOn_const (measure_Ioc_lt_top.ne)) hlim\n      have hp : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]\n      rw [← intervalIntegral.integral_of_le hp] at ht\n      simpa only [← intervalIntegral.integral_of_le hp, intervalIntegral.integral_const,\n        sub_neg_eq_add, two_mul] using ht\n    have hf := product_integrable φ hφ hcompact ζ\n    refine ⟨hf, ?_⟩\n    have hK : IsCompact (tsupport φ) := hcompact\n    obtain ⟨r, hr⟩ := hK.isBounded.subset_ball ζ\n    let L : ℝ := max r 1\n    have hL : 0 < L := lt_of_lt_of_le zero_lt_one (le_max_right r 1)\n    have hs : tsupport φ ⊆ Metric.ball ζ L :=\n      hr.trans (Metric.ball_subset_ball (le_max_left r 1))\n    have hfs : support (fun z => (z - ζ)⁻¹ * dbarTest φ z) ⊆ Metric.ball ζ L :=\n      (product_support φ ζ).trans hs\n    have hpuncture := puncture_convergence (fun z => (z - ζ)⁻¹ * dbarTest φ z)\n      hf ζ L hfs (by simp only [sub_self, inv_zero, zero_mul])\n    have hboundary := boundary_convergence φ hφ.continuous hcompact ζ\n    have heq : ∀ᶠ ε : ℝ in 𝓝[>] 0,\n        (∫ z in {z : ℂ | ε < ‖z - ζ‖ ∧ ‖z - ζ‖ < L}, (z - ζ)⁻¹ * dbarTest φ z) =\n          -(1 / 2 : ℂ) * ∫ t in (-Real.pi)..Real.pi,\n            φ (ζ + (ε : ℂ) * ((Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I)) := by\n      have hzero : Filter.Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds\n      have hpos : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin\n      filter_upwards [hpos, hzero.eventually (gt_mem_nhds hL)] with ε hε hεL\n      exact (compact_test_inverse_kernel_annulus φ hφ hcompact ζ L ε hε hεL hs).2\n    have hc : Filter.Tendsto (fun _ : ℝ => -(1 / 2 : ℂ)) (𝓝[>] 0) (𝓝 (-(1 / 2 : ℂ))) :=\n      tendsto_const_nhds\n    have hright := hc.mul hboundary\n    have htarget := Filter.Tendsto.congr' (Filter.Eventually.mono heq fun _ h => h.symm) hright\n    calc\n      (∫ z : ℂ, (z - ζ)⁻¹ * dbarTest φ z) =\n          -(1 / 2 : ℂ) * ((2 * Real.pi : ℝ) • φ ζ) := tendsto_nhds_unique hpuncture htarget\n      _ = -(Real.pi : ℂ) * φ ζ := by\n        rw [Complex.real_smul, Complex.ofReal_mul]\n        norm_num\n        ring\n  have coefficient_compact_test_joint_integrable : ∀ (R : ℝ) (hR : 0 < R)\n    (a b : ℂ → ℂ)\n    (ha : IntegrableOn a (Metric.ball (0 : ℂ) R) (volume : Measure ℂ))\n    (hb : Continuous b) (hcompact : HasCompactSupport b),\n    Integrable (fun x : ℂ × ℂ => (a x.1 * (x.2 - x.1)⁻¹) * b x.2)\n      (((volume : Measure ℂ).restrict (Metric.ball (0 : ℂ) R)).prod\n        (volume : Measure ℂ)) := by\n    intro R hR a b ha hb hcompact\n    obtain ⟨S, hS, hzero⟩ := hcompact.exists_pos_le_norm\n    obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) S).exists_bound_of_continuousOn\n      hb.continuousOn\n    let B : ℝ := max C 0\n    have hB : 0 ≤ B := le_max_right _ _\n    have hbound (z : ℂ) : ‖b z‖ ≤ B := by\n      by_cases hz : ‖z‖ < S\n      · exact (hC z (Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact hz.le))).trans\n          (le_max_left _ _)\n      · rw [hzero z (le_of_not_gt hz), norm_zero]\n        exact hB\n    have hkernel : IntegrableOn (fun z : ℂ => z⁻¹) (Metric.ball (0 : ℂ) (S + R)) volume := by\n      apply integrableOn_ball_of_norm_le_rpow (C := 1) (α := 1)\n        (by norm_num [Complex.finrank_real_complex])\n        (by norm_num [Complex.finrank_real_complex])\n      · exact Filter.Eventually.of_forall fun z => by\n          simp [norm_inv, Real.rpow_neg_one]\n      · exact aestronglyMeasurable_id.inv₀\n    let k : ℂ → ℝ := (Metric.ball (0 : ℂ) (S + R)).indicator (fun z : ℂ => ‖z⁻¹‖)\n    have hk : Integrable k volume :=\n      (integrable_indicator_iff Metric.isOpen_ball.measurableSet).mpr hkernel.norm\n    have hmajor : Integrable (fun x : ℂ × ℂ => (‖a x.1‖ * k (x.2 - x.1)) * B)\n        ((volume.restrict (Metric.ball (0 : ℂ) R)).prod volume) := by\n      exact ((measurePreserving_prod_sub (volume.restrict (Metric.ball (0 : ℂ) R)) volume).integrable_comp_of_integrable\n        (ha.norm.mul_prod hk)).mul_const B\n    apply hmajor.mono'\n    · exact ((ha.aestronglyMeasurable.comp_fst).mul\n        ((measurable_snd.sub measurable_fst).aestronglyMeasurable.inv₀)).mul\n        (hb.aestronglyMeasurable.comp_snd)\n    · have hfirst : ∀ᵐ x : ℂ × ℂ ∂((volume.restrict (Metric.ball (0 : ℂ) R)).prod volume),\n          x.1 ∈ Metric.ball (0 : ℂ) R :=\n        Measure.quasiMeasurePreserving_fst.ae\n          (ae_restrict_mem Metric.isOpen_ball.measurableSet)\n      filter_upwards [hfirst] with x hx\n      by_cases hz : ‖x.2‖ < S\n      · have hkx : x.2 - x.1 ∈ Metric.ball (0 : ℂ) (S + R) := by\n          rw [Metric.mem_ball, dist_zero_right] at hx ⊢\n          exact (norm_sub_le _ _).trans_lt (add_lt_add hz hx)\n        simp only [k, Set.indicator_of_mem hkx, norm_mul]\n        exact mul_le_mul_of_nonneg_left (hbound x.2) (mul_nonneg (norm_nonneg _) (norm_nonneg _))\n      · rw [hzero x.2 (le_of_not_gt hz), mul_zero, norm_zero]\n        exact mul_nonneg (mul_nonneg (norm_nonneg _) (Set.indicator_nonneg (fun z hz => norm_nonneg _) _)) hB\n  have bounded :\n    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ Metric.ball (0 : ℂ) R,\n      ‖literalCauchyPotential R a z‖ ≤ C := by\n    let q := Real.conjExponent p\n    have hp1 : 1 < p := by linarith\n    have hp0 : 0 < p := by linarith\n    have hq0 : 0 < q := div_pos hp0 (by linarith)\n    have hq2 : q < 2 := by\n      dsimp [q, Real.conjExponent]\n      apply (div_lt_iff₀ (by linarith : 0 < p - 1)).mpr\n      linarith\n    have hkernel : MemLp (fun z : ℂ => z⁻¹) (ENNReal.ofReal q)\n        (volume.restrict (Metric.ball 0 (2 * R))) := by\n      have hmeas : AEStronglyMeasurable (fun z : ℂ => z⁻¹) volume :=\n        aestronglyMeasurable_id.inv₀\n      apply (integrable_norm_rpow_iff hmeas.restrict\n        (by simp [hq0]) ENNReal.ofReal_ne_top).mp\n      simp only [ENNReal.toReal_ofReal hq0.le]\n      apply integrableOn_ball_of_norm_le_rpow (C := 1) (α := q)\n        (by norm_num [Complex.finrank_real_complex])\n        (by simpa only [Complex.finrank_real_complex, Nat.cast_ofNat] using hq2)\n      · exact Filter.Eventually.of_forall fun z => by\n          rw [norm_inv, Real.inv_rpow (norm_nonneg _), Real.rpow_neg (norm_nonneg _),\n            one_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]\n      · exact (hmeas.norm.aemeasurable.pow_const q).aestronglyMeasurable\n    let M := eLpNorm a (ENNReal.ofReal p) (volume.restrict (Metric.ball 0 R)) *\n      eLpNorm (fun ζ : ℂ => ζ⁻¹) (ENNReal.ofReal q) (volume.restrict (Metric.ball 0 (2 * R)))\n    have hM : M ≠ (∞ : ℝ≥0∞) := ENNReal.mul_ne_top ha.eLpNorm_ne_top hkernel.eLpNorm_ne_top\n    refine ⟨‖(1 / (Real.pi : ℂ))‖ * M.toReal, mul_nonneg (norm_nonneg _) ENNReal.toReal_nonneg, ?_⟩\n    intro z hz\n    have hsub : Metric.ball (0 : ℂ) R ⊆ (fun ζ : ℂ => z - ζ) ⁻¹' Metric.ball 0 (2 * R) := by\n      intro ζ hζ\n      change z - ζ ∈ Metric.ball (0 : ℂ) (2 * R)\n      rw [Metric.mem_ball, dist_zero_right] at hz hζ ⊢\n      exact (norm_sub_le z ζ).trans_lt (by linarith)\n    have ht := (hkernel).comp_measurePreserving\n      ((volume.measurePreserving_sub_left z).restrict_preimage Metric.isOpen_ball.measurableSet)\n    have htranslated := ht.mono_measure (Measure.restrict_mono hsub le_rfl)\n    have hknorm : eLpNorm (fun ζ : ℂ => (z - ζ)⁻¹) (ENNReal.ofReal q)\n        (volume.restrict (Metric.ball 0 R)) ≤\n        eLpNorm (fun ζ : ℂ => ζ⁻¹) (ENNReal.ofReal q) (volume.restrict (Metric.ball 0 (2 * R))) := by\n      calc\n        _ ≤ eLpNorm (fun ζ : ℂ => (z - ζ)⁻¹) (ENNReal.ofReal q)\n            (volume.restrict ((fun ζ : ℂ => z - ζ) ⁻¹' Metric.ball 0 (2 * R))) :=\n          eLpNorm_mono_measure _ (Measure.restrict_mono hsub le_rfl)\n        _ = _ := eLpNorm_comp_measurePreserving hkernel.aestronglyMeasurable\n          ((volume.measurePreserving_sub_left z).restrict_preimage Metric.isOpen_ball.measurableSet)\n    letI : (ENNReal.ofReal p).HolderConjugate (ENNReal.ofReal q) :=\n      (Real.HolderConjugate.conjExponent hp1).ennrealOfReal\n    have hmul : eLpNorm (fun ζ => a ζ / (z - ζ)) 1 (volume.restrict (Metric.ball 0 R)) ≤ M := by\n      have hh := eLpNorm_smul_le_mul_eLpNorm (m := Complex.measurableSpace) (p := ENNReal.ofReal p) (q := ENNReal.ofReal q)\n        (r := 1) ha.aestronglyMeasurable htranslated.aestronglyMeasurable\n      have hh' : eLpNorm (fun ζ => a ζ / (z - ζ)) 1 (volume.restrict (Metric.ball 0 R)) ≤\n          eLpNorm a (ENNReal.ofReal p) (volume.restrict (Metric.ball 0 R)) *\n            eLpNorm (fun ζ : ℂ => (z - ζ)⁻¹) (ENNReal.ofReal q) (volume.restrict (Metric.ball 0 R)) := by\n        have heq : (fun ζ => a ζ / (z - ζ)) =\n            a * ((fun ζ : ℂ => ζ⁻¹) ∘ (fun ζ : ℂ => z - ζ)) := by\n          funext ζ\n          exact div_eq_mul_inv _ _\n        rw [heq]\n        simpa only [Pi.smul_apply, smul_eq_mul, Pi.mul_apply, Function.comp_def] using hh\n      exact hh'.trans (mul_le_mul_right hknorm _)\n    have hi : ‖∫ ζ in Metric.ball (0 : ℂ) R, a ζ / (z - ζ)‖ ≤ M.toReal := by\n      have he := (enorm_integral_le_lintegral_enorm (fun ζ => a ζ / (z - ζ))).trans\n        (lintegral_enorm_le_eLpNorm_one.trans hmul)\n      simpa only [toReal_enorm] using ENNReal.toReal_mono hM he\n    change ‖(1 / (Real.pi : ℂ)) * ∫ ζ in Metric.ball (0 : ℂ) R, a ζ / (z - ζ)‖ ≤ _\n    rw [norm_mul]\n    exact mul_le_mul_of_nonneg_left hi (norm_nonneg _)\n  have exponent :\n    0 < cauchyExponent p ∧ cauchyExponent p < 1 ∧\n      (cauchyExponent p : ℝ) = 1 - 2 / p := by\n    have hp0 : 0 < p := by linarith\n    have hpos : 0 < 1 - 2 / p := by\n      apply sub_pos.mpr\n      apply (div_lt_iff₀ hp0).mpr\n      linarith\n    have hlt : 1 - 2 / p < 1 := by\n      have : 0 < 2 / p := div_pos (by norm_num) hp0\n      linarith\n    have hc : (cauchyExponent p : ℝ) = 1 - 2 / p := Real.coe_toNNReal _ hpos.le\n    exact ⟨by exact_mod_cast (hc ▸ hpos), by exact_mod_cast (hc ▸ hlt), hc⟩\n  have holder :\n    ∃ C : ℝ≥0, HolderOnWith C (cauchyExponent p)\n      (literalCauchyPotential R a) (Metric.ball (0 : ℂ) R) := by\n    have kernel : ∀ (q : ℝ), 1 < q → q < 2 →\n      let B := eLpNorm (fun z : ℂ => z⁻¹ - (z - 1)⁻¹) (ENNReal.ofReal q) volume\n      B < (∞ : ℝ≥0∞) ∧ ∀ z w : ℂ,\n        MemLp (fun ζ : ℂ => (z - ζ)⁻¹ - (w - ζ)⁻¹) (ENNReal.ofReal q) volume ∧\n        eLpNorm (fun ζ : ℂ => (z - ζ)⁻¹ - (w - ζ)⁻¹) (ENNReal.ofReal q) volume =\n          ENNReal.ofReal (‖z - w‖ ^ (2 / q - 1)) * B := by\n      intro q hq1 hq2\n      have normalized : ∀ (c : ℂ), c ≠ 0 →\n        MemLp (fun z : ℂ => z⁻¹ - (z - c)⁻¹) (ENNReal.ofReal q) volume ∧\n        eLpNorm (fun z : ℂ => z⁻¹ - (z - c)⁻¹) (ENNReal.ofReal q) volume =\n          ENNReal.ofReal (‖c‖ ^ (2 / q - 1)) *\n            eLpNorm (fun z : ℂ => z⁻¹ - (z - 1)⁻¹) (ENNReal.ofReal q) volume := by\n        intro c hc\n        have hbase : MemLp (fun z : ℂ => z⁻¹ - (z - 1)⁻¹) (ENNReal.ofReal q) volume := by\n          have hq0 : 0 < q := by linarith\n          have hmeas : AEStronglyMeasurable (fun z : ℂ => z⁻¹ - (z - 1)⁻¹) volume :=\n            aestronglyMeasurable_id.inv₀.sub ((aestronglyMeasurable_id.sub aestronglyMeasurable_const).inv₀)\n          have near (r : ℝ) : MemLp (fun z : ℂ => z⁻¹) (ENNReal.ofReal q)\n              (volume.restrict (Metric.ball 0 r)) := by\n            have hm : AEStronglyMeasurable (fun z : ℂ => z⁻¹) volume := aestronglyMeasurable_id.inv₀\n            apply (integrable_norm_rpow_iff hm.restrict (by simp [hq0]) ENNReal.ofReal_ne_top).mp\n            simp only [ENNReal.toReal_ofReal hq0.le]\n            apply integrableOn_ball_of_norm_le_rpow (C := 1) (α := q)\n              (by norm_num [Complex.finrank_real_complex])\n              (by simpa only [Complex.finrank_real_complex, Nat.cast_ofNat] using hq2)\n            · exact Filter.Eventually.of_forall fun z => by\n                rw [norm_inv, Real.inv_rpow (norm_nonneg _), Real.rpow_neg (norm_nonneg _),\n                  one_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]\n            · exact (hm.norm.aemeasurable.pow_const q).aestronglyMeasurable\n          have hnear : MemLp (fun z : ℂ => z⁻¹ - (z - 1)⁻¹) (ENNReal.ofReal q)\n              (volume.restrict (Metric.ball 0 2)) := by\n            have htrans : MeasurePreserving (fun z : ℂ => z - 1) volume volume := by\n              simpa only [sub_eq_add_neg] using measurePreserving_add_right volume (-1 : ℂ)\n            have ht := (near 3).comp_measurePreserving\n              (htrans.restrict_preimage Metric.isOpen_ball.measurableSet)\n            have hs : Metric.ball (0 : ℂ) 2 ⊆ (fun z : ℂ => z - 1) ⁻¹' Metric.ball 0 3 := by\n              intro z hz\n              change z - 1 ∈ Metric.ball (0 : ℂ) 3\n              rw [Metric.mem_ball, dist_zero_right] at hz ⊢\n              exact (norm_sub_le z 1).trans_lt (by simpa only [norm_one] using (show ‖z‖ + 1 < 3 by linarith))\n            exact (near 2).sub (ht.mono_measure (Measure.restrict_mono hs le_rfl))\n          have hfar_pointwise (z : ℂ) (hz : 2 ≤ ‖z‖) :\n              ‖z⁻¹ - (z - 1)⁻¹‖ ≤ 2 * ‖z‖ ^ (-2 : ℝ) := by\n            have hx : 0 < ‖z‖ := by linarith\n            have htri : ‖z‖ ≤ ‖z - 1‖ + 1 := by\n              simpa using norm_add_le (z - 1) (1 : ℂ)\n            have hy : 0 < ‖z - 1‖ := by linarith\n            have hz0 := norm_pos_iff.mp hx\n            have hz1 := norm_pos_iff.mp hy\n            have he : z⁻¹ - (z - 1)⁻¹ = -(1 / (z * (z - 1))) := by\n              field_simp (disch := first | assumption | positivity | norm_num | (apply ne_of_gt; linarith) | (norm_cast; assumption) | (apply mul_ne_zero <;> assumption))\n              <;> ring\n            rw [he, norm_neg, norm_div, norm_one, norm_mul,\n              Real.rpow_neg (norm_nonneg _), Real.rpow_two]\n            rw [← div_eq_mul_inv]\n            apply (div_le_div_iff₀ (mul_pos hx hy) (sq_pos_of_pos hx)).mpr\n            nlinarith [mul_nonneg hx.le (show 0 ≤ 2 * ‖z - 1‖ - ‖z‖ by linarith)]\n          have hradial : Integrable (fun z : ℂ => (Ioi (1 : ℝ)).indicator\n              (fun r : ℝ => r ^ (-2 * q)) ‖z‖) volume := by\n            rw [integrable_fun_norm_addHaar volume]\n            simp only [Complex.finrank_real_complex, Nat.reduceSub, pow_one, smul_eq_mul]\n            have hi := integrableOn_Ioi_rpow_of_lt (by linarith : 1 - 2 * q < -1) (by norm_num : (0 : ℝ) < 1)\n            have hi' : Integrable ((Ioi (1 : ℝ)).indicator (fun r : ℝ => r ^ (1 - 2 * q))) :=\n              (integrable_indicator_iff measurableSet_Ioi).mpr hi\n            apply hi'.integrableOn.congr_fun _ measurableSet_Ioi\n            intro r hr\n            by_cases h : 1 < r\n            · simp only [Set.indicator_of_mem (show r ∈ Ioi (1 : ℝ) from h)]\n              change r ^ (1 - 2 * q) = r * r ^ (-2 * q)\n              conv_rhs => lhs; rw [← Real.rpow_one r]\n              rw [← Real.rpow_add hr]\n              congr 1\n              ring\n            · simp [h]\n          have hfar : IntegrableOn (fun z : ℂ => ‖z⁻¹ - (z - 1)⁻¹‖ ^ q)\n              (Metric.ball (0 : ℂ) 2)ᶜ volume := by\n            apply Integrable.mono' (hradial.const_mul (2 ^ q)).integrableOn\n              ((hmeas.norm.aemeasurable.pow_const q).aestronglyMeasurable.restrict)\n            filter_upwards [self_mem_ae_restrict Metric.isOpen_ball.measurableSet.compl] with z hz\n            have hz' : 2 ≤ ‖z‖ := by simpa using hz\n            rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]\n            change ‖z⁻¹ - (z - 1)⁻¹‖ ^ q ≤ 2 ^ q * (Ioi (1 : ℝ)).indicator (fun r : ℝ => r ^ (-2 * q)) ‖z‖\n            rw [Set.indicator_of_mem (show ‖z‖ ∈ Ioi (1 : ℝ) by change 1 < ‖z‖; linarith)]\n            calc\n              _ ≤ (2 * ‖z‖ ^ (-2 : ℝ)) ^ q := Real.rpow_le_rpow (norm_nonneg _) (hfar_pointwise z hz') hq0.le\n              _ = _ := by rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul (norm_nonneg _)]\n          apply (integrable_norm_rpow_iff hmeas (by simp [hq0]) ENNReal.ofReal_ne_top).mp\n          simp only [ENNReal.toReal_ofReal hq0.le]\n          exact (integrableOn_univ.mp (by\n            rw [← union_compl_self (Metric.ball (0 : ℂ) 2), integrableOn_union]\n            exact ⟨by simpa only [IntegrableOn, ENNReal.toReal_ofReal hq0.le] using! hnear.integrable_norm_rpow (by simp [hq0]) ENNReal.ofReal_ne_top, hfar⟩))\n        have scale_integral : ∀ (f : ℂ → ℝ) (c : ℂ) (hc : c ≠ 0),\n              (∫ z : ℂ, f (c * z)) = (‖c‖ ^ 2)⁻¹ * ∫ z : ℂ, f z := by\n          intro f c hc\n          have hnorm : 0 < ‖c‖ := norm_pos_iff.mpr hc\n          let u : Circle := ⟨c / (‖c‖ : ℂ), by\n            apply mem_sphere_zero_iff_norm.mpr\n            simp [norm_div, Complex.norm_real, abs_of_pos hnorm, ne_of_gt hnorm]⟩\n          have he (z : ℂ) : c * z = ‖c‖ • rotation u z := by\n            change c * z = ‖c‖ • ((c / (‖c‖ : ℂ)) * z)\n            rw [Complex.real_smul]\n            have hcn : (‖c‖ : ℂ) ≠ 0 := by exact_mod_cast hnorm.ne'\n            field_simp (disch := first | assumption | positivity | norm_num | (apply ne_of_gt; linarith) | (norm_cast; assumption) | (apply mul_ne_zero <;> assumption))\n          simp_rw [he]\n          rw [(rotation u).measurePreserving.integral_comp\n            (rotation u).toHomeomorph.measurableEmbedding (fun x : ℂ => f (‖c‖ • x))]\n          simpa only [Complex.finrank_real_complex, smul_eq_mul,\n            abs_of_nonneg (inv_nonneg.mpr (sq_nonneg ‖c‖))] using volume.integral_comp_smul f ‖c‖\n        have scale_integrable : ∀ (f : ℂ → ℝ) (c : ℂ) (hc : c ≠ 0),\n              Integrable (fun z : ℂ => f (c * z)) ↔ Integrable f := by\n          intro f c hc\n          have hnorm : 0 < ‖c‖ := norm_pos_iff.mpr hc\n          let u : Circle := ⟨c / (‖c‖ : ℂ), by\n            apply mem_sphere_zero_iff_norm.mpr\n            simp [norm_div, Complex.norm_real, abs_of_pos hnorm, ne_of_gt hnorm]⟩\n          have he (z : ℂ) : c * z = ‖c‖ • rotation u z := by\n            change c * z = ‖c‖ • ((c / (‖c‖ : ℂ)) * z)\n            rw [Complex.real_smul]\n            have hcn : (‖c‖ : ℂ) ≠ 0 := by exact_mod_cast hnorm.ne'\n            field_simp (disch := first | assumption | positivity | norm_num | (apply ne_of_gt; linarith) | (norm_cast; assumption) | (apply mul_ne_zero <;> assumption))\n          simp_rw [he]\n          change Integrable ((fun x : ℂ => f (‖c‖ • x)) ∘ rotation u) ↔ Integrable f\n          rw [(rotation u).measurePreserving.integrable_comp_emb\n            (rotation u).toHomeomorph.measurableEmbedding]\n          exact integrable_comp_smul_iff volume f hnorm.ne'\n        have hq0 : 0 < q := by linarith\n        have hnorm : 0 < ‖c‖ := norm_pos_iff.mpr hc\n        have hnorm2 : ‖c‖ ^ 2 ≠ 0 := pow_ne_zero 2 hnorm.ne'\n        have he (z : ℂ) : (c * z)⁻¹ - (c * z - c)⁻¹ = c⁻¹ * (z⁻¹ - (z - 1)⁻¹) := by\n          rw [show c * z - c = c * (z - 1) by ring, mul_inv, mul_inv, mul_sub]\n        have hen (z : ℂ) : ‖(c * z)⁻¹ - (c * z - c)⁻¹‖ ^ q =\n            ‖c‖ ^ (-q) * ‖z⁻¹ - (z - 1)⁻¹‖ ^ q := by\n          rw [he, norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _), norm_inv,\n            Real.inv_rpow (norm_nonneg _), Real.rpow_neg (norm_nonneg _)]\n        have hbaseI : Integrable (fun z : ℂ => ‖z⁻¹ - (z - 1)⁻¹‖ ^ q) volume := by\n          simpa only [ENNReal.toReal_ofReal hq0.le] using hbase.integrable_norm_rpow (by simp [hq0]) ENNReal.ofReal_ne_top\n        have hscaledI : Integrable (fun z : ℂ => ‖z⁻¹ - (z - c)⁻¹‖ ^ q) volume := by\n          apply (scale_integrable _ c hc).mp\n          simp_rw [hen]\n          exact hbaseI.const_mul _\n        have hm : AEStronglyMeasurable (fun z : ℂ => z⁻¹ - (z - c)⁻¹) volume :=\n          aestronglyMeasurable_id.inv₀.sub ((aestronglyMeasurable_id.sub aestronglyMeasurable_const).inv₀)\n        have hmem : MemLp (fun z : ℂ => z⁻¹ - (z - c)⁻¹) (ENNReal.ofReal q) volume := by\n          apply (integrable_norm_rpow_iff hm (by simp [hq0]) ENNReal.ofReal_ne_top).mp\n          simpa only [ENNReal.toReal_ofReal hq0.le] using hscaledI\n        have hint : (∫ z : ℂ, ‖z⁻¹ - (z - c)⁻¹‖ ^ q) =\n            ‖c‖ ^ (2 - q) * ∫ z : ℂ, ‖z⁻¹ - (z - 1)⁻¹‖ ^ q := by\n          calc\n            _ = ‖c‖ ^ 2 * ∫ z : ℂ, ‖(c * z)⁻¹ - (c * z - c)⁻¹‖ ^ q := by\n              rw [scale_integral (fun z : ℂ => ‖z⁻¹ - (z - c)⁻¹‖ ^ q) c hc]\n              field_simp (disch := first | assumption | positivity | norm_num | (apply ne_of_gt; linarith) | (norm_cast; assumption) | (apply mul_ne_zero <;> assumption))\n            _ = ‖c‖ ^ 2 * (‖c‖ ^ (-q) * ∫ z : ℂ, ‖z⁻¹ - (z - 1)⁻¹‖ ^ q) := by\n              simp_rw [hen]\n              rw [integral_const_mul]\n            _ = _ := by rw [← mul_assoc, ← Real.rpow_two ‖c‖, ← Real.rpow_add hnorm]; congr 2\n        refine ⟨hmem, ?_⟩\n        rw [hmem.eLpNorm_eq_integral_rpow_norm (by simp [hq0]) ENNReal.ofReal_ne_top,\n          hbase.eLpNorm_eq_integral_rpow_norm (by simp [hq0]) ENNReal.ofReal_ne_top]\n        simp only [ENNReal.toReal_ofReal hq0.le]\n        rw [hint, Real.mul_rpow (by positivity) (integral_nonneg (fun z => Real.rpow_nonneg (norm_nonneg _) _)),\n          ← Real.rpow_mul hnorm.le, ENNReal.ofReal_mul (by positivity)]\n        congr 2\n        field_simp (disch := first | assumption | positivity | norm_num | (apply ne_of_gt; linarith) | (norm_cast; assumption) | (apply mul_ne_zero <;> assumption))\n      have hq0 : 0 < q := by linarith\n      have he : 0 < 2 / q - 1 := by\n        apply sub_pos.mpr\n        apply (lt_div_iff₀ hq0).mpr\n        linarith\n      refine ⟨(normalized 1 one_ne_zero).1, ?_⟩\n      intro z w\n      by_cases hzw : z = w\n      · subst w\n        simp [Real.zero_rpow he.ne']\n      · have hc : z - w ≠ 0 := sub_ne_zero.mpr hzw\n        obtain ⟨hm, hn⟩ := normalized (z - w) hc\n        have hpres := volume.measurePreserving_sub_left z\n        have hfun : (fun ζ : ℂ => (z - ζ)⁻¹ - (w - ζ)⁻¹) =\n            (fun t : ℂ => t⁻¹ - (t - (z - w))⁻¹) ∘ (fun ζ : ℂ => z - ζ) := by\n          funext ζ\n          simp only [Function.comp_apply]\n          congr 2\n          ring\n        rw [hfun]\n        refine ⟨hm.comp_measurePreserving hpres, ?_⟩\n        rw [eLpNorm_comp_measurePreserving hm.aestronglyMeasurable hpres, hn]\n    have integrable_at (z : ℂ) : IntegrableOn (fun ζ => a ζ / (z - ζ)) (Metric.ball (0 : ℂ) R) := by\n      let q := Real.conjExponent p\n      have hp1 : 1 < p := by linarith\n      have hp0 : 0 < p := by linarith\n      have hq0 : 0 < q := div_pos hp0 (by linarith)\n      have hq2 : q < 2 := by\n        dsimp [q, Real.conjExponent]\n        apply (div_lt_iff₀ (by linarith : 0 < p - 1)).mpr\n        linarith\n      have htranslated : MemLp (fun ζ : ℂ => (z - ζ)⁻¹) (ENNReal.ofReal q)\n          (volume.restrict (Metric.ball 0 R)) := by\n        have hkernel (R : ℝ) : MemLp (fun z : ℂ => z⁻¹) (ENNReal.ofReal q)\n            (volume.restrict (Metric.ball 0 R)) := by\n          have hmeas : AEStronglyMeasurable (fun z : ℂ => z⁻¹) volume :=\n            aestronglyMeasurable_id.inv₀\n          apply (integrable_norm_rpow_iff hmeas.restrict\n            (by simp [hq0]) ENNReal.ofReal_ne_top).mp\n          simp only [ENNReal.toReal_ofReal hq0.le]\n          apply integrableOn_ball_of_norm_le_rpow (C := 1) (α := q)\n            (by norm_num [Complex.finrank_real_complex])\n            (by simpa only [Complex.finrank_real_complex, Nat.cast_ofNat] using hq2)\n          · exact Filter.Eventually.of_forall fun z => by\n              rw [norm_inv, Real.inv_rpow (norm_nonneg _), Real.rpow_neg (norm_nonneg _),\n                one_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]\n          · exact (hmeas.norm.aemeasurable.pow_const q).aestronglyMeasurable\n        have ht := (hkernel (‖z‖ + R)).comp_measurePreserving\n          ((volume.measurePreserving_sub_left z).restrict_preimage Metric.isOpen_ball.measurableSet)\n        apply ht.mono_measure\n        apply Measure.restrict_mono _ le_rfl\n        intro ζ hζ\n        change z - ζ ∈ Metric.ball (0 : ℂ) (‖z‖ + R)\n        rw [Metric.mem_ball, dist_zero_right] at hζ ⊢\n        exact (norm_sub_le z ζ).trans_lt (by linarith)\n      letI : (ENNReal.ofReal p).HolderConjugate (ENNReal.ofReal q) :=\n        (Real.HolderConjugate.conjExponent hp1).ennrealOfReal\n      have hh := MemLp.integrable_mul (m := Complex.measurableSpace) ha htranslated\n      change Integrable (fun ζ => a ζ / (z - ζ)) (volume.restrict (Metric.ball 0 R))\n      have heq : (fun ζ => a ζ / (z - ζ)) = a * (fun ζ => (z - ζ)⁻¹) := by\n        funext ζ\n        exact div_eq_mul_inv _ _\n      rw [heq]\n      exact hh\n    let q := Real.conjExponent p\n    have hp1 : 1 < p := by linarith\n    have hp0 : 0 < p := by linarith\n    have hq1 : 1 < q := by\n      dsimp [q, Real.conjExponent]\n      apply (lt_div_iff₀ (by linarith : 0 < p - 1)).mpr\n      linarith\n    have hq0 : 0 < q := by linarith\n    have hq2 : q < 2 := by\n      dsimp [q, Real.conjExponent]\n      apply (div_lt_iff₀ (by linarith : 0 < p - 1)).mpr\n      linarith\n    have hbeta : 0 < 2 / q - 1 := by\n      apply sub_pos.mpr\n      apply (lt_div_iff₀ hq0).mpr\n      linarith\n    have he : 2 / q - 1 = 1 - 2 / p := by\n      dsimp [q, Real.conjExponent]\n      field_simp (disch := first | assumption | positivity | norm_num | (apply ne_of_gt; linarith) | (norm_cast; assumption) | (apply mul_ne_zero <;> assumption))\n      <;> ring\n    have hexp : (cauchyExponent p : ℝ) = 2 / q - 1 := by\n      rw [he]\n      exact Real.coe_toNNReal _ (by linarith [he, hbeta])\n    let N := eLpNorm a (ENNReal.ofReal p) (volume.restrict (Metric.ball (0 : ℂ) R))\n    let B := eLpNorm (fun z : ℂ => z⁻¹ - (z - 1)⁻¹) (ENNReal.ofReal q) volume\n    have hb : B < (∞ : ℝ≥0∞) := (kernel q hq1 hq2).1\n    have hN : N ≠ (∞ : ℝ≥0∞) := ha.eLpNorm_ne_top\n    let C : ℝ≥0 := ⟨‖(1 / (Real.pi : ℂ))‖ * (N * B).toReal, by positivity⟩\n    refine ⟨C, ?_⟩\n    intro z hz w hw\n    obtain ⟨hm, hn⟩ := (kernel q hq1 hq2).2 z w\n    have hmr := hm.restrict (Metric.ball (0 : ℂ) R)\n    let D := ENNReal.ofReal (‖z - w‖ ^ (2 / q - 1))\n    have hbound : eLpNorm (fun ζ : ℂ => (z - ζ)⁻¹ - (w - ζ)⁻¹) (ENNReal.ofReal q)\n        (volume.restrict (Metric.ball (0 : ℂ) R)) ≤ D * B := by\n      exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans_eq hn\n    letI : (ENNReal.ofReal p).HolderConjugate (ENNReal.ofReal q) :=\n      (Real.HolderConjugate.conjExponent hp1).ennrealOfReal\n    have hprod : eLpNorm (fun ζ : ℂ => a ζ * ((z - ζ)⁻¹ - (w - ζ)⁻¹)) 1\n        (volume.restrict (Metric.ball (0 : ℂ) R)) ≤ N * (D * B) := by\n      have ht := eLpNorm_smul_le_mul_eLpNorm (m := Complex.measurableSpace)\n        (p := ENNReal.ofReal p) (q := ENNReal.ofReal q) (r := 1)\n        ha.aestronglyMeasurable hmr.aestronglyMeasurable\n      have ht' : eLpNorm (fun ζ : ℂ => a ζ * ((z - ζ)⁻¹ - (w - ζ)⁻¹)) 1\n          (volume.restrict (Metric.ball (0 : ℂ) R)) ≤ N *\n          eLpNorm (fun ζ : ℂ => (z - ζ)⁻¹ - (w - ζ)⁻¹) (ENNReal.ofReal q)\n            (volume.restrict (Metric.ball (0 : ℂ) R)) := by\n        have heq : (fun ζ : ℂ => a ζ * ((z - ζ)⁻¹ - (w - ζ)⁻¹)) =\n            a * (fun ζ : ℂ => (z - ζ)⁻¹ - (w - ζ)⁻¹) := rfl\n        rw [heq]\n        simpa only [N, smul_eq_mul] using ht\n      exact ht'.trans (mul_le_mul_right hbound _)\n    have hM : N * (D * B) ≠ (∞ : ℝ≥0∞) := ENNReal.mul_ne_top hN (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hb.ne)\n    have hi : ‖∫ ζ in Metric.ball (0 : ℂ) R, a ζ * ((z - ζ)⁻¹ - (w - ζ)⁻¹)‖ ≤\n        (N * B).toReal * ‖z - w‖ ^ (2 / q - 1) := by\n      have hle := (enorm_integral_le_lintegral_enorm\n        (fun ζ : ℂ => a ζ * ((z - ζ)⁻¹ - (w - ζ)⁻¹))).trans\n        (lintegral_enorm_le_eLpNorm_one.trans hprod)\n      have hreal := ENNReal.toReal_mono hM hle\n      simpa only [toReal_enorm, ENNReal.toReal_mul, D,\n        ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) _),\n        mul_assoc, mul_left_comm, mul_comm] using hreal\n    have hdiff : literalCauchyPotential R a z - literalCauchyPotential R a w =\n        (1 / (Real.pi : ℂ)) * ∫ ζ in Metric.ball (0 : ℂ) R, a ζ * ((z - ζ)⁻¹ - (w - ζ)⁻¹) := by\n      change (1 / (Real.pi : ℂ)) * (∫ ζ in Metric.ball (0 : ℂ) R, a ζ / (z - ζ)) - (1 / (Real.pi : ℂ)) * (∫ ζ in Metric.ball (0 : ℂ) R, a ζ / (w - ζ)) = _\n      rw [← mul_sub, ← integral_sub (integrable_at z) (integrable_at w)]\n      congr 1\n      apply integral_congr_ae\n      filter_upwards with ζ\n      simp only [div_eq_mul_inv, mul_sub]\n    have hC : (C : ℝ) = ‖(1 / (Real.pi : ℂ))‖ * (N * B).toReal := rfl\n    have hdist : dist (literalCauchyPotential R a z) (literalCauchyPotential R a w) ≤\n        (C : ℝ) * dist z w ^ (cauchyExponent p : ℝ) := by\n      rw [dist_eq_norm, hdiff, norm_mul, dist_eq_norm, hexp, hC]\n      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hi (norm_nonneg (1 / (Real.pi : ℂ)))\n    rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg (cauchyExponent p).coe_nonneg,\n      ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul C.coe_nonneg]\n    exact ENNReal.ofReal_le_ofReal hdist\n  have weak :\n    WeakDbarIdentityOn (Metric.ball (0 : ℂ) R) (literalCauchyPotential R a) a := by\n    letI : IsFiniteMeasure (volume.restrict (Metric.ball (0 : ℂ) R)) :=\n      isFiniteMeasure_restrict.mpr measure_ball_ne_top\n    have ha1 : IntegrableOn a (Metric.ball (0 : ℂ) R) :=\n      ha.integrable (by rw [← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff (by positivity)]; linarith)\n    intro φ hφ hcφ hsφ\n    have hdcont : Continuous (dbarTest φ) := by\n      have hf := hφ.continuous_fderiv (by simp)\n      exact continuous_const.mul ((hf.clm_apply continuous_const).add\n        (continuous_const.mul (hf.clm_apply continuous_const)))\n    have hdcompact : HasCompactSupport (dbarTest φ) := by\n      apply hcφ.mono'\n      intro z hz\n      by_contra hn\n      have hz0 : fderiv ℝ φ z = 0 := fderiv_of_notMem_tsupport ℝ hn\n      exact hz (by change (1 / 2 : ℂ) * ((fderiv ℝ φ z) 1 + Complex.I * (fderiv ℝ φ z) Complex.I) = 0; simp only [hz0, zero_apply, mul_zero, add_zero])\n    have hd0 (z : ℂ) (hz : z ∉ Metric.ball (0 : ℂ) R) : dbarTest φ z = 0 := by\n      have hzt : z ∉ tsupport φ := fun h => hz (hsφ h)\n      change (1 / 2 : ℂ) * ((fderiv ℝ φ z) 1 + Complex.I * (fderiv ℝ φ z) Complex.I) = 0; simp only [fderiv_of_notMem_tsupport ℝ hzt, zero_apply, mul_zero, add_zero]\n    have hjoint := coefficient_compact_test_joint_integrable R hR a (dbarTest φ) ha1 hdcont hdcompact\n    have hinner (z : ℂ) :\n        (∫ ζ in Metric.ball (0 : ℂ) R, (a ζ * (z - ζ)⁻¹) * dbarTest φ z) =\n          (∫ ζ in Metric.ball (0 : ℂ) R, a ζ / (z - ζ)) * dbarTest φ z := by\n      rw [integral_mul_const]\n      simp only [div_eq_mul_inv]\n    have hpotential_int : Integrable (fun z : ℂ => literalCauchyPotential R a z * dbarTest φ z) := by\n      have hi := hjoint.integral_prod_right.const_mul (1 / (Real.pi : ℂ))\n      simp only [hinner] at hi\n      change Integrable (fun z : ℂ => ((1 / (Real.pi : ℂ)) * (∫ ζ in Metric.ball (0 : ℂ) R, a ζ / (z - ζ))) * dbarTest φ z) volume; simpa only [mul_assoc] using hi\n    have hproduct_int : IntegrableOn (fun z : ℂ => a z * φ z) (Metric.ball (0 : ℂ) R) := by\n      obtain ⟨C, hC⟩ := hφ.continuous.bounded_above_of_compact_support hcφ\n      exact ha1.mul_bdd hφ.continuous.aestronglyMeasurable.restrict\n        (Filter.Eventually.of_forall fun z => hC z)\n    refine ⟨hpotential_int.integrableOn, hproduct_int, ?_⟩\n    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by rw [hd0 z hz, mul_zero])]\n    calc\n      (∫ z : ℂ, literalCauchyPotential R a z * dbarTest φ z) =\n          (1 / (Real.pi : ℂ)) * ∫ z : ℂ, ∫ ζ in Metric.ball (0 : ℂ) R,\n            (a ζ * (z - ζ)⁻¹) * dbarTest φ z := by\n        rw [← integral_const_mul]\n        apply integral_congr_ae\n        filter_upwards with z\n        rw [hinner]\n        change ((1 / (Real.pi : ℂ)) * (∫ ζ in Metric.ball (0 : ℂ) R, a ζ / (z - ζ))) * dbarTest φ z = _; rw [mul_assoc]\n      _ = (1 / (Real.pi : ℂ)) * ∫ ζ in Metric.ball (0 : ℂ) R,\n            ∫ z : ℂ, (a ζ * (z - ζ)⁻¹) * dbarTest φ z := by\n        rw [← integral_integral_swap hjoint]\n      _ = (1 / (Real.pi : ℂ)) * ∫ ζ in Metric.ball (0 : ℂ) R,\n            a ζ * (-(Real.pi : ℂ) * φ ζ) := by\n        congr 1\n        apply integral_congr_ae\n        filter_upwards with ζ\n        simp_rw [mul_assoc]\n        rw [integral_const_mul,\n          (compact_test_inverse_kernel_fundamental_solution φ hφ hcφ ζ).2]\n      _ = -(∫ ζ in Metric.ball (0 : ℂ) R, a ζ * φ ζ) := by\n        have he (ζ : ℂ) : a ζ * (-(Real.pi : ℂ) * φ ζ) =\n            -(Real.pi : ℂ) * (a ζ * φ ζ) := by ring\n        simp_rw [he]\n        rw [integral_const_mul]\n        have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero\n        field_simp (disch := first | assumption | positivity | norm_num | (apply ne_of_gt; linarith) | (norm_cast; assumption) | (apply mul_ne_zero <;> assumption))\n  exact ⟨bounded, exponent, holder, weak⟩\n\n)"))


theorem weak_gauge_product_holomorphic (U : Set ℂ) (hU : IsOpen U)
    (p : ℝ) (hp : 2 < p) (a w omega : ℂ → ℂ)
    (ha : MemLp a (ENNReal.ofReal p) (volume.restrict U))
    (hw : ContinuousOn w U) (homega : ContinuousOn omega U)
    (heq : WeakVekuaOn U w a (fun _ => 0))
    (hdbar : WeakDbarIdentityOn U omega a) :
    DifferentiableOn ℂ (fun z => w z * Complex.exp (-omega z)) U := by
  have smooth_multiplier (U : Set ℂ) (w a : ℂ → ℂ) (hu : IsOpen U) (hw : ContinuousOn w U)
      (hd : WeakDbarIdentityOn U w a) (eta : ℂ → ℂ) (he : ContDiff ℝ ∞ eta) :
      WeakDbarIdentityOn U (fun z => w z * eta z)
        (fun z => a z * eta z + w z * dbarTest eta z) := by
    have dbar_mul (f g : ℂ → ℂ) (z : ℂ)
        (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
        dbarTest (fun y => f y * g y) z = f z * dbarTest g z + dbarTest f z * g z := by
      change (1 / 2 : ℂ) * (fderiv ℝ (fun y => f y * g y) z 1 +
        Complex.I * fderiv ℝ (fun y => f y * g y) z Complex.I) =
        f z * ((1 / 2 : ℂ) * (fderiv ℝ g z 1 + Complex.I * fderiv ℝ g z Complex.I)) +
        ((1 / 2 : ℂ) * (fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I)) * g z
      rw [fderiv_fun_mul hf hg]
      simp only [add_apply, smul_apply, smul_eq_mul]
      ring
    have dbar_cont (f : ℂ → ℂ) (hf : ContDiff ℝ ∞ f) : Continuous (dbarTest f) := by
      change Continuous (fun z => (1 / 2 : ℂ) * (fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I))
      exact continuous_const.mul (((hf.continuous_fderiv (by simp)).clm_apply continuous_const).add
        (continuous_const.mul ((hf.continuous_fderiv (by simp)).clm_apply continuous_const)))
    have dbar_supp (f : ℂ → ℂ) : tsupport (dbarTest f) ⊆ tsupport f := by
      apply closure_minimal
      · intro z hz
        by_contra hn
        change dbarTest f z ≠ 0 at hz
        apply hz
        change (1 / 2 : ℂ) * (fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I) = 0
        rw [fderiv_of_notMem_tsupport ℝ hn]
        simp
      · exact isClosed_tsupport f
    have integral_product (F psi : ℂ → ℂ) (hF : ContinuousOn F U)
        (hpsi : Continuous psi) (hc : HasCompactSupport psi) (hs : tsupport psi ⊆ U) :
        Integrable (fun z => F z * psi z) := by
      apply (integrableOn_iff_integrable_of_support_subset ?_).mp
        (((hF.mono hs).mul hpsi.continuousOn).integrableOn_compact hc)
      intro z hz
      exact subset_tsupport psi ((mul_ne_zero_iff.mp hz).2)
    intro φ hφ hc hs
    have htest : tsupport (fun z => eta z * φ z) ⊆ U :=
      (tsupport_mul_subset_right).trans hs
    obtain ⟨hi, hai, heq⟩ := hd (fun z => eta z * φ z) (he.mul hφ) hc.mul_left htest
    have hfirst : IntegrableOn (fun z => w z * eta z * dbarTest φ z) U :=
      (integral_product _ _ (hw.mul he.continuous.continuousOn) (dbar_cont φ hφ)
        (hc.of_isClosed_subset (isClosed_tsupport _) (dbar_supp φ)) ((dbar_supp φ).trans hs)).integrableOn
    have hcross : IntegrableOn (fun z => w z * dbarTest eta z * φ z) U :=
      (integral_product _ _ (hw.mul (dbar_cont eta he).continuousOn) hφ.continuous hc hs).integrableOn
    have haint : IntegrableOn (fun z => a z * eta z * φ z) U := by
      simpa only [mul_assoc] using hai
    refine ⟨hfirst, ?_, ?_⟩
    · simp only [add_mul]
      exact Integrable.add (m := Complex.measurableSpace) haint hcross
    · have hpoint : (fun z => w z * dbarTest (fun y => eta y * φ y) z) =
          (fun z => w z * eta z * dbarTest φ z + w z * dbarTest eta z * φ z) := by
        funext z
        rw [dbar_mul eta φ z (he.differentiable (by simp) z) (hφ.differentiable (by simp) z)]
        ring
      rw [hpoint, integral_add hfirst hcross] at heq
      have hassoc : (fun z => a z * (eta z * φ z)) = (fun z => a z * eta z * φ z) := by
        funext z
        exact (mul_assoc (a z) (eta z) (φ z)).symm
      rw [hassoc] at heq
      simp only [add_mul]
      rw [integral_add haint hcross]
      linear_combination heq
  have exponential_chain (omega : ℂ → ℂ) (z : ℂ) (h : DifferentiableAt ℝ omega z) :
      dbarTest (fun y => Complex.exp (-omega y)) z =
        -Complex.exp (-omega z) * dbarTest omega z := by
    have hd := (Complex.hasDerivAt_exp (-omega z)).complexToReal_fderiv.comp z h.hasFDerivAt.neg
    change HasFDerivAt (fun y => Complex.exp (-omega y)) _ z at hd
    change (1 / 2 : ℂ) * (fderiv ℝ (fun y => Complex.exp (-omega y)) z 1 +
      Complex.I * fderiv ℝ (fun y => Complex.exp (-omega y)) z Complex.I) =
      -Complex.exp (-omega z) * ((1 / 2 : ℂ) *
        (fderiv ℝ omega z 1 + Complex.I * fderiv ℝ omega z Complex.I))
    rw [hd.fderiv]
    simp only [ContinuousLinearMap.comp_apply, neg_apply, smul_apply, ContinuousLinearMap.one_apply, smul_eq_mul]
    ring
  have w_dbar : WeakDbarIdentityOn U w (fun z => a z * w z) := by
    intro φ hφ hc hs
    simpa only [zero_mul, add_zero] using heq.2 φ hφ hc hs
  have a_locally_integrable : LocallyIntegrableOn a U := by
    apply locallyIntegrableOn_of_locallyIntegrable_restrict
    exact ha.locallyIntegrable (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith))
  have product_cont : ContinuousOn (fun z => w z * Complex.exp (-omega z)) U :=
    hw.mul (Complex.continuous_exp.comp_continuousOn homega.neg)
  have smooth_gauge_identity (eta : ℂ → ℂ) (heta : ContDiff ℝ ∞ eta) :
      WeakDbarIdentityOn U (fun z => w z * Complex.exp (-eta z))
        (fun z => w z * Complex.exp (-eta z) * (a z - dbarTest eta z)) := by
    have hfactor : ContDiff ℝ ∞ (fun z => Complex.exp (-eta z)) :=
      Complex.contDiff_exp.comp heta.neg
    have hh := smooth_multiplier U w (fun z => a z * w z) hU hw w_dbar
      (fun z => Complex.exp (-eta z)) hfactor
    have hrhs : (fun z => (a z * w z) * Complex.exp (-eta z) +
        w z * dbarTest (fun y => Complex.exp (-eta y)) z) =
        (fun z => w z * Complex.exp (-eta z) * (a z - dbarTest eta z)) := by
      funext z
      rw [exponential_chain eta z (heta.differentiable (by simp) z)]
      ring
    rwa [hrhs] at hh
  have local_approximation (U : Set ℂ) (hU : IsOpen U) (omega a : ℂ → ℂ)
      (homega : ContinuousOn omega U) (ha : LocallyIntegrableOn a U)
      (hdbar : WeakDbarIdentityOn U omega a)
      (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U)
      (phi : ℕ → ContDiffBump (0 : ℂ))
      (hphi : Filter.Tendsto (fun n => (phi n).rOut) Filter.atTop (𝓝 0)) :
      ∃ eta : ℕ → ℂ → ℂ, (∀ n, ContDiff ℝ ∞ (eta n)) ∧
        TendstoUniformlyOn eta omega Filter.atTop K ∧
        (∀ n, IntegrableOn (fun z => dbarTest (eta n) z-a z) K) ∧
        Filter.Tendsto (fun n => ∫ z in K, ‖dbarTest (eta n) z-a z‖) Filter.atTop (𝓝 0) :=
    set_option maxHeartbeats 6000000 in
    open Filter ContinuousLinearMap Metric in
    open scoped Topology in by
    have source_identity (U : Set ℂ) (f a F A g : ℂ → ℂ)
        (hF : LocallyIntegrable F) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
        (hf : WeakDbarIdentityOn U f a) (z : ℂ)
        (hloc : ∀ y, z-y ∈ tsupport g → y ∈ U ∧ F y = f y ∧ A y = a y) :
        dbarTest (MeasureTheory.convolution F g (ContinuousLinearMap.mul ℝ ℂ) volume) z =
          (MeasureTheory.convolution A g (ContinuousLinearMap.mul ℝ ℂ) volume) z := by
      have convolution_dbar (F g : ℂ → ℂ) (hF : LocallyIntegrable F) (hg : ContDiff ℝ ∞ g)
          (hgc : HasCompactSupport g) (z : ℂ) :
          dbarTest (MeasureTheory.convolution F g (ContinuousLinearMap.mul ℝ ℂ) volume) z =
            ∫ y : ℂ, F y * dbarTest g (z-y) := by
        let L := ContinuousLinearMap.mul ℝ ℂ
        have hd := hgc.hasFDerivAt_convolution_right L hF (hg.of_le (by simp)) z
        have hi := (hgc.fderiv ℝ).convolutionExists_right (L.precompR ℂ) hF
          (hg.continuous_fderiv (by simp)) z
        have hI1 := (ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).integrable_comp hi
        have hII := (ContinuousLinearMap.apply ℝ ℂ Complex.I).integrable_comp hi
        change (1/2:ℂ) * (fderiv ℝ (MeasureTheory.convolution F g L volume) z 1 +
          Complex.I * fderiv ℝ (MeasureTheory.convolution F g L volume) z Complex.I) = _
        rw [hd.fderiv]
        simp only [convolution_def, ContinuousLinearMap.integral_apply hi]
        simp only [L, ContinuousLinearMap.precompR_apply, ContinuousLinearMap.compL_apply,
          ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply'] at *
        change Integrable (fun y => F y * fderiv ℝ g (z-y) 1) at hI1
        change Integrable (fun y => F y * fderiv ℝ g (z-y) Complex.I) at hII
        rw [← integral_const_mul, ← integral_add hI1 (hII.const_mul Complex.I), ← integral_const_mul]
        congr 1
        funext y
        change (1/2:ℂ) * (F y * fderiv ℝ g (z-y) 1 + Complex.I * (F y * fderiv ℝ g (z-y) Complex.I)) =
          F y * ((1/2:ℂ) * (fderiv ℝ g (z-y) 1 + Complex.I * fderiv ℝ g (z-y) Complex.I))
        ring
      have translated_dbar (g : ℂ → ℂ) (hg : Differentiable ℝ g) (z y : ℂ) :
          dbarTest (fun t => g (z-t)) y = -dbarTest g (z-y) := by
        have hd := (hg (z-y)).hasFDerivAt.comp y ((hasFDerivAt_id y).const_sub z)
        change HasFDerivAt (fun t => g (z-t)) _ y at hd
        change (1/2:ℂ) * (fderiv ℝ (fun t => g (z-t)) y 1 +
          Complex.I * fderiv ℝ (fun t => g (z-t)) y Complex.I) =
          -((1/2:ℂ) * (fderiv ℝ g (z-y) 1 + Complex.I * fderiv ℝ g (z-y) Complex.I))
        rw [hd.fderiv]
        simp only [ContinuousLinearMap.comp_apply, neg_apply, ContinuousLinearMap.id_apply, map_neg]
        ring
    
      let phi : ℂ → ℂ := fun y => g (z-y)
      have hphi : ContDiff ℝ ∞ phi := hg.comp (contDiff_const.sub contDiff_id)
      have hphic : HasCompactSupport phi := hgc.comp_homeomorph (Homeomorph.subLeft z)
      have hphis : tsupport phi ⊆ U := by
        intro y hy
        exact (hloc y (tsupport_comp_subset_preimage g (continuous_const.sub continuous_id) hy)).1
      have htest := (hf phi hphi hphic hphis).2.2
      have hderzero (y : ℂ) (hy : z-y ∉ tsupport g) : dbarTest phi y = 0 := by
        rw [translated_dbar g (hg.differentiable (by simp))]
        change -((1/2:ℂ) * (fderiv ℝ g (z-y) 1 + Complex.I * fderiv ℝ g (z-y) Complex.I)) = 0
        rw [fderiv_of_notMem_tsupport ℝ hy]
        simp
      have hpzero (y : ℂ) (hy : z-y ∉ tsupport g) : phi y = 0 := by
        exact Function.notMem_support.mp (fun h => hy (subset_tsupport g h))
      have hleft : (∫ y : ℂ, F y * dbarTest phi y) = ∫ y in U, f y * dbarTest phi y := by
        calc
          _ = ∫ y : ℂ, f y * dbarTest phi y := by
            apply integral_congr_ae
            filter_upwards [] with y
            by_cases hy : z-y ∈ tsupport g
            · rw [(hloc y hy).2.1]
            · rw [hderzero y hy]; simp
          _ = _ := by
            symm
            apply setIntegral_eq_integral_of_forall_compl_eq_zero
            intro y hy
            rw [hderzero y (fun h => hy (hloc y h).1), mul_zero]
      have hright : (∫ y : ℂ, A y * phi y) = ∫ y in U, a y * phi y := by
        calc
          _ = ∫ y : ℂ, a y * phi y := by
            apply integral_congr_ae
            filter_upwards [] with y
            by_cases hy : z-y ∈ tsupport g
            · rw [(hloc y hy).2.2]
            · rw [hpzero y hy]; simp
          _ = _ := by
            symm
            apply setIntegral_eq_integral_of_forall_compl_eq_zero
            intro y hy
            rw [hpzero y (fun h => hy (hloc y h).1), mul_zero]
      have he : (fun y => F y * dbarTest phi y) =
          (fun y => -(F y * dbarTest g (z-y))) := by
        funext y
        rw [translated_dbar g (hg.differentiable (by simp))]
        ring
      rw [← hleft, ← hright, he, integral_neg] at htest
      rw [convolution_dbar F g hF hg hgc z]
      change (∫ y : ℂ, F y * dbarTest g (z-y)) = ∫ y : ℂ, A y * phi y
      exact neg_injective htest
    have local_L1 (F : ℂ → ℂ) (hF : Integrable F) (K : Set ℂ)
        [IsFiniteMeasure (volume.restrict K)]
        (phi : ℕ → ContDiffBump (0 : ℂ))
        (hphi : Filter.Tendsto (fun n => (phi n).rOut) Filter.atTop (𝓝 0)) :
        Filter.Tendsto (fun n => ∫ x in K, ‖(MeasureTheory.convolution ((phi n).normed volume) F (lsmul ℝ ℝ) volume) x - F x‖)
          Filter.atTop (𝓝 0) := by
      have contraction (F : ℂ → ℂ) (hF : Integrable F) (phi : ContDiffBump (0 : ℂ)) :
          (∫ x : ℂ, ‖(MeasureTheory.convolution (phi.normed volume) F (lsmul ℝ ℝ) volume) x‖) ≤ ∫ x : ℂ, ‖F x‖ := by
        have hn : ∀ x : ℂ, ‖(MeasureTheory.convolution (phi.normed volume) F (lsmul ℝ ℝ) volume) x‖ ≤
            (MeasureTheory.convolution (phi.normed volume) (fun y => ‖F y‖) (lsmul ℝ ℝ) volume) x := by
          intro x
          rw [convolution_def, convolution_def]
          calc
            _ ≤ ∫ y : ℂ, ‖phi.normed volume y • F (x-y)‖ := norm_integral_le_integral_norm _
            _ = _ := by
              apply integral_congr_ae
              filter_upwards [] with y
              simp only [lsmul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (phi.nonneg_normed y), smul_eq_mul]
        calc
          _ ≤ ∫ x : ℂ, (MeasureTheory.convolution (phi.normed volume) (fun y => ‖F y‖) (lsmul ℝ ℝ) volume) x :=
            integral_mono (phi.integrable_normed.integrable_convolution (lsmul ℝ ℝ) hF).norm
              (phi.integrable_normed.integrable_convolution (lsmul ℝ ℝ) hF.norm) hn
          _ = _ := by
            rw [integral_convolution (lsmul ℝ ℝ) phi.integrable_normed hF.norm]
            simp only [lsmul_apply, phi.integral_normed, smul_eq_mul, one_mul]
      have bounded_continuous_L1 (g : BoundedContinuousFunction ℂ ℂ) (hg : Integrable g) (K : Set ℂ)
          [IsFiniteMeasure (volume.restrict K)]
          (phi : ℕ → ContDiffBump (0 : ℂ))
          (hphi : Filter.Tendsto (fun n => (phi n).rOut) Filter.atTop (𝓝 0)) :
          Filter.Tendsto (fun n => ∫ x in K, ‖(MeasureTheory.convolution ((phi n).normed volume) g (lsmul ℝ ℝ) volume) x - g x‖)
            Filter.atTop (𝓝 0) := by
        have hi (n : ℕ) := (phi n).integrable_normed.integrable_convolution (lsmul ℝ ℝ) hg
        have hbound (n : ℕ) (x : ℂ) :
            ‖(MeasureTheory.convolution ((phi n).normed volume) g (lsmul ℝ ℝ) volume) x - g x‖ ≤ 2*‖g‖ := by
          rw [← dist_eq_norm]
          apply (phi n).dist_normed_convolution_le g.continuous.aestronglyMeasurable
          intro y _
          calc
            dist (g y) (g x) = ‖g y - g x‖ := dist_eq_norm _ _
            _ ≤ ‖g y‖ + ‖g x‖ := norm_sub_le _ _
            _ ≤ 2*‖g‖ := by linarith [g.norm_coe_le_norm y, g.norm_coe_le_norm x]
        have ht := tendsto_integral_of_dominated_convergence (μ := volume.restrict K)
          (fun _ : ℂ => 2*‖g‖)
          (fun n => ((hi n).sub hg).norm.aestronglyMeasurable.restrict)
          (integrable_const _) (fun n => Filter.Eventually.of_forall (fun x => by
            rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
            exact hbound n x))
          (show ∀ᵐ x : ℂ ∂volume.restrict K,
            Filter.Tendsto (fun n => ‖(MeasureTheory.convolution ((phi n).normed volume) g (lsmul ℝ ℝ) volume) x - g x‖)
              Filter.atTop (𝓝 (0 : ℝ)) from Filter.Eventually.of_forall (fun x => by
                have hh := ((ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume) hphi g.continuous x).sub
                  (show Filter.Tendsto (fun _ : ℕ => g x) Filter.atTop (𝓝 (g x)) from tendsto_const_nhds)).norm
                simpa only [sub_self, norm_zero] using hh))
        simpa only [integral_zero, Pi.sub_apply] using ht
      apply Metric.tendsto_nhds.mpr
      intro eps heps
      obtain ⟨g, hgerr, hgi⟩ := hF.exists_boundedContinuous_integral_sub_le (show 0 < eps/4 by linarith)
      have hgt := bounded_continuous_L1 g hgi K phi hphi
      have hev := (tendsto_order.mp hgt).2 (eps/4) (by linarith)
      filter_upwards [hev] with n hn
      let M : (ℂ → ℂ) → ℂ → ℂ := fun f => MeasureTheory.convolution ((phi n).normed volume) f (lsmul ℝ ℝ) volume
      have hMI (f : ℂ → ℂ) (hf : Integrable f) : Integrable (M f) :=
        (phi n).integrable_normed.integrable_convolution (lsmul ℝ ℝ) hf
      have hsub (x : ℂ) : M (fun y => F y-g y) x = M F x - M g x := by
        have h1 := ((phi n).hasCompactSupport_normed (μ := volume)).convolutionExists_left (lsmul ℝ ℝ)
          (phi n).continuous_normed hF.locallyIntegrable x
        have h2 := ((phi n).hasCompactSupport_normed (μ := volume)).convolutionExists_left (lsmul ℝ ℝ)
          (phi n).continuous_normed hgi.locallyIntegrable x
        change (∫ t : ℂ, (phi n).normed volume t • (F (x-t)-g (x-t))) =
          (∫ t : ℂ, (phi n).normed volume t • F (x-t)) - ∫ t : ℂ, (phi n).normed volume t • g (x-t)
        simp only [smul_sub]
        exact integral_sub h1 h2
      have hpt (x : ℂ) : ‖M F x-F x‖ ≤
          ‖M (fun y => F y-g y) x‖ + ‖M g x-g x‖ + ‖g x-F x‖ := by
        have he : M F x-F x = (M (fun y => F y-g y) x + (M g x-g x)) + (g x-F x) := by
          rw [hsub]
          ring
        rw [he]
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      have h1i := (hMI (fun y => F y-g y) (hF.sub hgi)).norm
      have h2i := ((hMI g hgi).sub hgi).norm
      have h3i := (hgi.sub hF).norm
      change Integrable (fun x => ‖M g x-g x‖) at h2i
      change Integrable (fun x => ‖g x-F x‖) at h3i
      have hb : (∫ x in K, ‖M F x-F x‖) ≤ eps/4 + (∫ x in K, ‖M g x-g x‖) + eps/4 := by
        calc
          _ ≤ ∫ x in K, (‖M (fun y => F y-g y) x‖ + ‖M g x-g x‖ + ‖g x-F x‖) :=
            integral_mono (((hMI F hF).sub hF).norm.integrableOn)
              ((h1i.add h2i).add h3i).integrableOn hpt
          _ = (∫ x in K, ‖M (fun y => F y-g y) x‖) +
              (∫ x in K, ‖M g x-g x‖) + ∫ x in K, ‖g x-F x‖ := by
            have hs1 := integral_add (μ := volume.restrict K) (h1i.add h2i).integrableOn h3i.integrableOn
            have hs2 := integral_add (μ := volume.restrict K) h1i.integrableOn h2i.integrableOn
            simp only [Pi.add_apply] at hs1 hs2
            rw [hs1, hs2]
          _ ≤ _ := by
            apply add_le_add
            · apply add_le_add
              ·
                exact (setIntegral_le_integral h1i (Filter.Eventually.of_forall (fun x => norm_nonneg _))).trans
                  ((contraction _ (hF.sub hgi) (phi n)).trans hgerr)
              · exact le_rfl
            · apply (setIntegral_le_integral h3i (Filter.Eventually.of_forall (fun x => norm_nonneg _))).trans
              have he : (fun x : ℂ => ‖g x-F x‖) = (fun x => ‖F x-g x‖) := by
                funext x
                exact norm_sub_rev _ _
              rw [he]
              exact hgerr
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
      change (∫ x in K, ‖M F x-F x‖) < eps
      change (∫ x in K, ‖M g x-g x‖) < eps/4 at hn
      linarith
    have uniform_compact (f F : ℂ → ℂ) (K : Set ℂ) (hK : IsCompact K) (r : ℝ) (hr : 0 < r)
        (hf : ContinuousOn f (cthickening r K)) (hF : AEStronglyMeasurable F volume)
        (heq : ∀ y ∈ cthickening r K, F y = f y)
        (phi : ℕ → ContDiffBump (0 : ℂ))
        (hphi : Filter.Tendsto (fun n => (phi n).rOut) Filter.atTop (𝓝 0)) :
        TendstoUniformlyOn (fun n => MeasureTheory.convolution ((phi n).normed volume) F (lsmul ℝ ℝ) volume)
          f Filter.atTop K := by
      apply Metric.tendstoUniformlyOn_iff.mpr
      intro eps heps
      have huc := hK.cthickening.uniformContinuousOn_of_continuous hf
      obtain ⟨d, hd, hdclose⟩ := Metric.uniformContinuousOn_iff.mp huc (eps/2) (by linarith)
      have hevent : ∀ᶠ n in Filter.atTop, (phi n).rOut < min r d :=
        (tendsto_order.1 hphi).2 _ (lt_min hr hd)
      filter_upwards [hevent] with n hn
      intro x hx
      have hxc : x ∈ cthickening r K := self_subset_cthickening (δ := r) K hx
      have hbound : dist ((MeasureTheory.convolution ((phi n).normed volume) F (lsmul ℝ ℝ) volume) x) (F x) ≤ eps/2 := by
        apply (phi n).dist_normed_convolution_le hF
        intro y hy
        have hyc : y ∈ cthickening r K := mem_cthickening_of_dist_le y x r K hx
          ((mem_ball.mp hy).trans_le (le_trans hn.le (min_le_left r d))).le
        rw [heq y hyc, heq x hxc]
        apply le_of_lt
        apply hdclose y hyc x hxc
        exact (mem_ball.mp hy).trans (hn.trans_le (min_le_right r d))
      rw [heq x hxc] at hbound
      rw [dist_comm]
      exact hbound.trans_lt (by linarith)
    obtain ⟨r, hr, hsub⟩ := hK.exists_cthickening_subset_open hU hKU
    let E : Set ℂ := cthickening r K
    have hE : IsCompact E := hK.cthickening
    let F : ℂ → ℂ := E.indicator omega
    let A : ℂ → ℂ := E.indicator a
    have hFI : Integrable F := (integrable_indicator_iff hE.measurableSet).mpr
      ((homega.mono hsub).integrableOn_compact hE)
    have hAI : Integrable A := (integrable_indicator_iff hE.measurableSet).mpr
      (ha.integrableOn_compact_subset hsub hE)
    have hFagree (y : ℂ) (hy : y ∈ E) : F y = omega y := indicator_of_mem hy omega
    have hAagree (y : ℂ) (hy : y ∈ E) : A y = a y := indicator_of_mem hy a
    let g : ℕ → ℂ → ℂ := fun n y => ((phi n).normed volume y : ℂ)
    let eta : ℕ → ℂ → ℂ := fun n => MeasureTheory.convolution F (g n) (ContinuousLinearMap.mul ℝ ℂ) volume
    have hgsmooth (n : ℕ) : ContDiff ℝ ∞ (g n) :=
      Complex.ofRealCLM.contDiff.comp (phi n).contDiff_normed
    have hgc (n : ℕ) : HasCompactSupport (g n) :=
      ((phi n).hasCompactSupport_normed (μ := volume)).comp_left (g := Complex.ofRealCLM) rfl
    have hconv_eq (H : ℂ → ℂ) (n : ℕ) :
        (MeasureTheory.convolution H (g n) (ContinuousLinearMap.mul ℝ ℂ) volume) =
          MeasureTheory.convolution ((phi n).normed volume) H (lsmul ℝ ℝ) volume := by
      funext z
      rw [convolution_eq_swap]
      simp only [convolution_def, ContinuousLinearMap.mul_apply', lsmul_apply]
      apply integral_congr_ae
      filter_upwards [] with y
      change H (z-y) * ((phi n).normed volume y : ℂ) = (phi n).normed volume y • H (z-y)
      rw [Complex.real_smul, mul_comm]
    have hetasmooth (n : ℕ) : ContDiff ℝ ∞ (eta n) :=
      (hgc n).contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℂ) hFI.locallyIntegrable (hgsmooth n)
    refine ⟨eta, hetasmooth, ?_, ?_, ?_⟩
    · have ht := uniform_compact omega F K hK r hr (homega.mono hsub)
        hFI.aestronglyMeasurable hFagree phi hphi
      have hh : eta = (fun n => MeasureTheory.convolution ((phi n).normed volume) F (lsmul ℝ ℝ) volume) :=
        funext (hconv_eq F)
      rw [hh]
      exact ht
    · intro n
      have hc : Continuous (dbarTest (eta n)) := by
        change Continuous (fun z => (1/2:ℂ) * (fderiv ℝ (eta n) z 1 +
          Complex.I * fderiv ℝ (eta n) z Complex.I))
        exact continuous_const.mul
          ((((hetasmooth n).continuous_fderiv (by simp)).clm_apply continuous_const).add
            (continuous_const.mul (((hetasmooth n).continuous_fderiv (by simp)).clm_apply continuous_const)))
      exact (hc.continuousOn.integrableOn_compact hK).sub (ha.integrableOn_compact_subset hKU hK)
    · letI : IsFiniteMeasure (volume.restrict K) := ⟨by simpa only [Measure.restrict_apply_univ] using hK.measure_lt_top⟩
      have ht := local_L1 A hAI K phi hphi
      apply ht.congr'
      filter_upwards [(tendsto_order.mp hphi).2 r hr] with n hn
      apply setIntegral_congr_fun hK.measurableSet
      intro z hz
      have hgs : tsupport (g n) ⊆ closedBall 0 (phi n).rOut :=
        (tsupport_comp_subset (g := Complex.ofRealCLM) rfl ((phi n).normed volume)).trans
          (by rw [(phi n).tsupport_normed_eq])
      have he : dbarTest (eta n) z = (MeasureTheory.convolution A (g n) (ContinuousLinearMap.mul ℝ ℂ) volume) z := by
        apply source_identity U omega a F A (g n) hFI.locallyIntegrable (hgsmooth n) (hgc n) hdbar z
        intro y hy
        have hdist : dist y z ≤ (phi n).rOut := by
          have h := Metric.mem_closedBall.mp (hgs hy)
          rw [dist_zero_right] at h
          rw [dist_eq_norm_sub']
          exact h
        have hyE : y ∈ E := mem_cthickening_of_dist_le y z r K hz (hdist.trans hn.le)
        exact ⟨hsub hyE, hFagree y hyE, hAagree y hyE⟩
      dsimp only
      rw [he, hconv_eq A n, hAagree z (self_subset_cthickening (δ := r) K hz)]
  have gauge_limit (U : Set ℂ) (w omega a phi : ℂ → ℂ)
      (hw : ContinuousOn w U) (homega : ContinuousOn omega U)
      (hphi : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ U)
      (eta : ℕ → ℂ → ℂ)
      (heta : TendstoUniformlyOn eta omega Filter.atTop (tsupport phi))
      (hdi : ∀ n, IntegrableOn (fun z => dbarTest (eta n) z-a z) (tsupport phi))
      (hdt : Filter.Tendsto (fun n => ∫ z in tsupport phi, ‖dbarTest (eta n) z-a z‖) Filter.atTop (𝓝 0))
      (hint : IntegrableOn (fun z => (w z * Complex.exp (-omega z)) * dbarTest phi z) U)
      (hres : ∀ n,
        IntegrableOn (fun z => (w z * Complex.exp (-eta n z)) * dbarTest phi z) U ∧
        IntegrableOn (fun z => (w z * Complex.exp (-eta n z) * (a z-dbarTest (eta n) z)) * phi z) U ∧
        (∫ z in U, (w z * Complex.exp (-eta n z)) * dbarTest phi z) =
          -(∫ z in U, (w z * Complex.exp (-eta n z) * (a z-dbarTest (eta n) z)) * phi z)) :
      (∫ z in U, (w z * Complex.exp (-omega z)) * dbarTest phi z) = 0 :=
    set_option maxHeartbeats 6000000 in
    open Filter ContinuousLinearMap Metric in
    open scoped Topology in by
    obtain ⟨Co, hCo⟩ := hc.exists_bound_of_continuousOn (homega.mono hs)
    obtain ⟨Cw0, hCw0⟩ := hc.exists_bound_of_continuousOn (hw.mono hs)
    obtain ⟨Cp0, hCp0⟩ := hc.exists_bound_of_continuousOn hphi.continuous.continuousOn
    let Cw := max Cw0 0
    let Cp := max Cp0 0
    let Ce := Real.exp (Co+1)
    have hCw (z : ℂ) (hz : z ∈ tsupport phi) : ‖w z‖ ≤ Cw := (hCw0 z hz).trans (le_max_left _ _)
    have hCp (z : ℂ) (hz : z ∈ tsupport phi) : ‖phi z‖ ≤ Cp := (hCp0 z hz).trans (le_max_left _ _)
    have hCwpos : 0 ≤ Cw := le_max_right _ _
    have hCppos : 0 ≤ Cp := le_max_right _ _
    have hCepos : 0 ≤ Ce := (Real.exp_pos _).le
    have hbounds : ∀ᶠ n in Filter.atTop, ∀ z ∈ tsupport phi, ‖Complex.exp (-eta n z)‖ ≤ Ce := by
      filter_upwards [Metric.tendstoUniformlyOn_iff.mp heta 1 zero_lt_one] with n hn
      intro z hz
      have hdist := hn z hz
      have hen : ‖eta n z‖ ≤ Co+1 := by
        calc
          _ = ‖(eta n z-omega z)+omega z‖ := by congr 1; ring
          _ ≤ ‖eta n z-omega z‖ + ‖omega z‖ := norm_add_le _ _
          _ ≤ Co+1 := by
            rw [← dist_eq_norm, dist_comm]
            linarith [hCo z hz]
      exact (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr (by simpa only [norm_neg] using hen))
    have hd0 (z : ℂ) (hz : z ∉ tsupport phi) : dbarTest phi z = 0 := by
      change (1/2:ℂ) * (fderiv ℝ phi z 1 + Complex.I * fderiv ℝ phi z Complex.I) = 0
      rw [fderiv_of_notMem_tsupport ℝ hz]
      simp
    have hp0 (z : ℂ) (hz : z ∉ tsupport phi) : phi z = 0 :=
      Function.notMem_support.mp (fun h => hz (subset_tsupport phi h))
    have hdcont : Continuous (dbarTest phi) := by
      change Continuous (fun z => (1/2:ℂ) * (fderiv ℝ phi z 1 + Complex.I * fderiv ℝ phi z Complex.I))
      exact continuous_const.mul (((hphi.continuous_fderiv (by simp)).clm_apply continuous_const).add
        (continuous_const.mul ((hphi.continuous_fderiv (by simp)).clm_apply continuous_const)))
    have hbase : IntegrableOn (fun z => w z * dbarTest phi z) U := by
      have hsupport : Function.support (fun z => w z * dbarTest phi z) ⊆ tsupport phi := by
        intro z hz
        by_contra hn
        apply hz
        change w z * dbarTest phi z = 0
        rw [hd0 z hn, mul_zero]
      exact ((integrableOn_iff_integrable_of_support_subset hsupport).mp
        (((hw.mono hs).mul hdcont.continuousOn).integrableOn_compact hc)).integrableOn
    have hleft : Filter.Tendsto (fun n => ∫ z in U, (w z * Complex.exp (-eta n z)) * dbarTest phi z)
        Filter.atTop (𝓝 (∫ z in U, (w z * Complex.exp (-omega z)) * dbarTest phi z)) := by
      apply tendsto_integral_filter_of_dominated_convergence (fun z => Ce * ‖w z * dbarTest phi z‖)
      · exact Filter.Eventually.of_forall (fun n => (hres n).1.aestronglyMeasurable)
      · filter_upwards [hbounds] with n hn
        filter_upwards [] with z
        by_cases hz : z ∈ tsupport phi
        · simp only [norm_mul]
          calc
            _ = ‖Complex.exp (-eta n z)‖ * (‖w z‖ * ‖dbarTest phi z‖) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right (hn z hz) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        · rw [hd0 z hz]
          simp only [mul_zero, norm_zero]
          exact le_rfl
      · exact hbase.norm.const_mul Ce
      · filter_upwards [] with z
        by_cases hz : z ∈ tsupport phi
        · exact (((heta.tendsto_at hz).neg.cexp).const_mul (w z)).mul_const (dbarTest phi z)
        · simp only [hd0 z hz, mul_zero]
          exact tendsto_const_nhds
    have hright : Filter.Tendsto (fun n => ∫ z in U,
        (w z * Complex.exp (-eta n z) * (a z-dbarTest (eta n) z)) * phi z) Filter.atTop (𝓝 0) := by
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
        (g := fun n => (Cw*Ce*Cp) * ∫ z in tsupport phi, ‖dbarTest (eta n) z-a z‖)
      · filter_upwards [hbounds] with n hn
        have hdom : (∫ z in U, (w z * Complex.exp (-eta n z) * (a z-dbarTest (eta n) z)) * phi z) =
            ∫ z in tsupport phi, (w z * Complex.exp (-eta n z) * (a z-dbarTest (eta n) z)) * phi z := by
          calc
            _ = ∫ z : ℂ, (w z * Complex.exp (-eta n z) * (a z-dbarTest (eta n) z)) * phi z :=
              setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by rw [hp0 z (fun h => hz (hs h)), mul_zero])
            _ = _ := (setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by rw [hp0 z hz, mul_zero])).symm
        rw [hdom, ← integral_const_mul]
        apply norm_integral_le_of_norm_le ((hdi n).norm.const_mul (Cw*Ce*Cp))
        filter_upwards [ae_restrict_mem hc.measurableSet] with z hz
        simp only [norm_mul]
        calc
          _ = ‖w z‖ * ‖Complex.exp (-eta n z)‖ * ‖phi z‖ * ‖dbarTest (eta n) z-a z‖ := by
            rw [norm_sub_rev (a z)]
            ring
          _ ≤ _ := by gcongr; exact hCw z hz; exact hn z hz; exact hCp z hz
      · simpa only [mul_zero] using hdt.const_mul (Cw*Ce*Cp)
    have hzero : Filter.Tendsto (fun n => ∫ z in U, (w z * Complex.exp (-eta n z)) * dbarTest phi z)
        Filter.atTop (𝓝 0) := by
      have hh := hright.neg
      simp only [neg_zero] at hh
      exact hh.congr' (Filter.Eventually.of_forall (fun n => (hres n).2.2.symm))
    exact tendsto_nhds_unique hleft hzero
  have product_weak : WeakDbarIdentityOn U (fun z => w z * Complex.exp (-omega z)) (fun _ => 0) := by
    intro φ hφ hc hs
    have dbar_cont : Continuous (dbarTest φ) := by
      change Continuous (fun z => (1 / 2 : ℂ) * (fderiv ℝ φ z 1 +
        Complex.I * fderiv ℝ φ z Complex.I))
      exact continuous_const.mul (((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).add
        (continuous_const.mul ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)))
    have hsupport : support (fun z => (w z * Complex.exp (-omega z)) * dbarTest φ z) ⊆ tsupport φ := by
      intro z hz
      by_contra hn
      apply hz
      change (w z * Complex.exp (-omega z)) * ((1 / 2 : ℂ) *
        (fderiv ℝ φ z 1 + Complex.I * fderiv ℝ φ z Complex.I)) = 0
      rw [fderiv_of_notMem_tsupport ℝ hn]
      simp
    have hint : IntegrableOn (fun z => (w z * Complex.exp (-omega z)) * dbarTest φ z) U :=
      ((integrableOn_iff_integrable_of_support_subset hsupport).mp
        (((product_cont.mono hs).mul dbar_cont.continuousOn).integrableOn_compact hc)).integrableOn
    refine ⟨hint, by simpa using (integrableOn_zero : IntegrableOn (fun _ : ℂ => (0 : ℂ)) U), ?_⟩
    simp only [zero_mul, integral_zero, neg_zero]
    let bumps : ℕ → ContDiffBump (0 : ℂ) := fun n =>
      { rIn := (1 / ((n:ℝ)+1))/2
        rOut := 1 / ((n:ℝ)+1)
        rIn_pos := by positivity
        rIn_lt_rOut := by
          have : 0 < 1 / ((n:ℝ)+1) := by positivity
          linarith }
    have hbumps : Filter.Tendsto (fun n => (bumps n).rOut) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    obtain ⟨eta, heta, hu, hi, ht⟩ := local_approximation U hU omega a homega
      a_locally_integrable hdbar (tsupport φ) hc hs bumps hbumps
    exact gauge_limit U w omega a φ hw homega hφ hc hs eta hu hi ht hint
      (fun n => smooth_gauge_identity (eta n) (heta n) φ hφ hc hs)
  have continuous_weak_cr (U : Set ℂ) (hU : IsOpen U) (f : ℂ → ℂ)
      (hf : ContinuousOn f U) (hweak : WeakDbarIdentityOn U f (fun _ => 0)) :
      DifferentiableOn ℂ f U :=
    set_option maxHeartbeats 3000000 in
    open Filter ContinuousLinearMap Metric in
    open scoped Topology Convolution in by
    have mollified_holomorphic (U : Set ℂ) (f F g : ℂ → ℂ)
        (hF : LocallyIntegrable F) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
        (hf : WeakDbarIdentityOn U f (fun _ => 0)) (z : ℂ)
        (hloc : ∀ y, z-y ∈ tsupport g → y ∈ U ∧ F y = f y) :
        DifferentiableAt ℂ (MeasureTheory.convolution F g (ContinuousLinearMap.mul ℝ ℂ) volume) z := by
      have convolution_dbar (F g : ℂ → ℂ) (hF : LocallyIntegrable F) (hg : ContDiff ℝ ∞ g)
          (hgc : HasCompactSupport g) (z : ℂ) :
          dbarTest (MeasureTheory.convolution F g (ContinuousLinearMap.mul ℝ ℂ) volume) z =
            ∫ y : ℂ, F y * dbarTest g (z-y) := by
        let L := ContinuousLinearMap.mul ℝ ℂ
        have hd := hgc.hasFDerivAt_convolution_right L hF (hg.of_le (by simp)) z
        have hi := (hgc.fderiv ℝ).convolutionExists_right (L.precompR ℂ) hF
          (hg.continuous_fderiv (by simp)) z
        have hI1 := (ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).integrable_comp hi
        have hII := (ContinuousLinearMap.apply ℝ ℂ Complex.I).integrable_comp hi
        change (1/2:ℂ) * (fderiv ℝ (MeasureTheory.convolution F g L volume) z 1 +
          Complex.I * fderiv ℝ (MeasureTheory.convolution F g L volume) z Complex.I) = _
        rw [hd.fderiv]
        simp only [convolution_def, ContinuousLinearMap.integral_apply hi]
        simp only [L, ContinuousLinearMap.precompR_apply, ContinuousLinearMap.compL_apply,
          ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply'] at *
        change Integrable (fun y => F y * fderiv ℝ g (z-y) 1) at hI1
        change Integrable (fun y => F y * fderiv ℝ g (z-y) Complex.I) at hII
        rw [← integral_const_mul, ← integral_add hI1 (hII.const_mul Complex.I), ← integral_const_mul]
        congr 1
        funext y
        change (1/2:ℂ) * (F y * fderiv ℝ g (z-y) 1 + Complex.I * (F y * fderiv ℝ g (z-y) Complex.I)) =
          F y * ((1/2:ℂ) * (fderiv ℝ g (z-y) 1 + Complex.I * fderiv ℝ g (z-y) Complex.I))
        ring
      have translated_dbar (g : ℂ → ℂ) (hg : Differentiable ℝ g) (z y : ℂ) :
          dbarTest (fun t => g (z-t)) y = -dbarTest g (z-y) := by
        have hd := (hg (z-y)).hasFDerivAt.comp y ((hasFDerivAt_id y).const_sub z)
        change HasFDerivAt (fun t => g (z-t)) _ y at hd
        change (1/2:ℂ) * (fderiv ℝ (fun t => g (z-t)) y 1 +
          Complex.I * fderiv ℝ (fun t => g (z-t)) y Complex.I) =
          -((1/2:ℂ) * (fderiv ℝ g (z-y) 1 + Complex.I * fderiv ℝ g (z-y) Complex.I))
        rw [hd.fderiv]
        simp only [ContinuousLinearMap.comp_apply, neg_apply, ContinuousLinearMap.id_apply, map_neg]
        ring
    
      let phi : ℂ → ℂ := fun y => g (z-y)
      have hphi : ContDiff ℝ ∞ phi := hg.comp (contDiff_const.sub contDiff_id)
      have hphic : HasCompactSupport phi := hgc.comp_homeomorph (Homeomorph.subLeft z)
      have hphis : tsupport phi ⊆ U := by
        intro y hy
        exact (hloc y (tsupport_comp_subset_preimage g (continuous_const.sub continuous_id) hy)).1
      have hzero : ∫ y in U, f y * dbarTest phi y = 0 := by
        simpa only [zero_mul, integral_zero, neg_zero] using (hf phi hphi hphic hphis).2.2
      have hderzero (y : ℂ) (hy : z-y ∉ tsupport g) : dbarTest phi y = 0 := by
        rw [translated_dbar g (hg.differentiable (by simp))]
        change -((1/2:ℂ) * (fderiv ℝ g (z-y) 1 + Complex.I * fderiv ℝ g (z-y) Complex.I)) = 0
        rw [fderiv_of_notMem_tsupport ℝ hy]
        simp
      have hfull : ∫ y : ℂ, F y * dbarTest phi y = 0 := by
        calc
          _ = ∫ y : ℂ, f y * dbarTest phi y := by
            apply integral_congr_ae
            filter_upwards [] with y
            by_cases hy : z-y ∈ tsupport g
            · rw [(hloc y hy).2]
            · rw [hderzero y hy]
              simp
          _ = ∫ y in U, f y * dbarTest phi y := by
            symm
            apply setIntegral_eq_integral_of_forall_compl_eq_zero
            intro y hy
            rw [hderzero y (fun h => hy (hloc y h).1), mul_zero]
          _ = 0 := hzero
      have hdbar : dbarTest (MeasureTheory.convolution F g (ContinuousLinearMap.mul ℝ ℂ) volume) z = 0 := by
        rw [convolution_dbar F g hF hg hgc z]
        have he : (fun y => F y * dbarTest phi y) =
            (fun y => -(F y * dbarTest g (z-y))) := by
          funext y
          rw [translated_dbar g (hg.differentiable (by simp))]
          ring
        rw [he, integral_neg] at hfull
        exact neg_eq_zero.mp hfull
      have hreal := (hgc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℂ)
        hF (hg.of_le (by simp)) z).differentiableAt
      apply differentiableAt_complex_iff_differentiableAt_real.mpr
      refine ⟨hreal, ?_⟩
      let D := fderiv ℝ (MeasureTheory.convolution F g (ContinuousLinearMap.mul ℝ ℂ) volume) z
      change (1/2:ℂ) * (D 1 + Complex.I * D Complex.I) = 0 at hdbar
      have hh := (mul_eq_zero.mp hdbar).resolve_left (by norm_num)
      have hI : Complex.I * D 1 - D Complex.I = 0 := by
        calc
          _ = Complex.I * (D 1 + Complex.I * D Complex.I) := by
            rw [mul_add, ← mul_assoc, Complex.I_mul_I]
            ring
          _ = 0 := by rw [hh, mul_zero]
      change D Complex.I = Complex.I * D 1
      linear_combination -hI
    have uniform_mollifier (f F : ℂ → ℂ) (c : ℂ) (r : ℝ) (hr : 0 < r)
        (hf : ContinuousOn f (closedBall c (2*r)))
        (hF : AEStronglyMeasurable F volume)
        (heq : ∀ y ∈ closedBall c (2*r), F y = f y)
        (phi : ℕ → ContDiffBump (0 : ℂ))
        (hphi : Tendsto (fun n => (phi n).rOut) atTop (𝓝 0)) :
        TendstoUniformlyOn (fun n => MeasureTheory.convolution ((phi n).normed volume) F (lsmul ℝ ℝ) volume)
          f atTop (ball c r) := by
      apply Metric.tendstoUniformlyOn_iff.mpr
      intro eps heps
      have huc := (isCompact_closedBall c (2*r)).uniformContinuousOn_of_continuous hf
      obtain ⟨d, hd, hdclose⟩ := Metric.uniformContinuousOn_iff.mp huc (eps/2) (by linarith)
      have hevent : ∀ᶠ n in atTop, (phi n).rOut < min r d :=
        (tendsto_order.1 hphi).2 _ (lt_min hr hd)
      filter_upwards [hevent] with n hn
      intro x hx
      have hxc : x ∈ closedBall c (2*r) := by
        apply mem_closedBall.mpr
        have := mem_ball.mp hx
        linarith
      have hbound : dist ((MeasureTheory.convolution ((phi n).normed volume) F (lsmul ℝ ℝ) volume) x) (F x) ≤ eps/2 := by
        apply (phi n).dist_normed_convolution_le hF
        intro y hy
        have hyc : y ∈ closedBall c (2*r) := by
          apply mem_closedBall.mpr
          have ht := dist_triangle y x c
          have hxy := mem_ball.mp hy
          have hxc' := mem_ball.mp hx
          have hnr := lt_of_lt_of_le hn (min_le_left r d)
          linarith
        rw [heq y hyc, heq x hxc]
        apply le_of_lt
        apply hdclose y hyc x hxc
        exact (mem_ball.mp hy).trans (hn.trans_le (min_le_right r d))
      rw [heq x hxc] at hbound
      rw [dist_comm]
      exact hbound.trans_lt (by linarith)
    intro c hc
    obtain ⟨e, he, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hc)
    let r : ℝ := e/2
    have hr : 0 < r := by dsimp [r]; linarith
    have h2r : 2*r = e := by dsimp [r]; ring
    let F : ℂ → ℂ := (closedBall c e).indicator f
    have hFI : Integrable F := by
      apply (integrable_indicator_iff isClosed_closedBall.measurableSet).mpr
      exact (hf.mono hsub).integrableOn_compact (isCompact_closedBall c e)
    have hFagree (y : ℂ) (hy : y ∈ closedBall c e) : F y = f y := indicator_of_mem hy f
    let phi : ℕ → ContDiffBump (0 : ℂ) := fun n =>
      { rIn := (1 / ((n:ℝ)+1))/2
        rOut := 1 / ((n:ℝ)+1)
        rIn_pos := by positivity
        rIn_lt_rOut := by
          have : 0 < 1 / ((n:ℝ)+1) := by positivity
          linarith }
    have hphi : Tendsto (fun n => (phi n).rOut) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    let g : ℕ → ℂ → ℂ := fun n y => ((phi n).normed volume y : ℂ)
    let G : ℕ → ℂ → ℂ := fun n => MeasureTheory.convolution F (g n) (ContinuousLinearMap.mul ℝ ℂ) volume
    have hgeq (n : ℕ) : G n = MeasureTheory.convolution ((phi n).normed volume) F (lsmul ℝ ℝ) volume := by
      funext z
      change (MeasureTheory.convolution F (g n) (ContinuousLinearMap.mul ℝ ℂ) volume) z = _
      rw [convolution_eq_swap]
      simp only [convolution_def, ContinuousLinearMap.mul_apply', lsmul_apply]
      apply integral_congr_ae
      filter_upwards [] with y
      change F (z-y) * ((phi n).normed volume y : ℂ) = (phi n).normed volume y • F (z-y)
      rw [Complex.real_smul, mul_comm]
    have hlim : TendstoUniformlyOn G f atTop (ball c r) := by
      have hlim' := uniform_mollifier f F c r hr (by rw [h2r]; exact hf.mono hsub)
        hFI.aestronglyMeasurable (by rw [h2r]; exact hFagree) phi hphi
      have hGG : G = (fun n => MeasureTheory.convolution ((phi n).normed volume) F (lsmul ℝ ℝ) volume) := funext hgeq
      rw [hGG]
      exact hlim'
    have hhol : ∀ᶠ n in atTop, DifferentiableOn ℂ (G n) (ball c r) := by
      filter_upwards [(tendsto_order.mp hphi).2 r hr] with n hn
      intro z hz
      have hgsmooth : ContDiff ℝ ∞ (g n) :=
        Complex.ofRealCLM.contDiff.comp (phi n).contDiff_normed
      have hgc : HasCompactSupport (g n) := ((phi n).hasCompactSupport_normed (μ := volume)).comp_left (g := Complex.ofRealCLM) rfl
      have hgs : tsupport (g n) ⊆ closedBall 0 (phi n).rOut := by
        exact (tsupport_comp_subset (g := Complex.ofRealCLM) rfl ((phi n).normed volume)).trans
          (by rw [(phi n).tsupport_normed_eq])
      apply DifferentiableAt.differentiableWithinAt
      apply mollified_holomorphic U f F (g n) hFI.locallyIntegrable hgsmooth hgc hweak z
      intro y hy
      have hdist : dist y z ≤ (phi n).rOut := by
        have h := Metric.mem_closedBall.mp (hgs hy)
        rw [dist_zero_right] at h
        rw [dist_eq_norm_sub']
        exact h
      have hyc : y ∈ closedBall c e := by
        apply mem_closedBall.mpr
        have htri := dist_triangle y z c
        have hzc := mem_ball.mp hz
        rw [← h2r]
        linarith
      exact ⟨hsub hyc, hFagree y hyc⟩
    have hlocal : DifferentiableOn ℂ f (ball c r) :=
      hlim.tendstoLocallyUniformlyOn.differentiableOn hhol isOpen_ball
    exact ((hlocal c (mem_ball_self hr)).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr))).differentiableWithinAt
  exact continuous_weak_cr U hU _ product_cont product_weak


end SeifertSurfaces.OriginalEndpoints.B1Tangency.CauchyGauge
