import B1L1IndependentLower
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
set_option autoImplicit false
noncomputable section
open Set Topology Function MeasureTheory
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak.AnalyticLower
open SeifertSurfaces.AppendixACoordinates L1Independent
theorem native_Green_actual_boundary_AE (R : ℝ) (Ω : SmoothFlatJordanDomain R)
    (d : Fin 2 → E2 → E2) (theta : ℝ → ℝ) (sigma : ℝ)
    (lift : WeakMonotoneBoundaryLift Ω theta sigma) :
    ∀ u : E2 → E2,
      ContinuousOn u (closedDisc 1) →
      (∀ i, H1On (disc 1) (fun x => u x i) (d i)) →
      HasGreenBoundaryTrace u d (liftedBoundaryValue Ω theta) →
      (fun t => u (unitCircleParameter t)) =ᵐ[volume.restrict (Icc 0 (2 * Real.pi))]
        liftedBoundaryValue Ω theta := by
  set_option cleanup.letToHave false in
  set_option maxHeartbeats 0 in
  exact (by
    have hradial (g : E2 → ℝ) (hg : ContinuousOn g (closedDisc 1)) :
        Filter.Tendsto (fun n : ℕ => ∫ x in disc 1,
          (2 * ((n : ℝ) + 1)) * (‖x‖ ^ 2) ^ n * g x) Filter.atTop
          (𝓝 (∫ t in Icc 0 (2 * Real.pi), g (unitCircleParameter t))) := by
      have hpolar (f : E2 → ℝ) :
          (∫ x in disc 1, f x) =
            ∫ p in Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi,
              p.1 * f (p.1 • unitCircleParameter p.2) := by
        let e : E2 ≃L[ℝ] (ℝ × ℝ) :=
          (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).trans
            (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
        have hmp : MeasurePreserving e volume volume :=
          (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))
        let Q := Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi
        have he (r t : ℝ) : e.symm (polarCoord.symm (r,t)) = r • unitCircleParameter t := by
          apply PiLp.ext
          intro i
          fin_cases i <;> dsimp only [e, unitCircleParameter] <;> simp [polarCoord_symm_apply]
        have hnorm (r t : ℝ) : ‖r • unitCircleParameter t‖ = |r| := by
          rw [norm_smul, Real.norm_eq_abs]
          suffices ‖unitCircleParameter t‖ = 1 by rw [this,mul_one]
          have h : ‖unitCircleParameter t‖ ^ 2 = 1 := by
            rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
            exact Real.cos_sq_add_sin_sq t
          nlinarith [norm_nonneg (unitCircleParameter t)]
        have hdisc : MeasurableSet (disc (1 : ℝ)) := Metric.isOpen_ball.measurableSet
        have hq : MeasurableSet Q := measurableSet_Ioo.prod measurableSet_Ioo
        have hsub : Q ⊆ polarCoord.target := by intro p hp; exact ⟨hp.1.1,hp.2⟩
        calc
          (∫ x in disc 1, f x) = ∫ x : E2, (disc 1).indicator f x := (integral_indicator hdisc).symm
          _ = ∫ p : ℝ × ℝ, (disc 1).indicator f (e.symm p) := by
            simpa only [e.symm_apply_apply] using
              (hmp.integral_comp e.toHomeomorph.measurableEmbedding (fun p => (disc 1).indicator f (e.symm p)))
          _ = ∫ p in polarCoord.target, p.1 * (disc 1).indicator f (e.symm (polarCoord.symm p)) := by
            simpa only [smul_eq_mul] using (integral_comp_polarCoord_symm (fun p => (disc 1).indicator f (e.symm p))).symm
          _ = ∫ p in polarCoord.target, Q.indicator (fun p => p.1 * f (p.1 • unitCircleParameter p.2)) p := by
            apply setIntegral_congr_fun polarCoord.open_target.measurableSet
            intro p hp
            have hm : e.symm (polarCoord.symm p) ∈ disc 1 ↔ p ∈ Q := by
              rw [he p.1 p.2]
              change dist (p.1 • unitCircleParameter p.2) 0 < 1 ↔ _
              rw [dist_zero_right, hnorm, abs_of_pos hp.1]
              exact ⟨fun h => ⟨⟨hp.1,h⟩,hp.2⟩,fun h => h.1.2⟩
            change p.1 * (disc 1).indicator f (e.symm (polarCoord.symm p)) = _
            by_cases hh : p ∈ Q
            · rw [indicator_of_mem hh,indicator_of_mem (hm.mpr hh), he p.1 p.2]
            · rw [indicator_of_notMem hh,indicator_of_notMem (mt hm.mp hh),mul_zero]
          _ = ∫ p in polarCoord.target ∩ Q, p.1 * f (p.1 • unitCircleParameter p.2) := by
            rw [setIntegral_indicator hq]
          _ = ∫ p in Q, p.1 * f (p.1 • unitCircleParameter p.2) := by
            rw [inter_eq_right.mpr hsub]
      have hpeak (H : ℝ → ℝ) (hH : ContinuousOn H (Icc 0 1)) :
          Filter.Tendsto (fun n : ℕ => (2 * ((n : ℝ) + 1)) *
            ∫ r in Ioo (0 : ℝ) 1, r ^ (2*n+1) * H r) Filter.atTop (𝓝 (H 1)) := by
        have hc : ContinuousOn (fun r : ℝ => r) (Icc 0 1) := continuousOn_id
        have hmax : ∀ y ∈ Icc (0 : ℝ) 1, y ≠ 1 → y < 1 := by
          intro y hy hn
          exact lt_of_le_of_ne hy.2 hn
        have hcl : (1 : ℝ) ∈ closure (interior (Icc (0 : ℝ) 1)) := by
          rw [interior_Icc, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
          exact ⟨by norm_num,le_rfl⟩
        have hl := tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_continuousOn
          (μ := (volume : Measure ℝ)) isCompact_Icc hc hmax (fun x hx => hx.1) (by norm_num) hcl hH
        have hi (n : ℕ) : (∫ r in Icc (0 : ℝ) 1, r ^ n) = ((n : ℝ) + 1)⁻¹ := by
          rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
          rw [integral_pow]
          simp
        have ht : Filter.Tendsto (fun n : ℕ => 2*n+1) Filter.atTop Filter.atTop := by
          apply Filter.tendsto_atTop_mono (fun n : ℕ => show n ≤ 2*n+1 from (Nat.le_mul_of_pos_left n (by decide : 0 < 2)).trans (Nat.le_add_right _ _)) Filter.tendsto_id
        have h := hl.comp ht
        simp only [hi, inv_inv, smul_eq_mul, Function.comp_def, integral_Icc_eq_integral_Ioo,
          Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at h
        convert h using 1
        congr 1
        funext n
        ring
      have hcircle (t : ℝ) : ‖unitCircleParameter t‖ = 1 := by
        have h : ‖unitCircleParameter t‖ ^ 2 = 1 := by
          rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
          exact Real.cos_sq_add_sin_sq t
        nlinarith [norm_nonneg (unitCircleParameter t)]
      have hc : Continuous unitCircleParameter := by
        change Continuous (fun t : ℝ => WithLp.toLp 2 ![Real.cos t, Real.sin t])
        fun_prop
      have hmem (r t : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) : r • unitCircleParameter t ∈ closedDisc 1 := by
        change dist (r • unitCircleParameter t) 0 ≤ 1
        rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr.1, hcircle, mul_one]
        exact hr.2
      let H : ℝ → ℝ := fun r => ∫ t in Ioo (-Real.pi) Real.pi, g (r • unitCircleParameter t)
      have hH : ContinuousOn H (Icc 0 1) := by
        rw [continuousOn_iff_continuous_restrict]
        have hcomp : Continuous (fun p : Icc (0 : ℝ) 1 × ℝ => g ((p.1 : ℝ) • unitCircleParameter p.2)) := by
          exact hg.comp_continuous ((continuous_subtype_val.comp continuous_fst).smul (hc.comp continuous_snd))
            (fun p => hmem p.1 p.2 p.1.property)
        have hh := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
          (μ := (volume : Measure ℝ)) (f := fun (r : Icc (0 : ℝ) 1) (t : ℝ) => g ((r : ℝ) • unitCircleParameter t)) hcomp (-Real.pi) Real.pi
        change Continuous (fun r : Icc (0 : ℝ) 1 => ∫ t in Ioo (-Real.pi) Real.pi, g ((r : ℝ) • unitCircleParameter t))
        simpa only [ intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi),
          integral_Ioc_eq_integral_Ioo] using hh
      have he (n : ℕ) : (∫ x in disc 1, (2 * ((n : ℝ) + 1)) * (‖x‖ ^ 2) ^ n * g x) =
          (2 * ((n : ℝ) + 1)) * ∫ r in Ioo (0 : ℝ) 1, r ^ (2*n+1) * H r := by
        rw [hpolar]
        let F : ℝ × ℝ → ℝ := fun p => p.1 * ((2 * ((n : ℝ) + 1)) * (‖p.1 • unitCircleParameter p.2‖ ^ 2) ^ n * g (p.1 • unitCircleParameter p.2))
        have hFc : ContinuousOn F (Icc (0 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi) := by
          apply ContinuousOn.mul continuous_fst.continuousOn
          apply ContinuousOn.mul
          · fun_prop
          · exact hg.comp ((continuous_fst.smul (hc.comp continuous_snd)).continuousOn) (fun p hp => hmem p.1 p.2 hp.1)
        have hFi : IntegrableOn F (Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi) :=
          (hFc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
        change (∫ p in Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi, F p) = _
        rw [Measure.volume_eq_prod, setIntegral_prod F (by simpa only [Measure.volume_eq_prod] using hFi)]
        rw [← integral_const_mul]
        apply setIntegral_congr_fun measurableSet_Ioo
        intro r hr
        change (∫ t in Ioo (-Real.pi) Real.pi, r * ((2 * ((n : ℝ) + 1)) * (‖r • unitCircleParameter t‖ ^ 2) ^ n * g (r • unitCircleParameter t))) = _
        have halg (t : ℝ) : r * ((2 * ((n : ℝ) + 1)) * (‖r • unitCircleParameter t‖ ^ 2) ^ n * g (r • unitCircleParameter t)) =
            ((2 * ((n : ℝ) + 1)) * r ^ (2*n+1)) * g (r • unitCircleParameter t) := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr.1, hcircle, mul_one, ← pow_mul]
          ring
        simp_rw [halg]
        rw [integral_const_mul]
        dsimp only [H]
        ring
      have hlim := hpeak H hH
      have hp : Function.Periodic (fun t => g (unitCircleParameter t)) (2 * Real.pi) := by
        intro t
        apply congrArg g
        apply PiLp.ext
        intro i
        fin_cases i <;> dsimp only [unitCircleParameter] <;> simp [Real.cos_add_two_pi, Real.sin_add_two_pi]
      have hH1 : H 1 = ∫ t in Icc 0 (2 * Real.pi), g (unitCircleParameter t) := by
        dsimp [H]
        simp only [one_smul]
        rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
        have hperiod := hp.intervalIntegral_add_eq (-Real.pi) 0
        have hepi : -Real.pi + 2 * Real.pi = Real.pi := by ring
        rw [hepi, zero_add] at hperiod
        rw [hperiod, intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
        exact integral_Icc_eq_integral_Ioc.symm
      simpa only [he, hH1] using hlim
    have hreduction (u : E2 → E2) (d : Fin 2 → E2 → E2) (b : ℝ → E2)
        (hu : ContinuousOn u (closedDisc 1)) (hG : HasGreenBoundaryTrace u d b)
        (hRadial : ∀ g : E2 → ℝ, ContinuousOn g (closedDisc 1) →
          Filter.Tendsto (fun n : ℕ => ∫ x in disc 1,
            (2 * ((n : ℝ) + 1)) * (‖x‖ ^ 2) ^ n * g x) Filter.atTop
            (𝓝 (∫ t in Icc 0 (2 * Real.pi), g (unitCircleParameter t)))) :
        ∀ (ψ : E2 → ℝ), ContDiff ℝ ∞ ψ → ∀ i j : Fin 2,
          (∫ t in Icc 0 (2 * Real.pi),
            (u (unitCircleParameter t) i - b t i) * ψ (unitCircleParameter t) *
              unitCircleParameter t j) = 0 := by
      intro ψ hψ i j
      let q : E2 → ℝ := fun x => ‖x‖ ^ 2
      let a : E2 → ℝ := fun x => u x i * fderiv ℝ ψ x (coordinateVector 2 j) +
        d i x j * ψ x
      let g : E2 → ℝ := fun x => u x i * ψ x * x j
      have hq : ContDiff ℝ ∞ q := contDiff_id.norm_sq ℝ
      have hqD (x : E2) : fderiv ℝ q x (coordinateVector 2 j) = 2 * x j := by
        simp [q, fderiv_norm_sq_apply, coordinateVector, EuclideanSpace.inner_single_right]
      have hcircle (t : ℝ) : q (unitCircleParameter t) = 1 := by
        dsimp [q]
        rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
        exact Real.cos_sq_add_sin_sq t
      have hcmem (t : ℝ) : unitCircleParameter t ∈ closedDisc 1 := by
        change dist (unitCircleParameter t) 0 ≤ 1
        rw [dist_zero_right]
        have h := hcircle t
        dsimp [q] at h
        nlinarith [norm_nonneg (unitCircleParameter t)]
      have hc : Continuous unitCircleParameter := by
        change Continuous (fun t : ℝ => WithLp.toLp 2 ![Real.cos t, Real.sin t])
        fun_prop
      have hgc : ContinuousOn g (closedDisc 1) := by
        exact ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) i).comp_continuousOn hu).mul
          hψ.continuous.continuousOn |>.mul (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) j).continuousOn
      have hgi : IntegrableOn g (disc 1) :=
        (hgc.integrableOn_compact (isCompact_closedBall (0 : E2) 1)).mono_set
          Metric.ball_subset_closedBall
      have hai : IntegrableOn a (disc 1) := (hG ψ hψ i j).1
      have hqc : Continuous q := hq.continuous
      have hqbound : ∀ x ∈ disc 1, 0 ≤ q x ∧ q x < 1 := by
        intro x hx
        have hx' : ‖x‖ < 1 := by change dist x 0 < 1 at hx; rwa [dist_zero_right] at hx
        exact ⟨sq_nonneg _, by dsimp [q]; nlinarith [norm_nonneg x]⟩
      have hsmall : Filter.Tendsto (fun n : ℕ => ∫ x in disc 1, a x * q x ^ (n + 1))
          Filter.atTop (𝓝 (0 : ℝ)) := by
        have hpoint : ∀ᵐ x ∂volume.restrict (disc 1),
            Filter.Tendsto (fun n : ℕ => a x * q x ^ (n + 1)) Filter.atTop (𝓝 0) := by
          filter_upwards [ae_restrict_mem (show MeasurableSet (disc 1) from Metric.isOpen_ball.measurableSet)] with x hx
          have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one (hqbound x hx).1 (hqbound x hx).2
          simpa using (tendsto_const_nhds.mul (hlim.comp (Filter.tendsto_add_atTop_nat 1)))
        have hdom : ∀ n : ℕ, ∀ᵐ x ∂volume.restrict (disc 1),
            ‖a x * q x ^ (n + 1)‖ ≤ ‖a x‖ := by
          intro n
          filter_upwards [ae_restrict_mem (show MeasurableSet (disc 1) from Metric.isOpen_ball.measurableSet)] with x hx
          rw [norm_mul, Real.norm_of_nonneg (pow_nonneg (hqbound x hx).1 (n+1))]
          exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (hqbound x hx).1 (hqbound x hx).2.le)
        have hm (n : ℕ) : AEStronglyMeasurable (fun x => a x * q x ^ (n + 1))
            (volume.restrict (disc 1)) :=
          hai.aestronglyMeasurable.mul ((hqc.pow (n+1)).aestronglyMeasurable.restrict)
        simpa using tendsto_integral_of_dominated_convergence (fun x => ‖a x‖)
          hm hai.norm hdom hpoint
      have he (n : ℕ) :
          (∫ x in disc 1, a x * q x ^ (n + 1)) +
          (∫ x in disc 1, (2 * ((n : ℝ) + 1)) * q x ^ n * g x) =
          ∫ t in Icc 0 (2 * Real.pi), b t i * ψ (unitCircleParameter t) * unitCircleParameter t j := by
        have hw : ContDiff ℝ ∞ (fun x => ψ x * q x ^ (n+1)) := hψ.mul (hq.pow (n+1))
        have hwd (x : E2) :
            fderiv ℝ (fun x => ψ x * q x ^ (n+1)) x (coordinateVector 2 j) =
            fderiv ℝ ψ x (coordinateVector 2 j) * q x ^ (n+1) +
            ψ x * ((n : ℝ) + 1) * q x ^ n * (2 * x j) := by
          change (fderiv ℝ (ψ * fun x => q x ^ (n+1)) x) _ = _
          rw [fderiv_mul (hψ.differentiable (by simp) x) ((hq.pow (n+1)).differentiable (by simp) x)]
          simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
          rw [((hq.differentiable (by simp) x).hasFDerivAt.pow (n+1)).fderiv]
          simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, hqD]
          ring
        have heq := (hG _ hw i j).2.2
        have hint1 : IntegrableOn (fun x => a x * q x ^ (n+1)) (disc 1) := by
          apply hai.mul_bdd (c := 1) ((hqc.pow (n+1)).aestronglyMeasurable.restrict)
          filter_upwards [ae_restrict_mem (show MeasurableSet (disc 1) from Metric.isOpen_ball.measurableSet)] with x hx
          change ‖q x ^ (n+1)‖ ≤ 1
          rw [Real.norm_of_nonneg (pow_nonneg (hqbound x hx).1 _)]
          exact pow_le_one₀ (hqbound x hx).1 (hqbound x hx).2.le
        have hint2 : IntegrableOn (fun x => (2 * ((n : ℝ) + 1)) * q x ^ n * g x) (disc 1) := by
          apply (ContinuousOn.integrableOn_compact (isCompact_closedBall (0 : E2) 1)
            ((continuousOn_const.mul (hqc.pow n).continuousOn).mul hgc)).mono_set Metric.ball_subset_closedBall
        rw [← integral_add hint1 hint2]
        calc
          _ = ∫ x in disc 1, u x i * fderiv ℝ (fun x => ψ x * q x ^ (n+1)) x (coordinateVector 2 j) +
              d i x j * (ψ x * q x ^ (n+1)) := by
            apply integral_congr_ae
            filter_upwards with x
            rw [hwd]
            dsimp [a, g]
            ring
          _ = _ := by simpa only [hcircle, one_pow, mul_one] using heq
      have hlimit := hsmall.add (hRadial g hgc)
      have heq : (∫ t in Icc 0 (2 * Real.pi), g (unitCircleParameter t)) =
          ∫ t in Icc 0 (2 * Real.pi), b t i * ψ (unitCircleParameter t) * unitCircleParameter t j := by
        apply tendsto_nhds_unique (by simpa only [zero_add] using hlimit)
        change Filter.Tendsto (fun n : ℕ => (∫ x in disc 1, a x * q x ^ (n+1)) +
          ∫ x in disc 1, (2 * ((n : ℝ) + 1)) * q x ^ n * g x) _ _
        simpa only [he] using (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ =>
          ∫ t in Icc 0 (2 * Real.pi), b t i * ψ (unitCircleParameter t) * unitCircleParameter t j) Filter.atTop _)
      have hgb : IntegrableOn (fun t => g (unitCircleParameter t)) (Icc 0 (2 * Real.pi)) :=
        (hgc.comp_continuous hc hcmem).integrableOn_Icc
      have hbb := (hG ψ hψ i j).2.1
      calc
        _ = (∫ t in Icc 0 (2 * Real.pi), g (unitCircleParameter t)) -
            ∫ t in Icc 0 (2 * Real.pi), b t i * ψ (unitCircleParameter t) * unitCircleParameter t j := by
          rw [← integral_sub hgb hbb]
          apply integral_congr_ae
          filter_upwards with t
          dsimp [g]
          ring
        _ = 0 := sub_eq_zero.mpr heq
    have hseparate (v : ℝ → E2) (hv : Continuous v)
        (hmoment : ∀ (ψ : E2 → ℝ), ContDiff ℝ ∞ ψ → ∀ i j : Fin 2,
          (∫ t in Icc 0 (2 * Real.pi), v t i * ψ (unitCircleParameter t) * unitCircleParameter t j) = 0) :
        v =ᵐ[volume.restrict (Icc 0 (2 * Real.pi))] 0 := by
      classical
      let T := Ioo (0 : ℝ) (2 * Real.pi)
      letI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
      have hTo : IsOpen T := isOpen_Ioo
      letI : PolishSpace T := hTo.polishSpace
      letI : MeasureSpace T := MeasureTheory.Measure.Subtype.measureSpace (p := fun x : ℝ => x ∈ T)
      let c : T → E2 := fun t => unitCircleParameter t
      have hc : Continuous unitCircleParameter := by
        change Continuous (fun t : ℝ => WithLp.toLp 2 ![Real.cos t, Real.sin t])
        fun_prop
      have hci : Injective c := by
        intro s t hst
        apply Subtype.ext
        have hs : (s : ℝ) ∈ Ico 0 (0 + 2 * Real.pi) := by simpa [T] using Ioo_subset_Ico_self s.property
        have ht : (t : ℝ) ∈ Ico 0 (0 + 2 * Real.pi) := by simpa [T] using Ioo_subset_Ico_self t.property
        apply (AddCircle.coe_eq_coe_iff_of_mem_Ico hs ht).mp
        apply Real.Angle.cos_sin_inj
        · exact congrArg (fun x : E2 => x 0) hst
        · exact congrArg (fun x : E2 => x 1) hst
      have hcme : MeasurableEmbedding c :=
        (hc.comp continuous_subtype_val).measurableEmbedding hci
      letI hnT : Nonempty T := ⟨⟨Real.pi, by constructor <;> linarith [Real.pi_pos]⟩⟩
      let μ : Measure E2 := Measure.map c (volume : Measure T)
      let V : E2 → E2 := fun x => v (hcme.invFun x)
      have hV (t : T) : V (c t) = v t := by dsimp [V]; rw [hcme.leftInverse_invFun]
      have hcoord (i j : Fin 2) :
          ∀ᵐ t : T, v t i * c t j = 0 := by
        let F : E2 → ℝ := fun x => V x i * x j
        have hcont : Continuous (fun t : ℝ => v t i * unitCircleParameter t j) := by
          exact ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) i).comp hv).mul
            ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) j).comp hc)
        have hi : Integrable (F ∘ c) (volume : Measure T) := by
          have hi := (hcont.integrableOn_Icc (μ := volume) (a := 0) (b := 2 * Real.pi)).mono_set Ioo_subset_Icc_self
          rw [integrableOn_iff_comap_subtypeVal measurableSet_Ioo] at hi
          simpa only [F, comp_def, hV, c, T, Measure.Subtype.volume_def] using hi
        have hFi : Integrable F μ := hcme.integrable_map_iff.mpr hi
        have hz : ∀ᵐ x ∂μ, F x = 0 := by
          apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hFi.locallyIntegrable
          intro ψ hψ hcompact
          change (∫ x, ψ x • F x ∂Measure.map c (volume : Measure T)) = 0
          rw [hcme.integral_map]
          simp only [smul_eq_mul, F, hV]
          have he : (∫ t : T, ψ (c t) * (v t i * c t j)) =
              ∫ t in Icc 0 (2 * Real.pi), v t i * ψ (unitCircleParameter t) * unitCircleParameter t j := by
            rw [show (∫ t : T, ψ (c t) * (v t i * c t j)) =
              ∫ t in T, ψ (unitCircleParameter t) * (v t i * unitCircleParameter t j) from
              integral_subtype (s := T) measurableSet_Ioo (fun t : ℝ => ψ (unitCircleParameter t) * (v t i * unitCircleParameter t j))]
            rw [show volume.restrict T = volume.restrict (Icc 0 (2 * Real.pi)) from restrict_Ioo_eq_restrict_Icc]
            apply integral_congr_ae
            filter_upwards with t
            ring
          rw [he]
          exact hmoment ψ hψ i j
        have hz' := hcme.ae_map_iff.mp hz
        simpa only [F, hV] using hz'
      have h0 : ∀ᵐ t : T, v t = 0 := by
        filter_upwards [hcoord 0 0, hcoord 0 1, hcoord 1 0, hcoord 1 1] with t h00 h01 h10 h11
        have hcirc : (c t 0) ^ 2 + (c t 1) ^ 2 = 1 := Real.cos_sq_add_sin_sq t
        apply PiLp.ext
        intro i
        fin_cases i
        · change v t 0 = 0
          nlinarith [sq_nonneg (v t 0), mul_eq_zero.mp h00, mul_eq_zero.mp h01]
        · change v t 1 = 0
          nlinarith [sq_nonneg (v t 1), mul_eq_zero.mp h10, mul_eq_zero.mp h11]
      rw [← restrict_Ioo_eq_restrict_Icc]
      change ∀ᵐ t ∂volume.restrict T, v t = 0
      exact (ae_restrict_iff_subtype measurableSet_Ioo).mpr h0
    intro u hu hH1 hG
    have hc : Continuous unitCircleParameter := by
      change Continuous (fun t : ℝ => WithLp.toLp 2 ![Real.cos t, Real.sin t])
      fun_prop
    have hcmem (t : ℝ) : unitCircleParameter t ∈ closedDisc 1 := by
      have hn : ‖unitCircleParameter t‖ ^ 2 = 1 := by
        rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
        exact Real.cos_sq_add_sin_sq t
      change dist (unitCircleParameter t) 0 ≤ 1
      rw [dist_zero_right]
      nlinarith [norm_nonneg (unitCircleParameter t)]
    have huc : Continuous (fun t => u (unitCircleParameter t)) :=
      hu.comp_continuous hc hcmem
    have hbc : Continuous (liftedBoundaryValue Ω theta) :=
      Ω.boundary.smooth.continuous.comp lift.2.1
    have hm := hreduction u d (liftedBoundaryValue Ω theta) hu hG hradial
    have hz := hseparate (fun t => u (unitCircleParameter t) - liftedBoundaryValue Ω theta t)
      (huc.sub hbc) hm
    filter_upwards [hz] with t ht
    exact sub_eq_zero.mp ht
  )
end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak.AnalyticLower
