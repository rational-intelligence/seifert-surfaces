import IsothermalPDEData

noncomputable section
open Set Topology MeasureTheory
open scoped ContDiff NNReal ENNReal

namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower
open SeifertSurfaces.AppendixACoordinates

/-- A continuous, locally original-alpha Holder weakly closed field on the
full ball has a center-normalized potential with the same exponent. -/
theorem continuous_weak_poincare_ball_original_alpha
    (y : E2) (r : ℝ) (radius_positive : 0 < r)
    (alpha : ℝ≥0) (alpha_positive : 0 < alpha) (F : E2 → E2)
    (continuous_F : ContinuousOn F (Metric.ball y r))
    (local_holder : ∀ x ∈ Metric.ball y r, ∃ s : ℝ,
      0 < s ∧ Metric.ball x s ⊆ Metric.ball y r ∧
      ∀ i : Fin 2, ∃ C : ℝ≥0,
        HolderOnWith C alpha (fun z => F z i) (Metric.ball x s))
    (weak_closed : ∀ φ : E2 → ℝ,
      ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Metric.ball y r →
      IntegrableOn
        (fun x => F x 1 * planarGradient φ x 0 - F x 0 * planarGradient φ x 1)
        (Metric.ball y r) ∧
      (∫ x in Metric.ball y r,
        F x 1 * planarGradient φ x 0 - F x 0 * planarGradient φ x 1) = 0) :
    ∃ b : E2 → ℝ, b y = 0 ∧ ScalarC1AlphaOn alpha b (Metric.ball y r) ∧
      ∀ x ∈ Metric.ball y r, planarGradient b x = F x := by
  let b : E2 → ℝ := fun z =>
    ∫ t in (0 : ℝ)..1, inner ℝ (F (y + t • (z - y))) (z - y)
  have hlineIntegrable : ∀ x ∈ Metric.ball y r, ∀ z ∈ Metric.ball y r,
      IntervalIntegrable (fun t : ℝ => inner ℝ (F (x + t • (z - x))) (z - x))
        MeasureTheory.volume 0 1 := by
    intro x hx z hz
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    apply (continuous_F.comp
      (continuous_const.add (continuous_id.smul continuous_const)).continuousOn ?_).inner
      continuousOn_const
    intro t ht
    exact (convex_ball y r).add_smul_sub_mem hx hz ht
  have hsegment : ∀ x ∈ Metric.ball y r, ∀ z ∈ Metric.ball y r,
      b z - b x =
        ∫ t in (0 : ℝ)..1, inner ℝ (F (x + t • (z - x))) (z - x) := by
    have htranslated_gradient (a : E2) (k : E2 → ℝ) (hk : ContDiff ℝ ∞ k)
        (z : E2) (i : Fin 2) :
        planarGradient (fun z => k (a - z)) z i =
          -fderiv ℝ k (a - z) (coordinateVector 2 i) := by
      have hD := (hk.differentiable (by simp) (a - z)).hasFDerivAt.comp z
        ((hasFDerivAt_const a z).sub (hasFDerivAt_id z))
      change HasFDerivAt (fun z => k (a - z)) _ z at hD
      simp only [planarGradient, hD.fderiv]
      fin_cases i <;> simp [coordinateVector]
    have hkernel_closed (a : E2) (k : E2 → ℝ)
        (hk : ContDiff ℝ ∞ k) (hkc : HasCompactSupport k)
        (hku : tsupport (fun z => k (a - z)) ⊆ Metric.ball y r) :
        IntegrableOn (fun z =>
          F z 1 * fderiv ℝ k (a - z) (coordinateVector 2 0) -
          F z 0 * fderiv ℝ k (a - z) (coordinateVector 2 1)) (Metric.ball y r) ∧
        (∫ z in Metric.ball y r,
          F z 1 * fderiv ℝ k (a - z) (coordinateVector 2 0) -
          F z 0 * fderiv ℝ k (a - z) (coordinateVector 2 1)) = 0 := by
      let φ : E2 → ℝ := fun z => k (a - z)
      have hφ : ContDiff ℝ ∞ φ := hk.comp (contDiff_const.sub contDiff_id)
      have hφc : HasCompactSupport φ := by
        let T : Homeomorph E2 E2 := (Homeomorph.neg E2).trans (Homeomorph.addLeft a)
        simpa [φ, T, Function.comp_def, sub_eq_add_neg] using hkc.comp_homeomorph T
      have hw := weak_closed φ hφ hφc hku
      have heq : (fun z => F z 1 * planarGradient φ z 0 -
          F z 0 * planarGradient φ z 1) =
          (fun z => -(F z 1 * fderiv ℝ k (a - z) (coordinateVector 2 0) -
            F z 0 * fderiv ℝ k (a - z) (coordinateVector 2 1))) := by
        funext z
        dsimp [φ]
        rw [htranslated_gradient a k hk, htranslated_gradient a k hk]
        ring
      rw [heq] at hw
      refine ⟨integrable_neg_iff.mp hw.1, ?_⟩
      simpa only [integral_neg, neg_eq_zero] using hw.2
    have hkernel_global (a : E2) (k : E2 → ℝ)
        (hk : ContDiff ℝ ∞ k) (hkc : HasCompactSupport k)
        (hku : tsupport (fun z => k (a - z)) ⊆ Metric.ball y r)
        (G : E2 → E2) (hGF : ∀ z ∈ tsupport (fun z => k (a - z)), G z = F z) :
        (∫ z, G z 1 * fderiv ℝ k (a - z) (coordinateVector 2 0) -
          G z 0 * fderiv ℝ k (a - z) (coordinateVector 2 1)) = 0 := by
      have hzero (z : E2) (hz : z ∉ tsupport (fun z => k (a - z))) (i : Fin 2) :
          fderiv ℝ k (a - z) (coordinateVector 2 i) = 0 := by
        have h := htranslated_gradient a k hk z i
        rw [planarGradient_eq_zero_off_support _ hz] at h
        simpa using h.symm
      have heq : (fun z => G z 1 * fderiv ℝ k (a - z) (coordinateVector 2 0) -
          G z 0 * fderiv ℝ k (a - z) (coordinateVector 2 1)) =
          (fun z => F z 1 * fderiv ℝ k (a - z) (coordinateVector 2 0) -
            F z 0 * fderiv ℝ k (a - z) (coordinateVector 2 1)) := by
        funext z
        by_cases hz : z ∈ tsupport (fun z => k (a - z))
        · rw [hGF z hz]
        · simp [hzero z hz]
      rw [heq]
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Metric.ball y r)]
      · exact (hkernel_closed a k hk hkc hku).2
      · intro z hz
        have hzs : z ∉ tsupport (fun z => k (a - z)) := fun h => hz (hku h)
        simp [hzero z hzs]
    have hsmoothed_cross (a : E2) (k : E2 → ℝ)
        (hk : ContDiff ℝ ∞ k) (hkc : HasCompactSupport k)
        (hku : tsupport (fun z => k (a - z)) ⊆ Metric.ball y r)
        (G : E2 → E2) (hG : Continuous G)
        (hGF : ∀ z ∈ tsupport (fun z => k (a - z)), G z = F z) :
        fderiv ℝ (convolution (fun z => G z 1) k (ContinuousLinearMap.lsmul ℝ ℝ)) a
            (coordinateVector 2 0) =
          fderiv ℝ (convolution (fun z => G z 0) k (ContinuousLinearMap.lsmul ℝ ℝ)) a
            (coordinateVector 2 1) := by
      have hGi (i : Fin 2) : Continuous (fun z => G z i) :=
        (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp hG
      have hD (i j : Fin 2) :
          fderiv ℝ (convolution (fun z => G z i) k (ContinuousLinearMap.lsmul ℝ ℝ)) a
            (coordinateVector 2 j) =
            ∫ z, G z i * fderiv ℝ k (a - z) (coordinateVector 2 j) := by
        rw [(hkc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
          (hGi i).locallyIntegrable (hk.of_le (by simp)) a).fderiv]
        rw [convolution_precompR_apply (ContinuousLinearMap.lsmul ℝ ℝ) (hGi i).locallyIntegrable (hkc.fderiv ℝ)
          (hk.continuous_fderiv (by simp))]
        rfl
      have hInt (i j : Fin 2) :
          Integrable (fun z => G z i * fderiv ℝ k (a - z) (coordinateVector 2 j)) := by
        exact (hkc.fderiv_apply ℝ (coordinateVector 2 j)).convolutionExists_right
          (ContinuousLinearMap.lsmul ℝ ℝ) (hGi i).locallyIntegrable
          ((hk.continuous_fderiv (by simp)).clm_apply continuous_const) a
      rw [hD, hD]
      have hzero := hkernel_global a k hk hkc hku G hGF
      rw [integral_sub (hInt 1 0) (hInt 0 1)] at hzero
      exact sub_eq_zero.mp hzero
    have hsmoothed_triangle (R : ℝ) (hR : 0 < R) (k : E2 → ℝ)
        (hk : ContDiff ℝ ∞ k) (hkc : HasCompactSupport k)
        (G : E2 → E2) (hG : Continuous G)
        (hku : ∀ a ∈ Metric.ball y R, tsupport (fun z => k (a - z)) ⊆ Metric.ball y r)
        (hGF : ∀ a ∈ Metric.ball y R,
          ∀ z ∈ tsupport (fun z => k (a - z)), G z = F z)
        (x : E2) (hx : x ∈ Metric.ball y R) (z : E2) (hz : z ∈ Metric.ball y R) :
        let form : E2 → E2 →L[ℝ] ℝ := fun a => ∑ i : Fin 2,
          (convolution (fun z => G z i) k (ContinuousLinearMap.lsmul ℝ ℝ) volume a) •
            innerSL ℝ (coordinateVector 2 i)
        (∫ t in (0 : ℝ)..1, form (y + t • (z - y)) (z - y)) -
            (∫ t in (0 : ℝ)..1, form (y + t • (x - y)) (x - y)) =
          ∫ t in (0 : ℝ)..1, form (x + t • (z - x)) (z - x) := by
      let g (i : Fin 2) : E2 → ℝ :=
        convolution (fun z => G z i) k (ContinuousLinearMap.lsmul ℝ ℝ)
      let form : E2 → E2 →L[ℝ] ℝ := fun a => ∑ i : Fin 2,
        g i a • innerSL ℝ (coordinateVector 2 i)
      change (∫ t in (0 : ℝ)..1, form (y + t • (z - y)) (z - y)) -
          (∫ t in (0 : ℝ)..1, form (y + t • (x - y)) (x - y)) =
        ∫ t in (0 : ℝ)..1, form (x + t • (z - x)) (z - x)
      have hg (i : Fin 2) : ContDiff ℝ ∞ (g i) :=
        hkc.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
          ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp hG).locallyIntegrable hk
      have hform (a : E2) : HasFDerivAt form
          (∑ i : Fin 2, (fderiv ℝ (g i) a).smulRight (innerSL ℝ (coordinateVector 2 i))) a :=
        HasFDerivAt.fun_sum fun i _ =>
          ((hg i).differentiable (by simp) a).hasFDerivAt.smul_const
            (innerSL ℝ (coordinateVector 2 i))
      have heval (a u : E2) (j : Fin 2) :
          fderiv ℝ form a u (coordinateVector 2 j) =
            fderiv ℝ (g j) a u := by
        rw [(hform a).fderiv]
        fin_cases j <;>
          simp [Fin.sum_univ_two, coordinateVector, EuclideanSpace.inner_single_right]
      have hsym (a : E2) (ha : a ∈ Metric.ball y R) (u v : E2) :
          fderiv ℝ form a u v = fderiv ℝ form a v u := by
        have huv (w : E2) : w = w 0 • coordinateVector 2 0 + w 1 • coordinateVector 2 1 := by
          ext i
          fin_cases i <;> simp [coordinateVector]
        have hc := hsmoothed_cross a k hk hkc (hku a ha) G hG (hGF a ha)
        change fderiv ℝ (g 1) a (coordinateVector 2 0) =
          fderiv ℝ (g 0) a (coordinateVector 2 1) at hc
        calc
          fderiv ℝ form a u v =
              v 0 * fderiv ℝ (g 0) a u + v 1 * fderiv ℝ (g 1) a u := by
            conv_lhs => rw [huv v]
            simp [heval]
          _ = u 0 * fderiv ℝ (g 0) a v + u 1 * fderiv ℝ (g 1) a v := by
            conv_lhs => rw [huv u]
            conv_rhs => rw [huv v]
            simp only [map_add, map_smul, smul_eq_mul]
            rw [hc]
            ring
          _ = fderiv ℝ form a v u := by
            conv_rhs => rw [huv u]
            simp [heval]
      have ht := (convex_ball y R).curveIntegral_segment_add_eq_of_hasFDerivWithinAt_symmetric
        («ω» := form) (dω := fderiv ℝ form)
        (fun a _ => ((hform a).differentiableAt.hasFDerivAt).hasFDerivWithinAt)
        (fun a ha u _ v _ => hsym a ha u v)
        (Metric.mem_ball_self hR) hx hz
      simp only [curveIntegral_segment, AffineMap.lineMap_apply_module] at ht
      have hline (a c : E2) (t : ℝ) : (1 - t) • a + t • c = a + t • (c - a) := by
        module
      simp only [hline] at ht
      linarith
    intro x hx z hz
    obtain ⟨R, hRlo, hRhi⟩ := exists_between (max_lt (show dist x y < r from hx)
      (show dist z y < r from hz))
    have hR : 0 < R := lt_of_le_of_lt (le_max_of_le_left dist_nonneg) hRlo
    have hxR : x ∈ Metric.ball y R := (le_max_left _ _).trans_lt hRlo
    have hzR : z ∈ Metric.ball y R := (le_max_right _ _).trans_lt hRlo
    have hyR : y ∈ Metric.ball y R := Metric.mem_ball_self hR
    obtain ⟨S, hRS, hSr⟩ := exists_between hRhi
    have hSU : Metric.closedBall y S ⊆ Metric.ball y r := fun a ha => ha.trans_lt hSr
    let Fclosed : C(Metric.closedBall y S, E2) :=
      ⟨fun a => F a, (continuous_F.mono hSU).domRestrict⟩
    obtain ⟨G, hGext⟩ := ContinuousMap.exists_restrict_eq Metric.isClosed_closedBall Fclosed
    have hGF (a : E2) (ha : a ∈ Metric.closedBall y S) : G a = F a := by
      exact congrArg (fun q : C(Metric.closedBall y S, E2) => q ⟨a, ha⟩) hGext
    let δ : ℕ → ℝ := fun n => (S - R) / ((n : ℝ) + 1)
    have hδ (n : ℕ) : 0 < δ n := div_pos (sub_pos.mpr hRS) (by positivity)
    have hδle (n : ℕ) : δ n ≤ S - R := div_le_self (sub_pos.mpr hRS).le (by linarith [Nat.cast_nonneg (α := ℝ) n])
    have hδlim : Filter.Tendsto δ Filter.atTop (𝓝 0) := by
      exact Filter.Tendsto.const_div_atTop
        (Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop) (S - R)
    let bump (n : ℕ) : ContDiffBump (0 : E2) :=
      ⟨δ n / 2, δ n, half_pos (hδ n), half_lt_self (hδ n)⟩
    let k (n : ℕ) : E2 → ℝ := (bump n).normed volume
    have hk (n : ℕ) : ContDiff ℝ ∞ (k n) := (bump n).contDiff_normed
    have hkc (n : ℕ) : HasCompactSupport (k n) := (bump n).hasCompactSupport_normed
    have hlocal (n : ℕ) (a : E2) (ha : a ∈ Metric.ball y R) (v : E2)
        (hv : dist v a ≤ δ n) : v ∈ Metric.closedBall y S := by
      have hat : dist a y < R := ha
      exact (dist_triangle v a y).trans (by linarith [hδle n])
    have hsupport (n : ℕ) (a : E2) (ha : a ∈ Metric.ball y R) :
        tsupport (fun v => k n (a - v)) ⊆ Metric.closedBall y S := by
      intro v hv
      have hpre := tsupport_comp_subset_preimage (k n) (continuous_const.sub continuous_id) hv
      have hvd : dist v a ≤ δ n := by
        simpa [k, ContDiffBump.tsupport_normed_eq, bump, Metric.mem_closedBall,
          dist_eq_norm, norm_sub_rev] using hpre
      exact hlocal n a ha v hvd
    let g (n : ℕ) (i : Fin 2) : E2 → ℝ :=
      convolution (fun a => G a i) (k n) (ContinuousLinearMap.lsmul ℝ ℝ)
    let form (n : ℕ) : E2 → E2 →L[ℝ] ℝ := fun a =>
      ∑ i : Fin 2, g n i a • innerSL ℝ (coordinateVector 2 i)
    have htriangle (n : ℕ) :
        (∫ t in (0 : ℝ)..1, form n (y + t • (z - y)) (z - y)) -
            (∫ t in (0 : ℝ)..1, form n (y + t • (x - y)) (x - y)) =
          ∫ t in (0 : ℝ)..1, form n (x + t • (z - x)) (z - x) :=
      hsmoothed_triangle R hR (k n) (hk n) (hkc n) G G.continuous
        (fun a ha => (hsupport n a ha).trans hSU)
        (fun a ha v hv => hGF v (hsupport n a ha hv)) x hxR z hzR
    have hg_cont (n : ℕ) (i : Fin 2) : Continuous (g n i) :=
      ((hkc n).contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
        ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp G.continuous).locallyIntegrable
        (hk n)).continuous
    have hcomm (n : ℕ) (i : Fin 2) :
        g n i = convolution (k n) (fun a => G a i) (ContinuousLinearMap.lsmul ℝ ℝ) := by
      exact convolution_symm (ContinuousLinearMap.lsmul ℝ ℝ) (by ext; rfl)
    have hg_lim (i : Fin 2) (a : E2) :
        Filter.Tendsto (fun n => g n i a) Filter.atTop (𝓝 (G a i)) := by
      simp only [hcomm]
      exact ContDiffBump.convolution_tendsto_right_of_continuous (φ := bump) hδlim
        ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp G.continuous) a
    obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall y S).exists_bound_of_continuousOn G.continuous.continuousOn
    let M := max M₀ 0
    have hM : 0 ≤ M := le_max_right _ _
    have hg_bound (n : ℕ) (i : Fin 2) (a : E2) (ha : a ∈ Metric.ball y R) :
        ‖g n i a‖ ≤ M := by
      rw [hcomm]
      have hd := dist_convolution_le (μ := volume) (g := fun a => G a i)
        (x₀ := a) (R := δ n) (z₀ := 0) hM
        (f := k n) (by simp [k, bump, ContDiffBump.support_normed_eq])
        ((bump n).nonneg_normed) ((bump n).integral_normed)
        (((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp G.continuous).aestronglyMeasurable)
        (fun v hv => ?_)
      · simpa using hd
      · simpa [M] using (PiLp.norm_apply_le (G v) i).trans
          ((hM₀ v (hlocal n a ha v (show dist v a ≤ δ n from hv.le))).trans (le_max_left M₀ 0))
    have hform_eval (n : ℕ) (a v : E2) :
        form n a v = g n 0 a * v 0 + g n 1 a * v 1 := by
      simp [form, Fin.sum_univ_two, coordinateVector, EuclideanSpace.inner_single_left]
    have hform_cont (n : ℕ) (v : E2) : Continuous (fun a => form n a v) := by
      simp_rw [hform_eval]
      exact ((hg_cont n 0).mul continuous_const).add ((hg_cont n 1).mul continuous_const)
    have hform_lim (a v : E2) (ha : a ∈ Metric.ball y R) :
        Filter.Tendsto (fun n => form n a v) Filter.atTop (𝓝 (inner ℝ (F a) v)) := by
      have hh := ((hg_lim 0 a).mul_const (v 0)).add ((hg_lim 1 a).mul_const (v 1))
      have haS : a ∈ Metric.closedBall y S := (show dist a y < R from ha).le.trans hRS.le
      simpa [hform_eval, hGF a haS, EuclideanSpace.inner_eq_star_dotProduct,
        dotProduct, Fin.sum_univ_two, mul_comm] using hh
    have hform_bound (n : ℕ) (a v : E2) (ha : a ∈ Metric.ball y R) :
        ‖form n a v‖ ≤ M * (‖v 0‖ + ‖v 1‖) := by
      rw [hform_eval]
      calc
        ‖g n 0 a * v 0 + g n 1 a * v 1‖ ≤ ‖g n 0 a‖ * ‖v 0‖ + ‖g n 1 a‖ * ‖v 1‖ := by
          simpa only [norm_mul] using norm_add_le (g n 0 a * v 0) (g n 1 a * v 1)
        _ ≤ M * ‖v 0‖ + M * ‖v 1‖ :=
          add_le_add (mul_le_mul_of_nonneg_right (hg_bound n 0 a ha) (norm_nonneg _))
            (mul_le_mul_of_nonneg_right (hg_bound n 1 a ha) (norm_nonneg _))
        _ = _ := by ring
    have hintegral (a : E2) (ha : a ∈ Metric.ball y R)
        (c : E2) (hc : c ∈ Metric.ball y R) :
        Filter.Tendsto (fun n => ∫ t in (0 : ℝ)..1, form n (a + t • (c - a)) (c - a))
          Filter.atTop (𝓝 (∫ t in (0 : ℝ)..1, inner ℝ (F (a + t • (c - a))) (c - a))) := by
      simp only [intervalIntegral.integral_of_le zero_le_one]
      apply tendsto_integral_of_dominated_convergence
        (fun _ : ℝ => M * (‖(c - a) 0‖ + ‖(c - a) 1‖))
      · intro n
        exact ((hform_cont n (c - a)).comp
          (continuous_const.add (continuous_id.smul continuous_const))).aestronglyMeasurable
      · exact integrable_const _
      · intro n
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact hform_bound n _ _
          ((convex_ball y R).add_smul_sub_mem ha hc ⟨le_of_lt ht.1, ht.2⟩)
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact hform_lim _ _
          ((convex_ball y R).add_smul_sub_mem ha hc ⟨le_of_lt ht.1, ht.2⟩)
    have hleft := (hintegral y hyR z hzR).sub (hintegral y hyR x hxR)
    have hright := hintegral x hxR z hzR
    have heq : (fun n =>
        (∫ t in (0 : ℝ)..1, form n (y + t • (z - y)) (z - y)) -
          (∫ t in (0 : ℝ)..1, form n (y + t • (x - y)) (x - y))) =
        (fun n => ∫ t in (0 : ℝ)..1, form n (x + t • (z - x)) (z - x)) :=
      funext htriangle
    rw [heq] at hleft
    exact tendsto_nhds_unique hleft hright
  have hderiv : ∀ x ∈ Metric.ball y r, HasFDerivAt b (innerSL ℝ (F x)) x := by
    intro x hx
    rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
    intro ε hε
    have hFc : ContinuousAt F x := continuous_F.continuousAt (Metric.isOpen_ball.mem_nhds hx)
    obtain ⟨δ, hδ, hδF⟩ := Metric.continuousAt_iff.1 hFc ε hε
    obtain ⟨ρ, hρ, hρU⟩ := Metric.isOpen_iff.1 Metric.isOpen_ball x hx
    apply Metric.eventually_nhds_iff.2
    refine ⟨min δ ρ, lt_min hδ hρ, ?_⟩
    intro h hh
    have hh' : ‖h‖ < min δ ρ := by simpa using hh
    have hpath_dist : ∀ t ∈ Set.Icc (0 : ℝ) 1, dist (x + t • h) x ≤ ‖h‖ := by
      intro t ht
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1]
      exact mul_le_of_le_one_left (norm_nonneg _) ht.2
    have hpathU : ∀ t ∈ Set.Icc (0 : ℝ) 1, x + t • h ∈ Metric.ball y r := by
      intro t ht
      apply hρU
      exact (hpath_dist t ht).trans_lt (hh'.trans_le (min_le_right _ _))
    have hxph : x + h ∈ Metric.ball y r := by simpa using hpathU 1 ⟨zero_le_one, le_rfl⟩
    have hint : IntervalIntegrable (fun t : ℝ => inner ℝ (F (x + t • h)) h)
        MeasureTheory.volume 0 1 := by
      simpa only [add_sub_cancel_left] using hlineIntegrable x hx (x + h) hxph
    have hid : b (x + h) - b x - (innerSL ℝ (F x)) h =
        ∫ t in (0 : ℝ)..1, inner ℝ (F (x + t • h) - F x) h := by
      rw [hsegment x hx (x + h) hxph]
      simp only [add_sub_cancel_left]
      simp only [inner_sub_left]
      rw [intervalIntegral.integral_sub hint intervalIntegrable_const]
      simp
    rw [hid]
    have hbound : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
        ‖inner ℝ (F (x + t • h) - F x) h‖ ≤ ε * ‖h‖ := by
      intro t ht
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
        simpa only [Set.uIcc_of_le zero_le_one] using (Set.uIoc_subset_uIcc ht)
      have hsmall : ‖F (x + t • h) - F x‖ < ε := by
        simpa only [dist_eq_norm] using
          hδF ((hpath_dist t ht').trans_lt (hh'.trans_le (min_le_left _ _)))
      exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hsmall.le (norm_nonneg _))
    simpa using intervalIntegral.norm_integral_le_of_norm_le_const hbound
  have hgrad : ∀ x ∈ Metric.ball y r, planarGradient b x = F x := by
    intro x hx
    ext i
    simp only [planarGradient, (hderiv x hx).fderiv]
    fin_cases i <;>
      simp [coordinateVector, EuclideanSpace.inner_single_right]
  have hC1 : ContDiffOn ℝ 1 b (Metric.ball y r) := by
    rw [show (1 : ℕ∞ω) = 0 + 1 from rfl,
      contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn Metric.isOpen_ball.uniqueDiffOn]
    refine ⟨by simp, fun x => innerSL ℝ (F x), ?_, fun x hx => (hderiv x hx).hasFDerivWithinAt⟩
    rw [contDiffOn_zero]
    exact (innerSL ℝ).continuous.comp_continuousOn continuous_F
  refine ⟨b, ?_, ⟨hC1, ?_⟩, hgrad⟩
  · simp [b]
  · intro x hx
    obtain ⟨s, hs, hsU, hsH⟩ := local_holder x hx
    refine ⟨s, hs, hsU, ?_⟩
    intro i
    obtain ⟨C, hC⟩ := hsH i
    refine ⟨C, ?_⟩
    intro z hz w hw
    simpa only [hgrad z (hsU hz), hgrad w (hsU hw)] using hC z hz w hw

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower
