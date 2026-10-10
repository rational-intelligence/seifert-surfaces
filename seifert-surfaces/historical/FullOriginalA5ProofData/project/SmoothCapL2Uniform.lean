import B1L1IndependentLower
set_option autoImplicit false
noncomputable section
open Set Topology Function MeasureTheory
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak.AnalyticLower
open SeifertSurfaces.AppendixACoordinates L1Independent

theorem smooth_cap_l2_uniform :
∃ A : ℝ, 0 ≤ A ∧
      ∀ ψ : E2 → ℝ, ContDiff ℝ ∞ ψ →
      ∀ x ∈ closedDisc 1, ∀ r : ℝ, 0 < r → r ≤ 1 →
        eLpNorm (fun z => ψ z - ⨍ y in planarCap x r, ψ y) 2
            (volume.restrict (planarCap x r)) ≤
          ENNReal.ofReal (A * r) * eLpNorm (fun z => ‖fderiv ℝ ψ z‖) 2
            (volume.restrict (planarCap x r)) := by
  set_option maxHeartbeats 600000 in
  open scoped Pointwise in
  classical
  have hsegment (ψ : E2 → ℝ) (hψ : ContDiff ℝ ∞ ψ) (a b : E2) :
      (ψ a - ψ (((1 / 2 : ℝ) • a) + (1 / 2 : ℝ) • b)) ^ 2 ≤
        (1 / 2 : ℝ) * ‖b - a‖ ^ 2 *
          ∫ t in (0 : ℝ)..(1 / 2 : ℝ),
            ‖fderiv ℝ ψ ((1-t) • a + t • b)‖ ^ 2 := by
    let γ : ℝ → E2 := fun t => (1-t) • a + t • b
    let D : ℝ → ℝ := fun t => (fderiv ℝ ψ (γ t)) (b-a)
    have hc : Continuous (fderiv ℝ ψ) := hψ.continuous_fderiv (by simp)
    have hγ : ∀ t, HasDerivAt γ (b-a) t := by
      intro t
      convert (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).smul_const a).add
        ((hasDerivAt_id t).smul_const b) using 1 <;> simp [γ, sub_eq_add_neg, add_comm, Pi.add_def]
    have hd : ∀ t, HasDerivAt (ψ ∘ γ) (D t) t := by
      intro t
      exact (hψ.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt t (hγ t)
    have hDc : Continuous D := by dsimp [D, γ]; fun_prop
    have hgc : Continuous (fun t => ‖fderiv ℝ ψ (γ t)‖ ^ 2) := by dsimp [γ]; fun_prop
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ))
      (b := (1/2 : ℝ)) (fun t _ => hd t) (hDc.intervalIntegrable _ _)
    have hcs : (∫ t in (0 : ℝ)..(1/2 : ℝ), D t) ^ 2 ≤
        (1/2 : ℝ) * ∫ t in (0 : ℝ)..(1/2 : ℝ), (D t)^2 := by
      let m := ∫ t in (0 : ℝ)..(1/2 : ℝ), D t
      have hnonneg := intervalIntegral.integral_nonneg (μ := volume) (a := (0 : ℝ)) (b := (1/2 : ℝ))
        (by norm_num) (fun t _ => sq_nonneg (D t - 2*m))
      have heq : (fun t => (D t - 2*m)^2) =
          (fun t => (D t)^2 - (4*m) * D t + 4*m^2) := by ext t; ring
      have hD2 : IntervalIntegrable (fun t => (D t)^2) volume 0 (1/2) :=
        (hDc.pow 2).intervalIntegrable _ _
      have hmul : IntervalIntegrable (fun t => (4*m) * D t) volume 0 (1/2) :=
        (hDc.const_mul _).intervalIntegrable _ _
      have hconst : IntervalIntegrable (fun _ : ℝ => 4*m^2) volume 0 (1/2) :=
        continuous_const.intervalIntegrable _ _
      rw [heq, intervalIntegral.integral_add (hD2.sub hmul) hconst,
        intervalIntegral.integral_sub hD2 hmul,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at hnonneg
      change 0 ≤ (∫ t in (0 : ℝ)..(1/2 : ℝ), (D t)^2) - (4*m)*m + ((1/2 : ℝ)-0)*(4*m^2) at hnonneg
      dsimp [m] at hnonneg
      nlinarith
    have hop : ∫ t in (0 : ℝ)..(1/2 : ℝ), (D t)^2 ≤
        ‖b-a‖^2 * ∫ t in (0 : ℝ)..(1/2 : ℝ), ‖fderiv ℝ ψ (γ t)‖^2 := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_mono_on (by norm_num)
        ((hDc.pow 2).intervalIntegrable _ _)
        ((hgc.const_mul _).intervalIntegrable _ _)
      intro t ht
      have hb := (fderiv ℝ ψ (γ t)).le_opNorm (b-a)
      have hb' := sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) |>.mpr hb
      simpa [D, Real.norm_eq_abs, sq_abs, mul_pow, mul_comm] using hb'
    have hfinal := hcs.trans (mul_le_mul_of_nonneg_left hop (by norm_num))
    simp only [Function.comp_apply, γ, zero_smul, sub_zero, one_smul, add_zero] at hftc
    have hf : ψ a - ψ ((1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b) =
        -(∫ t in (0 : ℝ)..(1/2 : ℝ), D t) := by
      norm_num at hftc
      linarith
    rw [hf, neg_sq]
    simpa [γ, mul_assoc] using hfinal
  have haffine (s : Set E2) (hs : MeasurableSet s) (hconv : Convex ℝ s)
      (g : E2 → ℝ) (hg : ∀ z, 0 ≤ g z) (hgi : IntegrableOn g s)
      (b : E2) (hb : b ∈ s) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (1/2 : ℝ)) :
      (∫ a in s, g ((1-t) • a + t • b)) ≤ 4 * ∫ z in s, g z := by
    have htpos : 0 < 1-t := by linarith [ht.2]
    let T : Set E2 := (fun y : E2 => y + t • b) '' ((1-t) • s)
    have hT : T ⊆ s := by
      rintro _ ⟨y, ⟨a, ha, rfl⟩, rfl⟩
      exact hconv ha hb (by linarith [ht.2]) ht.1 (by ring)
    have hchange : (∫ a in s, g ((1-t) • a + t • b)) =
        ((1-t)^2)⁻¹ * ∫ z in T, g z := by
      rw [Measure.setIntegral_comp_smul_of_pos volume (fun y : E2 => g (y+t • b)) s htpos]
      have he := (measurePreserving_add_right (volume : Measure E2) (t • b)).setIntegral_image_emb
        (MeasurableEquiv.addRight (t • b)).measurableEmbedding g ((1-t) • s)
      rw [← he]
      simp only [finrank_euclideanSpace_fin, smul_eq_mul]
      rfl
    have hbound : (∫ z in T, g z) ≤ ∫ z in s, g z :=
      setIntegral_mono_set hgi (Filter.Eventually.of_forall hg) (Filter.Eventually.of_forall hT)
    have hfactor : ((1-t)^2)⁻¹ ≤ (4 : ℝ) := by
      rw [inv_eq_one_div]
      apply (div_le_iff₀ (sq_pos_of_pos htpos)).2
      nlinarith [ht.2, ht.1]
    rw [hchange]
    exact (mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr (sq_nonneg _))).trans
      (mul_le_mul_of_nonneg_right hfactor (setIntegral_nonneg hs (fun z _ => hg z)))
  refine ⟨4, by norm_num, ?_⟩
  intro ψ hψ x hx r hr hr1
  let s := planarCap x r
  let K := Metric.closedBall (0 : E2) 1
  let μ : Measure E2 := volume.restrict s
  have hs : MeasurableSet s := Metric.isOpen_ball.measurableSet.inter Metric.isOpen_ball.measurableSet
  have hKs : s ⊆ K := fun z hz => Metric.ball_subset_closedBall hz.1
  have hK : IsCompact K := isCompact_closedBall _ _
  have hconv : Convex ℝ s := (convex_ball (0 : E2) (1 : ℝ)).inter (convex_ball x r)
  have hfinite : volume s ≠ (⊤ : ℝ≥0∞) := (measure_mono hKs).trans_lt hK.measure_lt_top |>.ne
  let : IsFiniteMeasure μ := ⟨by simpa [μ] using hfinite.lt_top⟩
  by_cases hzero : volume s = 0
  · have hm : μ = 0 := (Measure.restrict_eq_zero.mpr hzero)
    change eLpNorm _ 2 μ ≤ ENNReal.ofReal (4*r) * eLpNorm _ 2 μ
    simp [hm]
  have hv : 0 < (volume s).toReal := ENNReal.toReal_pos hzero hfinite
  let v : ℝ := (volume s).toReal
  have hint (f : E2 → ℝ) (hf : Continuous f) : Integrable f μ :=
    (hf.continuousOn.integrableOn_compact hK).mono_set hKs
  have hint2 (f : E2 × E2 → ℝ) (hf : Continuous f) : Integrable f (μ.prod μ) := by
    dsimp only [μ]
    rw [Measure.prod_restrict]
    exact (hf.continuousOn.integrableOn_compact (hK.prod hK)).mono_set
      (fun p hp => ⟨hKs hp.1, hKs hp.2⟩)
  have hmem (f : E2 → ℝ) (hf : Continuous f) : MemLp f 2 μ := by
    obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
    apply memLp_of_bounded (a := -C) (b := C) _ hf.aestronglyMeasurable 2
    filter_upwards [ae_restrict_mem hs] with z hz
    exact abs_le.mp (hC z (hKs hz))
  have hcont (f : E2 × E2 → ℝ) (hf : Continuous f) :
      Continuous (fun a => ∫ b in s, f (a,b)) := by
    have h := continuous_parametric_integral_of_continuous (μ := μ)
      (f := fun a b => f (a,b)) hf hK
    change Continuous (fun a => ∫ b, f (a,b) ∂(volume.restrict s).restrict K) at h
    rw [Measure.restrict_restrict hK.measurableSet, inter_eq_right.mpr hKs] at h
    exact h
  let g : E2 → ℝ := fun z => ‖fderiv ℝ ψ z‖ ^ 2
  have hgc : Continuous g := (hψ.continuous_fderiv (by simp)).norm.pow 2
  have hgi : Integrable g μ := hint g hgc
  have hg0 : ∀ z, 0 ≤ g z := fun z => sq_nonneg _
  let I : ℝ := ∫ z in s, g z
  have hI : 0 ≤ I := integral_nonneg hg0
  let J : E2 → E2 → ℝ := fun a b =>
    ∫ t in (0 : ℝ)..(1/2 : ℝ), g ((1-t) • a + t • b)
  have hJc : Continuous (fun p : E2 × E2 => J p.1 p.2) := by
    have hc : Continuous (fun p : (E2 × E2) × ℝ =>
        g ((1-p.2) • p.1.1 + p.2 • p.1.2)) := by fun_prop
    have h := continuous_parametric_integral_of_continuous
      (f := fun p : E2 × E2 => fun t : ℝ => g ((1-t) • p.1 + t • p.2)) (μ := volume) hc
      (isCompact_Icc : IsCompact (Icc (0 : ℝ) (1/2 : ℝ)))
    simpa only [J, intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1/2 by norm_num),
      integral_Icc_eq_integral_Ioc] using h
  have hJ0 (a b : E2) : 0 ≤ J a b :=
    intervalIntegral.integral_nonneg (by norm_num) (fun t _ => hg0 _)
  have hJbound (b : E2) (hb : b ∈ s) : (∫ a in s, J a b) ≤ 2*I := by
    have hp : Continuous (fun p : ℝ × E2 => g ((1-p.1) • p.2 + p.1 • b)) := by fun_prop
    have hprod : Integrable (fun p : ℝ × E2 => g ((1-p.1) • p.2 + p.1 • b))
        ((volume.restrict (uIoc (0 : ℝ) (1/2 : ℝ))).prod μ) := by
      dsimp only [μ]
      rw [Measure.prod_restrict]
      apply (hp.continuousOn.integrableOn_compact (isCompact_Icc.prod hK)).mono_set
      intro p hp
      have hpt : p.1 ∈ Ioc (0 : ℝ) (1/2 : ℝ) := by
        simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1/2)] using hp.1
      exact ⟨⟨hpt.1.le, hpt.2⟩, hKs hp.2⟩
    have hswap := intervalIntegral_integral_swap (f := fun t a => g ((1-t) • a + t • b))
      (a := (0 : ℝ)) (b := (1/2 : ℝ)) (μ := μ) hprod
    change (∫ t in (0 : ℝ)..(1/2 : ℝ), ∫ a in s, g ((1-t) • a + t • b)) =
      (∫ a in s, J a b) at hswap
    rw [← hswap]
    have hc : Continuous (fun t : ℝ => ∫ a in s, g ((1-t) • a + t • b)) := by
      have hh := continuous_parametric_integral_of_continuous (μ := μ)
        (f := fun t a => g ((1-t) • a + t • b)) hp hK
      change Continuous (fun t => ∫ a, g ((1-t) • a + t • b) ∂(volume.restrict s).restrict K) at hh
      rw [Measure.restrict_restrict hK.measurableSet, inter_eq_right.mpr hKs] at hh
      exact hh
    calc
      _ ≤ ∫ _t in (0 : ℝ)..(1/2 : ℝ), (4*I) :=
        intervalIntegral.integral_mono_on (by norm_num) (hc.intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _) (fun t ht => haffine s hs hconv g hg0 hgi b hb t ht)
      _ = 2*I := by rw [intervalIntegral.integral_const]; simp only [smul_eq_mul]; ring
  have hd (a b : E2) (ha : a ∈ s) (hb : b ∈ s) : ‖b-a‖ ≤ 2*r := by
    have h1 := Metric.mem_ball.mp ha.2
    have h2 := Metric.mem_ball.mp hb.2
    calc
      ‖b-a‖ = dist b a := (dist_eq_norm _ _).symm
      _ ≤ dist b x + dist x a := dist_triangle _ _ _
      _ ≤ r+r := add_le_add h2.le (by simpa [dist_comm] using h1.le)
      _ = 2*r := by ring
  have hpair (a b : E2) (ha : a ∈ s) (hb : b ∈ s) :
      (ψ a - ψ b)^2 ≤ 4*r^2*(J a b + J b a) := by
    have ha' := hsegment ψ hψ a b
    have hb' := hsegment ψ hψ b a
    rw [add_comm ((1/2 : ℝ) • b)] at hb'
    have hdist : ‖b-a‖^2 ≤ (2*r)^2 := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (hd a b ha hb)
    rw [norm_sub_rev a b] at hb'
    change (ψ a - ψ ((1/2 : ℝ) • a + (1/2 : ℝ) • b))^2 ≤ (1/2 : ℝ)*‖b-a‖^2*J a b at ha'
    change (ψ b - ψ ((1/2 : ℝ) • a + (1/2 : ℝ) • b))^2 ≤ (1/2 : ℝ)*‖b-a‖^2*J b a at hb'
    have hA : (ψ a - ψ ((1/2 : ℝ) • a + (1/2 : ℝ) • b))^2 ≤ 2*r^2*J a b := by
      calc
        _ ≤ (1/2 : ℝ)*‖b-a‖^2*J a b := ha'
        _ ≤ (1/2 : ℝ)*(2*r)^2*J a b := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hdist (by norm_num)) (hJ0 a b)
        _ = _ := by ring
    have hB : (ψ b - ψ ((1/2 : ℝ) • a + (1/2 : ℝ) • b))^2 ≤ 2*r^2*J b a := by
      calc
        _ ≤ (1/2 : ℝ)*‖b-a‖^2*J b a := hb'
        _ ≤ (1/2 : ℝ)*(2*r)^2*J b a := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hdist (by norm_num)) (hJ0 b a)
        _ = _ := by ring
    calc
      _ ≤ 2*(ψ a - ψ ((1/2 : ℝ) • a + (1/2 : ℝ) • b))^2 +
          2*(ψ b - ψ ((1/2 : ℝ) • a + (1/2 : ℝ) • b))^2 := by
        nlinarith only [sq_nonneg (ψ a + ψ b - 2*ψ ((1/2 : ℝ) • a + (1/2 : ℝ) • b))]
      _ ≤ 2*(2*r^2*J a b)+2*(2*r^2*J b a) := add_le_add
        (mul_le_mul_of_nonneg_left hA (by norm_num)) (mul_le_mul_of_nonneg_left hB (by norm_num))
      _ = _ := by ring
  let Q : E2 → E2 → ℝ := fun a b => (ψ a - ψ b)^2
  have hQc : Continuous (fun p : E2 × E2 => Q p.1 p.2) := ((hψ.continuous.comp continuous_fst).sub (hψ.continuous.comp continuous_snd)).pow 2
  have hJswap : Continuous (fun p : E2 × E2 => J p.2 p.1) :=
    by
    have h : Continuous ((fun p : E2 × E2 => J p.1 p.2) ∘ Prod.swap) := Continuous.comp hJc continuous_swap
    exact h
  have hsum : Continuous (fun p : E2 × E2 => 4*r^2*(J p.1 p.2 + J p.2 p.1)) :=
    (hJc.add hJswap).const_mul _
  have hdouble : (∫ a in s, ∫ b in s, Q a b) ≤
      ∫ a in s, ∫ b in s, 4*r^2*(J a b+J b a) := by
    apply setIntegral_mono_on (hint _ (hcont _ hQc)) (hint _ (hcont _ hsum)) hs
    intro a ha
    apply setIntegral_mono_on
      (hint _ (hQc.comp (continuous_const.prodMk continuous_id)))
      (hint _ (hsum.comp (continuous_const.prodMk continuous_id))) hs
    intro b hb
    exact hpair a b ha hb
  have hJouter : (∫ b in s, ∫ a in s, J a b) ≤ v*(2*I) := by
    calc
      _ ≤ ∫ _b in s, 2*I :=
        setIntegral_mono_on (hint _ (hcont _ hJswap)) (integrable_const _) hs hJbound
      _ = v*(2*I) := by simp [v, measureReal_def]
  have hswap := integral_integral_swap (f := J) (hint2 (fun p : E2 × E2 => J p.1 p.2) hJc)
  change (∫ a in s, ∫ b in s, J a b) = (∫ b in s, ∫ a in s, J a b) at hswap
  have hpairint : (∫ a in s, ∫ b in s, Q a b) ≤ 16*r^2*v*I := by
    have heq : (∫ a in s, ∫ b in s, 4*r^2*(J a b+J b a)) =
        4*r^2*((∫ a in s, ∫ b in s, J a b)+(∫ a in s, ∫ b in s, J b a)) := by
      simp_rw [integral_const_mul]
      rw [integral_integral_add (hint2 _ hJc) (hint2 _ hJswap)]
    rw [heq, hswap] at hdouble
    have hmul := mul_le_mul_of_nonneg_left (add_le_add hJouter hJouter)
      (show 0 ≤ 4*r^2 by positivity)
    calc
      _ ≤ 4*r^2*((∫ b in s, ∫ a in s, J a b)+(∫ b in s, ∫ a in s, J a b)) := hdouble
      _ ≤ 4*r^2*(v*(2*I)+v*(2*I)) := hmul
      _ = _ := by ring
  let m := ⨍ y in s, ψ y
  have hmcont : Continuous (fun a => (ψ a-m)^2) := (hψ.continuous.sub continuous_const).pow 2
  let : NeZero μ := ⟨by intro hz; exact hzero (Measure.restrict_eq_zero.mp hz)⟩
  have hmean (a : E2) : (ψ a-m)^2 ≤ v⁻¹ * ∫ b in s, Q a b := by
    have hsq : ConvexOn ℝ univ (fun z : ℝ => z^2) :=
      (show Even (2 : ℕ) by decide).convexOn_pow
    have h := hsq.map_average_le (continuous_pow 2).continuousOn isClosed_univ
      (f := fun b => ψ a - ψ b) (μ := μ) (Filter.Eventually.of_forall fun _ => mem_univ _)
      (hint _ (continuous_const.sub hψ.continuous)) (hint _ ((continuous_const.sub hψ.continuous).pow 2))
    have hav : (⨍ b, ψ a-ψ b ∂μ) = ψ a-m := by
      change (⨍ b, ((fun _ : E2 => ψ a) - ψ) b ∂μ) = _
      rw [average_sub (integrable_const _) (hint ψ hψ.continuous), average_const]
    rw [hav, average_eq] at h
    simpa only [μ, Measure.restrict_apply_univ, measureReal_def, smul_eq_mul, Q, v] using h
  have hmain : (∫ a in s, (ψ a-m)^2) ≤ (4*r)^2*I := by
    calc
      _ ≤ ∫ a in s, v⁻¹ * ∫ b in s, Q a b :=
        integral_mono_ae (hint _ hmcont) (hint _ ((hcont _ hQc).const_mul _))
          (Filter.Eventually.of_forall hmean)
      _ = v⁻¹ * ∫ a in s, ∫ b in s, Q a b := integral_const_mul _ _
      _ ≤ v⁻¹ * (16*r^2*v*I) := mul_le_mul_of_nonneg_left hpairint (inv_nonneg.mpr hv.le)
      _ = (4*r)^2*I := by field_simp [show v ≠ 0 from hv.ne']; ring
  have hl2 (f : E2 → ℝ) (hf : MemLp f 2 μ) :
      (eLpNorm f 2 μ).toReal^2 = ∫ a, (f a)^2 ∂μ := by
    rw [← Lp.norm_toLp f hf, ← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with a ha
    simp only [ha, RCLike.inner_apply, conj_trivial, sq]
  have hfm := hmem (fun a => ψ a-m) (hψ.continuous.sub continuous_const)
  have hgm := hmem (fun a => ‖fderiv ℝ ψ a‖) ((hψ.continuous_fderiv (by simp)).norm)
  have hnorm : (eLpNorm (fun a => ψ a-m) 2 μ).toReal ≤
      (4*r) * (eLpNorm (fun a => ‖fderiv ℝ ψ a‖) 2 μ).toReal := by
    change (∫ a, (ψ a-m)^2 ∂μ) ≤ (4*r)^2 * ∫ a, ‖fderiv ℝ ψ a‖^2 ∂μ at hmain
    rw [← hl2 _ hfm, ← hl2 _ hgm] at hmain
    nlinarith only [hmain, mul_nonneg (show 0 ≤ 4*r by positivity) (ENNReal.toReal_nonneg (a := eLpNorm (fun a => ‖fderiv ℝ ψ a‖) 2 μ)), ENNReal.toReal_nonneg (a := eLpNorm (fun a => ψ a-m) 2 μ),
      ENNReal.toReal_nonneg (a := eLpNorm (fun a => ‖fderiv ℝ ψ a‖) 2 μ)]
  apply (ENNReal.toReal_le_toReal hfm.eLpNorm_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hgm.eLpNorm_ne_top)).mp
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (show 0 ≤ 4*r by positivity)] using hnorm


end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak.AnalyticLower
