import B1L1DirectWeakLower
set_option autoImplicit false
noncomputable section
open Set Topology Function MeasureTheory
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak
open SeifertSurfaces.AppendixACoordinates

theorem newtonian_kernel_morrey_estimate :
∀ (r : ℝ), 0 < r → ∀ (gamma : ℝ≥0), 0 < gamma → gamma < 1 →
  let T := fun (F : E2 → ℝ) (x : E2) =>
      ∫ y, ((halfDisc r).indicator F y) • ((‖x - y‖ ^ 2)⁻¹ • (x - y))
    ∃ (B H : ℝ), 0 ≤ B ∧ 0 ≤ H ∧
      ∀ (F : E2 → ℝ) (L : ℝ), ScalarGrowth univ ((halfDisc r).indicator F) gamma L →
        (∀ x ∈ closedHalfDisc r,
          Integrable (fun y => ((halfDisc r).indicator F y) • ((‖x - y‖ ^ 2)⁻¹ • (x - y))) ∧
          ‖T F x‖ ≤ B * L) ∧
        (∀ x ∈ closedHalfDisc r, ∀ z ∈ closedHalfDisc r,
          ‖T F x - T F z‖ ≤ H * L * Real.rpow (dist x z) (gamma : ℝ)) := by run_tac do Lean.Elab.Tactic.evalTactic (← Lean.ofExcept (Lean.Parser.runParserCategory (← Lean.getEnv) `tactic "exact (by\nintro r hr gamma hg0 hg1\nhave near :\n    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : E2 → ℝ, ∀ L : ℝ,\n      ScalarGrowth univ g gamma L → ∀ x : E2, ∀ R : ℝ, 0 < R →\n        IntegrableOn (fun y => |g y| / ‖x-y‖) (Metric.closedBall x R) ∧\n        (∫ y in Metric.closedBall x R, |g y| / ‖x-y‖) ≤ C * L * Real.rpow R gamma := by\n  have hgpos : (0:ℝ) < gamma := by exact_mod_cast hg0\n  let q : ℝ := Real.rpow (1/2) gamma\n  have hq0 : 0 ≤ q := Real.rpow_nonneg (by norm_num) _\n  have hq1 : q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hgpos\n  let C : ℝ := (2 * Real.rpow 2 (1+(gamma:ℝ))) / (1-q)\n  have hC : 0 ≤ C := by dsimp [C]; positivity\n  refine ⟨C, hC, ?_⟩\n  intro g L hg x R hR\n  have hgi : Integrable g := integrableOn_univ.mp hg.1\n  have hL : 0 ≤ L := hg.2.1\n  have growth : ∀ a : ℝ, 0 < a → (∫ y in Metric.ball x a, |g y|) ≤\n      L * Real.rpow a (1+(gamma:ℝ)) := by\n    intro a ha\n    simpa only [univ_inter] using hg.2.2 x a ha\n  let u := fun y : E2 => |g y| / ‖x-y‖\n  have hu : AEStronglyMeasurable u := by\n    exact hgi.abs.aestronglyMeasurable.mul\n      ((continuous_const.sub continuous_id).norm.measurable.inv).aestronglyMeasurable\n  have hu0 : ∀ y, 0 ≤ u y := fun y => div_nonneg (abs_nonneg _) (norm_nonneg _)\n  let a : ℕ → ℝ := fun n => R * (1/2 : ℝ)^n\n  let A : ℕ → Set E2 := fun n => Metric.closedBall x (a n) \\ Metric.closedBall x (a (n+1))\n  have ha : ∀ n, 0 < a n := fun n => mul_pos hR (pow_pos (by norm_num) _)\n  have hm : ∀ n, MeasurableSet (A n) := fun n =>\n    measurableSet_closedBall.diff measurableSet_closedBall\n  have hpoint : ∀ n, ∀ y ∈ A n, u y ≤ (a (n+1))⁻¹ * |g y| := by\n    intro n y hy\n    have hd : a (n+1) < ‖x-y‖ := by\n      have hd' : a (n+1) < dist y x := not_le.mp hy.2\n      simpa only [dist_eq_norm, norm_sub_rev] using hd'\n    change |g y| * ‖x-y‖⁻¹ ≤ (a (n+1))⁻¹ * |g y|\n    exact (mul_le_mul_of_nonneg_left ((inv_le_inv₀ ((ha _).trans hd) (ha _)).mpr hd.le)\n      (abs_nonneg (g y))).trans_eq (mul_comm _ _)\n  have hui : ∀ n, IntegrableOn u (A n) := by\n    intro n\n    apply (hgi.abs.integrableOn.const_mul ((a (n+1))⁻¹)).mono' hu.restrict\n    filter_upwards [ae_restrict_mem (hm n)] with y hy\n    rw [Real.norm_of_nonneg (hu0 y)]\n    exact hpoint n y hy\n  let D : ℝ := 2 * Real.rpow 2 (1+(gamma:ℝ)) * L * Real.rpow R gamma\n  have hD : 0 ≤ D := by dsimp [D]; positivity\n  have hbound : ∀ n, (∫ y in A n, u y) ≤ D * q^n := by\n    intro n\n    have hsub : A n ⊆ Metric.ball x (2*a n) := by\n      intro y hy\n      change dist y x < 2*a n\n      exact hy.1.trans_lt (by linarith [ha n])\n    calc\n      (∫ y in A n, u y) ≤ ∫ y in A n, (a (n+1))⁻¹ * |g y| :=\n        setIntegral_mono_on (hui n) (hgi.abs.integrableOn.const_mul _) (hm n) (hpoint n)\n      _ = (a (n+1))⁻¹ * ∫ y in A n, |g y| := integral_const_mul _ _\n      _ ≤ (a (n+1))⁻¹ * (L * Real.rpow (2*a n) (1+(gamma:ℝ))) := by\n        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (ha _).le)\n        exact (setIntegral_mono_set hgi.abs.integrableOn\n          (Filter.Eventually.of_forall (fun y => abs_nonneg _))\n          (Filter.Eventually.of_forall hsub)).trans (growth _ (by positivity))\n      _ = D * q^n := by\n        have hbase : 0 < (1/2:ℝ)^n := pow_pos (by norm_num) _\n        dsimp [a, D, q]\n        rw [Real.rpow_add (by positivity), Real.rpow_one, Real.mul_rpow (by norm_num) (by positivity),\n          Real.mul_rpow hR.le hbase.le,\n          ← Real.rpow_natCast_mul (by norm_num), mul_comm (n:ℝ) (gamma:ℝ),\n          Real.rpow_mul_natCast (by norm_num), pow_succ,\n          Real.rpow_add (by norm_num : (0:ℝ)<2), Real.rpow_one]\n        field_simp (disch := positivity)\n  have hsumD : Summable (fun n : ℕ => D*q^n) :=\n    (summable_geometric_of_norm_lt_one (by rw [Real.norm_of_nonneg hq0]; exact hq1)).mul_left D\n  have hsum : Summable (fun n => ∫ y in A n, u y) :=\n    hsumD.of_nonneg_of_le (fun n => integral_nonneg (fun y => hu0 y)) hbound\n  have hsumNorm : Summable (fun n => ∫ y in A n, ‖u y‖) := by\n    simpa only [Real.norm_of_nonneg (hu0 _)] using hsum\n  have hiU : IntegrableOn u (⋃ n, A n) :=\n    integrableOn_iUnion_of_summable_integral_norm hui hsumNorm\n  have hcover : (⋃ n, A n) = Metric.closedBall x R \\ {x} := by\n    ext y\n    constructor\n    · intro hy\n      obtain ⟨n, hn⟩ := mem_iUnion.mp hy\n      have hlow : a (n+1) < dist y x := not_le.mp hn.2\n      refine ⟨?_, ?_⟩\n      · exact hn.1.trans (mul_le_of_le_one_right hR.le\n          (pow_le_one₀ (by norm_num) (by norm_num)))\n      · intro hyx\n        have hy : y = x := mem_singleton_iff.mp hyx\n        simp only [hy, dist_self] at hlow\n        exact (ha _).not_ge hlow.le\n    · intro hy\n      have hpos : 0 < dist y x := dist_pos.mpr (fun h => hy.2 (mem_singleton_iff.mpr h))\n      obtain ⟨n, hnlo, hnhi⟩ := exists_nat_pow_near_of_lt_one\n        (div_pos hpos hR) ((div_le_one hR).mpr hy.1) (by norm_num : (0:ℝ)<1/2)\n        (by norm_num : (1/2:ℝ)<1)\n      refine mem_iUnion.mpr ⟨n, ?_⟩\n      constructor\n      · exact (div_le_iff₀ hR).mp hnhi |>.trans_eq (mul_comm _ _)\n      · exact not_le.mpr (by simpa only [mul_comm] using (lt_div_iff₀ hR).mp hnlo)\n  have hdj : Pairwise (Disjoint on A) := by\n    intro n m hnm\n    have hdis : ∀ n m : ℕ, n < m → Disjoint (A n) (A m) := by\n      intro n m hlt\n      apply disjoint_left.mpr\n      intro y hyn hym\n      have hsmall : a m ≤ a (n+1) := by\n        apply mul_le_mul_of_nonneg_left _ hR.le\n        exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hlt\n      exact hyn.2 (hym.1.trans hsmall)\n    rcases lt_or_gt_of_ne hnm with hlt | hlt\n    · exact hdis n m hlt\n    · exact (hdis m n hlt).symm\n  have hsing : {x} ⊆ Metric.closedBall x R := by\n    intro y hy\n    rw [mem_singleton_iff.mp hy]\n    change dist x x ≤ R\n    rw [dist_self]\n    exact hR.le\n  have hi : IntegrableOn u (Metric.closedBall x R) := by\n    have hi' := integrableOn_union.mpr ⟨hcover ▸ hiU,\n      (integrableOn_singleton (f:=u) (x:=x)\n        (hx:=by rw [measure_singleton]; exact ENNReal.zero_lt_top))⟩\n    simpa only [sdiff_union_of_subset hsing] using hi'\n  have heq : (∫ y in Metric.closedBall x R, u y) = ∫ y in ⋃ n, A n, u y := by\n    rw [hcover, setIntegral_sdiff (measurableSet_singleton x) hi hsing]\n    rw [integral_singleton]\n    simp only [measureReal_def, measure_singleton, ENNReal.toReal_zero, zero_smul, sub_zero]\n  refine ⟨hi, ?_⟩\n  rw [heq, integral_iUnion hm hdj hiU]\n  calc\n    (∑' n, ∫ y in A n, u y) ≤ ∑' n : ℕ, D*q^n := Summable.tsum_le_tsum hbound hsum hsumD\n    _ = C * L * Real.rpow R gamma := by\n      rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]\n      dsimp [D, C]\n      ring\nhave far :\n    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : E2 → ℝ, ∀ L : ℝ,\n      ScalarGrowth univ g gamma L → ∀ x : E2, ∀ R : ℝ, 0 < R →\n        IntegrableOn (fun y => |g y| / ‖x-y‖^2) (Metric.ball x R)ᶜ ∧\n        (∫ y in (Metric.ball x R)ᶜ, |g y| / ‖x-y‖^2) ≤\n          C * L * Real.rpow R ((gamma:ℝ)-1) := by\n  have hgneg : (gamma:ℝ)-1 < 0 := by\n    have hglt : (gamma:ℝ) < 1 := by exact_mod_cast hg1\n    linarith\n  let q : ℝ := Real.rpow 2 ((gamma:ℝ)-1)\n  have hq0 : 0 ≤ q := Real.rpow_nonneg (by norm_num) _\n  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hgneg\n  let C : ℝ := Real.rpow 2 (1+(gamma:ℝ)) / (1-q)\n  have hC : 0 ≤ C := by dsimp [C]; positivity\n  refine ⟨C, hC, ?_⟩\n  intro g L hg x R hR\n  have hgi : Integrable g := integrableOn_univ.mp hg.1\n  have hL : 0 ≤ L := hg.2.1\n  have growth : ∀ a : ℝ, 0 < a → (∫ y in Metric.ball x a, |g y|) ≤\n      L * Real.rpow a (1+(gamma:ℝ)) := by\n    intro a ha\n    simpa only [univ_inter] using hg.2.2 x a ha\n  let u := fun y : E2 => |g y| / ‖x-y‖^2\n  have hu : AEStronglyMeasurable u := by\n    exact hgi.abs.aestronglyMeasurable.mul\n      (((continuous_const.sub continuous_id).norm.measurable.pow_const 2).inv).aestronglyMeasurable\n  have hu0 : ∀ y, 0 ≤ u y := fun y => div_nonneg (abs_nonneg _) (sq_nonneg _)\n  let a : ℕ → ℝ := fun n => R * (2:ℝ)^n\n  let A : ℕ → Set E2 := fun n => Metric.ball x (a (n+1)) \\ Metric.ball x (a n)\n  have ha : ∀ n, 0 < a n := fun n => mul_pos hR (pow_pos (by norm_num) _)\n  have hm : ∀ n, MeasurableSet (A n) := fun n => measurableSet_ball.diff measurableSet_ball\n  have hpoint : ∀ n, ∀ y ∈ A n, u y ≤ ((a n)^2)⁻¹ * |g y| := by\n    intro n y hy\n    have hd : a n ≤ ‖x-y‖ := by\n      have hd' : a n ≤ dist y x := not_lt.mp hy.2\n      simpa only [dist_eq_norm, norm_sub_rev] using hd'\n    change |g y| * (‖x-y‖^2)⁻¹ ≤ ((a n)^2)⁻¹ * |g y|\n    exact (mul_le_mul_of_nonneg_left\n      ((inv_le_inv₀ (sq_pos_of_pos ((ha n).trans_le hd)) (sq_pos_of_pos (ha n))).mpr\n        (pow_le_pow_left₀ (ha n).le hd 2)) (abs_nonneg (g y))).trans_eq (mul_comm _ _)\n  have hui : ∀ n, IntegrableOn u (A n) := by\n    intro n\n    apply (hgi.abs.integrableOn.const_mul (((a n)^2)⁻¹)).mono' hu.restrict\n    filter_upwards [ae_restrict_mem (hm n)] with y hy\n    rw [Real.norm_of_nonneg (hu0 y)]\n    exact hpoint n y hy\n  let D : ℝ := Real.rpow 2 (1+(gamma:ℝ)) * L * Real.rpow R ((gamma:ℝ)-1)\n  have hD : 0 ≤ D := by dsimp [D]; positivity\n  have hbound : ∀ n, (∫ y in A n, u y) ≤ D * q^n := by\n    intro n\n    have hsub : A n ⊆ Metric.ball x (a (n+1)) := sdiff_subset\n    calc\n      (∫ y in A n, u y) ≤ ∫ y in A n, ((a n)^2)⁻¹ * |g y| :=\n        setIntegral_mono_on (hui n) (hgi.abs.integrableOn.const_mul _) (hm n) (hpoint n)\n      _ = ((a n)^2)⁻¹ * ∫ y in A n, |g y| := integral_const_mul _ _\n      _ ≤ ((a n)^2)⁻¹ * (L * Real.rpow (a (n+1)) (1+(gamma:ℝ))) := by\n        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (sq_nonneg _))\n        exact (setIntegral_mono_set hgi.abs.integrableOn\n          (Filter.Eventually.of_forall (fun y => abs_nonneg _))\n          (Filter.Eventually.of_forall hsub)).trans (growth _ (ha _))\n      _ = D * q^n := by\n        have hbase : 0 < (2:ℝ)^n := pow_pos (by norm_num) _\n        dsimp [a, D, q]\n        rw [show (2:ℝ)^(n+1) = 2^n*2 from pow_succ _ _, Real.mul_rpow hR.le (by positivity),\n          Real.mul_rpow hbase.le (by norm_num),\n          Real.rpow_add hR, Real.rpow_one,\n          Real.rpow_add hbase, Real.rpow_one,\n          Real.rpow_sub hR, Real.rpow_one,\n          ← Real.rpow_mul_natCast (by norm_num), mul_comm ((gamma:ℝ)-1) (n:ℝ),\n          Real.rpow_natCast_mul (by norm_num), Real.rpow_sub hbase, Real.rpow_one]\n        field_simp (disch := positivity)\n  have hsumD : Summable (fun n : ℕ => D*q^n) :=\n    (summable_geometric_of_norm_lt_one (by rw [Real.norm_of_nonneg hq0]; exact hq1)).mul_left D\n  have hsum : Summable (fun n => ∫ y in A n, u y) :=\n    hsumD.of_nonneg_of_le (fun n => integral_nonneg (fun y => hu0 y)) hbound\n  have hsumNorm : Summable (fun n => ∫ y in A n, ‖u y‖) := by\n    simpa only [Real.norm_of_nonneg (hu0 _)] using hsum\n  have hiU : IntegrableOn u (⋃ n, A n) :=\n    integrableOn_iUnion_of_summable_integral_norm hui hsumNorm\n  have hcover : (⋃ n, A n) = (Metric.ball x R)ᶜ := by\n    ext y\n    constructor\n    · intro hy\n      obtain ⟨n, hn⟩ := mem_iUnion.mp hy\n      have hlow : a n ≤ dist y x := not_lt.mp hn.2\n      change ¬dist y x < R\n      apply not_lt.mpr\n      simpa only [mul_one] using (mul_le_mul_of_nonneg_left (one_le_pow₀ (by norm_num)) hR.le).trans hlow\n    · intro hy\n      have hlow : R ≤ dist y x := not_lt.mp hy\n      obtain ⟨n, hnlo, hnhi⟩ := exists_nat_pow_near ((one_le_div hR).mpr hlow)\n        (by norm_num : (1:ℝ)<2)\n      refine mem_iUnion.mpr ⟨n, ?_⟩\n      constructor\n      · exact (div_lt_iff₀ hR).mp hnhi |>.trans_eq (mul_comm _ _)\n      · exact not_lt.mpr (by simpa only [mul_comm] using (le_div_iff₀ hR).mp hnlo)\n  have hdj : Pairwise (Disjoint on A) := by\n    intro n m hnm\n    have hdis : ∀ n m : ℕ, n < m → Disjoint (A n) (A m) := by\n      intro n m hlt\n      apply disjoint_left.mpr\n      intro y hyn hym\n      have hsmall : a (n+1) ≤ a m := by\n        apply mul_le_mul_of_nonneg_left _ hR.le\n        exact pow_le_pow_right₀ (by norm_num) hlt\n      exact hym.2 (hyn.1.trans_le hsmall)\n    rcases lt_or_gt_of_ne hnm with hlt | hlt\n    · exact hdis n m hlt\n    · exact (hdis m n hlt).symm\n  refine ⟨hcover ▸ hiU, ?_⟩\n  rw [← hcover, integral_iUnion hm hdj hiU]\n  calc\n    (∑' n, ∫ y in A n, u y) ≤ ∑' n : ℕ, D*q^n := Summable.tsum_le_tsum hbound hsum hsumD\n    _ = C * L * Real.rpow R ((gamma:ℝ)-1) := by\n      rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]\n      dsimp [D, C]\n      ring\nobtain ⟨N, hN, near_est⟩ := near\nobtain ⟨Q, hQ, far_est⟩ := far\nlet B : ℝ := N * Real.rpow (2*r) gamma\nlet H : ℝ := (N+Q) * Real.rpow 2 gamma + N * Real.rpow 3 gamma\nhave hB : 0 ≤ B := by dsimp [B]; positivity\nhave hH : 0 ≤ H := by dsimp [H]; positivity\ndsimp only\nrefine ⟨B, H, hB, hH, ?_⟩\nintro F L hg\nlet g := (halfDisc r).indicator F\nhave hgi : Integrable g := integrableOn_univ.mp hg.1\nhave hL : 0 ≤ L := hg.2.1\nlet K := fun x y : E2 => g y • ((‖x-y‖^2)⁻¹ • (x-y))\nhave hnorm : ∀ x y : E2, ‖K x y‖ = |g y| / ‖x-y‖ := by\n  intro x y\n  dsimp [K]\n  by_cases h : x-y=0\n  · rw [h]\n    simp only [norm_zero, smul_zero, div_zero]\n  · have hn : ‖x-y‖ ≠ 0 := norm_ne_zero_iff.mpr h\n    simp only [norm_smul, Real.norm_eq_abs,\n      abs_of_nonneg (inv_nonneg.mpr (sq_nonneg ‖x-y‖))]\n    field_simp (disch := positivity)\nhave hKi : ∀ x ∈ closedHalfDisc r, Integrable (K x) := by\n  intro x hx\n  have hi := (near_est g L hg x (2*r) (by positivity)).1\n  have hm : AEStronglyMeasurable (K x) := by\n    exact hgi.aestronglyMeasurable.smul\n      ((((continuous_const.sub continuous_id).norm.measurable.pow_const 2).inv.smul\n        (continuous_const.sub continuous_id).measurable).aestronglyMeasurable)\n  have hik : IntegrableOn (K x) (Metric.closedBall x (2*r)) := by\n    apply hi.mono' hm.restrict\n    filter_upwards with y\n    exact (hnorm x y).le\n  apply hik.integrable_of_forall_notMem_eq_zero\n  intro y hy\n  have hnot : y ∉ halfDisc r := by\n    intro hyt\n    apply hy\n    have hxn : ‖x‖ ≤ r := by\n      have hx' := hx.1\n      change dist x (0:E2) ≤ r at hx'\n      simpa only [dist_zero_right] using hx'\n    have hyn : ‖y‖ < r := by\n      have hy' := hyt.1\n      change dist y (0:E2) < r at hy'\n      simpa only [dist_zero_right] using hy'\n    change dist y x ≤ 2*r\n    rw [dist_eq_norm]\n    exact (norm_sub_le y x).trans (by linarith)\n  have hg0 : g y = 0 := indicator_of_notMem hnot F\n  dsimp [K]\n  rw [hg0]\n  exact zero_smul ℝ _\nhave hscalar : ∀ x ∈ closedHalfDisc r,\n    Integrable (fun y => |g y| / ‖x-y‖) := by\n  intro x hx\n  simpa only [hnorm] using (hKi x hx).norm\nconstructor\n· intro x hx\n  refine ⟨hKi x hx, ?_⟩\n  have hsupp : ∀ y, y ∉ Metric.closedBall x (2*r) → |g y| / ‖x-y‖ = 0 := by\n    intro y hy\n    have hnot : y ∉ halfDisc r := by\n      intro hyt\n      apply hy\n      have hxn : ‖x‖ ≤ r := by\n        have hx' := hx.1\n        change dist x (0:E2) ≤ r at hx'\n        simpa only [dist_zero_right] using hx'\n      have hyn : ‖y‖ < r := by\n        have hy' := hyt.1\n        change dist y (0:E2) < r at hy'\n        simpa only [dist_zero_right] using hy'\n      change dist y x ≤ 2*r\n      rw [dist_eq_norm]\n      exact (norm_sub_le y x).trans (by linarith)\n    have hg0 : g y = 0 := indicator_of_notMem hnot F\n    rw [hg0]\n    simp only [abs_zero, zero_div]\n  calc\n    ‖∫ y, K x y‖ ≤ ∫ y, ‖K x y‖ := norm_integral_le_integral_norm _\n    _ = ∫ y in Metric.closedBall x (2*r), |g y| / ‖x-y‖ := by\n      simp_rw [hnorm]\n      exact (setIntegral_eq_integral_of_forall_compl_eq_zero hsupp).symm\n    _ ≤ B*L := (near_est g L hg x (2*r) (by positivity)).2.trans_eq (by dsimp [B]; ring)\n· intro x hx z hz\n  by_cases h : x=z\n  · subst z\n    simp only [sub_self, norm_zero, dist_self]\n    exact mul_nonneg (mul_nonneg hH hL) (Real.rpow_nonneg (by norm_num) _)\n  have hd : 0 < dist x z := dist_pos.mpr h\n  let d := dist x z\n  let S := Metric.ball x (2*d)\n  have hmS : MeasurableSet S := measurableSet_ball\n  have hdiff : Integrable (fun y => K x y - K z y) := (hKi x hx).sub (hKi z hz)\n  have hnear : (∫ y in S, ‖K x y-K z y‖) ≤\n      N * L * Real.rpow (2*d) gamma + N * L * Real.rpow (3*d) gamma := by\n    have hsubx : S ⊆ Metric.closedBall x (2*d) := Metric.ball_subset_closedBall\n    have hsubz : S ⊆ Metric.closedBall z (3*d) := by\n      intro y hy\n      change dist y z ≤ 3*d\n      have hdxy : dist y x < 2*d := hy\n      have hdxz : dist x z = d := rfl\n      exact (dist_triangle y x z).trans (by linarith)\n    calc\n      (∫ y in S, ‖K x y-K z y‖) ≤ ∫ y in S, (|g y| / ‖x-y‖ + |g y| / ‖z-y‖) := by\n        apply setIntegral_mono_on hdiff.norm.integrableOn\n          ((hscalar x hx).add (hscalar z hz)).integrableOn hmS\n        intro y hy\n        exact (norm_sub_le _ _).trans_eq (by simp only [hnorm, Pi.add_apply])\n      _ = (∫ y in S, |g y| / ‖x-y‖) + ∫ y in S, |g y| / ‖z-y‖ :=\n        integral_add (hscalar x hx).integrableOn (hscalar z hz).integrableOn\n      _ ≤ N * L * Real.rpow (2*d) gamma + N * L * Real.rpow (3*d) gamma := by\n        apply add_le_add\n        · exact (setIntegral_mono_set (near_est g L hg x (2*d) (by positivity)).1\n            (Filter.Eventually.of_forall (fun y => div_nonneg (abs_nonneg _) (norm_nonneg _)))\n            (Filter.Eventually.of_forall hsubx)).trans (near_est g L hg x (2*d) (by positivity)).2\n        · exact (setIntegral_mono_set (near_est g L hg z (3*d) (by positivity)).1\n            (Filter.Eventually.of_forall (fun y => div_nonneg (abs_nonneg _) (norm_nonneg _)))\n            (Filter.Eventually.of_forall hsubz)).trans (near_est g L hg z (3*d) (by positivity)).2\n  have hfar : (∫ y in Sᶜ, ‖K x y-K z y‖) ≤\n      (2*d) * (Q * L * Real.rpow (2*d) ((gamma:ℝ)-1)) := by\n    calc\n      (∫ y in Sᶜ, ‖K x y-K z y‖) ≤ ∫ y in Sᶜ, (2*d) * (|g y| / ‖x-y‖^2) := by\n        apply setIntegral_mono_on hdiff.norm.integrableOn\n          ((far_est g L hg x (2*d) (by positivity)).1.const_mul (2*d)) hmS.compl\n        intro y hy\n        have hlow : 2*d ≤ ‖x-y‖ := by\n          have hlow' : 2*d ≤ dist y x := not_lt.mp hy\n          simpa only [dist_eq_norm, norm_sub_rev] using hlow'\n        have hxy : x ≠ y := by\n          intro hh\n          simp only [hh, sub_self, norm_zero] at hlow\n          linarith\n        have hzy : z ≠ y := by\n          intro hh\n          rw [←hh, ←dist_eq_norm] at hlow\n          change 2*d ≤ d at hlow\n          linarith\n        have hnormpos : 0 < ‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)\n        have hznormpos : 0 < ‖z-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzy)\n        have htri : ‖x-y‖ ≤ d + ‖z-y‖ := by\n          simpa only [d, dist_eq_norm] using dist_triangle x z y\n        have hhalf : ‖x-y‖/2 ≤ ‖z-y‖ := by linarith\n        have hkinv := dist_div_norm_sq_smul (sub_ne_zero.mpr hxy) (sub_ne_zero.mpr hzy) 1\n        have heq : ‖(‖x-y‖ ^ 2)⁻¹ • (x-y) - (‖z-y‖ ^ 2)⁻¹ • (z-y)‖ =\n            d / (‖x-y‖ * ‖z-y‖) := by\n          simpa only [d, one_div, inv_pow, one_pow, dist_eq_norm,\n            sub_sub_sub_cancel_right, div_eq_mul_inv, one_mul, mul_comm] using hkinv\n        have hnormdiff : ‖K x y-K z y‖ = |g y| * (d / (‖x-y‖ * ‖z-y‖)) := by\n          dsimp [K]\n          rw [←smul_sub, norm_smul, Real.norm_eq_abs, heq]\n        rw [hnormdiff]\n        have hratio : d / (‖x-y‖ * ‖z-y‖) ≤ (2*d) / ‖x-y‖^2 := by\n          apply (div_le_div_iff₀ (mul_pos hnormpos hznormpos) (sq_pos_of_pos hnormpos)).mpr\n          nlinarith [mul_nonneg (norm_nonneg (x-y)) (by linarith : 0 ≤ 2*‖z-y‖-‖x-y‖)]\n        exact (mul_le_mul_of_nonneg_left hratio (abs_nonneg _)).trans_eq (by ring)\n      _ = (2*d) * ∫ y in Sᶜ, |g y| / ‖x-y‖^2 := integral_const_mul _ _\n      _ ≤ (2*d) * (Q * L * Real.rpow (2*d) ((gamma:ℝ)-1)) :=\n        mul_le_mul_of_nonneg_left (far_est g L hg x (2*d) (by positivity)).2 (by positivity)\n  have htwod : 0 < 2*d := by positivity\n  have hthreed : 0 < 3*d := by positivity\n  calc\n    ‖(∫ y, K x y) - (∫ y, K z y)‖ = ‖∫ y, K x y-K z y‖ := by\n      rw [integral_sub (hKi x hx) (hKi z hz)]\n    _ ≤ ∫ y, ‖K x y-K z y‖ := norm_integral_le_integral_norm _\n    _ = (∫ y in S, ‖K x y-K z y‖) + ∫ y in Sᶜ, ‖K x y-K z y‖ :=\n      (integral_add_compl hmS hdiff.norm).symm\n    _ ≤ (N * L * Real.rpow (2*d) gamma + N * L * Real.rpow (3*d) gamma) +\n        (2*d) * (Q * L * Real.rpow (2*d) ((gamma:ℝ)-1)) := add_le_add hnear hfar\n    _ = H * L * Real.rpow (dist x z) gamma := by\n      simp only [Real.rpow_eq_pow]\n      rw [Real.rpow_sub htwod, Real.rpow_one,\n        Real.mul_rpow (by norm_num : (0:ℝ)≤2) hd.le,\n        Real.mul_rpow (by norm_num : (0:ℝ)≤3) hd.le]\n      dsimp [H, d]\n      field_simp (disch := positivity)\n      ring\n\n)"))

theorem newtonian_kernel_compact_test_identity :
∀ (r : ℝ), 0 < r → ∀ (gamma : ℝ≥0), 0 < gamma → gamma < 1 →
  let T := fun (F : E2 → ℝ) (x : E2) =>
      ∫ y, ((halfDisc r).indicator F y) • ((‖x - y‖ ^ 2)⁻¹ • (x - y))
    ∀ (F : E2 → ℝ) (L : ℝ), ScalarGrowth univ ((halfDisc r).indicator F) gamma L →
      ∀ psi : E2 → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
        tsupport psi ⊆ halfDisc r →
        (∫ x in halfDisc r, F x * psi x) =
          -(2 * Real.pi)⁻¹ * ∫ x in halfDisc r, inner ℝ (T F x) (planarGradient psi x) := by
  classical
  intro r hr gamma hgamma hgamma1
  dsimp only
  intro F L hgrowth psi hpsi hcpsi hspsi
  have hbase : ∀ y : E2, (∫ x, inner ℝ ((‖x - y‖ ^ 2)⁻¹ • (x - y)) (planarGradient psi x)) =
      -(2 * Real.pi) * psi y := by
    classical
    let K : E2 → E2 := fun z => (‖z‖ ^ 2)⁻¹ • z
    let c : ℝ → E2 := unitCircleParameter
    have hn (t : ℝ) : ‖c t‖ = 1 := by
      have hs : ‖c t‖ ^ 2 = 1 := by
        rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
        exact Real.cos_sq_add_sin_sq t
      nlinarith [norm_nonneg (c t)]
    have hKn (z : E2) : ‖K z‖ = ‖z‖⁻¹ := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (sq_nonneg _)]
      by_cases hz : z = 0
      · simp [hz]
      · have hne : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
        simp only [pow_two, mul_inv_rev, mul_assoc, inv_mul_cancel₀ hne, mul_one]
    have hKm : Measurable K := by
      exact (measurable_norm.pow_const 2).inv.smul measurable_id
    have hKl : LocallyIntegrable K volume := by
      refine locallyIntegrable_of_norm_le_rpow (C := 1) (α := 1)
        (by simp [E2]) (by simp [E2]) ?_ hKm.aestronglyMeasurable
      filter_upwards [] with z
      rw [hKn]
      simp [Real.rpow_neg_one]
    have hG : Continuous (planarGradient psi) := continuous_planarGradient hpsi
    have hGc : HasCompactSupport (planarGradient psi) := by
      apply hcpsi.of_isClosed_subset (isClosed_tsupport _)
      apply closure_minimal
      · intro x hx
        by_contra hx'
        exact hx (planarGradient_eq_zero_off_support psi hx')
      · exact isClosed_tsupport psi
    have hgrad (x v : E2) : inner ℝ v (planarGradient psi x) = fderiv ℝ psi x v := by
      have hv : v = v 0 • coordinateVector 2 0 + v 1 • coordinateVector 2 1 := by
        ext i
        fin_cases i <;> simp [coordinateVector, EuclideanSpace.single]
      conv_rhs => rw [hv]
      simp [planarGradient, Fin.sum_univ_two, PiLp.inner_apply, RCLike.inner_apply,
        coordinateVector, EuclideanSpace.single]
      ring
    let e0 : E2 ≃ᵐ ℝ × ℝ :=
      (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.toMeasurableEquiv.trans MeasurableEquiv.finTwoArrow
    have he0 : MeasurePreserving e0 volume volume :=
      (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))
    intro y
    let e : (ℝ × ℝ) ≃ᵐ E2 := e0.symm
    have he : MeasurePreserving e volume volume := he0.symm e0
    have hepolar (rt : ℝ × ℝ) : e (polarCoord.symm rt) = rt.1 • c rt.2 := by
      ext k
      fin_cases k <;> rfl
    let G : E2 → E2 := fun z => planarGradient psi (y + z)
    have hGcont : Continuous G := hG.comp (continuous_const.add continuous_id)
    have hGcompact : HasCompactSupport G :=
      hGc.comp_isClosedEmbedding (Homeomorph.addLeft y).isClosedEmbedding
    have hKnloc : LocallyIntegrable (fun z => ‖K z‖) volume := fun x => (hKl x).norm
    have hpair : Integrable (fun z => inner ℝ (K z) (G z)) := by
      apply (hKnloc.integrable_smul_right_of_hasCompactSupport hGcont hGcompact).norm.mono'
        (hKm.aestronglyMeasurable.inner hGcont.aestronglyMeasurable)
      filter_upwards [] with z
      exact (norm_inner_le_norm _ _).trans_eq (by simp [norm_smul])
    have hpolar : IntegrableOn
        (fun rt : ℝ × ℝ => rt.1 * inner ℝ (K (rt.1 • c rt.2)) (G (rt.1 • c rt.2)))
        polarCoord.target := by
      have hI : Integrable ((fun z => inner ℝ (K z) (G z)) ∘ e) :=
        (he.integrable_comp_emb e.measurableEmbedding).mpr hpair
      have h := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
        polarCoord.open_target.measurableSet
        (fun rt _ => (hasFDerivAt_polarCoord_symm rt).hasFDerivWithinAt)
        polarCoord.symm.injOn ((fun z => inner ℝ (K z) (G z)) ∘ e)).mp hI.integrableOn
      apply h.congr_fun _ polarCoord.open_target.measurableSet
      intro rt hrt
      dsimp only
      rw [det_fderivPolarCoordSymm, abs_of_pos hrt.1]
      simp only [comp_apply, hepolar, smul_eq_mul]
    have hcancel (rt : ℝ × ℝ) (hrt : rt ∈ polarCoord.target) :
        rt.1 * inner ℝ (K (rt.1 • c rt.2)) (G (rt.1 • c rt.2)) =
          fderiv ℝ psi (y + rt.1 • c rt.2) (c rt.2) := by
      have hr : rt.1 ≠ 0 := hrt.1.ne'
      have hrpos : 0 < rt.1 := hrt.1
      simp only [K, norm_smul, Real.norm_eq_abs, abs_of_pos hrpos, hn, mul_one,
        G, hgrad]
      rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      rw [pow_two, mul_inv_rev]
      calc
        _ = (rt.1 * rt.1⁻¹) * (rt.1⁻¹ * rt.1) *
            (fderiv ℝ psi (y + rt.1 • c rt.2)) (c rt.2) := by ring
        _ = _ := by rw [mul_inv_cancel₀ hr, inv_mul_cancel₀ hr, one_mul, one_mul]
    have hpd : IntegrableOn
        (fun rt : ℝ × ℝ => fderiv ℝ psi (y + rt.1 • c rt.2) (c rt.2)) polarCoord.target :=
      hpolar.congr_fun hcancel polarCoord.open_target.measurableSet
    have hprod : (volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (-Real.pi) Real.pi)) =
        volume.restrict polarCoord.target := by
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
      rfl
    have hray (t : ℝ) :
        (∫ s in Ioi (0 : ℝ), fderiv ℝ psi (y + s • c t) (c t)) = -psi y := by
      have hisom : Isometry (fun s : ℝ => y + s • c t) := by
        apply Isometry.of_dist_eq
        intro s u
        rw [dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul,
          norm_smul, hn, mul_one]
      have hcs : HasCompactSupport (fun s : ℝ => psi (y + s • c t)) :=
        hcpsi.comp_isClosedEmbedding hisom.isClosedEmbedding
      have hds : ContDiff ℝ 1 (fun s : ℝ => psi (y + s • c t)) :=
        hpsi.of_le (by simp) |>.comp (by fun_prop)
      have hd (s : ℝ) : HasDerivAt (fun s : ℝ => psi (y + s • c t))
          (fderiv ℝ psi (y + s • c t) (c t)) s := by
        have hd0 := (hpsi.differentiable (by simp) (y + s • c t)).hasFDerivAt.comp_hasDerivAt s
          ((hasDerivAt_id s).smul_const (c t) |>.const_add y)
        simpa only [Function.comp_def, id_eq, one_smul] using hd0
      calc
        _ = ∫ s in Ioi (0 : ℝ), deriv (fun s : ℝ => psi (y + s • c t)) s := by
          apply integral_congr_ae
          filter_upwards [] with s
          exact (hd s).deriv.symm
        _ = -psi y := by simpa using hcs.integral_Ioi_deriv_eq hds 0
    calc
      (∫ x, inner ℝ ((‖x - y‖ ^ 2)⁻¹ • (x - y)) (planarGradient psi x)) =
          ∫ z, inner ℝ (K z) (G z) := by
        simpa only [K, G, add_sub_cancel_left] using
          (integral_add_left_eq_self
            (fun x => inner ℝ ((‖x - y‖ ^ 2)⁻¹ • (x - y)) (planarGradient psi x)) y).symm
      _ = ∫ rt in polarCoord.target,
          rt.1 * inner ℝ (K (rt.1 • c rt.2)) (G (rt.1 • c rt.2)) := by
        calc
          _ = ∫ rt, inner ℝ (K (e rt)) (G (e rt)) := (he.integral_comp' _).symm
          _ = _ := by
            simpa only [comp_apply, hepolar, smul_eq_mul] using
              (integral_comp_polarCoord_symm ((fun z => inner ℝ (K z) (G z)) ∘ e)).symm
      _ = ∫ rt in polarCoord.target, fderiv ℝ psi (y + rt.1 • c rt.2) (c rt.2) :=
        setIntegral_congr_fun polarCoord.open_target.measurableSet hcancel
      _ = ∫ t in Ioo (-Real.pi) Real.pi,
          ∫ s in Ioi (0 : ℝ), fderiv ℝ psi (y + s • c t) (c t) := by
        rw [← hprod]
        exact integral_prod_symm _ (by simpa only [IntegrableOn, ← hprod] using hpd)
      _ = -(2 * Real.pi) * psi y := by
        simp only [hray, setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Ioo,
          ENNReal.toReal_ofReal (by linarith [Real.pi_pos] : 0 ≤ Real.pi - -Real.pi)]
        ring
  let D : Set E2 := halfDisc r
  let K : E2 → E2 := fun z => (‖z‖ ^ 2)⁻¹ • z
  let k : E2 → E2 := (Metric.ball 0 (2 * r)).indicator K
  let F0 : E2 → ℝ := D.indicator F
  have hD : MeasurableSet D := by
    have hc : Continuous (fun x : E2 => x 1) := by fun_prop
    exact (Metric.isOpen_ball.inter (isOpen_lt continuous_const hc)).measurableSet
  have hKmeas : Measurable K := (measurable_norm.pow_const 2).inv.smul measurable_id
  have hKnorm (z : E2) : ‖K z‖ = ‖z‖⁻¹ := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (sq_nonneg _)]
    by_cases hz : z = 0
    · simp [hz]
    · have hne : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
      simp only [pow_two, mul_inv_rev, mul_assoc, inv_mul_cancel₀ hne, mul_one]
  have hKlocal : LocallyIntegrable K volume := by
    refine locallyIntegrable_of_norm_le_rpow (C := 1) (α := 1)
      (by simp [E2]) (by simp [E2]) ?_ hKmeas.aestronglyMeasurable
    filter_upwards [] with z
    rw [hKnorm]
    simp [Real.rpow_neg_one]
  have hk : Integrable k :=
    (integrable_indicator_iff measurableSet_ball).mpr
      ((hKlocal.integrableOn_isCompact (isCompact_closedBall 0 (2 * r))).mono_set
        Metric.ball_subset_closedBall)
  have hF0 : Integrable F0 := by
    simpa only [IntegrableOn, Measure.restrict_univ] using hgrowth.1
  have hpg : Continuous (planarGradient psi) := continuous_planarGradient hpsi
  have hpgc : HasCompactSupport (planarGradient psi) := by
    apply hcpsi.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal
    · intro x hx
      by_contra hx'
      exact hx (planarGradient_eq_zero_off_support psi hx')
    · exact isClosed_tsupport psi
  obtain ⟨C, hC⟩ := hpgc.exists_bound_of_continuousOn hpg.continuousOn
  have hpgbound (x : E2) : ‖planarGradient psi x‖ ≤ max C 0 := by
    by_cases hx : x ∈ tsupport (planarGradient psi)
    · exact (hC x hx).trans (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hx, norm_zero]
      exact le_max_right _ _
  have hvector : Integrable (fun xy : E2 × E2 => F0 xy.2 • k (xy.1 - xy.2))
      (volume.prod volume) := hF0.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) hk
  have hdouble : Integrable (fun xy : E2 × E2 =>
      inner ℝ (F0 xy.2 • k (xy.1 - xy.2)) (planarGradient psi xy.1))
      (volume.prod volume) := by
    apply (hvector.norm.mul_const (max C 0)).mono'
      (hvector.aestronglyMeasurable.inner (hpg.comp continuous_fst).aestronglyMeasurable)
    filter_upwards [] with xy
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hpgbound xy.1) (norm_nonneg _))
  have hcut (x y : E2) (hx : x ∈ D) (hy : y ∈ D) : k (x - y) = K (x - y) := by
    have hxn : ‖x‖ < r := by
      have hx' : dist x 0 < r := hx.1
      simpa only [dist_eq_norm, sub_zero] using hx'
    have hyn : ‖y‖ < r := by
      have hy' : dist y 0 < r := hy.1
      simpa only [dist_eq_norm, sub_zero] using hy'
    apply indicator_of_mem
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    exact (norm_sub_le _ _).trans_lt (by linarith)
  have hT (x : E2) (hx : x ∈ D) :
      (∫ y, F0 y • K (x - y)) = ∫ y, F0 y • k (x - y) := by
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : y ∈ D
    · rw [hcut x y hx hy]
    · simp only [F0, indicator_of_notMem hy, zero_smul]
  have heval (y : E2) (hy : y ∈ D) :
      (∫ x, inner ℝ (k (x - y)) (planarGradient psi x)) = -(2 * Real.pi) * psi y := by
    calc
      _ = ∫ x, inner ℝ (K (x - y)) (planarGradient psi x) := by
        apply integral_congr_ae
        filter_upwards [] with x
        by_cases hx : x ∈ tsupport psi
        · rw [hcut x y (hspsi hx) hy]
        · simp only [planarGradient_eq_zero_off_support psi hx, inner_zero_right]
      _ = _ := hbase y
  have hzero (x : E2) (hx : x ∉ D) : planarGradient psi x = 0 :=
    planarGradient_eq_zero_off_support psi (fun hx' => hx (hspsi hx'))
  have hident :
      (∫ x in D, inner ℝ (∫ y, F0 y • K (x - y)) (planarGradient psi x)) =
        -(2 * Real.pi) * (∫ x in D, F x * psi x) := by
    calc
      _ = ∫ x in D, inner ℝ (∫ y, F0 y • k (x - y)) (planarGradient psi x) :=
        setIntegral_congr_fun hD (fun x hx => by rw [hT x hx])
      _ = ∫ x, inner ℝ (∫ y, F0 y • k (x - y)) (planarGradient psi x) := by
        rw [← integral_indicator hD]
        apply integral_congr_ae
        filter_upwards [] with x
        by_cases hx : x ∈ D
        · simp only [indicator_of_mem hx]
        · simp only [indicator_of_notMem hx, hzero x hx, inner_zero_right]
      _ = ∫ x, ∫ y, inner ℝ (F0 y • k (x - y)) (planarGradient psi x) := by
        apply integral_congr_ae
        filter_upwards [hvector.prod_right_ae] with x hx
        simpa only [real_inner_comm] using (integral_inner hx (planarGradient psi x)).symm
      _ = ∫ y, ∫ x, inner ℝ (F0 y • k (x - y)) (planarGradient psi x) :=
        integral_integral_swap hdouble
      _ = ∫ y, F0 y * ∫ x, inner ℝ (k (x - y)) (planarGradient psi x) := by
        congr 1
        funext y
        simp only [real_inner_smul_left, integral_const_mul]
      _ = ∫ y, F0 y * (-(2 * Real.pi) * psi y) := by
        apply integral_congr_ae
        filter_upwards [] with y
        by_cases hy : y ∈ D
        · rw [heval y hy]
        · simp only [F0, indicator_of_notMem hy, zero_mul]
      _ = -(2 * Real.pi) * ∫ y, F0 y * psi y := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with y
        ring
      _ = -(2 * Real.pi) * (∫ y in D, F y * psi y) := by
        congr 1
        rw [← integral_indicator hD]
        apply integral_congr_ae
        filter_upwards [] with y
        by_cases hy : y ∈ D <;> simp [F0, hy]
  change (∫ x in D, F x * psi x) =
    -(2 * Real.pi)⁻¹ * ∫ x in D, inner ℝ (∫ y, F0 y • K (x - y)) (planarGradient psi x)
  rw [hident]
  rw [← mul_assoc]
  have hc : -(2 * Real.pi)⁻¹ * (-(2 * Real.pi)) = (1 : ℝ) := by
    rw [neg_mul_neg,
      inv_mul_cancel₀ (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)]
  rw [hc, one_mul]


end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak
