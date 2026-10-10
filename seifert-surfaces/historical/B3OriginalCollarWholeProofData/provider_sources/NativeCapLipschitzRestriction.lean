import NativeSobolevEnergyDensity
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.L1Independent
set_option autoImplicit false
set_option maxHeartbeats 0

-- Localized reuse of the paid native cap-mean telescope; no convexity of S is required.
private theorem native_cap_excess_holderOn_restriction
    (V : E2 → Mat2)
    (L2 : ∀ i j, MemLp (fun x => V x i j) 2 (volume.restrict (disc 1)))
    (S : Set E2) (hS : S ⊆ closedDisc 1)
    (gamma : ℝ≥0) (gamma_pos : 0 < gamma)
    (C r0 : ℝ) (C_nonneg : 0 ≤ C) (r0_pos : 0 < r0) (r0_le_one : r0 ≤ 1)
    (excess : ∀ x ∈ S, ∀ r : ℝ, 0 < r → r ≤ r0 →
      capExcess V x r ≤ C * Real.rpow r (2 + 2 * (gamma : ℝ)))
    (origlim : ∀ x ∈ S, ∀ i j,
      Tendsto (fun n => capMean V x (dyadicRadius r0 n) i j) atTop (𝓝 (V x i j)))
    (Bound : ℝ) (hBound : 0 ≤ Bound) (hbound : ∀ x ∈ S, ∀ i j, |V x i j| ≤ Bound) :
    ∃ K : ℝ≥0, ∀ i j, HolderOnWith K gamma (fun x => V x i j) S := by
  classical
  have hCapMeas (x : E2) (r : ℝ) : MeasurableSet (planarCap x r) :=
    measurableSet_ball.inter measurableSet_ball
  have hCapFinite (x : E2) (r : ℝ) : volume (planarCap x r) ≠ ⊤ :=
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono inter_subset_right)
  have hCapL2 (x : E2) (r : ℝ) (i j : Fin 2) :
      MemLp (fun z => V z i j) 2 (volume.restrict (planarCap x r)) :=
    (L2 i j).mono_measure (Measure.restrict_mono inter_subset_left le_rfl)
  have hFrobNonneg (A : Mat2) : 0 ≤ frobeniusSquared A :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg (A i j)))
  have hFrobInt (x : E2) (r : ℝ) (A : Mat2) :
      IntegrableOn (fun z => frobeniusSquared (V z - A)) (planarCap x r) := by
    let : IsFiniteMeasure (volume.restrict (planarCap x r)) :=
      isFiniteMeasure_restrict.mpr (hCapFinite x r)
    have hs (i j : Fin 2) : IntegrableOn (fun z => (V z i j - A i j) ^ 2) (planarCap x r) :=
      ((hCapL2 x r i j).sub (memLp_const (A i j))).integrable_sq
    exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hs i j))
  have hFrobSplit (A B W : Mat2) :
      frobeniusSquared (A - B) ≤ 2 * frobeniusSquared (W - A) + 2 * frobeniusSquared (W - B) := by
    change (∑ i, ∑ j, (A i j - B i j) ^ 2) ≤
      2 * (∑ i, ∑ j, (W i j - A i j) ^ 2) + 2 * (∑ i, ∑ j, (W i j - B i j) ^ 2)
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    nlinarith [sq_nonneg (2 * W i j - A i j - B i j)]
  have hCapComparison (x y z : E2) (r t s : ℝ)
      (hzx : planarCap z s ⊆ planarCap x r) (hzy : planarCap z s ⊆ planarCap y t) :
      frobeniusSquared (capMean V x r - capMean V y t) * capVolume z s ≤
        2 * (capExcess V x r + capExcess V y t) := by
    let A := capMean V x r
    let B := capMean V y t
    have hconst : IntegrableOn (fun _ : E2 => frobeniusSquared (A - B)) (planarCap z s) :=
      integrableOn_const (hCapFinite z s)
    have hiA := hFrobInt z s A
    have hiB := hFrobInt z s B
    have hmono := setIntegral_mono_on hconst ((hiA.const_mul 2).add (hiB.const_mul 2))
      (hCapMeas z s) (fun w _ => hFrobSplit A B (V w))
    simp only [Pi.add_apply] at hmono
    rw [setIntegral_const, smul_eq_mul, integral_add (hiA.const_mul 2) (hiB.const_mul 2),
      integral_const_mul, integral_const_mul] at hmono
    have hA := setIntegral_mono_set (hFrobInt x r A)
      (Filter.Eventually.of_forall (fun w => hFrobNonneg (V w - A))) hzx.eventuallyLE
    have hB := setIntegral_mono_set (hFrobInt y t B)
      (Filter.Eventually.of_forall (fun w => hFrobNonneg (V w - B))) hzy.eventuallyLE
    change capVolume z s * frobeniusSquared (A - B) ≤ _ at hmono
    change (∫ w in planarCap z s, frobeniusSquared (V w - A)) ≤ _ at hA
    change (∫ w in planarCap z s, frobeniusSquared (V w - B)) ≤ _ at hB
    change frobeniusSquared (A - B) * capVolume z s ≤
      2 * ((∫ w in planarCap x r, frobeniusSquared (V w - A)) +
      ∫ w in planarCap y t, frobeniusSquared (V w - B))
    nlinarith
  have hRadiusSplit (r : ℝ) (hr : 0 < r) :
      Real.rpow r (2 + 2 * (gamma : ℝ)) = r ^ 2 * Real.rpow r (2 * (gamma : ℝ)) := by
    change r ^ ((2 : ℝ) + 2 * (gamma : ℝ)) = r ^ 2 * r ^ (2 * (gamma : ℝ))
    rw [Real.rpow_add hr, Real.rpow_two]
  have hNested (c : ℝ) (hc : 0 < c)
      (hvol : ∀ x ∈ S, ∀ r : ℝ, 0 < r → r ≤ r0 → c * r ^ 2 ≤ capVolume x r)
      (x : E2) (hx : x ∈ S) (r s : ℝ)
      (hr : 0 < r) (hr0 : r ≤ r0) (hrs : r / 2 ≤ s) (hsr : s ≤ r) :
      frobeniusSquared (capMean V x r - capMean V x s) ≤
        (16 * C / c) * Real.rpow r (2 * (gamma : ℝ)) := by
    have hs : 0 < s := lt_of_lt_of_le (half_pos hr) hrs
    have hsub : planarCap x s ⊆ planarCap x r :=
      inter_subset_inter_right _ (Metric.ball_subset_ball hsr)
    have hcomp := hCapComparison x x x r s s hsub Subset.rfl
    have hvr := hvol x hx s hs (hsr.trans hr0)
    have hnonneg := hFrobNonneg (capMean V x r - capMean V x s)
    have he1 := excess x hx r hr hr0
    have he2 := excess x hx s hs (hsr.trans hr0)
    have hpower : Real.rpow s (2 + 2 * (gamma : ℝ)) ≤ Real.rpow r (2 + 2 * (gamma : ℝ)) :=
      Real.rpow_le_rpow hs.le hsr (by positivity)
    have hsmall : c * r ^ 2 / 4 ≤ capVolume x s := by
      have hsq : r ^ 2 / 4 ≤ s ^ 2 := by nlinarith
      have hh := mul_le_mul_of_nonneg_left hsq hc.le
      nlinarith only [hh, hvr]
    have hproduct : frobeniusSquared (capMean V x r - capMean V x s) * (c * r ^ 2 / 4) ≤
        4 * C * Real.rpow r (2 + 2 * (gamma : ℝ)) := by
      calc _ ≤ frobeniusSquared (capMean V x r - capMean V x s) * capVolume x s :=
          mul_le_mul_of_nonneg_left hsmall hnonneg
        _ ≤ 2 * (capExcess V x r + capExcess V x s) := hcomp
        _ ≤ 4 * C * Real.rpow r (2 + 2 * (gamma : ℝ)) := by
          nlinarith [mul_le_mul_of_nonneg_left hpower C_nonneg]
    apply le_of_mul_le_mul_right (a := c * r ^ 2 / 4) ?_ (by positivity)
    calc _ ≤ 4 * C * Real.rpow r (2 + 2 * (gamma : ℝ)) := hproduct
      _ = (16 * C / c * Real.rpow r (2 * (gamma : ℝ))) * (c * r ^ 2 / 4) := by
        rw [hRadiusSplit r hr]
        field_simp (disch := positivity) <;> ring
  have hFrobSym (A B : Mat2) : frobeniusSquared (A - B) = frobeniusSquared (B - A) := by
    change (∑ i, ∑ j, (A i j - B i j) ^ 2) = ∑ i, ∑ j, (B i j - A i j) ^ 2
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hBigCap (c : ℝ) (hc : 0 < c)
      (hvol : ∀ x ∈ S, ∀ r : ℝ, 0 < r → r ≤ r0 → c * r ^ 2 ≤ capVolume x r)
      (x z : E2) (hx : x ∈ S) (hz : z ∈ S) (r : ℝ)
      (hr : 0 < r) (hr0 : 3 * r ≤ r0) (hzx : dist z x ≤ r) :
      frobeniusSquared (capMean V z r - capMean V x (3 * r)) ≤
        (2 * C / c * (1 + Real.rpow 3 (2 + 2 * (gamma : ℝ)))) *
          Real.rpow r (2 * (gamma : ℝ)) := by
    have hsub : planarCap z r ⊆ planarCap x (3 * r) := by
      intro w hw
      refine ⟨hw.1, ?_⟩
      have hh : dist w z < r := hw.2
      exact lt_of_le_of_lt (dist_triangle w z x) (by linarith)
    have hcomp := hCapComparison z x z r (3 * r) r Subset.rfl hsub
    have hv := hvol z hz r hr (by linarith)
    have hn := hFrobNonneg (capMean V z r - capMean V x (3 * r))
    have he1 := excess z hz r hr (by linarith)
    have he2 := excess x hx (3 * r) (by positivity) hr0
    have hp : Real.rpow (3 * r) (2 + 2 * (gamma : ℝ)) =
        Real.rpow 3 (2 + 2 * (gamma : ℝ)) * Real.rpow r (2 + 2 * (gamma : ℝ)) := by
      change (3 * r) ^ (2 + 2 * (gamma : ℝ)) = (3 : ℝ) ^ (2 + 2 * (gamma : ℝ)) * r ^ (2 + 2 * (gamma : ℝ))
      exact Real.mul_rpow (by norm_num) hr.le
    apply le_of_mul_le_mul_right (a := c * r ^ 2) ?_ (by positivity)
    calc _ ≤ frobeniusSquared (capMean V z r - capMean V x (3 * r)) * capVolume z r :=
          mul_le_mul_of_nonneg_left hv hn
      _ ≤ 2 * (capExcess V z r + capExcess V x (3 * r)) := hcomp
      _ ≤ 2 * C * (Real.rpow r (2 + 2 * (gamma : ℝ)) + Real.rpow (3 * r) (2 + 2 * (gamma : ℝ))) := by linarith
      _ = _ := by
        rw [hp, hRadiusSplit r hr]
        field_simp (disch := positivity) <;> ring
  have hNearby (c : ℝ) (hc : 0 < c)
      (hvol : ∀ x ∈ S, ∀ r : ℝ, 0 < r → r ≤ r0 → c * r ^ 2 ≤ capVolume x r)
      (x y : E2) (hx : x ∈ S) (hy : y ∈ S) (r : ℝ)
      (hr : 0 < r) (hr0 : 3 * r ≤ r0) (hxy : dist x y ≤ r) :
      frobeniusSquared (capMean V x r - capMean V y r) ≤
        (8 * C / c * (1 + Real.rpow 3 (2 + 2 * (gamma : ℝ)))) *
          Real.rpow r (2 * (gamma : ℝ)) := by
    have hxB := hBigCap c hc hvol x x hx hx r hr hr0 (by simpa using hr.le)
    have hyB := hBigCap c hc hvol x y hx hy r hr hr0 (by simpa [dist_comm] using hxy)
    have hsplit := hFrobSplit (capMean V x r) (capMean V y r) (capMean V x (3 * r))
    rw [hFrobSym (capMean V x (3 * r)) (capMean V x r),
      hFrobSym (capMean V x (3 * r)) (capMean V y r)] at hsplit
    have hh := hsplit.trans (add_le_add (mul_le_mul_of_nonneg_left hxB (by norm_num : (0 : ℝ) ≤ 2))
      (mul_le_mul_of_nonneg_left hyB (by norm_num : (0 : ℝ) ≤ 2)))
    convert hh using 1 <;> ring
  have hEntrySq (A : Mat2) (i j : Fin 2) : (A i j) ^ 2 ≤ frobeniusSquared A := by
    apply (Finset.single_le_sum (fun k _ => sq_nonneg (A i k)) (Finset.mem_univ j)).trans
    exact Finset.single_le_sum
      (fun k _ => Finset.sum_nonneg (fun l _ => sq_nonneg (A k l))) (Finset.mem_univ i)
  have hRpowSq (r : ℝ) (hr : 0 < r) :
      (Real.rpow r (gamma : ℝ)) ^ 2 = Real.rpow r (2 * (gamma : ℝ)) := by
    change (r ^ (gamma : ℝ)) ^ 2 = r ^ (2 * (gamma : ℝ))
    rw [← Real.rpow_mul_natCast hr.le (gamma : ℝ) 2]
    congr 1
    norm_num
    ring
  have hDyadicPos (n : ℕ) : 0 < dyadicRadius r0 n := by
    change 0 < r0 / (2 : ℝ) ^ n
    positivity
  have hDyadicLe (n : ℕ) : dyadicRadius r0 n ≤ r0 := by
    change r0 / (2 : ℝ) ^ n ≤ r0
    exact div_le_self r0_pos.le (one_le_pow₀ (by norm_num))
  have hDyadicHalf (n : ℕ) : dyadicRadius r0 (n + 1) = dyadicRadius r0 n / 2 := by
    change r0 / (2 : ℝ) ^ (n + 1) = (r0 / (2 : ℝ) ^ n) / 2
    rw [pow_succ, div_mul_eq_div_div]
  have hDyadicForm (n : ℕ) : dyadicRadius r0 n = r0 * (1 / 2 : ℝ) ^ n := by
    change r0 / (2 : ℝ) ^ n = r0 * (1 / 2 : ℝ) ^ n
    rw [one_div, inv_pow, div_eq_mul_inv]
  let q : ℝ := Real.rpow (1 / 2) (gamma : ℝ)
  have hq0 : 0 < q := Real.rpow_pos_of_pos (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) (by exact_mod_cast gamma_pos)
  have hDyadicPower (n : ℕ) :
      Real.rpow (dyadicRadius r0 n) (gamma : ℝ) = Real.rpow r0 (gamma : ℝ) * q ^ n := by
    change (dyadicRadius r0 n) ^ (gamma : ℝ) = r0 ^ (gamma : ℝ) * ((1 / 2 : ℝ) ^ (gamma : ℝ)) ^ n
    rw [hDyadicForm, Real.mul_rpow r0_pos.le (by positivity)]
    congr 1
    rw [← Real.rpow_natCast_mul (by norm_num), ← Real.rpow_mul_natCast (by norm_num)]
    congr 1
    ring
  have hDyadicReconstruction (A : ℝ) (hA : 0 ≤ A)
      (hstep : ∀ n : ℕ, ∀ x ∈ S,
        frobeniusSquared (capMean V x (dyadicRadius r0 n) - capMean V x (dyadicRadius r0 (n + 1))) ≤
          A ^ 2 * Real.rpow (dyadicRadius r0 n) (2 * (gamma : ℝ))) :
      ∃ Vc : E2 → Mat2,
        (∀ i j x, x ∈ S →
          Filter.Tendsto (fun n => capMean V x (dyadicRadius r0 n) i j) Filter.atTop (𝓝 (Vc x i j))) ∧
        (∀ n x, x ∈ S → ∀ i j,
          |capMean V x (dyadicRadius r0 n) i j - Vc x i j| ≤
            (A / (1 - q)) * Real.rpow (dyadicRadius r0 n) (gamma : ℝ)) ∧
        (∀ i j, TendstoUniformlyOn (fun n x => capMean V x (dyadicRadius r0 n) i j)
          (fun x => Vc x i j) Filter.atTop (S)) ∧
        (∀ n x, x ∈ S →
          frobeniusSquared (capMean V x (dyadicRadius r0 n) - Vc x) ≤
            (2 * A / (1 - q)) ^ 2 * Real.rpow (dyadicRadius r0 n) (2 * (gamma : ℝ))) := by
    have hScalarStep (x : E2) (hx : x ∈ S) (i j : Fin 2) (n : ℕ) :
        dist (capMean V x (dyadicRadius r0 n) i j) (capMean V x (dyadicRadius r0 (n + 1)) i j) ≤
          (A * Real.rpow r0 (gamma : ℝ)) * q ^ n := by
      have hs := (hEntrySq _ i j).trans (hstep n x hx)
      change (capMean V x (dyadicRadius r0 n) i j - capMean V x (dyadicRadius r0 (n + 1)) i j) ^ 2 ≤ _ at hs
      have hn : 0 ≤ Real.rpow (dyadicRadius r0 n) (gamma : ℝ) :=
        Real.rpow_nonneg (hDyadicPos n).le (gamma : ℝ)
      rw [← hRpowSq _ (hDyadicPos n)] at hs
      rw [Real.dist_eq]
      have hb : |capMean V x (dyadicRadius r0 n) i j - capMean V x (dyadicRadius r0 (n + 1)) i j| ≤
          A * Real.rpow (dyadicRadius r0 n) (gamma : ℝ) := by
        nlinarith [sq_abs (capMean V x (dyadicRadius r0 n) i j - capMean V x (dyadicRadius r0 (n + 1)) i j),
          abs_nonneg (capMean V x (dyadicRadius r0 n) i j - capMean V x (dyadicRadius r0 (n + 1)) i j),
          mul_nonneg hA hn]
      simpa only [hDyadicPower n, mul_assoc] using hb
    let Vc : E2 → Mat2 := fun x i j => Filter.limUnder Filter.atTop
      (fun n : ℕ => capMean V x (dyadicRadius r0 n) i j)
    have hlim (i j : Fin 2) (x : E2) (hx : x ∈ S) :
        Filter.Tendsto (fun n => capMean V x (dyadicRadius r0 n) i j) Filter.atTop (𝓝 (Vc x i j)) :=
      (cauchySeq_of_le_geometric q (A * Real.rpow r0 (gamma : ℝ)) hq1 (hScalarStep x hx i j)).tendsto_limUnder
    have htail (n : ℕ) (x : E2) (hx : x ∈ S) (i j : Fin 2) :
        |capMean V x (dyadicRadius r0 n) i j - Vc x i j| ≤
          (A / (1 - q)) * Real.rpow (dyadicRadius r0 n) (gamma : ℝ) := by
      have ht := dist_le_of_le_geometric_of_tendsto q (A * Real.rpow r0 (gamma : ℝ))
        hq1 (hScalarStep x hx i j) (hlim i j x hx) n
      rw [Real.dist_eq] at ht
      rw [hDyadicPower]
      convert ht using 1 <;> ring
    have hzero : Filter.Tendsto (fun n : ℕ => (A / (1 - q)) * Real.rpow (dyadicRadius r0 n) (gamma : ℝ))
        Filter.atTop (𝓝 0) := by
      have hmul (n : ℕ) : (A / (1 - q)) * Real.rpow (dyadicRadius r0 n) (gamma : ℝ) =
          ((A / (1 - q)) * Real.rpow r0 (gamma : ℝ)) * q ^ n := by
        rw [hDyadicPower]
        ring
      simp_rw [hmul]
      convert (tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1).const_mul
        (A / (1 - q) * Real.rpow r0 (gamma : ℝ)) using 1 <;> simp
    refine ⟨Vc, hlim, htail, ?_, ?_⟩
    · intro i j
      apply Metric.tendstoUniformlyOn_iff.mpr
      intro e he
      filter_upwards [hzero.eventually (gt_mem_nhds he)] with n hn x hx
      rw [Real.dist_eq, abs_sub_comm]
      exact (htail n x hx i j).trans_lt hn
    · intro n x hx
      have hentry (i j : Fin 2) :
          (capMean V x (dyadicRadius r0 n) i j - Vc x i j) ^ 2 ≤
            ((A / (1 - q)) * Real.rpow (dyadicRadius r0 n) (gamma : ℝ)) ^ 2 := by
        have hh := htail n x hx i j
        nlinarith [sq_abs (capMean V x (dyadicRadius r0 n) i j - Vc x i j),
          abs_nonneg (capMean V x (dyadicRadius r0 n) i j - Vc x i j)]
      have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 2)))
        (fun i _ => Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 2))) (fun j _ => hentry i j))
      change frobeniusSquared (capMean V x (dyadicRadius r0 n) - Vc x) ≤ _ at hh
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
      rw [← hRpowSq _ (hDyadicPos n)]
      convert hh using 1 <;> ring
  have hRadiusTendsto : Filter.Tendsto (dyadicRadius r0) Filter.atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Filter.Eventually.of_forall hDyadicPos⟩
    change Filter.Tendsto (fun n => dyadicRadius r0 n) Filter.atTop (𝓝 (0 : ℝ))
    simp_rw [hDyadicForm]
    convert (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).const_mul r0 using 1 <;> simp
  have hLocalHolder (Vc : E2 → Mat2) (B H : ℝ) (hB : 0 ≤ B) (hH : 0 ≤ H)
      (htail : ∀ n x, x ∈ S → ∀ i j,
        |capMean V x (dyadicRadius r0 n) i j - Vc x i j| ≤
          B * Real.rpow (dyadicRadius r0 n) (gamma : ℝ))
      (hnear : ∀ x ∈ S, ∀ y ∈ S, ∀ r : ℝ,
        0 < r → 3 * r ≤ r0 → dist x y ≤ r → ∀ i j,
        |capMean V x r i j - capMean V y r i j| ≤ H * Real.rpow r (gamma : ℝ))
      (x y : E2) (hx : x ∈ S) (hy : y ∈ S)
      (hxy : dist x y ≤ r0 / 6) (i j : Fin 2) :
      |Vc x i j - Vc y i j| ≤
        ((2 * B + H) * Real.rpow 2 (gamma : ℝ)) * Real.rpow (dist x y) (gamma : ℝ) := by
    by_cases heq : x = y
    · subst y
      simp only [sub_self, abs_zero]
      exact mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg (by norm_num) _))
        (Real.rpow_nonneg dist_nonneg _)
    have hd : 0 < dist x y := dist_pos.mpr heq
    obtain ⟨n, hnlo, hnhi⟩ := exists_nat_pow_near_of_lt_one (div_pos hd r0_pos)
      ((div_le_one r0_pos).mpr (by linarith : dist x y ≤ r0))
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    have hdlo : dist x y ≤ dyadicRadius r0 n := by
      rw [hDyadicForm]
      exact (div_le_iff₀ r0_pos).mp hnhi |>.trans_eq (mul_comm _ _)
    have hdhi : dyadicRadius r0 n < 2 * dist x y := by
      have hh := (lt_div_iff₀ r0_pos).mp hnlo
      rw [pow_succ] at hh
      rw [hDyadicForm]
      nlinarith only [hh]
    have hscale : 3 * dyadicRadius r0 n ≤ r0 := by linarith
    have hxT := htail n x hx i j
    have hyT := htail n y hy i j
    have hnT := hnear x hx y hy _ (hDyadicPos n) hscale hdlo i j
    have htri : |Vc x i j - Vc y i j| ≤
        (2 * B + H) * Real.rpow (dyadicRadius r0 n) (gamma : ℝ) := by
      have hh := abs_sub_le (Vc x i j) (capMean V x (dyadicRadius r0 n) i j) (Vc y i j)
      have hh' := abs_sub_le (capMean V x (dyadicRadius r0 n) i j)
        (capMean V y (dyadicRadius r0 n) i j) (Vc y i j)
      have hxT' : |Vc x i j - capMean V x (dyadicRadius r0 n) i j| ≤
          B * Real.rpow (dyadicRadius r0 n) (gamma : ℝ) := by
        simpa only [abs_sub_comm] using hxT
      linarith
    have hp : Real.rpow (dyadicRadius r0 n) (gamma : ℝ) ≤
        Real.rpow (2 * dist x y) (gamma : ℝ) :=
      Real.rpow_le_rpow (hDyadicPos n).le hdhi.le gamma.coe_nonneg
    have hmul : Real.rpow (2 * dist x y) (gamma : ℝ) =
        Real.rpow 2 (gamma : ℝ) * Real.rpow (dist x y) (gamma : ℝ) :=
      Real.mul_rpow (by norm_num) hd.le
    calc _ ≤ (2 * B + H) * Real.rpow (dyadicRadius r0 n) (gamma : ℝ) := htri
      _ ≤ (2 * B + H) * Real.rpow (2 * dist x y) (gamma : ℝ) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = _ := by rw [hmul]; ring
  have hVolumeComparison := planar_cap_volume_comparable
  have hVolumeLower : ∃ c : ℝ, 0 < c ∧ ∀ x ∈ S, ∀ r : ℝ,
      0 < r → r ≤ r0 → c * r ^ 2 ≤ capVolume x r := by
    obtain ⟨c, D, hc, _, hv⟩ := hVolumeComparison
    exact ⟨c, hc, fun x hx r hr hr0 => (hv x (hS hx) r hr (hr0.trans r0_le_one)).2.2.1⟩
  obtain ⟨c, hc, hvol⟩ := hVolumeLower
  let A : ℝ := Real.sqrt (16 * C / c)
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hAsq : A ^ 2 = 16 * C / c := Real.sq_sqrt (by positivity)
  have hstep : ∀ n : ℕ, ∀ x ∈ S,
      frobeniusSquared (capMean V x (dyadicRadius r0 n) - capMean V x (dyadicRadius r0 (n + 1))) ≤
        A ^ 2 * Real.rpow (dyadicRadius r0 n) (2 * (gamma : ℝ)) := by
    intro n x hx
    rw [hAsq, hDyadicHalf]
    exact hNested c hc hvol x hx _ _ (hDyadicPos n) (hDyadicLe n) le_rfl (by linarith [hDyadicPos n])
  obtain ⟨Vc, hlim, htail, huniform, hfrobTail⟩ := hDyadicReconstruction A hA hstep
  let B : ℝ := A / (1 - q)
  have hB : 0 ≤ B := div_nonneg hA (sub_pos.mpr hq1).le
  let H : ℝ := Real.sqrt (8 * C / c * (1 + Real.rpow 3 (2 + 2 * (gamma : ℝ))))
  have hH : 0 ≤ H := Real.sqrt_nonneg _
  have hHsq : H ^ 2 = 8 * C / c * (1 + Real.rpow 3 (2 + 2 * (gamma : ℝ))) :=
    Real.sq_sqrt (mul_nonneg (by positivity)
      (add_nonneg zero_le_one (Real.rpow_nonneg (by norm_num) _)))
  have hnear : ∀ x ∈ S, ∀ y ∈ S, ∀ r : ℝ,
      0 < r → 3 * r ≤ r0 → dist x y ≤ r → ∀ i j,
      |capMean V x r i j - capMean V y r i j| ≤ H * Real.rpow r (gamma : ℝ) := by
    intro x hx y hy r hr hr0 hxy i j
    have hs := (hEntrySq _ i j).trans (hNearby c hc hvol x y hx hy r hr hr0 hxy)
    change (capMean V x r i j - capMean V y r i j) ^ 2 ≤ _ at hs
    rw [← hHsq, ← hRpowSq r hr] at hs
    have hn : 0 ≤ Real.rpow r (gamma : ℝ) := Real.rpow_nonneg hr.le _
    nlinarith [sq_abs (capMean V x r i j - capMean V y r i j),
      abs_nonneg (capMean V x r i j - capMean V y r i j), mul_nonneg hH hn]
  let J : ℝ := (2 * B + H) * Real.rpow 2 (gamma : ℝ)
  have hJ : 0 ≤ J := mul_nonneg (by positivity) (Real.rpow_nonneg (by norm_num) _)
  have hsame : ∀ x ∈ S, Vc x = V x := by
    intro x hx
    funext i j
    exact tendsto_nhds_unique (hlim i j x hx) (origlim x hx i j)
  let G : ℝ := max J (2 * Bound / Real.rpow (r0 / 6) (gamma : ℝ))
  have hG : 0 ≤ G := hJ.trans (le_max_left _ _)
  have hglobal : ∀ x ∈ S, ∀ y ∈ S, ∀ i j,
      |V x i j - V y i j| ≤ G * Real.rpow (dist x y) (gamma : ℝ) := by
    intro x hx y hy i j
    by_cases hd : dist x y ≤ r0 / 6
    · have hh := hLocalHolder Vc B H hB hH htail hnear x y hx hy hd i j
      rw [hsame x hx, hsame y hy] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg dist_nonneg _))
    · have hrad : 0 < Real.rpow (r0 / 6) (gamma : ℝ) :=
        Real.rpow_pos_of_pos (by positivity) _
      have hdp : Real.rpow (r0 / 6) (gamma : ℝ) ≤ Real.rpow (dist x y) (gamma : ℝ) :=
        Real.rpow_le_rpow (by positivity) (le_of_lt (lt_of_not_ge hd)) gamma.coe_nonneg
      have hn : 0 ≤ 2 * Bound / Real.rpow (r0 / 6) (gamma : ℝ) := by positivity
      calc |V x i j - V y i j| ≤ |V x i j| + |V y i j| := abs_sub _ _
        _ ≤ 2 * Bound := by linarith [hbound x hx i j, hbound y hy i j]
        _ = (2 * Bound / Real.rpow (r0 / 6) (gamma : ℝ)) *
            Real.rpow (r0 / 6) (gamma : ℝ) := by field_simp
        _ ≤ (2 * Bound / Real.rpow (r0 / 6) (gamma : ℝ)) *
            Real.rpow (dist x y) (gamma : ℝ) := mul_le_mul_of_nonneg_left hdp hn
        _ ≤ G * Real.rpow (dist x y) (gamma : ℝ) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg dist_nonneg _)
  let K : ℝ≥0 := ⟨G, hG⟩
  refine ⟨K, ?_⟩
  intro i j x hx y hy
  rw [edist_dist, edist_dist,
    ENNReal.ofReal_rpow_of_nonneg dist_nonneg gamma.coe_nonneg,
    ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul K.coe_nonneg]
  apply ENNReal.ofReal_le_ofReal
  rw [Real.dist_eq]
  exact hglobal x hx y hy i j

#print axioms native_cap_excess_holderOn_restriction
