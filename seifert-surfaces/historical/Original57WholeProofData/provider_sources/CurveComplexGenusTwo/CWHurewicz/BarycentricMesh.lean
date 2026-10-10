import CurveComplexGenusTwo.CWHurewicz.BarycentricFlag

namespace CurveComplexGenusTwo.CWHurewicz

open Convexity
open Classical

/-- The ℓ¹ distance between two finite weight vectors. -/
def barycentricWeightL1 {I : Type*} [Fintype I] (x y : I → ℝ) : ℝ :=
  ∑ i, |x i - y i|

/-- A column-stochastic matrix with a common atom contracts ℓ¹ distance. -/
private theorem stochastic_common_atom_contract
    {I J : Type*} [Fintype I] [Fintype J]
    (a : I → J → ℝ) (p : I) (c : ℝ)
    (ha0 : ∀ i j, 0 ≤ a i j)
    (ha1 : ∀ j, ∑ i, a i j = 1)
    (hap : ∀ j, c ≤ a p j)
    (x y : J → ℝ) (hxy : ∑ j, (x j - y j) = 0) :
    barycentricWeightL1 (fun i => ∑ j, a i j * x j)
      (fun i => ∑ j, a i j * y j) ≤ (1 - c) * barycentricWeightL1 x y := by
  let b : I → J → ℝ := fun i j => a i j - if i = p then c else 0
  have hb0 (i : I) (j : J) : 0 ≤ b i j := by
    dsimp [b]
    split_ifs with h
    · subst i
      exact sub_nonneg.mpr (hap j)
    · simpa using ha0 i j
  have hb1 (j : J) : ∑ i, b i j = 1 - c := by
    simp only [b, Finset.sum_sub_distrib, ha1]
    simp
  have hformula (i : I) :
      (∑ j, a i j * x j) - (∑ j, a i j * y j) =
        ∑ j, b i j * (x j - y j) := by
    simp only [← Finset.sum_sub_distrib, ← mul_sub]
    by_cases hi : i = p
    · subst i
      simp only [b, sub_mul, Finset.sum_sub_distrib]
      simp [← Finset.mul_sum, hxy]
    · simp [b, hi]
  unfold barycentricWeightL1
  simp_rw [hformula]
  calc
    (∑ i, |∑ j, b i j * (x j - y j)|) ≤
        ∑ i, ∑ j, b i j * |x j - y j| := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        _ ≤ ∑ j, |b i j * (x j - y j)| := Finset.abs_sum_le_sum_abs _ _
        _ = _ := by congr 1; ext j; rw [abs_mul, abs_of_nonneg (hb0 i j)]
    _ = ∑ j, (∑ i, b i j) * |x j - y j| := by
      rw [Finset.sum_comm]
      congr 1
      ext j
      rw [Finset.sum_mul]
    _ = (1 - c) * ∑ j, |x j - y j| := by
      simp_rw [hb1]
      rw [Finset.mul_sum]

private noncomputable def flagMatrix (n : ℕ) (σ : Equiv.Perm (Fin (n + 1)))
    (i j : Fin (n + 1)) : ℝ :=
  (barycentricFlag n σ (.single j)).weights i

private theorem flagMatrix_nonneg (n : ℕ) (σ : Equiv.Perm (Fin (n + 1)))
    (i j : Fin (n + 1)) : 0 ≤ flagMatrix n σ i j :=
  (barycentricFlag n σ (.single j)).weights_nonneg i

private theorem flagMatrix_column_sum (n : ℕ) (σ : Equiv.Perm (Fin (n + 1)))
    (j : Fin (n + 1)) : ∑ i, flagMatrix n σ i j = 1 := by
  simp [flagMatrix]

private theorem flagMatrix_common_atom (n : ℕ)
    (σ : Equiv.Perm (Fin (n + 1))) (j : Fin (n + 1)) :
    ((n + 1 : ℕ) : ℝ)⁻¹ ≤ flagMatrix n σ (σ 0) j := by
  let S : Finset (Fin (n + 1)) := Finset.univ.filter (fun i => σ.symm i ≤ j)
  have hmem : σ 0 ∈ S := by simp [S]
  have hSne : S.Nonempty := ⟨σ 0, hmem⟩
  have hcard0 : 0 < S.card := Finset.card_pos.mpr ⟨σ 0, hmem⟩
  have hcard : S.card ≤ n + 1 := by
    calc S.card ≤ (Finset.univ : Finset (Fin (n + 1))).card := Finset.card_le_card (Finset.subset_univ _)
      _ = n + 1 := by simp
  have hweight : flagMatrix n σ (σ 0) j = (S.card : ℝ)⁻¹ := by
    unfold flagMatrix
    rw [barycentricFlag_vertex]
    change (StdSimplex.subBarycenter (K := ℝ) S hSne).weights (σ 0) = _
    simp [StdSimplex.weights_subBarycenter, Finsupp.single_apply, hmem]
  rw [hweight]
  have hcard0' : (0 : ℝ) < S.card := by exact_mod_cast hcard0
  have hcard' : (S.card : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast hcard
  simpa [one_div] using one_div_le_one_div_of_le hcard0' hcard'

private theorem flagMatrix_apply (n : ℕ)
    (σ : Equiv.Perm (Fin (n + 1)))
    (t : StdSimplex ℝ (Fin (n + 1))) (i : Fin (n + 1)) :
    (barycentricFlag n σ t).weights i =
      ∑ j, flagMatrix n σ i j * t.weights j := by
  change (barycentricFlagAffine n σ t).weights i = _
  simp only [barycentricFlagAffine,
    StdSimplex.affineMapMk_apply, StdSimplex.weights_iConvexComb]
  rw [Finsupp.sum_fintype _ _ (by simp)]
  simp [flagMatrix, barycentricFlag_vertex, mul_comm]

theorem barycentricFlag_weightL1_contract (n : ℕ)
    (σ : Equiv.Perm (Fin (n + 1)))
    (t u : StdSimplex ℝ (Fin (n + 1))) :
    barycentricWeightL1 (fun i => (barycentricFlag n σ t).weights i)
      (fun i => (barycentricFlag n σ u).weights i) ≤
      (1 - ((n + 1 : ℕ) : ℝ)⁻¹) *
        barycentricWeightL1 (fun i => t.weights i) (fun i => u.weights i) := by
  have hsum : ∑ j : Fin (n + 1), (t.weights j - u.weights j) = 0 := by
    simp [Finset.sum_sub_distrib]
  simpa only [flagMatrix_apply, mul_comm] using
    stochastic_common_atom_contract (flagMatrix n σ) (σ 0)
      (((n + 1 : ℕ) : ℝ)⁻¹)
      (flagMatrix_nonneg n σ) (flagMatrix_column_sum n σ)
      (flagMatrix_common_atom n σ) (fun j => t.weights j)
      (fun j => u.weights j) hsum

/-- Compose a list of barycentric flags in fixed dimension. -/
noncomputable def barycentricFlagIterate (n : ℕ)
    (ss : List (Equiv.Perm (Fin (n + 1)))) :
    StdSimplex ℝ (Fin (n + 1)) → StdSimplex ℝ (Fin (n + 1)) :=
  match ss with
  | [] => id
  | σ :: tail => barycentricFlagIterate n tail ∘ barycentricFlag n σ

theorem barycentricFlagIterate_weightL1 (n : ℕ)
    (ss : List (Equiv.Perm (Fin (n + 1))))
    (t u : StdSimplex ℝ (Fin (n + 1))) :
    barycentricWeightL1 (fun i => (barycentricFlagIterate n ss t).weights i)
      (fun i => (barycentricFlagIterate n ss u).weights i) ≤
      (1 - ((n + 1 : ℕ) : ℝ)⁻¹) ^ ss.length *
        barycentricWeightL1 (fun i => t.weights i) (fun i => u.weights i) := by
  induction ss generalizing t u with
  | nil => simp [barycentricFlagIterate]
  | cons σ ss ih =>
      simp only [barycentricFlagIterate, Function.comp_apply, List.length_cons]
      calc
        _ ≤ (1 - ((n + 1 : ℕ) : ℝ)⁻¹) ^ ss.length *
            barycentricWeightL1 (fun i => (barycentricFlag n σ t).weights i)
              (fun i => (barycentricFlag n σ u).weights i) := ih _ _
        _ ≤ (1 - ((n + 1 : ℕ) : ℝ)⁻¹) ^ ss.length *
            ((1 - ((n + 1 : ℕ) : ℝ)⁻¹) *
              barycentricWeightL1 (fun i => t.weights i) (fun i => u.weights i)) := by
          apply mul_le_mul_of_nonneg_left (barycentricFlag_weightL1_contract n σ t u)
          exact pow_nonneg (by
            have hn : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
            have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hn
            simp only [div_one, one_div] at h
            linarith) _
        _ = _ := by rw [pow_succ]; ring

private theorem simplex_weightL1_le_two (n : ℕ)
    (t u : StdSimplex ℝ (Fin (n + 1))) :
    barycentricWeightL1 (fun i => t.weights i) (fun i => u.weights i) ≤ 2 := by
  unfold barycentricWeightL1
  calc
    (∑ i, |t.weights i - u.weights i|) ≤
        ∑ i, (t.weights i + u.weights i) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_le]
      constructor <;> have ht := t.weights_nonneg i <;>
        have hu := u.weights_nonneg i <;> linarith
    _ = 2 := by simp [Finset.sum_add_distrib]; norm_num

noncomputable local instance barycentricMeshMetricSpace (n : ℕ) :
    MetricSpace (StdSimplex ℝ (Fin (n + 1))) :=
  (StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).comapMetricSpace
    (fun t => (t.weights : Fin (n + 1) → ℝ))

private theorem simplex_dist_le_weightL1 (n : ℕ)
    (t u : StdSimplex ℝ (Fin (n + 1))) :
    dist t u ≤ barycentricWeightL1 (fun i => t.weights i) (fun i => u.weights i) := by
  change dist (t.weights : Fin (n + 1) → ℝ) (u.weights : Fin (n + 1) → ℝ) ≤ _
  simp only [dist_pi_def, Real.nndist_eq]
  have hsup : (Finset.univ.sup fun i : Fin (n + 1) =>
      Real.nnabs (t.weights i - u.weights i)) ≤
      ∑ i : Fin (n + 1), Real.nnabs (t.weights i - u.weights i) := by
    apply Finset.sup_le
    intro i hi
    exact Finset.single_le_sum (fun j _ => show (0 : NNReal) ≤
      Real.nnabs (t.weights j - u.weights j) from bot_le) (Finset.mem_univ i)
  calc
    (↑(Finset.univ.sup fun i : Fin (n + 1) =>
      Real.nnabs (t.weights i - u.weights i)) : ℝ) ≤
        (↑(∑ i : Fin (n + 1), Real.nnabs (t.weights i - u.weights i)) : ℝ) :=
          by exact_mod_cast hsup
    _ = barycentricWeightL1 (fun i => t.weights i) (fun i => u.weights i) := by
      simp [barycentricWeightL1, Real.coe_nnabs]

theorem barycentricFlagIterate_mesh (n : ℕ)
    (ss : List (Equiv.Perm (Fin (n + 1))))
    (t u : StdSimplex ℝ (Fin (n + 1))) :
    dist (barycentricFlagIterate n ss t) (barycentricFlagIterate n ss u) ≤
      2 * (1 - ((n + 1 : ℕ) : ℝ)⁻¹) ^ ss.length := by
  calc
    _ ≤ barycentricWeightL1 (fun i => (barycentricFlagIterate n ss t).weights i)
      (fun i => (barycentricFlagIterate n ss u).weights i) :=
        simplex_dist_le_weightL1 n _ _
    _ ≤ (1 - ((n + 1 : ℕ) : ℝ)⁻¹) ^ ss.length *
      barycentricWeightL1 (fun i => t.weights i) (fun i => u.weights i) :=
        barycentricFlagIterate_weightL1 n ss t u
    _ ≤ 2 * (1 - ((n + 1 : ℕ) : ℝ)⁻¹) ^ ss.length := by
      have hq : 0 ≤ 1 - ((n + 1 : ℕ) : ℝ)⁻¹ := by
        have : (1 : ℝ) ≤ n + 1 := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
        have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) this
        have : ((n + 1 : ℕ) : ℝ)⁻¹ ≤ 1 := by simpa [one_div] using h
        linarith
      nlinarith [simplex_weightL1_le_two n t u, pow_nonneg hq ss.length]

/-- A fixed initial subdivision depth absorbs the factor two from the ℓ¹ bound. -/
theorem barycentricFlagIterate_mesh_power (n : ℕ) :
    ∃ m : ℕ, ∀ k : ℕ, ∀ ss : List (Equiv.Perm (Fin (n + 1))),
      ss.length = k + m → ∀ t u : StdSimplex ℝ (Fin (n + 1)),
      dist (barycentricFlagIterate n ss t) (barycentricFlagIterate n ss u) ≤
        (1 - ((n + 1 : ℕ) : ℝ)⁻¹) ^ k := by
  let q : ℝ := 1 - ((n + 1 : ℕ) : ℝ)⁻¹
  have hn : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hq0 : 0 ≤ q := by
    have hn1 : (1 : ℝ) ≤ (n + 1 : ℕ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hn1
    dsimp [q]
    simp only [div_one, one_div] at h
    linarith
  have hq1 : q < 1 := by
    dsimp [q]
    have : 0 < ((n + 1 : ℕ) : ℝ)⁻¹ := inv_pos.mpr hn
    linarith
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (by norm_num : (0 : ℝ) < 1 / 2) hq1
  refine ⟨m, ?_⟩
  intro k ss hss t u
  have hpow : 0 ≤ q ^ k := pow_nonneg hq0 _
  have hmul : 2 * q ^ m ≤ 1 := by linarith
  calc
    dist (barycentricFlagIterate n ss t) (barycentricFlagIterate n ss u) ≤
      2 * q ^ ss.length := barycentricFlagIterate_mesh n ss t u
    _ = (2 * q ^ m) * q ^ k := by rw [hss, pow_add]; ring
    _ ≤ q ^ k := by nlinarith

/-- Every fixed-dimensional sequence of barycentric flags eventually has arbitrarily small mesh. -/
theorem barycentricFlagIterate_eventually_small (n : ℕ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ k : ℕ, ∀ ss : List (Equiv.Perm (Fin (n + 1))),
      ss.length = k → ∀ t u : StdSimplex ℝ (Fin (n + 1)),
      dist (barycentricFlagIterate n ss t) (barycentricFlagIterate n ss u) < δ := by
  obtain ⟨m, hm⟩ := barycentricFlagIterate_mesh_power n
  have hn : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  let q : ℝ := 1 - ((n + 1 : ℕ) : ℝ)⁻¹
  have hq1 : q < 1 := by
    dsimp [q]
    have : 0 < ((n + 1 : ℕ) : ℝ)⁻¹ := inv_pos.mpr hn
    linarith
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hδ hq1
  refine ⟨k + m, ?_⟩
  intro ss hss t u
  exact (hm k ss hss t u).trans_lt hk

/-- One depth works for every branch of the subdivision and every simplex in a finite family. -/
theorem barycentricFlagIterate_finite_family_eventually_subordinate
    {X : Type*} [TopologicalSpace X] (n : ℕ) (A U : Set X)
    (fs : List C(StdSimplex ℝ (Fin (n + 1)), X))
    (δ : ℝ) (hδ : 0 < δ)
    (hcover : ∀ f ∈ fs, ∀ z : StdSimplex ℝ (Fin (n + 1)),
      f '' Metric.ball z δ ⊆ Uᶜ ∨ f '' Metric.ball z δ ⊆ A) :
    ∃ k : ℕ, ∀ f ∈ fs,
      ∀ ss : List (Equiv.Perm (Fin (n + 1))), ss.length = k →
      (f ∘ barycentricFlagIterate n ss) '' Set.univ ⊆ Uᶜ ∨
        (f ∘ barycentricFlagIterate n ss) '' Set.univ ⊆ A := by
  obtain ⟨k, hk⟩ := barycentricFlagIterate_eventually_small n δ hδ
  refine ⟨k, ?_⟩
  intro f hf ss hss
  let t : StdSimplex ℝ (Fin (n + 1)) := .single 0
  rcases hcover f hf (barycentricFlagIterate n ss t) with h | h
  · left
    rintro y ⟨u, -, rfl⟩
    apply h
    refine ⟨barycentricFlagIterate n ss u, ?_, rfl⟩
    exact Metric.mem_ball.mpr (hk ss hss u t)
  · right
    rintro y ⟨u, -, rfl⟩
    apply h
    refine ⟨barycentricFlagIterate n ss u, ?_, rfl⟩
    exact Metric.mem_ball.mpr (hk ss hss u t)

end CurveComplexGenusTwo.CWHurewicz
