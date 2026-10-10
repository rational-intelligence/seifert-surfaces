import NativeCutoffMinimum

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
set_option autoImplicit false
set_option maxHeartbeats 0

private theorem native_hole_filling_geometric
    (F : ℕ → ℝ) (B a b T : ℝ)
    (hB : 0 ≤ B) (ha : 0 ≤ a) (ha1 : a < 1) (hb : 0 ≤ b)
    (hab : a * b < 1) (hT : 0 ≤ T)
    (hstep : ∀ n, F n ≤ a * F (n + 1) + B * b ^ n)
    (hbound : ∀ n, F n ≤ T) :
    ∀ m n, F m ≤ B * b ^ m / (1 - a * b) + a ^ n * T := by
  intro m n
  induction n generalizing m with
  | zero =>
      have hden : 0 < 1 - a * b := sub_pos.mpr hab
      have hmain : 0 ≤ B * b ^ m / (1 - a * b) := by positivity
      simpa only [pow_zero, one_mul] using (hbound m).trans (le_add_of_nonneg_left hmain)
  | succ n ih =>
      have hden : 0 < 1 - a * b := sub_pos.mpr hab
      calc
        F m ≤ a * F (m + 1) + B * b ^ m := hstep m
        _ ≤ a * (B * b ^ (m + 1) / (1 - a * b) + a ^ n * T) + B * b ^ m := by
          exact add_le_add (mul_le_mul_of_nonneg_left (ih (m + 1)) ha) le_rfl
        _ = B * b ^ m / (1 - a * b) + a ^ (n + 1) * T := by
          rw [pow_succ, pow_succ]
          field_simp
          ring

private theorem native_hole_filling_limit
    (F : ℕ → ℝ) (B a b T : ℝ)
    (hB : 0 ≤ B) (ha : 0 ≤ a) (ha1 : a < 1) (hb : 0 ≤ b)
    (hab : a * b < 1) (hT : 0 ≤ T)
    (hstep : ∀ n, F n ≤ a * F (n + 1) + B * b ^ n)
    (hbound : ∀ n, F n ≤ T) :
    F 0 ≤ B / (1 - a * b) := by
  have htail := (tendsto_pow_atTop_nhds_zero_of_lt_one ha ha1).mul_const T
  have ht : Tendsto (fun n : ℕ => B / (1 - a * b) + a ^ n * T)
      atTop (𝓝 (B / (1 - a * b) + 0 * T)) := tendsto_const_nhds.add htail
  simp only [zero_mul, add_zero] at ht
  apply le_of_tendsto_of_tendsto tendsto_const_nhds ht
  exact Filter.Eventually.of_forall fun n => by
    simpa only [pow_zero, mul_one] using
      native_hole_filling_geometric F B a b T hB ha ha1 hb hab hT hstep hbound 0 n

#print axioms native_hole_filling_geometric
#print axioms native_hole_filling_limit

private theorem native_hole_filling_radii
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : ℝ → ℝ) (K I r R T : ℝ),
      0 ≤ K → 0 ≤ I → 0 < r → r < R → 0 ≤ T →
      (∀ t, r ≤ t → t < R → E t ≤ T) →
      (∀ s t, r ≤ s → s < t → t < R →
        E s ≤ q * E t + K * I / (t - s)^2) →
      E r ≤ C * K * I / (R - r)^2 := by
  let l : ℝ := (1 + q) / 2
  have hl : 0 < l := by dsimp [l]; linarith
  have hl1 : l < 1 := by dsimp [l]; linarith
  have hql : q < l ^ 2 := by dsimp [l]; nlinarith [sq_pos_of_pos (sub_pos.mpr hq1)]
  let b : ℝ := (l ^ 2)⁻¹
  have hb : 0 ≤ b := by positivity
  have hqb : q * b < 1 := by
    dsimp [b]
    exact (mul_inv_lt_iff₀ (sq_pos_of_pos hl)).mpr (by simpa using hql)
  let C : ℝ := 1 / ((1 - l)^2 * (1 - q * b))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro E K I r R T hK hI hr hrR hT hbound hstep
  let v : ℕ → ℝ := fun n => R - (R - r) * l ^ n
  have hvr (n : ℕ) : r ≤ v n := by
    have hpow : l ^ n ≤ 1 := pow_le_one₀ hl.le hl1.le
    dsimp [v]
    nlinarith [mul_le_mul_of_nonneg_left hpow (sub_pos.mpr hrR).le]
  have hvR (n : ℕ) : v n < R := by
    have hh := mul_pos (sub_pos.mpr hrR) (pow_pos hl n)
    dsimp [v]
    linarith
  have hvlt (n : ℕ) : v n < v (n + 1) := by
    dsimp [v]
    rw [pow_succ]
    nlinarith [pow_pos hl n, mul_pos (sub_pos.mpr hrR) (pow_pos hl n)]
  have hgap (n : ℕ) : v (n + 1) - v n = (R - r) * (1 - l) * l ^ n := by
    dsimp [v]
    rw [pow_succ]
    ring
  let B : ℝ := K * I / ((R - r)^2 * (1 - l)^2)
  have hB : 0 ≤ B := by positivity
  have hs (n : ℕ) : E (v n) ≤ q * E (v (n + 1)) + B * b ^ n := by
    have h := hstep (v n) (v (n + 1)) (hvr n) (hvlt n) (hvR (n + 1))
    convert h using 1
    rw [hgap]
    dsimp [B, b]
    rw [inv_pow, show (l ^ 2) ^ n = (l ^ n)^2 by rw [← pow_mul, ← pow_mul, Nat.mul_comm], mul_pow, mul_pow]
    field_simp
  have he := native_hole_filling_limit (fun n => E (v n)) B q b T hB hq hq1 hb hqb hT hs
    (fun n => hbound (v n) (hvr n) (hvR n))
  have hv0 : v 0 = r := by simp [v]
  rw [hv0] at he
  calc
    E r ≤ B / (1 - q * b) := he
    _ = C * K * I / (R - r)^2 := by
      dsimp [B, C]
      field_simp

#print axioms native_hole_filling_radii
