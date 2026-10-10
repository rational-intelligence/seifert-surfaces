/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco

Modified by FL-Prover (2026-10-04): the almost-everywhere identification is
adapted from Campanato/Holder.lean. This module adds the finite-radius
localization, segment chaining, and exact approved target data.
-/
import CampanatoVector.Holder
import WeakDivergenceData
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsor

noncomputable section
open Set MeasureTheory Metric Filter
open scoped NNReal ENNReal Topology
namespace SeifertSurfaces.WeakSchauder

open CampanatoVector

lemma ballMean_eq_ballAverage (G : V → V) (x : V) (r : ℝ) :
    ballMean G x r = ballAverage G x r := by
  simp [ballMean, ballAverage, average, integral_smul_measure]

lemma radius_le_of_ball_subset {a x : V} {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (h : ball a r ⊆ ball x s) : r ≤ s := by
  have hm := measureReal_mono h (μ := volume) measure_ball_lt_top.ne
  rw [measureReal_ball a hr, measureReal_ball x hs] at hm
  have hp : r ^ 3 ≤ s ^ 3 := (mul_le_mul_iff_left₀ (unitBallVolume_pos (d := 3))).mp hm
  exact (pow_le_pow_iff_left₀ hr.le hs.le (by norm_num : 3 ≠ 0)).mp hp

lemma local_campanato {R : ℝ} (hR : 0 < R) {β : NNReal} {M : ℝ} (hM : 0 ≤ M)
    {G : V → V} {center x : V} (hx : x ∈ ball center (R / 2))
    (hcamp : CampanatoBound G (ball center (3 * R / 4)) (R / 8) β M) :
    CampanatoOn (ball x (R / 8)) G β (Real.sqrt M) := by
  intro a r hr har
  have ha : a ∈ ball x (R / 8) := har (mem_ball_self hr)
  have hac : a ∈ ball center (3 * R / 4) := by
    rw [mem_ball] at ha hx ⊢
    calc dist a center ≤ dist a x + dist x center := dist_triangle _ _ _
      _ < 3 * R / 4 := by linarith
  have hb := hcamp a hac r hr (radius_le_of_ball_subset hr (by linarith) har)
  simpa [excess, ballMean_eq_ballAverage, Real.sq_sqrt hM] using hb

lemma local_ball_subset {R : ℝ} (hR : 0 < R) {center x : V}
    (hx : x ∈ ball center (R / 2)) : ball x (R / 8) ⊆ ball center R := by
  intro z hz
  rw [mem_ball] at hz hx ⊢
  calc dist z center ≤ dist z x + dist x center := dist_triangle _ _ _
    _ < R := by linarith

lemma limit_converges_local {R : ℝ} (hR : 0 < R) {β : NNReal} (hβ : 0 < β)
    {M : ℝ} (hM : 0 ≤ M) {G : V → V} {center : V}
    (hG : MemLp G 2 (volume.restrict (ball center R)))
    (hcamp : CampanatoBound G (ball center (3 * R / 4)) (R / 8) β M)
    {x : V} (hx : x ∈ ball center (R / 2)) :
    Tendsto (fun k : ℕ => ballAverage G x ((1 / 2 : ℝ) ^ k)) atTop
      (𝓝 (campanatoLimit G x)) := by
  exact tendsto_ballAverage_campanatoLimit (by exact_mod_cast hβ) (Real.sqrt_nonneg M)
    isOpen_ball (hG.mono_measure (Measure.restrict_mono (local_ball_subset hR hx) le_rfl))
    (local_campanato hR hM hx hcamp) (mem_ball_self (by linarith))

lemma limit_pair_local {R : ℝ} (hR : 0 < R) {β : NNReal} (hβ : 0 < β)
    {M : ℝ} (hM : 0 ≤ M) {G : V → V} {center : V}
    (hG : MemLp G 2 (volume.restrict (ball center R)))
    (hcamp : CampanatoBound G (ball center (3 * R / 4)) (R / 8) β M)
    {x y : V} (hx : x ∈ ball center (R / 2)) (hy : y ∈ ball center (R / 2))
    (hxy : dist x y ≤ R / 32) :
    ‖campanatoLimit G x - campanatoLimit G y‖ ≤
      campanatoHolderConst 3 β * Real.sqrt M * dist x y ^ (β : ℝ) := by
  rcases eq_or_ne x y with rfl | hne
  · simp [Real.zero_rpow (show (β : ℝ) ≠ 0 from ne_of_gt (by exact_mod_cast hβ))]
  have hyx : y ∈ ball x (R / 8) := by rw [mem_ball, dist_comm]; linarith
  have hsubx : ball x (2 * dist x y) ⊆ ball x (R / 8) :=
    ball_subset_ball (by linarith)
  have hsuby : ball y (2 * dist x y) ⊆ ball x (R / 8) := by
    intro z hz
    rw [mem_ball] at hz ⊢
    calc dist z x ≤ dist z y + dist y x := dist_triangle _ _ _
      _ < R / 8 := by rw [dist_comm y x]; linarith
  exact abs_campanatoLimit_sub_le (by exact_mod_cast hβ) (Real.sqrt_nonneg M) isOpen_ball
    (hG.mono_measure (Measure.restrict_mono (local_ball_subset hR hx) le_rfl))
    (local_campanato hR hM hx hcamp) (mem_ball_self (by linarith)) hyx hne hsubx hsuby

lemma limit_pair_global {R : ℝ} (hR : 0 < R) {β : NNReal} (hβ : 0 < β)
    {M : ℝ} (hM : 0 ≤ M) {G : V → V} {center : V}
    (hG : MemLp G 2 (volume.restrict (ball center R)))
    (hcamp : CampanatoBound G (ball center (3 * R / 4)) (R / 8) β M)
    {x y : V} (hx : x ∈ ball center (R / 2)) (hy : y ∈ ball center (R / 2)) :
    ‖campanatoLimit G x - campanatoLimit G y‖ ≤
      32 * campanatoHolderConst 3 β * Real.sqrt M * dist x y ^ (β : ℝ) := by
  let p : ℕ → V := fun i => AffineMap.lineMap x y ((i : ℝ) / 32)
  have hpmem : ∀ i : ℕ, i ≤ 32 → p i ∈ ball center (R / 2) := by
    intro i hi
    apply (convex_ball center (R / 2)).lineMap_mem hx hy
    constructor
    · positivity
    · exact (div_le_one (by norm_num)).mpr (by exact_mod_cast hi)
  have hpdist : ∀ i : ℕ, dist (p i) (p (i + 1)) = dist x y / 32 := by
    intro i
    dsimp [p]
    rw [dist_lineMap_lineMap, Real.dist_eq]
    push_cast
    rw [show (i : ℝ) / 32 - ((i : ℝ) + 1) / 32 = -(1 / 32) by ring]
    norm_num
    ring
  have hd : dist x y < R := by
    have hxc := mem_ball.mp hx
    have hyc := mem_ball.mp hy
    have h := dist_triangle x center y
    rw [dist_comm center y] at h
    linarith
  have hstep : ∀ i : ℕ, i < 32 →
      ‖campanatoLimit G (p i) - campanatoLimit G (p (i + 1))‖ ≤
        campanatoHolderConst 3 β * Real.sqrt M * dist x y ^ (β : ℝ) := by
    intro i hi
    have hb := limit_pair_local hR hβ hM hG hcamp (hpmem i (by omega))
      (hpmem (i + 1) (by omega)) (by rw [hpdist]; linarith)
    apply hb.trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg
      (campanatoHolderConst_nonneg (by exact_mod_cast hβ)) (Real.sqrt_nonneg M))
    apply Real.rpow_le_rpow dist_nonneg _ β.coe_nonneg
    rw [hpdist]
    nlinarith [dist_nonneg (x := x) (y := y)]
  have ht : ∀ n : ℕ, n ≤ 32 →
      ‖campanatoLimit G (p 0) - campanatoLimit G (p n)‖ ≤
        n * (campanatoHolderConst 3 β * Real.sqrt M * dist x y ^ (β : ℝ)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro hn
      calc ‖campanatoLimit G (p 0) - campanatoLimit G (p (n + 1))‖
          ≤ ‖campanatoLimit G (p 0) - campanatoLimit G (p n)‖ +
            ‖campanatoLimit G (p n) - campanatoLimit G (p (n + 1))‖ :=
              norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ n * (campanatoHolderConst 3 β * Real.sqrt M * dist x y ^ (β : ℝ)) +
            campanatoHolderConst 3 β * Real.sqrt M * dist x y ^ (β : ℝ) :=
              add_le_add (ih (by omega)) (hstep n (by omega))
        _ = (n + 1 : ℕ) * (campanatoHolderConst 3 β * Real.sqrt M * dist x y ^ (β : ℝ)) := by
          push_cast; ring
  simpa [p, mul_assoc] using ht 32 le_rfl

lemma limit_ae_eq_local {R : ℝ} (hR : 0 < R) {β : NNReal} (hβ : 0 < β)
    {M : ℝ} (hM : 0 ≤ M) {G : V → V} {center : V}
    (hG : MemLp G 2 (volume.restrict (ball center R)))
    (hcamp : CampanatoBound G (ball center (3 * R / 4)) (R / 8) β M) :
    campanatoLimit G =ᵐ[volume.restrict (ball center (R / 2))] G := by
  let Ω := ball center R
  have hΩ : IsOpen Ω := isOpen_ball
  have huint : IntegrableOn G Ω volume := hG.integrable (by norm_num)
  have hind : Integrable (Ω.indicator G) volume :=
    huint.integrable_indicator hΩ.measurableSet
  have hae := (Besicovitch.vitaliFamily (volume : Measure V)).ae_tendsto_average
    hind.locallyIntegrable
  have hδ : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (𝓝[>] 0) :=
    tendsto_pow_atTop_nhdsWithin_zero_of_lt_one (by norm_num) (by norm_num)
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_ball]
  filter_upwards [hae] with x hx hxB
  have hxΩ : x ∈ Ω := ball_subset_ball (by linarith : R / 2 ≤ R) hxB
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hΩ x hxΩ
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (1 / 2 : ℝ) ^ N < ε := exists_pow_lt_of_lt_one hε (by norm_num)
  have hcomp : Tendsto
      (fun k : ℕ => ⨍ y in closedBall x ((1 / 2 : ℝ) ^ k), Ω.indicator G y)
      atTop (𝓝 (Ω.indicator G x)) :=
    hx.comp ((Besicovitch.tendsto_filterAt volume x).comp hδ)
  have heq : ∀ᶠ k in atTop,
      (⨍ y in closedBall x ((1 / 2 : ℝ) ^ k), Ω.indicator G y)
        = ballAverage G x ((1 / 2 : ℝ) ^ k) := by
    filter_upwards [eventually_ge_atTop N] with k hk
    have hkε : (1 / 2 : ℝ) ^ k < ε :=
      lt_of_le_of_lt (pow_le_pow_of_le_one (by norm_num) (by norm_num) hk) hN
    have hsubΩ : closedBall x ((1 / 2 : ℝ) ^ k) ⊆ Ω :=
      (closedBall_subset_ball hkε).trans hball
    rw [setAverage_congr_fun measurableSet_closedBall
        (Filter.Eventually.of_forall fun y hy => Set.indicator_of_mem (hsubΩ hy) G),
      setAverage_congr (closedBall_ae_eq_ball (by norm_num) x ((1 / 2 : ℝ) ^ k))]
    rfl
  have h1 : Tendsto (fun k : ℕ => ballAverage G x ((1 / 2 : ℝ) ^ k)) atTop
      (𝓝 (Ω.indicator G x)) := hcomp.congr' heq
  have h2 := limit_converges_local hR hβ hM hG hcamp hxB
  rw [tendsto_nhds_unique h2 h1, Set.indicator_of_mem hxΩ]

end SeifertSurfaces.WeakSchauder
