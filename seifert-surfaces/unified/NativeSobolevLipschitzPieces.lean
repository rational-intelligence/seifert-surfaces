import NativeCapLipschitzRestriction
import NativeSobolevCapMeans

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

private theorem native_H1_countable_lipschitz_coincidences
    (u : E2 → E2) (d : Fin 2 → E2 → E2)
    (hH1 : ∀ i, H1On (disc 1) (fun x => u x i) (d i))
    (huc : ContinuousOn u (closedDisc 1)) :
    ∃ (v : ℕ → E2 → E2) (C : ℕ → ℝ≥0),
      (∀ n, LipschitzWith (C n) (v n)) ∧
      volume (disc 1 \ ⋃ n, {x | u x = v n x}) = 0 := by
  classical
  have henergyAE : ∀ᵐ x ∂volume, ∃ C r0 : ℝ, 0 ≤ C ∧ 0 < r0 ∧
      ∀ r : ℝ, 0 < r → r ≤ r0 →
        (∫ z in planarCap x r, euclideanJetDensity d z) ≤ C * r ^ 2 := by
    run_tac do
      let n := (Lean.Name.num `_private.NativeSobolevEnergyDensity 0).str
        "native_H1_ae_local_quadratic_energy_bound"
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        exact $(Lean.mkIdent n) $(Lean.mkIdent `u) $(Lean.mkIdent `d) $(Lean.mkIdent `hH1)))
  have hmeanAE : ∀ᵐ x ∂volume, x ∈ disc 1 → ∀ r0 : ℝ, 0 < r0 → ∀ i j,
      Tendsto (fun n => capMean (fun z i _j => u z i) x (dyadicRadius r0 n) i j)
        atTop (𝓝 (u x i)) := by
    run_tac do
      let n := (Lean.Name.num `_private.NativeSobolevCapMeans 0).str
        "native_H1_ae_cap_mean_limit"
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        exact $(Lean.mkIdent n) $(Lean.mkIdent `u) $(Lean.mkIdent `d) $(Lean.mkIdent `hH1)))
  obtain ⟨P, hP, hPoincare⟩ := AnalyticLower.native_H1_moving_cap_poincare u d hH1
  obtain ⟨Bound, hBound⟩ := (isCompact_closedBall (0 : E2) 1).exists_bound_of_continuousOn huc
  let B : ℝ := max Bound 0
  have hB : 0 ≤ B := le_max_right _ _
  have hb : ∀ x ∈ closedDisc 1, ∀ i : Fin 2, |u x i| ≤ B := by
    intro x hx i
    exact (PiLp.norm_apply_le (u x) i).trans ((hBound x hx).trans (le_max_left _ _))
  let S : ℕ → Set E2 := fun n => {x | x ∈ disc 1 ∧
    (∀ r : ℝ, 0 < r → r ≤ 1 / ((n : ℝ) + 1) →
      (∫ z in planarCap x r, euclideanJetDensity d z) ≤ ((n : ℝ) + 1) * r ^ 2) ∧
    ∀ r0 : ℝ, 0 < r0 → ∀ i j,
      Tendsto (fun k => capMean (fun z i _j => u z i) x (dyadicRadius r0 k) i j)
        atTop (𝓝 (u x i))}
  have hLevel : ∀ n, ∃ K : ℝ≥0, LipschitzOnWith K u (S n) := by
    intro n
    let r0 : ℝ := 1 / ((n : ℝ) + 1)
    let C : ℝ := P * ((n : ℝ) + 1)
    let V : E2 → Mat2 := fun z i _j => u z i
    have hS : S n ⊆ closedDisc 1 := fun x hx => Metric.ball_subset_closedBall hx.1
    have hr0 : 0 < r0 := by positivity
    have hr01 : r0 ≤ 1 := by
      have hden : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        exact le_add_of_nonneg_left (Nat.cast_nonneg n)
      simpa [r0] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hden
    have hC : 0 ≤ C := by positivity
    have hL2 : ∀ i j, MemLp (fun x => V x i j) 2 (volume.restrict (disc 1)) :=
      fun i _ => (hH1 i).2.1
    have hexcess : ∀ x ∈ S n, ∀ r : ℝ, 0 < r → r ≤ r0 →
        capExcess V x r ≤ C * Real.rpow r (2 + 2 * ((1 : ℝ≥0) : ℝ)) := by
      intro x hx r hr hrr
      have hp := hPoincare x (hS hx) r hr (hrr.trans hr01)
      have he := hx.2.1 r hr hrr
      apply hp.trans
      have hb := mul_le_mul_of_nonneg_left he (mul_nonneg hP (sq_nonneg r))
      have hpow : Real.rpow r (2 + 2 * ((1 : ℝ≥0) : ℝ)) = r ^ (4 : ℕ) := by
        norm_num
      rw [hpow]
      convert hb using 1 <;> dsimp [C] <;> ring
    have hlim : ∀ x ∈ S n, ∀ i j,
        Tendsto (fun k => capMean V x (dyadicRadius r0 k) i j) atTop (𝓝 (V x i j)) :=
      fun x hx i j => hx.2.2 r0 hr0 i j
    have hbV : ∀ x ∈ S n, ∀ i j, |V x i j| ≤ B :=
      fun x hx i _ => hb x (hS hx) i
    have hholder : ∃ K : ℝ≥0, ∀ i j, HolderOnWith K 1 (fun x => V x i j) (S n) := by
      run_tac do
        let pn := (Lean.Name.num `_private.NativeCapLipschitzRestriction 0).str
          "native_cap_excess_holderOn_restriction"
        Lean.Elab.Tactic.evalTactic (← `(tactic|
          exact $(Lean.mkIdent pn) $(Lean.mkIdent `V) $(Lean.mkIdent `hL2)
            ($(Lean.mkIdent `S) $(Lean.mkIdent `n)) $(Lean.mkIdent `hS)
            1 (by norm_num) $(Lean.mkIdent `C) $(Lean.mkIdent `r0)
            $(Lean.mkIdent `hC) $(Lean.mkIdent `hr0) $(Lean.mkIdent `hr01)
            $(Lean.mkIdent `hexcess) $(Lean.mkIdent `hlim)
            $(Lean.mkIdent `B) $(Lean.mkIdent `hB) $(Lean.mkIdent `hbV)))
    obtain ⟨K, hK⟩ := hholder
    have hcoord : ∀ i, LipschitzOnWith K (fun x => u x i) (S n) :=
      fun i => holderOnWith_one.mp (hK i 0)
    refine ⟨2 * K, LipschitzOnWith.of_dist_le_mul ?_⟩
    intro x hx y hy
    have hc (i : Fin 2) : |u x i - u y i| ≤ (K : ℝ) * dist x y := by
      simpa only [Real.dist_eq] using (hcoord i).dist_le_mul x hx y hy
    have h0 := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg K.coe_nonneg dist_nonneg)).mpr (hc 0)
    have h1 := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg K.coe_nonneg dist_nonneg)).mpr (hc 1)
    have hnorm : ‖u x - u y‖ ^ 2 = (u x 0 - u y 0) ^ 2 + (u x 1 - u y 1) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
      simp only [PiLp.sub_apply]
    rw [sq_abs] at h0 h1
    rw [dist_eq_norm]
    change ‖u x - u y‖ ≤ (2 * (K : ℝ)) * dist x y
    have hsquare : ‖u x - u y‖ ^ 2 ≤ ((2 * (K : ℝ)) * dist x y) ^ 2 := by
      rw [hnorm]
      nlinarith [h0, h1]
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by positivity) dist_nonneg)).mp hsquare
  choose K hK using hLevel
  have hext : ∀ n, ∃ v : E2 → E2,
      LipschitzWith (lipschitzExtensionConstant E2 * K n) v ∧ EqOn u v (S n) :=
    fun n => (hK n).extend_finite_dimension
  choose v hv heq using hext
  refine ⟨v, fun n => lipschitzExtensionConstant E2 * K n, hv, ?_⟩
  have hcoverAE : ∀ᵐ x ∂volume, x ∉ disc 1 \ ⋃ n, {x | u x = v n x} := by
    filter_upwards [henergyAE, hmeanAE] with x hx hm
    intro hbad
    obtain ⟨C, r, hC, hr, henergy⟩ := hx
    obtain ⟨n, hn⟩ := exists_nat_gt (max C (1 / r))
    have hCn : C ≤ (n : ℝ) + 1 := by linarith [le_max_left C (1 / r)]
    have hrn : 1 / ((n : ℝ) + 1) ≤ r := by
      have hinv : 1 / r < (n : ℝ) := (le_max_right C (1 / r)).trans_lt hn
      have hmul := (div_lt_iff₀ hr).mp hinv
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr
      nlinarith
    have hxS : x ∈ S n := by
      refine ⟨hbad.1, ?_, hm hbad.1⟩
      intro t ht htn
      exact (henergy t ht (htn.trans hrn)).trans
        (mul_le_mul_of_nonneg_right hCn (sq_nonneg t))
    exact hbad.2 (mem_iUnion.mpr ⟨n, heq n hxS⟩)
  apply ae_iff.mp at hcoverAE
  simpa only [not_not, Set.setOf_mem_eq] using hcoverAE

#print axioms native_H1_countable_lipschitz_coincidences
