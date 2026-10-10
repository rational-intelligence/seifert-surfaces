import InitialAllCenterContraction_v463
import B1L1DirectWeakLower

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates L1Independent

local macro "paid_all_center_contraction" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialAllCenterContraction_v463 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.original_minimizer_all_center_cap_contraction_v463)⟩

private theorem cap_contraction_iteration_v463
    {R : ℝ} {Ω : SmoothFlatJordanDomain R} {M : E2 → Mat2}
    {f : E2 → E2} {d : Fin 2 → E2 → E2}
    (minimum : SimultaneousMetricMinimum Ω M f d)
    (rho q : ℝ) (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hq : 0 < q) (hq1 : q < 1)
    (step : ∀ x∈closedDisc 1,∀ r:ℝ,0 < r → r ≤ rho →
      (∫ z in planarCap x (r/32),euclideanJetDensity d z) ≤
        q*∫ z in planarCap x r,euclideanJetDensity d z) :
    ∃ beta:ℝ≥0,0 < beta ∧ beta ≤ 1 ∧ DirectWeak.CapEnergyGrowth d beta := by
  classical
  let E : E2 → ℝ → ℝ := fun x r => ∫ z in planarCap x r, euclideanJetDensity d z
  let E0 : ℝ := ∫ z in disc 1, euclideanJetDensity d z
  have hi : IntegrableOn (euclideanJetDensity d) (disc 1) := by
    apply integrable_finsetSum
    intro i _
    exact (minimum.admissible.1 i).2.2.norm.integrable_sq
  have hn (x : E2) (r : ℝ) : 0 ≤ E x r :=
    integral_nonneg (fun z => Finset.sum_nonneg (fun i _ => sq_nonneg _))
  have hE0 : 0 ≤ E0 :=
    integral_nonneg (fun z => Finset.sum_nonneg (fun i _ => sq_nonneg _))
  have hm (x : E2) (r s : ℝ) (hrs : r ≤ s) : E x r ≤ E x s := by
    apply setIntegral_mono_set (hi.mono_set inter_subset_left)
      (Filter.Eventually.of_forall fun z => Finset.sum_nonneg (fun i _ => sq_nonneg _))
    exact Filter.Eventually.of_forall fun z hz =>
      ⟨hz.1, Metric.ball_subset_ball hrs hz.2⟩
  have htop (x : E2) (r : ℝ) : E x r ≤ E0 :=
    setIntegral_mono_set hi
      (Filter.Eventually.of_forall fun z => Finset.sum_nonneg (fun i _ => sq_nonneg _))
      (Filter.Eventually.of_forall fun z hz => hz.1)
  have hc : Continuous (fun b : ℝ => Real.rpow (1 / 32) (2 * b)) :=
    (Real.continuous_const_rpow (by norm_num : (1 / 32 : ℝ) ≠ 0)).comp
      (continuous_const.mul continuous_id)
  have hqzero : q < Real.rpow (1 / 32) (2 * (0 : ℝ)) := by simpa using hq1
  obtain ⟨a, ha, harpow⟩ := Metric.eventually_nhds_iff.mp
    ((hc.tendsto 0).eventually (eventually_gt_nhds hqzero))
  let b : ℝ := min 1 (a / 2)
  have hb : 0 < b := lt_min (by norm_num) (by positivity)
  have hb1 : b ≤ 1 := min_le_left _ _
  have hba : dist b 0 < a := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hb]
    exact (min_le_right _ _).trans_lt (by linarith)
  have hqr : q ≤ Real.rpow (1 / 32) (2 * b) := (harpow hba).le
  let beta : ℝ≥0 := ⟨b, hb.le⟩
  refine ⟨beta, hb, hb1, ?_⟩
  refine ⟨E0 * Real.rpow (32 / rho) (2 * b), rho,
    mul_nonneg hE0 (Real.rpow_nonneg (by positivity) _), hrho, hrho1, ?_⟩
  intro x hx r hr hrmax
  have hdyadic : ∀ n : ℕ, E x (rho * (1 / 32 : ℝ) ^ n) ≤ q ^ n * E x rho := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hspos : 0 < rho * (1 / 32 : ℝ) ^ n := by positivity
      have hsmax : rho * (1 / 32 : ℝ) ^ n ≤ rho := by
        exact mul_le_of_le_one_right hrho.le (pow_le_one₀ (by norm_num) (by norm_num))
      have hs := step x hx _ hspos hsmax
      have heq : rho * (1 / 32 : ℝ) ^ (n + 1) = (rho * (1 / 32 : ℝ) ^ n) / 32 := by
        rw [pow_succ]; ring
      rw [heq]
      calc
        _ ≤ q * E x (rho * (1 / 32 : ℝ) ^ n) := hs
        _ ≤ q * (q ^ n * E x rho) := mul_le_mul_of_nonneg_left ih hq.le
        _ = q ^ (n + 1) * E x rho := by rw [pow_succ]; ring
  obtain ⟨n, hlow, hupp⟩ := exists_nat_pow_near_of_lt_one
    (div_pos hr hrho) ((div_le_one hrho).mpr hrmax)
    (by norm_num : (0 : ℝ) < 1 / 32) (by norm_num : (1 / 32 : ℝ) < 1)
  have hrdyadic : r ≤ rho * (1 / 32 : ℝ) ^ n := by
    exact (div_le_iff₀ hrho).mp hupp |>.trans_eq (mul_comm _ _)
  have hhalfnext : (1 / 32 : ℝ) ^ n / 32 < r / rho := by
    rw [show (1 / 32 : ℝ) ^ n / 32 = (1 / 32 : ℝ) ^ (n + 1) by
      rw [pow_succ]; ring]
    exact hlow
  have hnext : (1 / 32 : ℝ) ^ n ≤ 32 * r / rho := by
    calc
      _ ≤ 32 * (r / rho) := by linarith only [hhalfnext]
      _ = 32 * r / rho := by ring
  have hpow : q ^ n ≤ Real.rpow ((1 / 32 : ℝ) ^ n) (2 * b) := by
    calc
      _ ≤ (Real.rpow (1 / 32) (2 * b)) ^ n := pow_le_pow_left₀ hq.le hqr n
      _ = Real.rpow ((1 / 32 : ℝ) ^ n) (2 * b) := by
        calc
          _ = Real.rpow (1 / 32) (2 * b * (n : ℝ)) :=
            (Real.rpow_mul_natCast (by norm_num) _ _).symm
          _ = Real.rpow (1 / 32) ((n : ℝ) * (2 * b)) := by rw [mul_comm]
          _ = Real.rpow ((1 / 32 : ℝ) ^ n) (2 * b) :=
            Real.rpow_natCast_mul (by norm_num) _ _
  have hscale : Real.rpow ((1 / 32 : ℝ) ^ n) (2 * b) ≤
      Real.rpow (32 * r / rho) (2 * b) :=
    Real.rpow_le_rpow (by positivity) hnext (by positivity)
  calc
    E x r ≤ E x (rho * (1 / 32 : ℝ) ^ n) := hm x _ _ hrdyadic
    _ ≤ q ^ n * E x rho := hdyadic n
    _ ≤ q ^ n * E0 := mul_le_mul_of_nonneg_left (htop x rho) (by positivity)
    _ ≤ Real.rpow ((1 / 32 : ℝ) ^ n) (2 * b) * E0 :=
      mul_le_mul_of_nonneg_right hpow hE0
    _ ≤ Real.rpow (32 * r / rho) (2 * b) * E0 :=
      mul_le_mul_of_nonneg_right hscale hE0
    _ = E0 * Real.rpow (32 / rho) (2 * b) * Real.rpow r (2 * (beta : ℝ)) := by
      have heq : 32 * r / rho = (32 / rho) * r := by ring
      rw [heq]
      change Real.rpow ((32 / rho) * r) (2 * b) * E0 =
        E0 * Real.rpow (32 / rho) (2 * b) * Real.rpow r (2 * b)
      have hmul : Real.rpow ((32 / rho) * r) (2 * b) =
          Real.rpow (32 / rho) (2 * b) * Real.rpow r (2 * b) :=
        Real.mul_rpow (x := 32 / rho) (y := r) (z := 2 * b)
          (by positivity) hr.le
      rw [hmul]
      ring


private theorem original_initial_cap_energy_decay_v463
    (R : ℝ) (A : E2 → Mat2) (G : InverseMetricData R A)
    (Ω : SmoothFlatJordanDomain R) (M : E2 → Mat2)
    (agreement : ∀ x∈closure Ω.domain,M x=inverseMetric A x)
    (symmetric : SymmetricOn M univ) (elliptic : UniformEllipticOn M univ)
    (holder : ∀ i j,∃ C:ℝ≥0,HolderWith C G.alpha (fun x=>M x i j))
    (identity_at_infinity : ∃ L:ℝ,0 < L ∧ ∀ x:E2,L ≤ ‖x‖ → M x=1)
    (f : E2 → E2) (d : Fin 2 → E2 → E2)
    (minimum : SimultaneousMetricMinimum Ω M f d) :
    ∃ beta:ℝ≥0,0 < beta ∧ beta ≤ 1 ∧ DirectWeak.CapEnergyGrowth d beta := by
  obtain ⟨rho,q,hrho,hrhohalf,hq,hq1,hstep⟩ :=
    paid_all_center_contraction R A G Ω M agreement symmetric elliptic
      holder identity_at_infinity f d minimum
  exact cap_contraction_iteration_v463 minimum rho q hrho (by linarith) hq hq1 hstep

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
