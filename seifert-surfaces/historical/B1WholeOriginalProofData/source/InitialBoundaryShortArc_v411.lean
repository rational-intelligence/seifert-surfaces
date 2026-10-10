import VM02aDirectMethod
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
open Set Topology Function
open scoped ContDiff NNReal

namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates

private theorem periodic_uniform_continuity_v411
    {F : Type*} [PseudoMetricSpace F] (g : ℝ → F) (T : ℝ)
    (hT : 0 < T) (hg : Continuous g) (hp : Periodic g T) :
    UniformContinuous g := by
  apply Metric.uniformContinuous_iff.mpr
  intro ε hε
  obtain ⟨a, ha, hlocal⟩ := Metric.uniformContinuousOn_iff.mp
    ((isCompact_Icc : IsCompact (Icc (-T) (2 * T))).uniformContinuousOn_of_continuous
      hg.continuousOn) ε hε
  refine ⟨min a (T / 2), lt_min ha (by positivity), ?_⟩
  intro s t hst
  let n : ℤ := toIcoDiv hT 0 s
  let c : ℝ := (n : ℝ) * T
  have hs : s - c ∈ Ico 0 T := by
    simpa only [zero_add, zsmul_eq_mul] using sub_toIcoDiv_zsmul_mem_Ico hT 0 s
  have heq : dist (s - c) (t - c) = dist s t := by
    simp only [Real.dist_eq, sub_sub_sub_cancel_right]
  have ht : t - c ∈ Icc (-T) (2 * T) := by
    have hdist : |s - t| < T / 2 := by
      have hdist' : |s - t| < min a (T / 2) := by
        simpa only [Real.dist_eq] using hst
      exact hdist'.trans_le (min_le_right _ _)
    obtain ⟨hleft, hright⟩ := abs_lt.mp hdist
    constructor <;> linarith [hs.1, hs.2]
  have hsmall := hlocal (s - c) ⟨by linarith [hs.1], by linarith [hs.2]⟩
    (t - c) ht (by rw [heq]; exact hst.trans_le (min_le_left _ _))
  rw [(hp.int_mul n).sub_eq s, (hp.int_mul n).sub_eq t] at hsmall
  exact hsmall

/-! The original lift is uniformly continuous without a normalization,
pointwise representative, or regularity hypothesis on f. -/
private theorem original_lift_uniform_continuity_v411
    {R : ℝ} (Ω : SmoothFlatJordanDomain R) (theta : ℝ → ℝ) (sigma : ℝ)
    (lift : WeakMonotoneBoundaryLift Ω theta sigma) :
    UniformContinuous theta := by
  let error : ℝ → ℝ := fun t => theta t - sigma * t
  have hc : Continuous error := lift.2.1.sub (continuous_const.mul continuous_id)
  have hp : Periodic error (2 * Real.pi) := by
    intro t
    dsimp only [error]
    rw [lift.2.2.2]
    ring
  have hu := periodic_uniform_continuity_v411 error (2 * Real.pi)
    (by positivity) hc hp
  have hs : UniformContinuous (fun t : ℝ => sigma * t) := by
    exact uniformContinuous_id.const_mul' sigma
  have heq : theta = error + (fun t => sigma * t) := by
    funext t
    simp only [Pi.add_apply, error, sub_add_cancel]
  rw [heq]
  exact hu.add hs

private theorem original_target_arc_uniform_smallness_v411
    {R : ℝ} (Ω : SmoothFlatJordanDomain R) (theta : ℝ → ℝ) (sigma : ℝ)
    (lift : WeakMonotoneBoundaryLift Ω theta sigma) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ s t : ℝ, dist s t ≤ δ →
        dist (theta s) (theta t) < ε := by
  intro ε hε
  obtain ⟨a, ha, hmod⟩ := Metric.uniformContinuous_iff.mp
    (original_lift_uniform_continuity_v411 Ω theta sigma lift) ε hε
  refine ⟨a / 2, by positivity, ?_⟩
  intro s t hst
  exact hmod (hst.trans_lt (by linarith))

/-! Fixed quantitative target-arc control for the actual smooth regular
Jordan curve. The constants are chosen before every real source parameter. -/
private theorem original_boundary_chord_bounds_v411
    {R : ℝ} (Ω : SmoothFlatJordanDomain R) :
    ∃ m L δ : ℝ, 0 < m ∧ 0 < L ∧ 0 < δ ∧
      (∀ s t : ℝ, dist (Ω.boundary.gamma s) (Ω.boundary.gamma t) ≤ L * dist s t) ∧
      (∀ s t : ℝ, dist s t ≤ δ →
        m * dist s t ≤ dist (Ω.boundary.gamma s) (Ω.boundary.gamma t)) := by
  let γ : ℝ → E2 := Ω.boundary.gamma
  have hγ : ContDiff ℝ ∞ γ := Ω.boundary.smooth
  have hd : Continuous (deriv γ) := hγ.continuous_deriv (by simp)
  have hp : Periodic (deriv γ) (2 * Real.pi) := by
    have heq : (fun t => γ (t + 2 * Real.pi)) = γ := funext Ω.boundary.periodic
    intro t
    rw [← deriv_comp_add_const, heq]
  have hc := hp.compact_of_continuous (by positivity : (2 * Real.pi : ℝ) ≠ 0) hd
  obtain ⟨m0, hm0, hmin⟩ := hc.exists_forall_le'
    (f := fun v : E2 => ‖v‖) continuous_norm.continuousOn
    (a := (0 : ℝ)) (by
      rintro v ⟨t, rfl⟩
      exact norm_pos_iff.mpr (Ω.boundary.regular t))
  obtain ⟨L0, hmax⟩ := hc.exists_bound_of_continuousOn continuous_id.continuousOn
  let L : ℝ := max L0 1
  have hL : 0 < L := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hbound (t : ℝ) : ‖deriv γ t‖ ≤ L :=
    (hmax _ ⟨t, rfl⟩).trans (le_max_left _ _)
  obtain ⟨a, ha, hmod⟩ := Metric.uniformContinuous_iff.mp
    (periodic_uniform_continuity_v411 (deriv γ) (2 * Real.pi)
      (by positivity) hd hp) (m0 / 2) (by positivity)
  refine ⟨m0 / 2, L, a / 2, by positivity, hL, by positivity, ?_, ?_⟩
  · intro s t
    have hb := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
      (f := γ) (fun x _ => hγ.differentiable (by simp) x)
      (fun x _ => hbound x) (mem_univ s) (mem_univ t)
    simpa only [dist_eq_norm, norm_sub_rev] using hb
  · intro s t hst
    have hdifference : ∀ u ∈ uIcc s t, ‖deriv γ u - deriv γ s‖ ≤ m0 / 2 := by
      intro u hu
      have hus : dist u s ≤ dist s t := by
        rw [Real.dist_eq, Real.dist_eq]
        rcases le_total s t with h | h
        · rw [uIcc_of_le h] at hu
          rw [abs_of_nonneg (by linarith [hu.1]), abs_of_nonpos (by linarith)]
          linarith [hu.2]
        · rw [uIcc_of_ge h] at hu
          rw [abs_of_nonpos (by linarith [hu.2]), abs_of_nonneg (by linarith)]
          linarith [hu.1]
      have hh := hmod (hus.trans_lt (hst.trans_lt (by linarith)))
      have hh' : ‖deriv γ u - deriv γ s‖ < m0 / 2 := by
        simpa only [dist_eq_norm] using hh
      exact hh'.le
    have hm := (convex_uIcc s t).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun u => γ u - u • deriv γ s)
      (f' := fun u => deriv γ u - deriv γ s)
      (fun u _ => by
        convert ((hγ.differentiable (by simp) u).hasDerivAt.sub
          ((hasDerivAt_id u).smul_const (deriv γ s))).hasDerivWithinAt using 1
        · funext z; simp
        · simp)
      hdifference left_mem_uIcc right_mem_uIcc
    have heq : (γ t - t • deriv γ s) - (γ s - s • deriv γ s) =
        (γ t - γ s) - (t - s) • deriv γ s := by module
    rw [heq] at hm
    have hnorm := norm_sub_norm_le ((t - s) • deriv γ s) (γ t - γ s)
    have hminimum := hmin (deriv γ s) ⟨s, rfl⟩
    have hmult := mul_le_mul_of_nonneg_left hminimum (norm_nonneg (t - s))
    rw [norm_smul] at hnorm
    rw [norm_sub_rev ((t - s) • deriv γ s) (γ t - γ s)] at hnorm
    have heqdist : dist s t = ‖t - s‖ := by rw [dist_eq_norm, norm_sub_rev]
    change m0 / 2 * dist s t ≤ dist (γ s) (γ t)
    rw [heqdist, dist_eq_norm, norm_sub_rev (γ s) (γ t)]
    nlinarith [hm, hnorm, hmult]

/- Every part of a sufficiently short ORIGINAL lifted boundary arc is
controlled by its endpoint chord, with one constant for all source parameters. -/
private theorem original_lift_arc_chord_control_v411
    {R : ℝ} (Ω : SmoothFlatJordanDomain R) (theta : ℝ → ℝ) (sigma : ℝ)
    (lift : WeakMonotoneBoundaryLift Ω theta sigma) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
      ∀ s t : ℝ, s ≤ t → t - s ≤ δ →
        ∀ u ∈ Icc s t, ∀ v ∈ Icc s t,
          dist (liftedBoundaryValue Ω theta u) (liftedBoundaryValue Ω theta v) ≤
            C * dist (liftedBoundaryValue Ω theta s) (liftedBoundaryValue Ω theta t) := by
  obtain ⟨m, L, a, hm, hL, ha, hupper, hlower⟩ := original_boundary_chord_bounds_v411 Ω
  obtain ⟨δ, hδ, hshort⟩ := original_target_arc_uniform_smallness_v411 Ω theta sigma lift a ha
  refine ⟨L / m, δ, div_pos hL hm, hδ, ?_⟩
  intro s t hst hlen u hu v hv
  have hendpoint : dist (theta s) (theta t) ≤ a :=
    (hshort s t (by rwa [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hst), neg_sub])).le
  have hinside : dist (theta u) (theta v) ≤ dist (theta s) (theta t) := by
    have hsu := lift.2.2.1 hu.1
    have hut := lift.2.2.1 hu.2
    have hsv := lift.2.2.1 hv.1
    have hvt := lift.2.2.1 hv.2
    have hst' := lift.2.2.1 hst
    rw [Real.dist_eq, Real.dist_eq]
    rcases lift.1 with hσ | hσ
    · simp only [hσ, one_mul] at hsu hut hsv hvt hst'
      rw [abs_of_nonpos (sub_nonpos.mpr hst'), neg_sub, abs_le]
      constructor <;> linarith
    · simp only [hσ, neg_one_mul] at hsu hut hsv hvt hst'
      rw [abs_of_nonneg (show 0 ≤ theta s - theta t by linarith), abs_le]
      constructor <;> linarith
  have he := hlower (theta s) (theta t) hendpoint
  change dist (Ω.boundary.gamma (theta u)) (Ω.boundary.gamma (theta v)) ≤
    L / m * dist (Ω.boundary.gamma (theta s)) (Ω.boundary.gamma (theta t))
  calc
    _ ≤ L * dist (theta u) (theta v) := hupper _ _
    _ ≤ L * dist (theta s) (theta t) := mul_le_mul_of_nonneg_left hinside hL.le
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left he (div_nonneg hL.le hm.le)
      have heq : (L / m) * (m * dist (theta s) (theta t)) =
          L * dist (theta s) (theta t) := by field_simp
      rwa [heq] at hh

private theorem original_boundary_cap_arc_chord_control_v411
    {R : ℝ} (Ω : SmoothFlatJordanDomain R) (theta : ℝ → ℝ) (sigma : ℝ)
    (lift : WeakMonotoneBoundaryLift Ω theta sigma) :
    ∃ C rho : ℝ, 0 < C ∧ 0 < rho ∧ rho ≤ 1 / 2 ∧
      ∀ s r : ℝ, 0 < r → r ≤ rho →
        let a : ℝ := 2 * Real.arcsin (r / 2)
        ∀ u ∈ Icc (s - a) (s + a), ∀ v ∈ Icc (s - a) (s + a),
          dist (liftedBoundaryValue Ω theta u) (liftedBoundaryValue Ω theta v) ≤
            C * dist (liftedBoundaryValue Ω theta (s - a))
              (liftedBoundaryValue Ω theta (s + a)) := by
  obtain ⟨C, δ, hC, hδ, hcontrol⟩ := original_lift_arc_chord_control_v411 Ω theta sigma lift
  have hc : Continuous (fun r : ℝ => 4 * Real.arcsin (r / 2)) :=
    continuous_const.mul (Real.continuous_arcsin.comp (continuous_id.div_const 2))
  have hz : 4 * Real.arcsin ((0 : ℝ) / 2) < δ := by simpa using hδ
  obtain ⟨b, hb, hsmall⟩ := Metric.eventually_nhds_iff.mp
    ((hc.tendsto 0).eventually (eventually_lt_nhds hz))
  refine ⟨C, min (1 / 2) (b / 2), hC,
    lt_min (by norm_num) (by positivity), min_le_left _ _, ?_⟩
  intro s r hr hrr
  dsimp only
  have harc : 0 ≤ 2 * Real.arcsin (r / 2) := by
    exact mul_nonneg (by norm_num) (Real.arcsin_nonneg.mpr (by positivity))
  apply hcontrol (s - 2 * Real.arcsin (r / 2)) (s + 2 * Real.arcsin (r / 2))
    (by linarith)
  have hd : dist r 0 < b := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hr]
    exact (hrr.trans (min_le_right _ _)).trans_lt (by linarith)
  have hh := hsmall hd
  linarith

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
