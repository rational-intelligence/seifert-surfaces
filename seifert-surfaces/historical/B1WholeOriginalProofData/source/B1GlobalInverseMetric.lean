import B1ChartMetricProvider

noncomputable section
open Set Topology
open scoped NNReal ENNReal

namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency

/-- Extend the supplied inverse metric globally, preserving its values on the domain closure.
Hildebrandt--von der Mosel [9], proof of Theorem 4.1, first step and (4.11). -/
theorem global_inverse_metric_extension (R : ℝ) (A : E2 → Mat2)
    (G : InverseMetricData R A) (Ω : SmoothFlatJordanDomain R) :
    ∃ M : E2 → Mat2,
      (∀ x ∈ closure Ω.domain, M x = inverseMetric A x) ∧
      SymmetricOn M Set.univ ∧ UniformEllipticOn M Set.univ ∧
      (∀ i j, ∃ C : ℝ≥0, HolderWith C G.alpha (fun x => M x i j)) ∧
      ∃ L : ℝ, 0 < L ∧ ∀ x : E2, L ≤ ‖x‖ → M x = 1 := by
  classical
  have hR := G.radius_pos
  have hretract :
      ∃ P : E2 → E2, (∀ x, P x ∈ closedHalfDisc R) ∧
        (∀ x ∈ closedHalfDisc R, P x = x) ∧ LipschitzWith 1 P := by
    have hc : Convex ℝ (closedHalfDisc R) := by
      intro x hx y hy a b ha hb hab
      refine ⟨(convex_closedBall (0 : E2) R) hx.1 hy.1 ha hb hab, ?_⟩
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      exact add_nonneg (mul_nonneg ha hx.2) (mul_nonneg hb hy.2)
    have hs : IsClosed (closedHalfDisc R) :=
      Metric.isClosed_closedBall.inter
        (isClosed_le (f := fun _ : E2 => (0 : ℝ)) continuous_const
          (EuclideanSpace.proj (1 : Fin 2)).continuous)
    have hzero : (0 : E2) ∈ closedHalfDisc R := by
      refine ⟨Metric.mem_closedBall_self hR.le, ?_⟩
      change (0 : ℝ) ≤ 0
      exact le_rfl
    have hn : (closedHalfDisc R).Nonempty := ⟨0, hzero⟩
    choose P hP hp using exists_norm_eq_iInf_of_complete_convex hn hs.isComplete hc
    have hi (x y : E2) : inner ℝ (x - P x) (P y - P x) ≤ 0 :=
      (norm_eq_iInf_iff_real_inner_le_zero hc (hP x)).mp (hp x) (P y) (hP y)
    have hl : LipschitzWith 1 P := by
      apply LipschitzWith.mk_one
      intro x y
      rw [dist_eq_norm, dist_eq_norm]
      have hxy := hi x y
      have hyx := hi y x
      have he : inner ℝ (x - y) (P x - P y) =
          ‖P x - P y‖ ^ 2 - inner ℝ (x - P x) (P y - P x) -
            inner ℝ (y - P y) (P x - P y) := by
        rw [← real_inner_self_eq_norm_sq]
        simp only [inner_sub_left, inner_sub_right]
        ring
      have hCS := real_inner_le_norm (x - y) (P x - P y)
      by_cases hzero : ‖P x - P y‖ = 0
      · rw [hzero]; positivity
      · have hpos := lt_of_le_of_ne (norm_nonneg (P x - P y)) (Ne.symm hzero)
        nlinarith
    refine ⟨P,hP,?_,hl⟩
    intro x hx
    have h := (norm_eq_iInf_iff_real_inner_le_zero hc (hP x)).mp (hp x) x hx
    rw [real_inner_self_eq_norm_sq] at h
    have : ‖x - P x‖ = 0 := by nlinarith [norm_nonneg (x-P x)]
    exact (sub_eq_zero.mp (norm_eq_zero.mp this)).symm
  obtain ⟨P, hP, hPid, hPlip⟩ := hretract
  let θ : E2 → ℝ := fun x => max 0 (min 1 (R + 1 - ‖x‖))
  have hθ0 (x : E2) : 0 ≤ θ x := le_max_left _ _
  have hθ1 (x : E2) : θ x ≤ 1 := max_le (by norm_num) (min_le_left _ _)
  have hθeq (x : E2) (hx : x ∈ closedHalfDisc R) : θ x = 1 := by
    have hn : ‖x‖ ≤ R := mem_closedBall_zero_iff.mp hx.1
    dsimp only [θ]
    rw [min_eq_left (by linarith), max_eq_right (by norm_num)]
  have hθfar (x : E2) (hx : R + 1 ≤ ‖x‖) : θ x = 0 := by
    dsimp only [θ]
    rw [max_eq_left]
    exact (min_le_right _ _).trans (by linarith)
  have hθlip : LipschitzWith 1 θ := by
    have hnorm : LipschitzWith 1 (fun x : E2 => ‖x‖) := by
      simpa only [dist_zero_right] using (LipschitzWith.dist_left (0 : E2))
    have hg : LipschitzWith 1 (fun x : E2 => R+1-‖x‖) := by
      apply LipschitzWith.mk_one
      intro x y
      simp only [Real.dist_eq, sub_sub_sub_cancel_left]
      simpa only [Real.dist_eq, NNReal.coe_one, one_mul, dist_comm y x] using hnorm.dist_le_mul y x
    exact (hg.const_min 1).const_max 0
  let M : E2 → Mat2 := fun x => θ x • inverseMetric A (P x) + (1 - θ x) • 1
  have haction (B : Mat2) (t : ℝ) (p : E2) :
      matrixAction (t • B + (1-t) • 1) p = t • matrixAction B p + (1-t) • p := by
    ext i
    dsimp only [matrixAction]
    simp only [Fin.sum_univ_two, PiLp.add_apply, PiLp.smul_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    fin_cases i <;> simp <;> ring
  have hquad (x p : E2) :
      inner ℝ p (matrixAction (M x) p) =
        θ x * inner ℝ p (matrixAction (inverseMetric A (P x)) p) +
          (1 - θ x) * ‖p‖ ^ 2 := by
    rw [haction, inner_add_right, inner_smul_right, inner_smul_right,
      real_inner_self_eq_norm_sq]
  refine ⟨M, ?_, ?_, ?_, ?_, R+1, by linarith, ?_⟩
  · intro x hx
    have hx' := Ω.closure_inside hx
    dsimp only [M]
    rw [hθeq x hx', hPid x hx']
    simp only [one_smul, sub_self, zero_smul, add_zero]
  · intro x hx i j
    change θ x * inverseMetric A (P x) i j + (1 - θ x) * (1 : Mat2) i j =
      θ x * inverseMetric A (P x) j i + (1 - θ x) * (1 : Mat2) j i
    rw [G.symmetric (P x) (hP x) i j]
    congr 2
    rw [Matrix.one_apply, Matrix.one_apply]
    by_cases h : i = j
    · subst j; rfl
    · rw [if_neg h, if_neg (Ne.symm h)]
  · obtain ⟨ell, C, hell, hC, hEll⟩ := G.elliptic
    refine ⟨min ell 1, max C 1, lt_min hell (by norm_num),
      lt_of_lt_of_le hC (le_max_left _ _), ?_⟩
    intro x hx p
    rw [hquad]
    have hq := hEll (P x) (hP x) p
    have hsq := sq_nonneg ‖p‖
    have ht := hθ0 x
    have ht' : 0 ≤ 1 - θ x := sub_nonneg.mpr (hθ1 x)
    have hlow := mul_le_mul_of_nonneg_left hq.1 ht
    have hupp := mul_le_mul_of_nonneg_left hq.2 ht
    have hminell := mul_le_mul_of_nonneg_right (min_le_left ell 1) hsq
    have hminone := mul_le_mul_of_nonneg_right (min_le_right ell 1) hsq
    have hmaxC := mul_le_mul_of_nonneg_right (le_max_left C 1) hsq
    have hmaxone := mul_le_mul_of_nonneg_right (le_max_right C 1) hsq
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left hminell ht,
        mul_le_mul_of_nonneg_left hminone ht']
    · nlinarith [mul_le_mul_of_nonneg_left hmaxC ht,
        mul_le_mul_of_nonneg_left hmaxone ht']
  · intro i j
    obtain ⟨K, hK, hLip⟩ := G.lipschitz i j
    let δ : ℝ := (1 : Mat2) i j
    let f : E2 → ℝ := fun x => inverseMetric A (P x) i j - δ
    let B : ℝ := K * R + |inverseMetric A 0 i j - δ|
    have hB : 0 ≤ B := add_nonneg (mul_nonneg hK hR.le) (abs_nonneg _)
    have hzero : (0 : E2) ∈ closedHalfDisc R := by
      refine ⟨Metric.mem_closedBall_self hR.le, ?_⟩
      change (0 : ℝ) ≤ 0
      exact le_rfl
    have hfb (x : E2) : |f x| ≤ B := by
      have hb := hLip (P x) (hP x) 0 hzero
      have hPn : dist (P x) 0 ≤ R := (hP x).1
      have ht := abs_add_le (inverseMetric A (P x) i j - inverseMetric A 0 i j)
        (inverseMetric A 0 i j - δ)
      have he : inverseMetric A (P x) i j - δ =
          (inverseMetric A (P x) i j - inverseMetric A 0 i j) +
            (inverseMetric A 0 i j - δ) := by ring
      dsimp only [f, B]
      rw [he]
      have hbd : |inverseMetric A (P x) i j - inverseMetric A 0 i j| ≤ K*R := by
        simpa only [Real.dist_eq] using hb.trans (mul_le_mul_of_nonneg_left hPn hK)
      linarith
    have hfl (x y : E2) : |f x - f y| ≤ K * dist x y := by
      have hb := hLip (P x) (hP x) (P y) (hP y)
      have hp : dist (P x) (P y) ≤ dist x y := by
        simpa only [NNReal.coe_one, one_mul] using hPlip.dist_le_mul x y
      simpa only [f, sub_sub_sub_cancel_right, Real.dist_eq] using
        hb.trans (mul_le_mul_of_nonneg_left hp hK)
    have hentry (x : E2) : M x i j = δ + θ x * f x := by
      change θ x * inverseMetric A (P x) i j + (1-θ x) * δ = _
      dsimp only [f]
      ring
    have hml : LipschitzWith ⟨K+B, add_nonneg hK hB⟩ (fun x => M x i j) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [Real.dist_eq, hentry x, hentry y, add_sub_add_left_eq_sub]
      have he : θ x * f x - θ y * f y =
          θ x * (f x - f y) + (θ x - θ y) * f y := by ring
      rw [he]
      have ht : |θ x| ≤ 1 := by rw [abs_of_nonneg (hθ0 x)]; exact hθ1 x
      have htl : |θ x - θ y| ≤ dist x y := by
        simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using hθlip.dist_le_mul x y
      calc
        |θ x * (f x - f y) + (θ x - θ y) * f y|
            ≤ |θ x| * |f x - f y| + |θ x - θ y| * |f y| := by
              simpa only [abs_mul] using abs_add_le (θ x * (f x - f y)) ((θ x-θ y)*f y)
        _ ≤ K * dist x y + dist x y * B := by
          apply add_le_add
          · exact (mul_le_mul_of_nonneg_right ht (abs_nonneg _)).trans
              (by simpa only [one_mul] using hfl x y)
          · exact mul_le_mul htl (hfb y) (abs_nonneg _) (dist_nonneg)
        _ = (K+B) * dist x y := by ring
    let D : ℝ≥0 := ⟨|δ|+B, add_nonneg (abs_nonneg _) hB⟩
    have hmb (x : E2) : |M x i j| ≤ D := by
      rw [hentry x]
      change _ ≤ |δ|+B
      calc
        |δ + θ x*f x| ≤ |δ| + |θ x| * |f x| := by simpa only [abs_mul] using abs_add_le δ (θ x*f x)
        _ ≤ |δ| + B := by
          apply add_le_add le_rfl
          have ht : |θ x| ≤ 1 := by rw [abs_of_nonneg (hθ0 x)]; exact hθ1 x
          exact (mul_le_mul_of_nonneg_right ht (abs_nonneg _)).trans
            (by simpa only [one_mul] using hfb x)
    have h0 : HolderWith (2*D) 0 (fun x => M x i j) := by
      intro x y
      simp only [NNReal.coe_zero, ENNReal.rpow_zero, mul_one, edist_dist]
      rw [ENNReal.ofReal_le_coe]
      simp only [Real.dist_eq, NNReal.coe_mul, NNReal.coe_ofNat]
      have h := abs_sub (M x i j) (M y i j)
      linarith [hmb x, hmb y]
    have hh := hml.holderWith.interpolate h0
      (add_tsub_cancel_of_le G.alpha_lt_one.le)
    exact ⟨_, by simpa only [one_mul, zero_mul, add_zero] using hh⟩
  · intro x hx
    dsimp only [M]
    rw [hθfar x hx]
    simp only [zero_smul, sub_zero, one_smul, zero_add]


end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider
