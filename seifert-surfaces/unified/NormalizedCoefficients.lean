import MatrixBounds

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology BigOperators ContDiff Matrix
namespace SeifertSurfaces.QuasilinearProviderBridge
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.QuasilinearLocalization

theorem R3_normalized_coefficients_on_three_ball
    (B : Set E2) (hB : IsOpen B) (C : LinearizedCoefficients)
    (v : E2 → ℝ) (κ M L : ℝ) (hκ : 0 < κ) (hM : 1 ≤ M) (hL : 0 ≤ L)
    (hbound : CoefficientBounds B C κ M) (hvbound : ∀ x ∈ B, |v x| ≤ L)
    (center : E3) (R : ℝ) (hR : 0 < R)
    (hball : Metric.ball center R ⊆ cylinder B)
    (hmeas : ∀ i j : Fin 3, AEMeasurable (fun y => liftMatrix C v (liftD κ M L) y i j)
      (volume.restrict (Metric.ball center R))) :
    ∃ A : DeGiorgi.NormalizedEllipticCoeff 3 (Metric.ball center R),
      A.1.Λ = liftLambda κ M L ∧
      (∀ y ∉ Metric.ball center R, A.1.a y = 1) ∧
      ∀ᵐ y ∂(volume.restrict (Metric.ball center R)), ∀ i j : Fin 3,
        A.1.a y i j = (min (κ / 2) 1)⁻¹ * liftMatrix C v (liftD κ M L) y i j := by
  classical
  let lam := min (κ / 2) 1
  have hlam : 0 < lam := lt_min (by positivity) (by norm_num)
  have hE : 0 < liftEntryBound κ M L := by
    unfold liftEntryBound liftD
    have hM0 : 0 < M := by linarith
    positivity
  let K := 3 * liftEntryBound κ M L / lam
  have hK : 0 < K := div_pos (by positivity) hlam
  let q : E3 → Matrix (Fin 3) (Fin 3) ℝ :=
    fun y i j => (hmeas i j).mk (fun y => liftMatrix C v (liftD κ M L) y i j) y
  let a : E3 → Matrix (Fin 3) (Fin 3) ℝ :=
    fun y => if y ∈ Metric.ball center R then lam⁻¹ • q y else 1
  have hrep : ∀ᵐ y ∂(volume.restrict (Metric.ball center R)),
      q y = liftMatrix C v (liftD κ M L) y := by
    have hr := ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => (hmeas i j).ae_eq_mk.symm))
    filter_upwards [hr] with y hy
    ext i j
    exact hy i j
  have haq : ∀ᵐ y ∂(volume.restrict (Metric.ball center R)),
      a y = lam⁻¹ • liftMatrix C v (liftD κ M L) y := by
    filter_upwards [hrep, ae_restrict_mem Metric.isOpen_ball.measurableSet] with y hy hym
    simp only [a, ite_eq_left hym, hy]
  have hcoer : ∀ᵐ y ∂(volume.restrict (Metric.ball center R)), ∀ ξ : E3,
      1 * ‖ξ‖ ^ 2 ≤ inner ℝ ξ (matrixAction (a y) ξ) := by
    filter_upwards [haq, ae_restrict_mem Metric.isOpen_ball.measurableSet] with y hy hym
    intro ξ
    have hl := R3_lift_coercive B C v κ M L hκ hM hL hbound hvbound y (hball hym) ξ
    have hmin : lam * ‖ξ‖ ^ 2 ≤ inner ℝ
        (matrixAction (liftMatrix C v (liftD κ M L) y) ξ) ξ := by
      rw [Helpers.norm_sq_planarPart]
      have hlamκ : lam ≤ κ / 2 := min_le_left _ _
      have hlam1 : lam ≤ 1 := min_le_right _ _
      nlinarith [sq_nonneg ‖planarPart ξ‖, sq_nonneg (ξ 2)]
    rw [hy, Helpers.matrixAction_smul, real_inner_smul_right, real_inner_comm]
    simpa [mul_assoc, ne_of_gt hlam] using mul_le_mul_of_nonneg_left hmin (inv_nonneg.mpr hlam.le)
  have hupper : ∀ᵐ y ∂(volume.restrict (Metric.ball center R)), ∀ ξ : E3,
      ‖matrixAction (a y) ξ‖ ≤ K * ‖ξ‖ := by
    filter_upwards [haq, ae_restrict_mem Metric.isOpen_ball.measurableSet] with y hy hym
    intro ξ
    have he := (R3_lift_entries_bounded B C v κ M L hκ hM hL hbound hvbound).2 y (hball hym)
    rw [hy, Helpers.matrixAction_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hlam)]
    have hu := Helpers.matrixAction_norm_le_of_entries _ _ hE.le he ξ
    have hu' := mul_le_mul_of_nonneg_left hu (inv_nonneg.mpr hlam.le)
    simpa only [K, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hu'
  let A : DeGiorgi.EllipticCoeff 3 (Metric.ball center R) := {
    a := a
    lam := 1
    Λ := liftLambda κ M L
    measurable_comp := by
      intro i j
      have hm : Measurable (fun y => lam⁻¹ * q y i j) :=
        measurable_const.mul (hmeas i j).measurable_mk
      have he : (fun y => a y i j) = (Metric.ball center R).piecewise
          (fun y => lam⁻¹ * q y i j) (fun _ => (1 : Matrix (Fin 3) (Fin 3) ℝ) i j) := by
        funext y
        by_cases hy : y ∈ Metric.ball center R
        · simp only [a, Set.piecewise, ite_eq_left hy, Matrix.smul_apply, smul_eq_mul]
        · simp only [a, Set.piecewise, ite_eq_right hy]
      rw [he]
      exact Measurable.piecewise Metric.isOpen_ball.measurableSet hm measurable_const
    hlam := by norm_num
    hΛ := by
      change 1 ≤ (max 1 K) ^ 2
      have hm := le_max_left (1 : ℝ) K
      nlinarith
    coercive := hcoer
    coercive_inv := by
      filter_upwards [hcoer, hupper] with y hc hu
      intro ξ
      have hi := R3_inverse_coercivity (a y) 1 K (by norm_num) hK hc hu ξ
      have hΛK : K ^ 2 ≤ liftLambda κ M L := by
        change K ^ 2 ≤ (max 1 K) ^ 2
        exact (sq_le_sq₀ hK.le (by positivity)).mpr (le_max_right _ _)
      have hΛp : 0 < liftLambda κ M L := by
        change 0 < (max 1 K) ^ 2
        exact sq_pos_of_pos (lt_of_lt_of_le (by norm_num) (le_max_left _ _))
      have hinv : (liftLambda κ M L)⁻¹ ≤ (K ^ 2)⁻¹ :=
        (inv_le_inv₀ hΛp (sq_pos_of_pos hK)).mpr hΛK
      simp only [one_div] at hi
      exact (mul_le_mul_of_nonneg_right hinv (sq_nonneg ‖ξ‖)).trans hi
  }
  refine ⟨⟨A, rfl⟩, rfl, ?_, ?_⟩
  · intro y hy
    exact ite_eq_right hy
  · filter_upwards [haq] with y hy
    intro i j
    exact congrFun (congrFun hy i) j

end SeifertSurfaces.QuasilinearProviderBridge
