import B1HalfDiscDirichletWeak_v468
noncomputable section
open Set Topology Function MeasureTheory
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1GraphCoefficients
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem quadratic_gradient_v468 (R M : ℝ) :
    planarGradient (fun x : E2 => 1 - M * (R ^ 2 - ‖x‖ ^ 2)) =
      fun x => (2 * M) • x := by
  funext x
  have hs : HasFDerivAt (fun y : E2 => 1 - M * (R ^ 2 - ‖y‖ ^ 2))
      ((2 * M) • innerSL ℝ x) x := by
    convert (hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) x).sub
      (((hasFDerivAt_const (𝕜 := ℝ) (R ^ 2) x).sub ((hasStrictFDerivAt_norm_sq x).hasFDerivAt)).const_mul M) using 1 <;>
      ext y <;> simp [innerSL_apply_apply] <;> ring
  unfold planarGradient
  rw [hs.fderiv]
  ext i
  fin_cases i <;>
    simp [Fin.sum_univ_two,coordinateVector,innerSL_apply_apply,
      EuclideanSpace.inner_single_right,EuclideanSpace.single]

private theorem quadratic_classical_v468 (R M : ℝ) (a : E2 → Mat2)
    (b : E2 → E2) (c : E2 → ℝ) (x : E2)
    (ha : ∀ i j, DifferentiableAt ℝ (fun y => a y i j) x) :
    classicalL a b c (fun y => 1 - M * (R ^ 2 - ‖y‖ ^ 2)) x =
      2 * M * (a x 0 0 + a x 1 1 +
        (∑ i : Fin 2, ∑ j : Fin 2,
          fderiv ℝ (fun y => a y i j) x (coordinateVector 2 i) * x j) + inner ℝ (b x) x) +
      c x * (1 - M * (R ^ 2 - ‖x‖ ^ 2)) := by
  rw [classicalL,quadratic_gradient_v468]
  have hflux (i : Fin 2) :
      fderiv ℝ (fun y => matrixAction (a y) ((2 * M) • y) i) x (coordinateVector 2 i) =
        2 * M * (∑ j : Fin 2,
          fderiv ℝ (fun y => a y i j) x (coordinateVector 2 i) * x j) + 2 * M * a x i i := by
    have heq : (fun y => matrixAction (a y) ((2 * M) • y) i) =
        fun y => ∑ j : Fin 2, a y i j * ((2 * M) * y j) := by
      funext y
      simp [matrixAction]
    rw [heq,fderiv_fun_sum]
    · simp only [ContinuousLinearMap.sum_apply]
      have he (j : Fin 2) :
          fderiv ℝ (fun y => a y i j * ((2 * M) * y j)) x (coordinateVector 2 i) =
            fderiv ℝ (fun y => a y i j) x (coordinateVector 2 i) * (2 * M * x j) +
              a x i j * (2 * M * (if i = j then 1 else 0)) := by
        have hp : DifferentiableAt ℝ (fun y : E2 => (2 * M) * y j) x :=
          (differentiableAt_const _).mul ((EuclideanSpace.proj (𝕜 := ℝ) j).differentiableAt)
        rw [fderiv_fun_mul (ha i j) hp]
        simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
        have hder : fderiv ℝ (fun y : E2 => (2 * M) * y j) x =
            (2 * M) • EuclideanSpace.proj (𝕜 := ℝ) j := by
          exact ((EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt.const_mul (2 * M)).fderiv
        rw [hder]
        fin_cases i <;> fin_cases j <;> simp [coordinateVector,EuclideanSpace.single] <;> ring
      simp_rw [he]
      fin_cases i <;> simp [Fin.sum_univ_two] <;> ring
    · intro j hj
      exact (ha i j).mul ((differentiableAt_const _).mul (EuclideanSpace.proj (𝕜 := ℝ) j).differentiableAt)
  simp_rw [hflux]
  rw [inner_smul_right]
  simp [Fin.sum_univ_two]
  ring

universe v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}

/-- An actual positive comparison barrier on a small original half-disc, with no sign assumption on c. -/
theorem actual_halfdisc_positive_barrier_v468 (D : B1OriginalData g J) (s : Circle)
    (W : CollarWindow D s) :
    ∃ R : ℝ, 0 < R ∧ R < W.R ∧ ∃ v : E2 → ℝ,
      ContDiff ℝ ∞ v ∧
      (∀ x ∈ closedHalfDisc R, (1/2 : ℝ) ≤ v x ∧ v x ≤ 1) ∧
      (∀ x ∈ halfDisc R, 1 ≤ classicalL W.a W.b W.c v x) := by
  obtain ⟨O,hO,hWO,hOU,hjets,hf,hdf,ha,hq,hlg,hlh,hb,hc⟩ :=
    actual_coefficient_open_tube D s W
  obtain ⟨hformula,hsym,ell,Ca,hell,hCa,hbounds⟩ := actual_slope_hessian_uniform_bounds D s W
  have hcompact : IsCompact (closedHalfDisc W.R) :=
    (isCompact_closedBall (0 : E2) W.R).inter_right
      (isClosed_le continuous_const (EuclideanSpace.proj (1 : Fin 2)).continuous)
  choose A hAb using (fun i j : Fin 2 =>
    hcompact.exists_bound_of_continuousOn
      (((ha i j).continuousOn_fderiv_of_isOpen hO (by simp)).clm_apply continuousOn_const |>.mono hWO :
        ContinuousOn (fun x => fderiv ℝ (fun y => W.a y i j) x (coordinateVector 2 i)) (closedHalfDisc W.R)))
  obtain ⟨B,hBb⟩ := hcompact.exists_bound_of_continuousOn (hb.continuousOn.mono hWO)
  obtain ⟨C,hCb⟩ := hcompact.exists_bound_of_continuousOn (hc.continuousOn.mono hWO)
  let A' := 1 + |A 0 0| + |A 0 1| + |A 1 0| + |A 1 1|
  let B' := max B 1
  let C' := max C 1
  let L := 4 * A' + B'
  have hA : 0 < A' := by dsimp [A']; positivity
  have hB : 0 < B' := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hC : 0 < C' := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hL : 0 < L := by dsimp [L]; positivity
  let M := (C' + 1) / ell
  have hM : 0 < M := div_pos (by positivity) hell
  let R := min (W.R / 2) (min 1 (min (ell / (2 * L)) (1 / (2 * M))))
  have hR : 0 < R := lt_min (half_pos W.R_pos) (lt_min zero_lt_one
    (lt_min (div_pos hell (by positivity)) (div_pos zero_lt_one (by positivity))))
  have hRW : R < W.R := lt_of_le_of_lt (min_le_left _ _) (by linarith [W.R_pos])
  have hR1 : R ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hRL : R ≤ ell / (2 * L) := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hRM : R ≤ 1 / (2 * M) := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  let v : E2 → ℝ := fun x => 1 - M * (R ^ 2 - ‖x‖ ^ 2)
  have hv : ContDiff ℝ ∞ v := by
    exact contDiff_const.sub (contDiff_const.mul (contDiff_const.sub (contDiff_norm_sq (𝕜 := ℝ) (n := ∞))))
  have hsub : closedHalfDisc R ⊆ closedHalfDisc W.R := fun x hx =>
    ⟨Metric.closedBall_subset_closedBall hRW.le hx.1,hx.2⟩
  have hvbound (x : E2) (hx : x ∈ closedHalfDisc R) : (1/2 : ℝ) ≤ v x ∧ v x ≤ 1 := by
    have hn : ‖x‖ ≤ R := by simpa only [closedDisc,Metric.mem_closedBall,dist_zero_right] using hx.1
    have hn2 : ‖x‖ ^ 2 ≤ R ^ 2 := (sq_le_sq₀ (norm_nonneg _) hR.le).mpr hn
    have hRsq : R ^ 2 ≤ R := by nlinarith
    have hRM' : R * (2 * M) ≤ 1 := (le_div_iff₀ (by positivity : 0 < 2 * M)).mp hRM
    dsimp [v]
    constructor <;> nlinarith [sq_nonneg ‖x‖,mul_nonneg hM.le (sub_nonneg.mpr hn2)]
  refine ⟨R,hR,hRW,v,hv,hvbound,?_⟩
  intro x hx
  have hxR : x ∈ closedHalfDisc R := ⟨Metric.ball_subset_closedBall hx.1,hx.2.le⟩
  have hxW := hsub hxR
  have hxO := hWO hxW
  have hdiff (i j : Fin 2) : DifferentiableAt ℝ (fun y => W.a y i j) x :=
    ((ha i j).contDiffAt (hO.mem_nhds hxO)).differentiableAt (by simp)
  have hentry (i j : Fin 2) : |fderiv ℝ (fun y => W.a y i j) x (coordinateVector 2 i)| ≤ A' := by
    have hh := hAb i j x hxW
    fin_cases i <;> fin_cases j <;>
      calc
        _ ≤ A _ _ := by simpa only [Real.norm_eq_abs] using hh
        _ ≤ |A _ _| := le_abs_self _
        _ ≤ A' := by dsimp [A']; linarith [abs_nonneg (A 0 0),abs_nonneg (A 0 1),abs_nonneg (A 1 0),abs_nonneg (A 1 1)]
  have hn : ‖x‖ ≤ R := by simpa only [closedDisc,Metric.mem_closedBall,dist_zero_right] using hxR.1
  have hbx : ‖W.b x‖ ≤ B' := (hBb x hxW).trans (le_max_left _ _)
  have hcx : |W.c x| ≤ C' := by simpa only [Real.norm_eq_abs] using (hCb x hxW).trans (le_max_left _ _)
  have htrace : 2 * ell ≤ W.a x 0 0 + W.a x 1 1 := by
    have h0 := (hbounds x hxW (coordinateVector 2 0)).1
    have h1 := (hbounds x hxW (coordinateVector 2 1)).1
    simp [coordinateVector,matrixAction,Fin.sum_univ_two,
      EuclideanSpace.inner_eq_star_dotProduct,dotProduct,EuclideanSpace.single,
      EuclideanSpace.real_norm_sq_eq] at h0 h1
    linarith
  have hterm (i j : Fin 2) :
      -(A' * R) ≤ fderiv ℝ (fun y => W.a y i j) x (coordinateVector 2 i) * x j := by
    have hncoord : |x j| ≤ R := (PiLp.norm_apply_le x j).trans hn
    have hh : |fderiv ℝ (fun y => W.a y i j) x (coordinateVector 2 i) * x j| ≤ A' * R := by
      rw [abs_mul]
      exact mul_le_mul (hentry i j) hncoord (abs_nonneg _) hA.le
    exact (neg_le_neg hh).trans (neg_abs_le _)
  have hbt : -(B' * R) ≤ inner ℝ (W.b x) x := by
    have hh := (abs_real_inner_le_norm (W.b x) x).trans
      (mul_le_mul hbx hn (norm_nonneg _) hB.le)
    exact (neg_le_neg hh).trans (neg_abs_le _)
  have hbracket : ell ≤ W.a x 0 0 + W.a x 1 1 +
      (∑ i : Fin 2, ∑ j : Fin 2,
        fderiv ℝ (fun y => W.a y i j) x (coordinateVector 2 i) * x j) + inner ℝ (W.b x) x := by
    have hLR : R * (2 * L) ≤ ell := (le_div_iff₀ (by positivity : 0 < 2 * L)).mp hRL
    simp only [Fin.sum_univ_two]
    dsimp [L] at hLR
    linarith [hterm 0 0,hterm 0 1,hterm 1 0,hterm 1 1]
  have hcv : -(C') ≤ W.c x * v x := by
    have hvx := hvbound x hxR
    have habsv : |v x| ≤ 1 := by rw [abs_of_nonneg (by linarith : 0 ≤ v x)]; exact hvx.2
    have hh : |W.c x * v x| ≤ C' := by
      rw [abs_mul]
      exact (mul_le_mul hcx habsv (abs_nonneg _) hC.le).trans_eq (mul_one _)
    exact (neg_le_neg hh).trans (neg_abs_le _)
  have hMe : M * ell = C' + 1 := div_mul_cancel₀ _ hell.ne'
  rw [show classicalL W.a W.b W.c v x = _ from quadratic_classical_v468 R M W.a W.b W.c x hdiff]
  have hm := mul_le_mul_of_nonneg_left hbracket (show 0 ≤ 2 * M by positivity)
  change -(C') ≤ W.c x * (1 - M * (R ^ 2 - ‖x‖ ^ 2)) at hcv
  nlinarith

end SeifertSurfaces.OriginalEndpoints.B1Tangency
