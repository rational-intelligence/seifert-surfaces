import B1HalfDiscNativeClassical_v468
noncomputable section
open Set Topology Function MeasureTheory
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1GraphCoefficients
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Literal gradient of the quadratic barrier vanishing on the flat edge. -/
theorem flat_barrier_gradient_v468 (R M : ℝ) :
    planarGradient (fun x : E2 => 1 + M * (2 * R * x 1 - (x 1)^2)) =
      fun x => (M * (2 * R - 2 * x 1)) • coordinateVector 2 1 := by
  funext x
  have hd : HasFDerivAt (fun y : E2 => 1 + M * (2 * R * y 1 - (y 1)^2))
      ((M * (2 * R - 2 * x 1)) • EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)) x := by
    convert (hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) x).add
      ((((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).hasFDerivAt.const_mul (2 * R)).sub
        (((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).hasFDerivAt).pow 2)).const_mul M) using 1 <;>
      ext y <;> simp <;> ring
  unfold planarGradient
  rw [hd.fderiv]
  ext i
  fin_cases i <;> simp [coordinateVector,EuclideanSpace.single,Fin.sum_univ_two]

/-- The divergence expression keeps the actual mixed coefficient and drift. -/
theorem flat_barrier_classical_v468 (R M : ℝ) (a : E2 → Mat2)
    (b : E2 → E2) (c : E2 → ℝ) (x : E2)
    (ha : ∀ i j, DifferentiableAt ℝ (fun y => a y i j) x) :
    classicalL a b c (fun y => 1 + M * (2 * R * y 1 - (y 1)^2)) x =
      M * (-2 * a x 1 1 + (2 * R - 2 * x 1) *
        ((∑ i : Fin 2, fderiv ℝ (fun y => a y i 1) x (coordinateVector 2 i)) + b x 1)) +
      c x * (1 + M * (2 * R * x 1 - (x 1)^2)) := by
  rw [classicalL,flat_barrier_gradient_v468]
  have hflux (i : Fin 2) : (fun y => matrixAction (a y)
      ((M * (2 * R - 2 * y 1)) • coordinateVector 2 1) i) =
      fun y => a y i 1 * (M * (2 * R - 2 * y 1)) := by
    funext y
    simp [matrixAction,coordinateVector,EuclideanSpace.single,Fin.sum_univ_two]
  have hdiff : DifferentiableAt ℝ (fun y : E2 => M * (2 * R - 2 * y 1)) x := by
    fun_prop
  have hd : fderiv ℝ (fun y : E2 => M * (2 * R - 2 * y 1)) x =
      (-2 * M) • EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2) := by
    convert (((hasFDerivAt_const (𝕜 := ℝ) (2 * R) x).sub
      ((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).hasFDerivAt.const_mul 2)).const_mul M).fderiv using 1 <;>
      ext y <;> simp <;> ring
  simp_rw [hflux,fderiv_fun_mul (ha _ 1) hdiff,hd]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  simp [Fin.sum_univ_two,coordinateVector,EuclideanSpace.single,inner_smul_right,
    EuclideanSpace.inner_single_right]
  ring

universe v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}

/-- A quadratic flat-edge supersolution for the literal original operator.
Its value tends to the datum 1 as the normal coordinate tends to zero. -/
theorem actual_flat_dirichlet_supersolution_v468
    (D : B1OriginalData g J) (s : Circle) (W : CollarWindow D s) :
    ∃ R M : ℝ, 0 < R ∧ R < W.R ∧ 0 < M ∧
      let v : E2 → ℝ := fun x => 1 + M * (2 * R * x 1 - (x 1)^2)
      ContDiff ℝ ∞ v ∧
      (∀ x ∈ closedHalfDisc R, 1 ≤ v x ∧ v x ≤ 3/2) ∧
      (∀ x ∈ halfDisc R, classicalL W.a W.b W.c v x ≤ -2 * |W.c x| - 1) := by
  obtain ⟨O,hO,hWO,hOU,hjets,hf,hdf,ha,hq,hlg,hlh,hb,hc⟩ :=
    actual_coefficient_open_tube D s W
  obtain ⟨hformula,hsym,ell,Ca,hell,hCa,hbounds⟩ := actual_slope_hessian_uniform_bounds D s W
  have hcompact : IsCompact (closedHalfDisc W.R) :=
    (isCompact_closedBall (0 : E2) W.R).inter_right
      (isClosed_le continuous_const (EuclideanSpace.proj (1 : Fin 2)).continuous)
  choose A hAb using (fun i : Fin 2 => hcompact.exists_bound_of_continuousOn
      (((ha i 1).continuousOn_fderiv_of_isOpen hO (by simp)).clm_apply continuousOn_const
        |>.mono hWO : ContinuousOn
        (fun x => fderiv ℝ (fun y => W.a y i 1) x (coordinateVector 2 i)) (closedHalfDisc W.R)))
  obtain ⟨B,hBb⟩ := hcompact.exists_bound_of_continuousOn (hb.continuousOn.mono hWO)
  obtain ⟨C,hCb⟩ := hcompact.exists_bound_of_continuousOn (hc.continuousOn.mono hWO)
  let A' := 1 + |A 0| + |A 1|
  let B' := max B 1
  let C' := max C 1
  let L := 2 * A' + B'
  have hA : 0 < A' := by dsimp [A']; positivity
  have hB : 0 < B' := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hC : 0 < C' := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hL : 0 < L := by dsimp [L]; positivity
  let M := (4 * C' + 1) / ell
  have hM : 0 < M := div_pos (by positivity) hell
  let R := min (W.R / 2) (min 1 (min (ell / (4 * L)) (1 / (2 * M))))
  have hR : 0 < R := lt_min (half_pos W.R_pos) (lt_min zero_lt_one
    (lt_min (div_pos hell (by positivity)) (div_pos zero_lt_one (by positivity))))
  have hRW : R < W.R := lt_of_le_of_lt (min_le_left _ _) (by linarith [W.R_pos])
  have hR1 : R ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hRL : R ≤ ell / (4 * L) := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hRM : R ≤ 1 / (2 * M) := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  let v : E2 → ℝ := fun x => 1 + M * (2 * R * x 1 - (x 1)^2)
  have hv : ContDiff ℝ ∞ v := by dsimp [v]; fun_prop
  have hsub : closedHalfDisc R ⊆ closedHalfDisc W.R := fun x hx =>
    ⟨Metric.closedBall_subset_closedBall hRW.le hx.1,hx.2⟩
  have hvbound (x : E2) (hx : x ∈ closedHalfDisc R) : 1 ≤ v x ∧ v x ≤ 3/2 := by
    have hn : ‖x‖ ≤ R := by simpa only [closedDisc,Metric.mem_closedBall,dist_zero_right] using hx.1
    have hy : x 1 ≤ R := (le_abs_self _).trans ((PiLp.norm_apply_le x 1).trans hn)
    have hshape : 0 ≤ 2*R*x 1-(x 1)^2 := by nlinarith [hx.2]
    have hshapehi : 2*R*x 1-(x 1)^2 ≤ R^2 := by nlinarith [sq_nonneg (R-x 1)]
    have hRsq : R^2 ≤ R := by nlinarith
    have hMR : R*(2*M) ≤ 1 := (le_div_iff₀ (by positivity : 0 < 2*M)).mp hRM
    dsimp [v]
    constructor <;> nlinarith [mul_nonneg hM.le hshape]
  refine ⟨R,M,hR,hRW,hM,hv,hvbound,?_⟩
  intro x hx
  have hxR : x ∈ closedHalfDisc R := ⟨Metric.ball_subset_closedBall hx.1,hx.2.le⟩
  have hxW := hsub hxR
  have hxO := hWO hxW
  have hdiff (i j : Fin 2) : DifferentiableAt ℝ (fun y => W.a y i j) x :=
    ((ha i j).contDiffAt (hO.mem_nhds hxO)).differentiableAt (by simp)
  have hentry (i : Fin 2) : |fderiv ℝ (fun y => W.a y i 1) x (coordinateVector 2 i)| ≤ A' := by
    have hh := hAb i x hxW
    calc
      _ ≤ A i := by simpa only [Real.norm_eq_abs] using hh
      _ ≤ |A i| := le_abs_self _
      _ ≤ A' := by fin_cases i <;> dsimp [A'] <;> linarith [abs_nonneg (A 0),abs_nonneg (A 1)]
  have hn : ‖x‖ ≤ R := by simpa only [closedDisc,Metric.mem_closedBall,dist_zero_right] using hxR.1
  have hy : x 1 ≤ R := (le_abs_self _).trans ((PiLp.norm_apply_le x 1).trans hn)
  have hb1 : |W.b x 1| ≤ B' := (PiLp.norm_apply_le (W.b x) 1).trans
    ((hBb x hxW).trans (le_max_left _ _))
  have hcx : |W.c x| ≤ C' := by
    simpa only [Real.norm_eq_abs] using (hCb x hxW).trans (le_max_left _ _)
  have ha11 : ell ≤ W.a x 1 1 := by
    have hh := (hbounds x hxW (coordinateVector 2 1)).1
    simpa [coordinateVector,matrixAction,Fin.sum_univ_two,
      EuclideanSpace.inner_eq_star_dotProduct,dotProduct,EuclideanSpace.single,
      EuclideanSpace.real_norm_sq_eq] using hh
  let t := (∑ i : Fin 2, fderiv ℝ (fun y => W.a y i 1) x (coordinateVector 2 i)) + W.b x 1
  have ht : t ≤ L := by
    dsimp [t,L]
    simp only [Fin.sum_univ_two]
    linarith [le_abs_self (fderiv ℝ (fun y => W.a y 0 1) x (coordinateVector 2 0)),
      le_abs_self (fderiv ℝ (fun y => W.a y 1 1) x (coordinateVector 2 1)),le_abs_self (W.b x 1),
      hentry 0,hentry 1]
  have hshape : 0 ≤ 2*R-2*x 1 := by linarith
  have hshapehi : 2*R-2*x 1 ≤ 2*R := by linarith [hx.2]
  have hterm : (2*R-2*x 1)*t ≤ 2*R*L :=
    (mul_le_mul_of_nonneg_left ht hshape).trans
      (mul_le_mul_of_nonneg_right hshapehi hL.le)
  have hbracket : -2*W.a x 1 1 + (2*R-2*x 1)*t ≤ -ell := by
    have hh : R*(4*L) ≤ ell := (le_div_iff₀ (by positivity : 0 < 4*L)).mp hRL
    linarith
  have hcv : W.c x * v x ≤ 2*C' := by
    have hvx := hvbound x hxR
    have hh : |W.c x * v x| ≤ C'*(3/2) := by
      rw [abs_mul,abs_of_nonneg (by linarith : 0 ≤ v x)]
      exact mul_le_mul hcx hvx.2 (by linarith) hC.le
    linarith [le_abs_self (W.c x*v x)]
  have hMe : M*ell = 4*C'+1 := div_mul_cancel₀ _ hell.ne'
  rw [show classicalL W.a W.b W.c v x = _ from flat_barrier_classical_v468 R M W.a W.b W.c x hdiff]
  have hm := mul_le_mul_of_nonneg_left hbracket hM.le
  change W.c x*(1+M*(2*R*x 1-(x 1)^2)) ≤ 2*C' at hcv
  dsimp [t] at hm
  nlinarith

end SeifertSurfaces.OriginalEndpoints.B1Tangency

