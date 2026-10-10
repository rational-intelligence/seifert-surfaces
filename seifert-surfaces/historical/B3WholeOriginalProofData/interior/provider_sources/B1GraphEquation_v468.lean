import B1CollarWindow_v468
import B1GraphCoefficients
import B1ActualGraphEquationNative_v475
noncomputable section
open Set Topology Function MeasureTheory
open scoped Manifold ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
universe v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}
set_option maxHeartbeats 0
theorem actual_minimal_graph_equations (D : B1OriginalData g J) (s : Circle)
    (W : CollarWindow D s) :
    (∀ x ∈ halfDisc W.R, W.residual (localHeight D s) x = 0) ∧
    (∀ x ∈ halfDisc W.R, W.residual (fun _ => 0) x = 0) := by
  exact actual_minimal_graph_equations_native_v475 D s W

/-- Mean-value linearization, with coefficients pinned to the same area density. -/
theorem actual_difference_equation (D : B1OriginalData g J) (s : Circle)
    (W : CollarWindow D s) :
    SmoothEllipticOn W.a W.b W.c (closedHalfDisc W.R) ∧
    ∀ x ∈ closedHalfDisc W.R,
      classicalL W.a W.b W.c (localHeight D s) x = 0 := by
  obtain ⟨O,hO,hWO,hOU,hjets,hheight,hgrad,ha,hq,hlg,hlh,hb,hc⟩ :=
    SeifertSurfaces.OriginalEndpoints.B1GraphCoefficients.actual_coefficient_open_tube D s W
  obtain ⟨hformula,hsym,hbounds⟩ :=
    SeifertSurfaces.OriginalEndpoints.B1GraphCoefficients.actual_slope_hessian_uniform_bounds D s W
  obtain ⟨hi1,hi2,hi3,hi4,hflux,hlower,hresidual⟩ :=
    SeifertSurfaces.OriginalEndpoints.B1GraphCoefficients.actual_coefficient_mean_value
      D s W O hO hOU hjets hq
  have hminimal := actual_minimal_graph_equations D s W
  refine ⟨⟨fun i j => (ha i j).mono hWO,hb.mono hWO,hc.mono hWO,hsym,hbounds⟩,?_⟩
  have hinside : halfDisc W.R ⊆ closedHalfDisc W.R :=
    fun x hx => ⟨Metric.ball_subset_closedBall hx.1,hx.2.le⟩
  have heq : EqOn (classicalL W.a W.b W.c (localHeight D s)) (fun _ => 0) (halfDisc W.R) := by
    intro x hx
    rw [← hresidual x (hWO (hinside hx)),hminimal.1 x hx,hminimal.2 x hx,sub_self]
  have hflux (i : Fin 2) : ContDiffOn ℝ ∞
      (fun x => matrixAction (W.a x) (planarGradient (localHeight D s) x) i) O := by
    change ContDiffOn ℝ ∞ (fun x => ∑ j : Fin 2, W.a x i j * planarGradient (localHeight D s) x j) O
    apply ContDiffOn.sum
    intro j hj
    exact (ha i j).mul ((EuclideanSpace.proj (𝕜 := ℝ) (j : Fin 2)).contDiff.contDiffOn.comp
      hgrad (fun x hx => mem_univ _))
  have hdcont : ContinuousOn (fun x => ∑ i : Fin 2,
      fderiv ℝ (fun y => matrixAction (W.a y) (planarGradient (localHeight D s) y) i) x
        (coordinateVector 2 i)) O := by
    apply continuousOn_finsetSum
    intro i hi
    intro x hx
    exact ((((hflux i x hx).contDiffAt (hO.mem_nhds hx)).fderiv_right (m := 0)
      (by simp)).continuousAt.clm_apply continuousAt_const).continuousWithinAt
  have hLcont : ContinuousOn (classicalL W.a W.b W.c (localHeight D s)) O :=
    (hdcont.add (hb.continuousOn.inner hgrad.continuousOn)).add
      (hc.continuousOn.mul hheight.continuousOn)
  let H := closedHalfDisc W.R
  have hconv : Convex ℝ H := by
    apply (convex_closedBall (0 : E2) W.R).inter
    exact convex_halfSpace_ge (f := fun x : E2 => x 1) ⟨by intros; rfl,by intros; rfl⟩ 0
  have hint : interior H = halfDisc W.R := by
    change interior (Metric.closedBall (0 : E2) W.R ∩ {x : E2 | 0 ≤ x 1}) = _
    rw [interior_inter,interior_closedBall _ W.R_pos.ne',interior_halfSpace]
    rfl
  have hnonempty : (interior H).Nonempty := by
    rw [hint]
    refine ⟨(W.R / 2) • coordinateVector 2 1,?_,?_⟩
    · apply Metric.mem_ball.mpr
      rw [dist_zero_right]
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (half_pos W.R_pos)]
      have hn : ‖coordinateVector 2 (1 : Fin 2)‖ = 1 := by
        simp [coordinateVector]
      rw [hn,mul_one]
      linarith [W.R_pos]
    · simpa [coordinateVector] using half_pos W.R_pos
  have hclosed : IsClosed H :=
    Metric.isClosed_closedBall.inter (isClosed_le continuous_const (EuclideanSpace.proj (1 : Fin 2)).continuous)
  have hcl : closure (halfDisc W.R) = H := by
    rw [← hint,hconv.closure_interior_eq_closure_of_nonempty_interior hnonempty,hclosed.closure_eq]
  exact heq.of_subset_closure (hLcont.mono hWO) continuousOn_const hinside (by rw [hcl])
end SeifertSurfaces.OriginalEndpoints.B1Tangency
