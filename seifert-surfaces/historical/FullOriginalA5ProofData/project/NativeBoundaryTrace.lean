import NativeBoundaryPreliminaries

set_option autoImplicit false
noncomputable section
open Set Filter Function
open scoped Topology ContDiff

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity

theorem flatBoundary_subset_closedHalfDisc (ρ : ℝ) :
    flatBoundary ρ ⊆ closedHalfDisc ρ := by
  intro x hx
  exact ⟨Metric.mem_closedBall.mpr (Metric.mem_ball.mp hx.1).le, le_of_eq hx.2.symm⟩

theorem flatBoundary_tangentCoordinate {ρ : ℝ} {x : E2}
    (hx : x ∈ flatBoundary ρ) : x 1 ∈ Ioo (-ρ) ρ := by
  have hnorm : ‖x‖ < ρ := by simpa only [Metric.mem_ball, dist_zero_right] using hx.1
  have hcoordle : |x 1| ≤ ‖x‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x (1 : Fin 2) (p := 2)
  have hcoord : |x 1| < ρ := hcoordle.trans_lt hnorm
  exact abs_lt.mp hcoord

theorem tangentPath_eventually_flatBoundary {ρ : ℝ} {x : E2}
    (hx : x ∈ flatBoundary ρ) :
    ∀ᶠ t : ℝ in 𝓝 0, x + t • coordinateVector 2 1 ∈ flatBoundary ρ := by
  have hc : Continuous (fun t : ℝ => x + t • coordinateVector 2 1) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hball : ∀ᶠ t : ℝ in 𝓝 0, x + t • coordinateVector 2 1 ∈ Metric.ball 0 ρ :=
    hc.continuousAt.eventually_mem (by simpa using Metric.isOpen_ball.mem_nhds hx.1)
  filter_upwards [hball] with t ht
  refine ⟨ht, ?_⟩
  have hxzero : x 0 = 0 := hx.2
  simpa [PiLp.add_apply, PiLp.smul_apply, coordinateVector, EuclideanSpace.single] using hxzero

theorem C1QuasilinearDirichletSolution.tangential_derivative_trace
    {ρ : ℝ} (hρ : 0 < ρ) {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    {x : E2} (hx : x ∈ flatBoundary ρ) :
    fderivWithin ℝ u (closedHalfDisc ρ) x (coordinateVector 2 1) = deriv g.value (x 1) := by
  have hud := (hsolution.c1.differentiableOn (by norm_num) x
    (flatBoundary_subset_closedHalfDisc ρ hx)).hasFDerivWithinAt
  have hpath : HasDerivAt (fun t : ℝ => x + t • coordinateVector 2 1)
      (coordinateVector 2 1) 0 := by
    convert (hasDerivAt_const (0 : ℝ) x).add ((hasDerivAt_id (0 : ℝ)).smul_const
      (coordinateVector 2 1)) using 1 <;> first | rfl | simp only [zero_add, one_smul]
  have hupath : HasDerivAt (fun t : ℝ => u (x + t • coordinateVector 2 1))
      (fderivWithin ℝ u (closedHalfDisc ρ) x (coordinateVector 2 1)) 0 := by
    apply hud.comp_hasDerivAt_of_eq 0 hpath
    · exact (tangentPath_eventually_flatBoundary hx).mono
        (fun t ht => flatBoundary_subset_closedHalfDisc ρ ht)
    · simp
  have hgat : DifferentiableAt ℝ g.value (x 1) :=
    (g.smooth.contDiffAt (isOpen_Ioo.mem_nhds (flatBoundary_tangentCoordinate hx))).differentiableAt
      (by simp)
  have hgpath : HasDerivAt (fun t : ℝ => g.value (x 1 + t)) (deriv g.value (x 1)) 0 := by
    have hg : HasDerivAt g.value (deriv g.value (x 1)) (x 1 + 0) := by
      simpa only [add_zero] using hgat.hasDerivAt
    convert hg.comp 0 ((hasDerivAt_const (0 : ℝ) (x 1)).add (hasDerivAt_id (0 : ℝ)))
      using 1 <;> simp only [Function.comp_def, Pi.add_apply, id_eq, zero_add, mul_one]
  have heq : (fun t : ℝ => u (x + t • coordinateVector 2 1)) =ᶠ[𝓝 0]
      (fun t : ℝ => g.value (x 1 + t)) := by
    filter_upwards [tangentPath_eventually_flatBoundary hx] with t ht
    simpa [PiLp.add_apply, PiLp.smul_apply, coordinateVector, EuclideanSpace.single] using
      hsolution.dirichlet_values _ ht
  exact (hupath.congr_of_eventuallyEq heq.symm).unique hgpath

theorem SmoothDirichletDatum.smooth_tangential_extension
    {ρ r : ℝ} (g : SmoothDirichletDatum ρ) (hrρ : r < ρ) :
    ContDiffOn ℝ ∞ (fun x : E2 => g.value (x 1)) (closedHalfDisc r) := by
  apply g.smooth.comp (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff.contDiffOn
  intro x hx
  have hn : ‖x‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx.1
  have hcle : |x 1| ≤ ‖x‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x (1 : Fin 2) (p := 2)
  have hc : |x 1| < ρ := hcle.trans_lt (hn.trans_lt hrρ)
  exact abs_lt.mp hc

theorem C1QuasilinearDirichletSolution.zero_trace_subtraction
    {ρ r : ℝ} {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u) (hrρ : r < ρ) :
    ContDiffOn ℝ 1 (fun x => u x - g.value (x 1)) (closedHalfDisc r) ∧
      (∀ x ∈ flatBoundary r, u x - g.value (x 1) = 0) := by
  refine ⟨(hsolution.c1.mono (closedHalfDisc_mono hrρ.le)).sub
    ((g.smooth_tangential_extension hrρ).of_le (by simp)), ?_⟩
  intro x hx
  exact sub_eq_zero.mpr (hsolution.dirichlet_values x
    ⟨Metric.ball_subset_ball hrρ.le hx.1, hx.2⟩)

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
