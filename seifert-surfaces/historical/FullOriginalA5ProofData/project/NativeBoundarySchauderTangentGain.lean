import NativeBoundaryClosedDerivativeReconstruction

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization

theorem C1QuasilinearDirichletSolution.local_C1_tangential_derivative
    {ρ : ℝ} (hρ : 0 < ρ) {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (c : E2) (hc : c ∈ flatBoundary ρ) :
    ∃ δ : ℝ, 0 < δ ∧ Metric.closedBall c δ ⊆ Metric.ball 0 ρ ∧
      ContDiffOn ℝ 1 (fun x => fderivWithin ℝ u (closedHalfDisc ρ) x (coordinateVector 2 1))
        (nativeClosedBoundaryCap c δ) := by
  obtain ⟨δ, hδ, hball, hC⟩ := hsolution.local_C1_zero_trace_tangential_derivative hρ c hc
  have hg : ContDiffOn ℝ 1 (fun x : E2 => deriv g.value (x 1)) (nativeClosedBoundaryCap c δ) :=
    (g.smooth_deriv_extension_on_ball.mono (fun x hx => hball hx.1)).of_le (by simp)
  refine ⟨δ, hδ, hball, ?_⟩
  convert hC.add hg using 1
  funext x
  simp only [Pi.add_apply, sub_add_cancel]

theorem nativeClosedBoundaryCap_uniqueDiffOn (c : E2) (r : ℝ)
    (hr : 0 < r) (hcf : c 0 = 0) : UniqueDiffOn ℝ (nativeClosedBoundaryCap c r) := by
  apply uniqueDiffOn_convex (nativeClosedBoundaryCap_convex c r)
  let y := c + (r / 2) • coordinateVector 2 0
  have hU : IsOpen (Metric.ball c r ∩ {x : E2 | 0 < x 0}) := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (0 : Fin 2)).continuous)
  have hsub : Metric.ball c r ∩ {x : E2 | 0 < x 0} ⊆ nativeClosedBoundaryCap c r :=
    fun x hx => ⟨Metric.ball_subset_closedBall hx.1, by change 0 ≤ x 0; exact le_of_lt hx.2⟩
  refine ⟨y, interior_maximal hsub hU ?_⟩
  refine ⟨?_, ?_⟩
  · change dist y c < r
    simp only [y, dist_eq_norm, add_sub_cancel_left, norm_smul]
    simp [coordinateVector, PiLp.norm_single]
    rw [abs_of_pos hr]
    linarith
  · change 0 < y 0
    simp [y, coordinateVector, hcf]
    positivity

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
