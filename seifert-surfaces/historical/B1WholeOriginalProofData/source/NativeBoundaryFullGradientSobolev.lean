import NativeBoundaryFullHessianEnergy

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization
open SeifertSurfaces.QuasilinearProviderBridge

theorem native_memW1p_of_C1_and_actual_gradient_memLp
    (U : Set E2) (hU : IsOpen U) (v : E2 → ℝ) (hc : ContDiffOn ℝ 1 v U)
    (hv : MemLp v 2 (volume.restrict U))
    (hG : MemLp (planarGradient v) 2 (volume.restrict U)) :
    DeGiorgi.MemW1p 2 v U := by
  have hw := Helpers.C1_hasWeakGrad U hU v hc
  refine ⟨hv, ?_⟩
  intro i
  refine ⟨fun x => planarGradient v x i, ?_, hw i⟩
  apply hG.norm.mono'
  · exact ((EuclideanSpace.proj i).continuous.comp_aestronglyMeasurable hG.aestronglyMeasurable)
  · exact Eventually.of_forall (fun x => PiLp.norm_apply_le (planarGradient v x) i (p := 2))

/-- The original full within-gradient has native H1 components up to the flat
boundary, derived from the actual Hessian equation and quotient energy. -/
theorem C1QuasilinearDirichletSolution.local_full_gradient_memW1p
    {ρ : ℝ} (hρ : 0 < ρ) {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (c : E2) (hc : c ∈ flatBoundary ρ) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall c r ⊆ Metric.ball 0 ρ ∧
      ∀ i : Fin 2,
        DeGiorgi.MemW1p 2 (fun x => fderivWithin ℝ u (closedHalfDisc ρ) x (coordinateVector 2 i))
          (Metric.ball c r ∩ {x : E2 | 0 < x 0}) := by
  obtain ⟨r, hr, hball, hgrad⟩ := hsolution.local_full_second_gradient_memLp hρ c hc
  let U := Metric.ball c r ∩ {x : E2 | 0 < x 0}
  have hU : IsOpen U := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (0 : Fin 2)).continuous)
  have hsub : U ⊆ openHalfDisc ρ := fun x hx =>
    ⟨hball (Metric.ball_subset_closedBall hx.1), hx.2⟩
  have hder := hsolution.c1.continuousOn_fderivWithin (closedHalfDisc_uniqueDiffOn hρ) (by norm_num)
  haveI : IsFiniteMeasure (volume.restrict U) :=
    isFiniteMeasure_restrict.mpr
      (lt_of_le_of_lt (measure_mono (show U ⊆ Metric.ball c r from fun x hx => hx.1))
        Metric.isBounded_ball.measure_lt_top).ne
  refine ⟨r, hr, hball, ?_⟩
  intro i
  let v : E2 → ℝ := fun x => fderivWithin ℝ u (closedHalfDisc ρ) x (coordinateVector 2 i)
  have hvc : ContDiffOn ℝ 1 v U :=
    (hsolution.smooth_partial_on_openHalfDisc i).mono hsub |>.of_le (by simp)
  obtain ⟨L, hL⟩ := (closedHalfDisc_isCompact ρ).exists_bound_of_continuousOn
    (hder.clm_apply (continuousOn_const (c := coordinateVector 2 i)))
  have hv : MemLp v 2 (volume.restrict U) := by
    apply MemLp.of_bound (hvc.continuousOn.aestronglyMeasurable hU.measurableSet) L
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    exact hL x (openHalfDisc_subset_closedHalfDisc ρ (hsub hx))
  exact native_memW1p_of_C1_and_actual_gradient_memLp U hU v hvc hv (hgrad i)

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
