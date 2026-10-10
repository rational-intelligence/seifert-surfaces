import B1HalfDiscCompletedBarrier_v468
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Smooth original tube data have literal L2 representatives on each smaller half-disc. -/
theorem halfdisc_smooth_classical_data_L2_v468
    (R : ℝ) (O : Set E2) (hO : IsOpen O) (hHO : closedHalfDisc R ⊆ O)
    (a : E2 → Mat2) (b : E2 → E2) (c v : E2 → ℝ)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) O)
    (hb : ContDiffOn ℝ ∞ b O) (hc : ContDiffOn ℝ ∞ c O)
    (hv : ContDiff ℝ ∞ v) :
    MemLp v 2 (volume.restrict (halfDisc R)) ∧
    MemLp (planarGradient v) 2 (volume.restrict (halfDisc R)) ∧
    MemLp (classicalL a b c v) 2 (volume.restrict (halfDisc R)) := by
  let U := halfDisc R
  let H := closedHalfDisc R
  have hU : MeasurableSet U := (Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous)).measurableSet
  have hUH : U ⊆ H := fun x hx => ⟨Metric.ball_subset_closedBall hx.1,hx.2.le⟩
  have hH : IsCompact H := (isCompact_closedBall (0 : E2) R).inter_right
    (isClosed_le continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous)
  haveI : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr
    (lt_of_le_of_lt (measure_mono (show U ⊆ Metric.ball (0 : E2) R from fun x hx => hx.1))
      measure_ball_lt_top).ne
  have smooth_lp {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
      (f : E2 → F) (hf : ContinuousOn f O) : MemLp f 2 (volume.restrict U) := by
    obtain ⟨B,hB⟩ := hH.exists_bound_of_continuousOn (hf.mono hHO)
    apply MemLp.of_bound ((hf.mono (hUH.trans hHO)).aestronglyMeasurable hU) B
    filter_upwards [ae_restrict_mem hU] with x hx
    exact hB x (hUH hx)
  have hgrad : ContDiff ℝ 1 (planarGradient v) := by
    unfold planarGradient
    apply ContDiff.sum
    intro i hi
    exact (hv.fderiv_right (m := 1) (by simp)).clm_apply contDiff_const |>.smul contDiff_const
  have hflux (i : Fin 2) : ContDiffOn ℝ 1
      (fun x => matrixAction (a x) (planarGradient v x) i) O := by
    change ContDiffOn ℝ 1 (fun x => ∑ j : Fin 2, a x i j * planarGradient v x j) O
    apply ContDiffOn.sum
    intro j hj
    exact ((ha i j).of_le (by simp)).mul
      (((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp hgrad).contDiffOn)
  have hdiv : ContinuousOn (fun x => ∑ i : Fin 2,
      fderiv ℝ (fun y => matrixAction (a y) (planarGradient v y) i) x (coordinateVector 2 i)) O := by
    apply continuousOn_finsetSum
    intro i hi
    exact ((hflux i).continuousOn_fderiv_of_isOpen hO (by simp)).clm_apply continuousOn_const
  exact ⟨smooth_lp v hv.continuous.continuousOn,
    smooth_lp (planarGradient v) hgrad.continuous.continuousOn,
    smooth_lp (classicalL a b c v) ((hdiv.add
      (hb.continuousOn.inner hgrad.continuous.continuousOn)).add
      (hc.continuousOn.mul hv.continuous.continuousOn))⟩

end SeifertSurfaces.OriginalEndpoints.B1Tangency
