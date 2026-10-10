import NativeBoundarySchauderWeakData
import NativeBoundarySchauderForcingExtension

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity

theorem native_continuous_closed_cap_memLp
    {F : Type*} [NormedAddCommGroup F]
    (c : E2) (r : ℝ) (f : E2 → F)
    (hf : ContinuousOn f (nativeClosedBoundaryCap c r)) :
    MemLp f 2 (volume.restrict (Metric.ball c r ∩ {x : E2 | 0 < x 0})) := by
  let U := Metric.ball c r ∩ {x : E2 | 0 < x 0}
  have hU : IsOpen U := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (0 : Fin 2)).continuous)
  have hUK : U ⊆ nativeClosedBoundaryCap c r := by
    intro x hx
    have hp : 0 < x 0 := hx.2
    exact ⟨Metric.ball_subset_closedBall hx.1, hp.le⟩
  have hK : IsCompact (nativeClosedBoundaryCap c r) :=
    (isCompact_closedBall c r).inter_right
      (isClosed_le continuous_const (EuclideanSpace.proj (0 : Fin 2)).continuous)
  haveI : IsFiniteMeasure (volume.restrict U) :=
    isFiniteMeasure_restrict.mpr ((measure_mono hUK).trans_lt hK.measure_lt_top).ne
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hf
  apply MemLp.of_bound
    (hf.aestronglyMeasurable_of_subset_isCompact hK hU.measurableSet hUK) B
  filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
  exact hB x (hUK hx)

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
