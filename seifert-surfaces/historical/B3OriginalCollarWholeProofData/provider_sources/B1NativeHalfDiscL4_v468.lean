import B1NativeHalfDiscEvenH1_v468
import B1NativeBallL4_v468
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open DifferentialGeometry.Analysis.Sobolev.Euclidean
set_option maxHeartbeats 1000000

/-- Native one-sided H1 has the full L4 gain up to the flat edge. -/
theorem native_halfdisc_H1_L4_v468 (R : ℝ) (hR : 0<R) (u : E2 → ℝ)
    (hs : ContDiffOn ℝ ∞ u (halfDisc R)) (hu : DeGiorgi.MemW1p 2 u (halfDisc R)) :
    MemLp u 4 (volume.restrict (halfDisc R)) := by
  have he := native_halfdisc_even_H1_v468 R u hs hu
  have hl := native_ball_H1_L4_v468 R hR _ he
  have hU : IsOpen (halfDisc R) := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)
  apply (hl.mono_measure (Measure.restrict_mono_set _ (fun x (hx : x∈halfDisc R) => hx.1))).ae_eq
  filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
  simp only [if_pos hx.2.le]

/-- Actual derivatives of a native boundary H2 function have L4, obtained
from its derivative H1 rather than from any supplied boundary derivative. -/
theorem native_halfdisc_H2_actual_gradient_L4_v468 (R : ℝ) (hR : 0<R) (u : E2 → ℝ)
    (hs : ContDiffOn ℝ ∞ u (halfDisc R)) (hu : MemWkp 2 2 u (halfDisc R)) :
    MemLp (planarGradient u) 4 (volume.restrict (halfDisc R)) := by
  have hU : IsOpen (halfDisc R) := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)
  apply memLp_piLp_iff.mpr
  intro i
  have hp := native_smooth_partial_memWkp_v468 _ hU u hs 1 hu i
  have hgs : ContDiffOn ℝ ∞ (fun x => planarGradient u x i) (halfDisc R) := by
    have he : (fun x => planarGradient u x i)=fun x => fderiv ℝ u x (coordinateVector 2 i) := by
      funext x
      exact QuasilinearLocalization.Helpers.gradient_apply u x i
    rw [he]
    exact (hs.fderiv_of_isOpen hU (m:=∞) (by simp)).clm_apply contDiffOn_const
  exact native_halfdisc_H1_L4_v468 R hR _ hgs hp.memW1p
end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.native_halfdisc_H1_L4_v468
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.native_halfdisc_H2_actual_gradient_L4_v468
