import B1ActualNativeClosedDirichlet_v468
import NativeBoundaryH10Translation
import NativeH10CutoffLocalization
import NativeH1Sum
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.TestFunction.Localization
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open ChartMetricProvider.Variational.IsothermalPDELower.NativeDirichlet
open ChartMetricProvider.Variational.DirectWeak
open ChartMetricProvider.Variational.DirectWeak.BoundaryContinuation
open SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
set_option maxHeartbeats 0

/-- Native zero trace is stable under scalar multiplication, including its supplied gradient. -/
theorem native_h10_smul_v468 (U : Set E2) (u : E2 → ℝ) (du : E2 → E2)
    (hu : H10On U u du) (a : ℝ) :
    H10On U (fun x => a * u x) (fun x => a • du x) := by
  have hv := hu.1.2.1.const_mul a
  have hg := hu.1.2.2.const_smul a
  apply (h10_pair_bridge U _ _ hv hg).mpr
  have hp := (h10_pair_bridge U u du hu.1.2.1 hu.1.2.2).mp hu
  convert (space U).smul_mem a hp using 1 <;> rfl

/-- Subtracting actual native zero-trace functions preserves zero trace. -/
theorem native_h10_sub_v468 (U : Set E2) (u v : E2 → ℝ) (du dv : E2 → E2)
    (hu : H10On U u du) (hv : H10On U v dv) :
    H10On U (fun x => u x-v x) (fun x => du x-dv x) := by
  apply (h10_pair_bridge U _ _ (hu.1.2.1.sub hv.1.2.1) (hu.1.2.2.sub hv.1.2.2)).mpr
  have hp := (h10_pair_bridge U u du hu.1.2.1 hu.1.2.2).mp hu
  have hq := (h10_pair_bridge U v dv hv.1.2.1 hv.1.2.2).mp hv
  convert (space U).sub_mem hp hq using 1 <;> rfl

/-- The literal B1 tangential shift preserves the normal half-space. -/
theorem b1_tangential_shift_normal_v468 (t : ℝ) (x : E2) :
    (x+t • coordinateVector 2 0) 1=x 1 := by
  simp [coordinateVector, PiLp.add_apply, PiLp.smul_apply, EuclideanSpace.single]

theorem b1_tangential_shift_norm_v468 (t : ℝ) (x : E2) :
      ‖x+t • coordinateVector 2 0‖ ≤ ‖x‖+|t| := by
  simpa [norm_smul, Real.norm_eq_abs, coordinateVector] using
    norm_add_le x (t • coordinateVector 2 0)

/-- Tangential translates of the original H10 solution remain valid local H10 tests
once multiplied by a genuine compact cutoff. No boundary C1 premise is used. -/
theorem native_tangential_cutoff_h10_v468
    (R r t : ℝ) (hroom : r+|t|<R)
    (chi : E2 → ℝ) (hs : ContDiff ℝ ∞ chi) (hc : HasCompactSupport chi)
    (ht : tsupport chi ⊆ Metric.ball 0 r)
    (u : E2 → ℝ) (du : E2 → E2) (hu : H10On (halfDisc R) u du) :
    H10On (halfDisc r) (fun x => chi x*u (x+t • coordinateVector 2 0))
      (cutoffGradient chi (fun x => u (x+t • coordinateVector 2 0))
        (fun x => du (x+t • coordinateVector 2 0))) := by
  let c : E2 := t • coordinateVector 2 0
  let U := (fun x : E2 => x+c) ⁻¹' halfDisc R
  have hm : MeasurableSet (halfDisc R) :=
    (Metric.isOpen_ball.inter (isOpen_lt continuous_const
      (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous)).measurableSet
  have huT := native_h10_translation (halfDisc R) hm c u du hu
  have hVU : halfDisc r ⊆ U := by
    intro x hx
    refine ⟨?_, ?_⟩
    · apply Metric.mem_ball.mpr
      rw [dist_zero_right]
      have hxnorm : ‖x‖<r := by
        simpa only [disc, Metric.mem_ball, dist_zero_right] using hx.1
      exact (b1_tangential_shift_norm_v468 t x).trans_lt (by linarith)
    · simpa only [c, b1_tangential_shift_normal_v468] using hx.2
  have hlocal : tsupport chi ∩ U ⊆ halfDisc r := by
    intro x hx
    refine ⟨ht hx.1, ?_⟩
    have hh : 0<(x+c) 1 := hx.2.2
    simpa only [c,b1_tangential_shift_normal_v468] using hh
  exact h10_cutoff_localization U (halfDisc r) hVU chi hs hc hlocal
    (fun x => u (x+c)) (fun x => du (x+c)) huT

/-- Actual compactly cut off tangential difference quotients are admissible native
zero-trace tests at the flat edge, directly from the original H10 datum. -/
theorem native_tangential_cutoff_quotient_h10_v468
    (R r t : ℝ) (hroom : r+|t|<R) (htne : t ≠ 0)
    (chi : E2 → ℝ) (hs : ContDiff ℝ ∞ chi) (hc : HasCompactSupport chi)
    (ht : tsupport chi ⊆ Metric.ball 0 r)
    (u : E2 → ℝ) (du : E2 → E2) (hu : H10On (halfDisc R) u du) :
    H10On (halfDisc r)
      (fun x => chi x*((u (x+t • coordinateVector 2 0)-u x)/t))
      (fun x => t⁻¹ •
        (cutoffGradient chi (fun y => u (y+t • coordinateVector 2 0))
          (fun y => du (y+t • coordinateVector 2 0)) x - cutoffGradient chi u du x)) := by
  have h0room : r+|(0:ℝ)|<R := by simpa using lt_of_le_of_lt (le_add_of_nonneg_right (abs_nonneg t)) hroom
  have hT := native_tangential_cutoff_h10_v468 R r t hroom chi hs hc ht u du hu
  have h0 := native_tangential_cutoff_h10_v468 R r 0 h0room chi hs hc ht u du hu
  simp only [zero_smul, add_zero] at h0
  have hd := native_h10_sub_v468 (halfDisc r) _ _ _ _ hT h0
  convert native_h10_smul_v468 (halfDisc r) _ _ hd t⁻¹ using 1
  funext x
  simp only [div_eq_mul_inv]
  ring

end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.native_tangential_cutoff_quotient_h10_v468
