import NativeBoundarySchauderH1Transport

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak.BoundaryContinuation

def nativeSchauderVectorInB1Coordinates (c : E2) (e : E2 → E2) (y : E2) : E2 :=
  coordinateSwap (e (coordinateSwap y + c))

theorem native_schauder_swap_vector_holder (c : E2) (e : E2 → E2) (H α : ℝ≥0)
    (he : HolderWith H α e) : HolderWith H α (nativeSchauderVectorInB1Coordinates c e) := by
  have hL : LipschitzWith 1 (fun y : E2 => coordinateSwap y + c) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [dist_add_right, coordinateSwap.dist_map, NNReal.coe_one, one_mul, le_refl]
  have hh := he.comp hL.holderWith
  intro x y
  simpa [nativeSchauderVectorInB1Coordinates, Function.comp_def,
    coordinateSwap.isometry.edist_eq] using hh x y

theorem native_schauder_swap_vector_bound (c : E2) (e : E2 → E2) (B : ℝ)
    (he : ∀ x, ‖e x‖ ≤ B) : ∀ y, ‖nativeSchauderVectorInB1Coordinates c e y‖ ≤ B := by
  intro y
  simpa only [nativeSchauderVectorInB1Coordinates, coordinateSwap.norm_map] using
    he (coordinateSwap y + c)

theorem native_swap_inner_left_right (v w : E2) :
    inner ℝ (coordinateSwap v) w = inner ℝ v (coordinateSwap w) := by
  have hh := coordinateSwap.inner_map_map v (coordinateSwap w)
  simpa only [coordinateSwap_involutive] using hh

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
