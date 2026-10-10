import NativeBoundaryCoefficientExtension

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak.BoundaryContinuation

/-- Actual translated coefficient conjugated by the native coordinate swap. -/
def nativeSchauderMatrixInB1Coordinates
    (c : E2) (a : E2 → Matrix (Fin 2) (Fin 2) ℝ) (y : E2) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => a (coordinateSwap y + c) (Equiv.swap (0 : Fin 2) 1 i) (Equiv.swap (0 : Fin 2) 1 j)

theorem native_matrixAction_eq_toEuclideanCLM (a : Matrix (Fin 2) (Fin 2) ℝ) (ξ : E2) :
    matrixAction a ξ = Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2) a ξ := by
  ext i
  simp [matrixAction, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct]

theorem native_schauder_swap_matrix_action
    (c : E2) (a : E2 → Matrix (Fin 2) (Fin 2) ℝ) (y ξ : E2) :
    matrixAction (nativeSchauderMatrixInB1Coordinates c a y) ξ =
      coordinateSwap (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2)
        (a (coordinateSwap y + c)) (coordinateSwap ξ)) := by
  rw [native_matrixAction_eq_toEuclideanCLM]
  ext i
  fin_cases i <;>
    simp [nativeSchauderMatrixInB1Coordinates, coordinateSwap,
      Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct, Fin.sum_univ_two, add_comm]

theorem native_schauder_swap_matrix_bounds
    (c : E2) (a : E2 → Matrix (Fin 2) (Fin 2) ℝ) (κ M : ℝ)
    (ha : ∀ x : E2, ∀ ξ : E2,
      κ * ‖ξ‖ ^ 2 ≤ inner ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2) (a x) ξ) ξ ∧
        ∀ i j, |a x i j| ≤ M) :
    ∀ y : E2, ∀ ξ : E2,
      κ * ‖ξ‖ ^ 2 ≤ inner ℝ ξ (matrixAction (nativeSchauderMatrixInB1Coordinates c a y) ξ) ∧
        ∀ i j, |nativeSchauderMatrixInB1Coordinates c a y i j| ≤ M := by
  intro y ξ
  obtain ⟨he, hb⟩ := ha (coordinateSwap y + c) (coordinateSwap ξ)
  refine ⟨?_, ?_⟩
  · rw [native_schauder_swap_matrix_action, real_inner_comm]
    have hi := coordinateSwap.inner_map_map
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2) (a (coordinateSwap y + c)) (coordinateSwap ξ))
      (coordinateSwap ξ)
    rw [coordinateSwap_involutive] at hi
    rw [hi]
    simpa only [coordinateSwap.norm_map] using he
  · intro i j
    simpa only [nativeSchauderMatrixInB1Coordinates] using
      hb (Equiv.swap (0 : Fin 2) 1 i) (Equiv.swap (0 : Fin 2) 1 j)

theorem native_schauder_swap_matrix_holder
    (c : E2) (a : E2 → Matrix (Fin 2) (Fin 2) ℝ) (H α : ℝ≥0)
    (ha : ∀ i j, HolderWith H α (fun x => a x i j)) :
    ∀ i j, HolderWith H α (fun y => nativeSchauderMatrixInB1Coordinates c a y i j) := by
  have hL : LipschitzWith 1 (fun y : E2 => coordinateSwap y + c) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [dist_add_right, coordinateSwap.dist_map, NNReal.coe_one, one_mul, le_refl]
  intro i j
  have hh := (ha (Equiv.swap (0 : Fin 2) 1 i) (Equiv.swap (0 : Fin 2) 1 j)).comp hL.holderWith
  convert hh using 1 <;> simp [nativeSchauderMatrixInB1Coordinates, Function.comp_def]

theorem native_swap_preimage_openHalfDisc (r : ℝ) :
    coordinateSwap ⁻¹' openHalfDisc r = halfDisc r := by
  ext x
  simp only [mem_preimage, openHalfDisc, halfDisc, disc, mem_inter_iff,
    Metric.mem_ball, dist_zero_right, mem_setOf_eq,
    coordinateSwap.norm_map, coordinateSwap_zero]

theorem native_swap_preimage_closedHalfDisc (r : ℝ) :
    coordinateSwap ⁻¹' SeifertSurfaces.AppendixACoordinates.closedHalfDisc r =
      SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc r := by
  ext x
  simp only [mem_preimage, SeifertSurfaces.AppendixACoordinates.closedHalfDisc,
    SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc, closedDisc,
    mem_inter_iff, Metric.mem_closedBall, dist_zero_right, mem_setOf_eq,
    coordinateSwap.norm_map, coordinateSwap_zero]

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
