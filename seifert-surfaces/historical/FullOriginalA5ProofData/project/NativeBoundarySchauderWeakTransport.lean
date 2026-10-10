import NativeBoundarySchauderForcingTransport

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak.BoundaryContinuation

/-- Transport of the exact H1 gradient and both integrable weak flux terms
under the native orthogonal coordinate permutation. -/
theorem native_zero_source_weak_divergence_coordinateSwap
    (U : Set E2) (hU : MeasurableSet U) (a : E2 → Matrix (Fin 2) (Fin 2) ℝ)
    (e : E2 → E2) (v : E2 → ℝ) (G : E2 → E2)
    (hw : WeakDivergenceWithData U a e (fun _ => 0) v G) :
    WeakDivergenceWithData (coordinateSwap ⁻¹' U)
      (nativeSchauderMatrixInB1Coordinates 0 a) (nativeSchauderVectorInB1Coordinates 0 e)
      (fun _ => 0) (fun y => v (coordinateSwap y))
      (fun y => coordinateSwap (G (coordinateSwap y))) := by
  refine ⟨native_h1_coordinateSwap U v G hw.1, ?_⟩
  intro φ hs hc ht
  let W := coordinateSwap ⁻¹' U
  let ψ : E2 → ℝ := fun x => φ (coordinateSwap x)
  have hψs : ContDiff ℝ ∞ ψ := hs.comp coordinateSwap.contDiff
  have hψc : HasCompactSupport ψ := hc.comp_homeomorph coordinateSwap.toHomeomorph
  have hψt : tsupport ψ ⊆ U := by
    intro x hx
    have hh := ht (tsupport_comp_subset_preimage φ coordinateSwap.continuous hx)
    change coordinateSwap (coordinateSwap x) ∈ U at hh
    simpa only [coordinateSwap_involutive] using hh
  obtain ⟨hiA, hie, hEq⟩ := hw.2 ψ hψs hψc hψt
  have hmp : MeasurePreserving coordinateSwap (volume.restrict W) (volume.restrict U) :=
    coordinateSwap.measurePreserving.restrict_preimage hU
  have hemb : MeasurableEmbedding coordinateSwap := coordinateSwap.toHomeomorph.measurableEmbedding
  have hgrad (y : E2) : planarGradient ψ (coordinateSwap y) =
      coordinateSwap (planarGradient φ y) := by
    rw [show planarGradient ψ (coordinateSwap y) = _ from coordinateSwap_gradient φ hs _,
      coordinateSwap_involutive]
  have hA (y : E2) :
      inner ℝ (matrixAction (nativeSchauderMatrixInB1Coordinates 0 a y)
        (coordinateSwap (G (coordinateSwap y)))) (planarGradient φ y) =
      inner ℝ (matrixAction (a (coordinateSwap y)) (G (coordinateSwap y)))
        (planarGradient ψ (coordinateSwap y)) := by
    rw [native_schauder_swap_matrix_action, coordinateSwap_involutive, add_zero,
      native_swap_inner_left_right, hgrad, native_matrixAction_eq_toEuclideanCLM]
  have he (y : E2) :
      inner ℝ (nativeSchauderVectorInB1Coordinates 0 e y) (planarGradient φ y) + 0 * φ y =
      inner ℝ (e (coordinateSwap y)) (planarGradient ψ (coordinateSwap y)) + 0 * ψ (coordinateSwap y) := by
    simp only [nativeSchauderVectorInB1Coordinates, add_zero, zero_mul,
      native_swap_inner_left_right, hgrad]
  have hiA' := (hmp.integrable_comp_emb hemb).mpr hiA
  have hie' := (hmp.integrable_comp_emb hemb).mpr hie
  refine ⟨?_, ?_, ?_⟩
  · apply hiA'.congr
    exact Eventually.of_forall fun y => (hA y).symm
  · apply hie'.congr
    exact Eventually.of_forall fun y => (he y).symm
  · have hleft := hmp.integral_comp hemb
      (fun x => inner ℝ (matrixAction (a x) (G x)) (planarGradient ψ x))
    have hright := hmp.integral_comp hemb
      (fun x => inner ℝ (e x) (planarGradient ψ x) + 0 * ψ x)
    rw [← hleft, ← hright] at hEq
    simpa only [← hA, ← he] using hEq

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
