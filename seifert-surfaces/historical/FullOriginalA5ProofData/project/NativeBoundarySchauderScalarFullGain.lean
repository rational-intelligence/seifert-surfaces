import NativeBoundarySchauderScalarHolderGain

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak

theorem native_zero_source_boundary_C1_holder_gain
    (r : ℝ) (hr : 0 < r) (α : ℝ≥0) (hα : 0 < α) (hα1 : α < 1)
    (a : E2 → Matrix (Fin 2) (Fin 2) ℝ) (κ M : ℝ) (hκ : 0 < κ) (hM : 0 < M)
    (ha : ∀ x ξ, κ * ‖ξ‖ ^ 2 ≤
      inner ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2) (a x) ξ) ξ ∧
      ∀ i j, |a x i j| ≤ M)
    (H : ℝ≥0) (hholder : ∀ i j, HolderWith H α (fun x => a x i j))
    (e : E2 → E2) (B : ℝ) (hB : 0 ≤ B) (Ce : ℝ≥0)
    (heB : ∀ x, ‖e x‖ ≤ B) (he : HolderWith Ce α e)
    (v : E2 → ℝ) (G : E2 → E2)
    (hv : ContinuousOn v (closedHalfDisc r))
    (hw : WeakDivergenceWithData (openHalfDisc r) a e (fun _ => 0) v G)
    (ht : FlatZeroTrace r (fun y => v (coordinateSwap y))
      (fun y => coordinateSwap (G (coordinateSwap y)))) :
    ContDiffOn ℝ 1 v (closedHalfDisc (r / 4)) ∧
      ∀ i, ∃ C : ℝ≥0, HolderOnWith C α
        (fun x => fderivWithin ℝ v (closedHalfDisc (r / 4)) x (coordinateVector 2 i))
        (closedHalfDisc (r / 4)) := by
  obtain ⟨A, _, hgain⟩ := zero_scalar_boundary_debt r hr α hα hα1
    (nativeSchauderMatrixInB1Coordinates 0 a) κ M hκ hM
    (native_schauder_swap_matrix_bounds 0 a κ M ha) H
    (native_schauder_swap_matrix_holder 0 a H α hholder)
  have hweak := native_zero_source_weak_divergence_coordinateSwap
    (openHalfDisc r) (openHalfDisc_isOpen r).measurableSet a e v G hw
  rw [native_swap_preimage_openHalfDisc] at hweak
  obtain ⟨w, hae, _, hwC1, _, _, _, hH⟩ := hgain
    (nativeSchauderVectorInB1Coordinates 0 e) (fun y => v (coordinateSwap y))
    (fun y => coordinateSwap (G (coordinateSwap y))) B hB Ce
    (fun y _ => native_schauder_swap_vector_bound 0 e B heB y)
    ((native_schauder_swap_vector_holder 0 e Ce α he).holderOnWith _) hweak ht
  exact native_scalar_representative_holder_transfer (r / 2) (r / 4) (by positivity)
    (by linarith) v w (hv.mono (closedHalfDisc_mono (by linarith))) hwC1 hae α
    (fun j => by obtain ⟨C, _, hC⟩ := hH j; exact ⟨C, hC⟩)

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
