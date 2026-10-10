import NativeBoundarySchauderActualGain
import NativeBoundarySchauderWeakTransport
import NativeA5FlatTraceBridgeV471

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak

theorem native_swap_preimage_B1_halfDisc (r : ℝ) :
    coordinateSwap ⁻¹' halfDisc r = openHalfDisc r := by
  ext x
  simp only [mem_preimage, halfDisc, disc, openHalfDisc, mem_inter_iff,
    Metric.mem_ball, dist_zero_right, coordinateSwap.norm_map, mem_setOf_eq,
    coordinateSwap_one]

theorem native_swap_preimage_B1_closedHalfDisc (r : ℝ) :
    coordinateSwap ⁻¹' SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc r =
      closedHalfDisc r := by
  ext x
  simp only [mem_preimage, SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc,
    closedHalfDisc, closedDisc, disc, mem_inter_iff, Metric.mem_closedBall,
    dist_zero_right, coordinateSwap.norm_map, mem_setOf_eq, coordinateSwap_one]

/-- The paid scalar boundary theorem gives regularity of the same actual
continuous scalar on a strictly smaller native closed cap. -/
theorem native_zero_source_boundary_C1_gain
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
    ContDiffOn ℝ 1 v (closedHalfDisc (r / 4)) := by
  obtain ⟨A, _, hgain⟩ := zero_scalar_boundary_debt r hr α hα hα1
    (nativeSchauderMatrixInB1Coordinates 0 a) κ M hκ hM
    (native_schauder_swap_matrix_bounds 0 a κ M ha) H
    (native_schauder_swap_matrix_holder 0 a H α hholder)
  have hweak := native_zero_source_weak_divergence_coordinateSwap
    (openHalfDisc r) (openHalfDisc_isOpen r).measurableSet a e v G hw
  rw [native_swap_preimage_openHalfDisc] at hweak
  obtain ⟨w, hae, _, hwC1, _⟩ := hgain
    (nativeSchauderVectorInB1Coordinates 0 e) (fun y => v (coordinateSwap y))
    (fun y => coordinateSwap (G (coordinateSwap y))) B hB Ce
    (fun y _ => native_schauder_swap_vector_bound 0 e B heB y)
    ((native_schauder_swap_vector_holder 0 e Ce α he).holderOnWith _) hweak ht
  have hmap : MapsTo coordinateSwap (closedHalfDisc (r / 2))
      (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc (r / 2)) := by
    intro x hx
    exact (Set.ext_iff.mp (native_swap_preimage_B1_closedHalfDisc (r / 2)) x).mpr hx
  have hcw : ContDiffOn ℝ 1 (fun x => w (coordinateSwap x)) (closedHalfDisc (r / 2)) :=
    hwC1.comp coordinateSwap.contDiff.contDiffOn hmap
  have hmp := coordinateSwap.measurePreserving.restrict_preimage
    (show MeasurableSet (halfDisc (r / 2)) from Metric.isOpen_ball.measurableSet.inter
      ((isOpen_lt continuous_const (EuclideanSpace.proj (1 : Fin 2)).continuous).measurableSet))
  rw [native_swap_preimage_B1_halfDisc] at hmp
  have heq : (fun x => w (coordinateSwap x)) =ᵐ[volume.restrict (openHalfDisc (r / 2))] v := by
    have hh := hmp.quasiMeasurePreserving.ae hae
    filter_upwards [hh] with x hx
    simpa only [coordinateSwap_involutive] using hx
  exact native_scalar_C1_gain_same_function (r / 2) (r / 4) (by linarith) v
    (fun x => w (coordinateSwap x)) (hv.mono (closedHalfDisc_mono (by linarith))) hcw heq

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
