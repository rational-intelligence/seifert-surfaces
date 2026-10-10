import B1InteriorDensityTransport_v475
import B1InteriorVekuaContinuation_v475
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- The paid density law and full-disc Vekua continuation propagate a literal
open zero germ through a constructed interior isothermal chart. -/
theorem native_interior_chart_zero_continuation_v475
    (F : NativeInteriorChart_v475) (O : Set E2) (hO : IsOpen O)
    (hsrc : F.chart.source ⊆ O)
    (a : E2 → Mat2) (b : E2 → E2) (u : E2 → ℝ)
    (ha : ∀ i j, ContinuousOn (fun x => a x i j) O)
    (hb : ContinuousOn b O) (hu : ContDiffOn ℝ 1 u O)
    (heq : WeakLinearEquationOn O a b (fun _ => 0) u (planarGradient u))
    (hdensity : ∀ z ∈ F.chart.target, densityLeading a F.chart (F.chart.symm z) = 1)
    (R : ℝ) (hR : 0 < R) (htarget : F.chart.target = disc R)
    (hbb : BoundedOn (F.bhat b) F.chart.target)
    (V : Set E2) (hV : IsOpen V) (hne : V.Nonempty) (hVS : V ⊆ F.chart.source)
    (hzero : EqOn u (fun _ => 0) V) : EqOn u (fun _ => 0) F.chart.source := by
  obtain ⟨hvC1,hbcont,hweak⟩ := native_interior_density_weak_transport_v475 F O hO hsrc
    a b u ha hb hu heq hdensity
  haveI : IsFiniteMeasure (volume.restrict F.chart.target) := by
    rw [htarget]
    exact isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hbbcopy := hbb
  obtain ⟨M,hM,hbound⟩ := hbbcopy
  have hbLp : MemLp (F.bhat b) ⊤ (volume.restrict F.chart.target) :=
    MemLp.of_bound (hbcont.aestronglyMeasurable F.target_open.measurableSet) M
      ((ae_restrict_mem F.target_open.measurableSet).mono (fun z hz => hbound z hz))
  let U := F.chart.target ∩ F.chart.symm ⁻¹' V
  have hU : IsOpen U := F.chart.continuousOn_symm.isOpen_inter_preimage F.target_open hV
  have hUT : U ⊆ disc R := by rw [← htarget]; exact inter_subset_left
  have hUzero : EqOn (F.vhat u) (fun _ => 0) U := fun z hz => hzero hz.2
  obtain ⟨x,hx⟩ := hne
  have hUS : U.Nonempty := ⟨F.chart x,F.chart.map_source (hVS hx),by
    change F.chart.symm (F.chart x) ∈ V
    rwa [F.chart.left_inv (hVS hx)]⟩
  have hz := native_interior_laplace_drift_zero_continuation_v475 R hR (F.vhat u) (F.bhat b)
    (htarget ▸ hvC1) (htarget ▸ hweak) (htarget ▸ hbb) (htarget ▸ hbLp)
    U hU hUS hUT hUzero
  intro y hy
  have hh := hz (show F.chart y ∈ disc R by rw [← htarget]; exact F.chart.map_source hy)
  change u (F.chart.symm (F.chart y)) = 0 at hh
  rwa [F.chart.left_inv hy] at hh

#print axioms native_interior_chart_zero_continuation_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
