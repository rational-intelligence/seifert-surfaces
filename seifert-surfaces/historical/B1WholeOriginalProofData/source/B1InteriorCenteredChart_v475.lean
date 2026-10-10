import B1InteriorMetricChart_v475
import B1InteriorChartContinuation_v475
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem native_interior_drift_continuous_v475
    (F : NativeInteriorChart_v475) (b : E2 → E2)
    (hb : ContinuousOn b F.chart.source) :
    ContinuousOn (F.bhat b) F.chart.target := by
  have hj (i j : Fin 2) : ContinuousOn (fun x => jacobian F.chart x i j) F.chart.source :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp_continuousOn
      ((F.forward_C1.continuousOn_fderiv_of_isOpen F.source_open (by simp)).clm_apply continuousOn_const)
  have hdet : ContinuousOn (fun x => Matrix.det (jacobian F.chart x)) F.chart.source := by
    simp only [Matrix.det_fin_two]
    exact ((hj 0 0).mul (hj 1 1)).sub ((hj 0 1).mul (hj 1 0))
  have hact : ContinuousOn (fun x => matrixAction (jacobian F.chart x) (b x)) F.chart.source := by
    apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp_continuousOn
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_finsetSum
    intro j hjj
    exact (hj i j).mul ((EuclideanSpace.proj (𝕜 := ℝ) j).continuous.comp_continuousOn hb)
  exact ((hdet.abs.inv₀ (fun x hx => abs_ne_zero.mpr (F.forward_det x hx))).smul hact).comp
    F.chart.continuousOn_symm (fun z hz => F.chart.map_target hz)

/-- Restrict an interior chart to a compact coordinate ball around its actual
working point and translate its target center to zero.  The drift bound is
obtained from compactness, without requiring any extra chart smoothness. -/
theorem native_interior_centered_chart_v475
    (F : NativeInteriorChart_v475) (p : E2) (hp : p ∈ F.chart.source)
    (a : E2 → Mat2) (b : E2 → E2)
    (hb : ContinuousOn b F.chart.source)
    (hdensity : ∀ z ∈ F.chart.target, densityLeading a F.chart (F.chart.symm z) = 1) :
    ∃ G : NativeInteriorChart_v475, ∃ r : ℝ,
      0 < r ∧ p ∈ G.chart.source ∧ G.chart.source ⊆ F.chart.source ∧
      G.chart.target = disc r ∧ BoundedOn (G.bhat b) G.chart.target ∧
      (∀ z ∈ G.chart.target, densityLeading a G.chart (G.chart.symm z) = 1) := by
  classical
  let z₀ := F.chart p
  have hz₀ : z₀ ∈ F.chart.target := F.chart.map_source hp
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp F.target_open z₀ hz₀
  let r := ε/2
  have hr : 0 < r := half_pos hε
  have hKT : Metric.closedBall z₀ r ⊆ F.chart.target := by
    intro z hz
    apply hball
    exact lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (by dsimp [r]; linarith)
  let S := F.chart.source ∩ F.chart ⁻¹' Metric.ball z₀ r
  have hS : IsOpen S := F.chart.continuousOn.isOpen_inter_preimage F.source_open Metric.isOpen_ball
  have hpS : p ∈ S := ⟨hp, by simp [z₀,hr]⟩
  have hshift (z : E2) : z ∈ disc r ↔ z+z₀ ∈ Metric.ball z₀ r := by
    simp only [disc,Metric.mem_ball,dist_eq_norm]
    simp
  let χ : PartialHomeomorph E2 E2 :=
    { toFun := fun x => F.chart x-z₀
      invFun := fun z => F.chart.symm (z+z₀)
      source := S
      target := disc r
      map_source' := by
        intro x hx
        rw [hshift]
        simpa only [sub_add_cancel] using (show F.chart x ∈ Metric.ball z₀ r from hx.2)
      map_target' := by
        intro z hz
        have hzt := hKT (Metric.ball_subset_closedBall (hshift z |>.mp hz))
        refine ⟨F.chart.map_target hzt,?_⟩
        change F.chart (F.chart.symm (z+z₀)) ∈ Metric.ball z₀ r
        rw [F.chart.right_inv hzt]
        exact (hshift z).mp hz
      left_inv' := by
        intro x hx
        simpa only [sub_add_cancel] using F.chart.left_inv hx.1
      right_inv' := by
        intro z hz
        have hzt := hKT (Metric.ball_subset_closedBall ((hshift z).mp hz))
        simp only [F.chart.right_inv hzt,add_sub_cancel_right]
      continuousOn_toFun := (F.chart.continuousOn.sub continuousOn_const).mono inter_subset_left
      continuousOn_invFun := F.chart.continuousOn_symm.comp
        (continuous_id.add continuous_const).continuousOn
        (fun z hz => hKT (Metric.ball_subset_closedBall ((hshift z).mp hz))) }
  have hjac (x : E2) (hx : x ∈ S) : jacobian χ x = jacobian F.chart x := by
    unfold jacobian
    change (fun i j => (fderiv ℝ (fun y => F.chart y-z₀) x (coordinateVector 2 j)) i) = _
    rw [fderiv_sub_const]
  let G : NativeInteriorChart_v475 :=
    { chart := χ
      source_open := hS
      target_open := Metric.isOpen_ball
      forward_C1 := (F.forward_C1.sub contDiffOn_const).mono inter_subset_left
      inverse_C1 := F.inverse_C1.comp (contDiff_id.add contDiff_const).contDiffOn
        (fun z hz => hKT (Metric.ball_subset_closedBall ((hshift z).mp hz)))
      forward_det := fun x hx => by rw [hjac x hx]; exact F.forward_det x hx.1 }
  have hbG (z : E2) (hz : z ∈ G.chart.target) : G.bhat b z = F.bhat b (z+z₀) := by
    unfold NativeInteriorChart_v475.bhat densityDrift
    rw [hjac _ (G.chart.map_target hz)]
    rfl
  obtain ⟨M,hM⟩ := (isCompact_closedBall z₀ r).exists_bound_of_continuousOn
    ((native_interior_drift_continuous_v475 F b hb).mono hKT)
  refine ⟨G,r,hr,hpS,inter_subset_left,rfl,⟨max M 0,le_max_right _ _,?_⟩,?_⟩
  · intro z hz
    rw [hbG z hz]
    exact (hM _ (Metric.ball_subset_closedBall ((hshift z).mp hz))).trans (le_max_left _ _)
  · intro z hz
    unfold densityLeading
    rw [hjac _ (G.chart.map_target hz)]
    exact hdensity (z+z₀) (hKT (Metric.ball_subset_closedBall ((hshift z).mp hz)))

#print axioms native_interior_centered_chart_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
