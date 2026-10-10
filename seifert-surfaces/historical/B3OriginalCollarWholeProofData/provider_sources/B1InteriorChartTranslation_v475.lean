import B1InteriorCenteredChart_v475
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

theorem native_vector_fderiv_translate_v475 (f : E2 → E2) (q x : E2)
    (hf : DifferentiableAt ℝ f (x+q)) :
    fderiv ℝ (fun y => f (y+q)) x = fderiv ℝ f (x+q) := by
  have ht : HasFDerivAt (fun y : E2 => y+q) (ContinuousLinearMap.id ℝ E2) x := by
    simpa using (hasFDerivAt_id x).add_const q
  convert (hf.hasFDerivAt.comp x ht).fderiv using 1 <;> simp [Function.comp_def]

/-- Translate the source of a constructed interior chart, preserving its
literal density leading term and density drift. -/
theorem native_interior_chart_translate_v475
    (F : NativeInteriorChart_v475) (q : E2)
    (a : E2 → Mat2) (b : E2 → E2)
    (hdensity : ∀ z ∈ F.chart.target,
      densityLeading (fun x => a (x+q)) F.chart (F.chart.symm z) = 1)
    (hbb : BoundedOn (F.bhat (fun x => b (x+q))) F.chart.target) :
    ∃ G : NativeInteriorChart_v475,
      G.chart.source = (fun x => x-q) ⁻¹' F.chart.source ∧
      G.chart.target = F.chart.target ∧
      (∀ z, G.chart.symm z = F.chart.symm z+q) ∧
      BoundedOn (G.bhat b) G.chart.target ∧
      (∀ z ∈ G.chart.target, densityLeading a G.chart (G.chart.symm z) = 1) := by
  classical
  let S := (fun x : E2 => x-q) ⁻¹' F.chart.source
  have hS : IsOpen S := F.source_open.preimage (continuous_id.sub continuous_const)
  let χ : PartialHomeomorph E2 E2 :=
    { toFun := fun x => F.chart (x-q)
      invFun := fun z => F.chart.symm z+q
      source := S
      target := F.chart.target
      map_source' := fun x hx => F.chart.map_source hx
      map_target' := fun z hz => by
        change F.chart.symm z+q-q ∈ F.chart.source
        simpa only [add_sub_cancel_right] using F.chart.map_target hz
      left_inv' := fun x hx => by
        change F.chart.symm (F.chart (x-q))+q=x
        rw [F.chart.left_inv hx,sub_add_cancel]
      right_inv' := fun z hz => by
        change F.chart (F.chart.symm z+q-q)=z
        rw [add_sub_cancel_right,F.chart.right_inv hz]
      continuousOn_toFun := F.chart.continuousOn.comp
        (continuous_id.sub continuous_const).continuousOn (fun x hx => hx)
      continuousOn_invFun := F.chart.continuousOn_symm.add continuousOn_const }
  have hjac (x : E2) (hx : x ∈ S) : jacobian χ x = jacobian F.chart (x-q) := by
    unfold jacobian
    change (fun i j => (fderiv ℝ (fun y => F.chart (y-q)) x (coordinateVector 2 j)) i) = _
    have hf : DifferentiableAt ℝ F.chart (x-q) :=
      ((F.forward_C1 _ hx).contDiffAt (F.source_open.mem_nhds hx)).differentiableAt (by simp)
    simpa only [sub_eq_add_neg] using congrArg
      (fun L : E2 →L[ℝ] E2 => fun i j => (L (coordinateVector 2 j)) i)
      (native_vector_fderiv_translate_v475 F.chart (-q) x (by simpa only [sub_eq_add_neg] using hf))
  let G : NativeInteriorChart_v475 :=
    { chart := χ
      source_open := hS
      target_open := F.target_open
      forward_C1 := F.forward_C1.comp (contDiff_id.sub contDiff_const).contDiffOn (fun x hx => hx)
      inverse_C1 := F.inverse_C1.add contDiffOn_const
      forward_det := fun x hx => by rw [hjac x hx]; exact F.forward_det _ hx }
  have hbG (z : E2) (hz : z ∈ G.chart.target) :
      G.bhat b z = F.bhat (fun x => b (x+q)) z := by
    unfold NativeInteriorChart_v475.bhat densityDrift
    rw [hjac _ (G.chart.map_target hz)]
    change |Matrix.det (jacobian F.chart (F.chart.symm z+q-q))|⁻¹ •
      matrixAction (jacobian F.chart (F.chart.symm z+q-q)) (b (F.chart.symm z+q)) = _
    rw [add_sub_cancel_right]
  obtain ⟨M,hM,hbound⟩ := hbb
  refine ⟨G,rfl,rfl,fun z => rfl,⟨M,hM,fun z hz => ?_⟩,?_⟩
  · rw [hbG z hz]
    exact hbound z hz
  · intro z hz
    unfold densityLeading
    rw [hjac _ (G.chart.map_target hz)]
    change |Matrix.det (jacobian F.chart (F.chart.symm z+q-q))|⁻¹ •
      (jacobian F.chart (F.chart.symm z+q-q)*a (F.chart.symm z+q)*
        (jacobian F.chart (F.chart.symm z+q-q)).transpose)=1
    rw [add_sub_cancel_right]
    exact hdensity z hz

#print axioms native_interior_chart_translate_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
