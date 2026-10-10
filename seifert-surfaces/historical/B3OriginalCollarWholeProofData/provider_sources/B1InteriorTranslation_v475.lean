import B1InteriorPositiveExistence_v475
import B1InteriorFixedRadiusBounds_v475
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Literal first derivatives under translation of the independent variable. -/
theorem native_fderiv_translate_v475 (f : E2 → ℝ) (q x : E2)
    (hf : DifferentiableAt ℝ f (x+q)) :
    fderiv ℝ (fun y => f (y+q)) x = fderiv ℝ f (x+q) := by
  have ht : HasFDerivAt (fun y : E2 => y+q) (ContinuousLinearMap.id ℝ E2) x := by
    simpa using (hasFDerivAt_id x).add_const q
  convert (hf.hasFDerivAt.comp x ht).fderiv using 1 <;> simp [Function.comp_def]

/-- Literal planar gradient under translation. -/
theorem native_planar_gradient_translate_v475 (u : E2 → ℝ) (q x : E2)
    (hu : DifferentiableAt ℝ u (x+q)) :
    planarGradient (fun y => u (y+q)) x = planarGradient u (x+q) := by
  unfold planarGradient
  rw [native_fderiv_translate_v475 u q x hu]

/-- Translation preserves the complete classical operator, including drift
and the zeroth-order coefficient. -/
theorem native_classical_translate_v475
    (O : Set E2) (hO : IsOpen O)
    (a : E2 → Mat2) (b : E2 → E2) (c u : E2 → ℝ)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) O)
    (hu : ContDiffOn ℝ ∞ u O) (q x : E2) (hx : x+q ∈ O) :
    classicalL (fun y => a (y+q)) (fun y => b (y+q)) (fun y => c (y+q))
      (fun y => u (y+q)) x = classicalL a b c u (x+q) := by
  let v := fun y => u (y+q)
  have hux : DifferentiableAt ℝ u (x+q) :=
    ((hu _ hx).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  have hg : ContDiffOn ℝ ∞ (planarGradient u) O := by
    unfold planarGradient
    apply ContDiffOn.sum
    intro i hi
    exact ((hu.fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const).smul_const _
  have hf (i : Fin 2) : DifferentiableAt ℝ
      (fun y => matrixAction (a y) (planarGradient u y) i) (x+q) := by
    change DifferentiableAt ℝ (fun y => ∑ j : Fin 2, a y i j * planarGradient u y j) _
    apply DifferentiableAt.fun_sum
    intro j hj
    exact (((ha i j _ hx).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)).mul
      ((EuclideanSpace.proj (𝕜 := ℝ) j).differentiableAt.comp _
        (((hg _ hx).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)))
  have he (i : Fin 2) :
      (fun y => matrixAction (a (y+q)) (planarGradient v y) i) =ᶠ[𝓝 x]
        (fun y => matrixAction (a (y+q)) (planarGradient u (y+q)) i) := by
    have hn : ∀ᶠ y in 𝓝 x, y+q ∈ O :=
      (continuous_id.add continuous_const).continuousAt.preimage_mem_nhds (hO.mem_nhds hx)
    filter_upwards [hn] with y hy
    rw [native_planar_gradient_translate_v475 u q y
      (((hu _ hy).contDiffAt (hO.mem_nhds hy)).differentiableAt (by simp))]
  unfold classicalL
  change (∑ i, fderiv ℝ (fun y => matrixAction (a (y+q)) (planarGradient v y) i) x
    (coordinateVector 2 i)) + _ + _ = _
  have hd (i : Fin 2) : fderiv ℝ (fun y => matrixAction (a (y+q)) (planarGradient v y) i) x =
      fderiv ℝ (fun y => matrixAction (a y) (planarGradient u y) i) (x+q) := by
    rw [(he i).fderiv_eq (𝕜 := ℝ)]
    exact native_fderiv_translate_v475 _ q x (hf i)
  simp_rw [hd]
  rw [native_planar_gradient_translate_v475 u q x hux]

#print axioms native_classical_translate_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
