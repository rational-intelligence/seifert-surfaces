import B1InteriorNormalizedEquation_v475
import B1InteriorOperatorScale_v475
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- The literal determinant-normalized operator kills the same quotient on
its whole open domain.  Every coefficient comes from the constructed h. -/
theorem native_interior_normalized_classical_v475 (N : InteriorNormalizationData_v475) :
    ∀ x ∈ N.O, classicalL N.normalizedA N.normalizedB (fun _ => 0) N.v x = 0 := by
  intro x hx
  have hO := N.isOpen_O
  have hhAt : ContDiffAt ℝ ∞ N.h x := (N.smooth_h x hx).contDiffAt (hO.mem_nhds hx)
  have huAt : ContDiffAt ℝ ∞ N.u x := (N.smooth_u x hx).contDiffAt (hO.mem_nhds hx)
  have hvAt : ContDiffAt ℝ ∞ N.v x := huAt.div hhAt (N.h_positive x hx).ne'
  have haAt (i j : Fin 2) : ContDiffAt ℝ ∞ (fun y => N.a y i j) x :=
    (N.elliptic.1 i j x hx).contDiffAt (hO.mem_nhds hx)
  have hleadAt (i j : Fin 2) : ContDiffAt ℝ ∞ (fun y => N.leading y i j) x :=
    hhAt.mul (haAt i j)
  have hgrad : ContDiffAt ℝ ∞ (planarGradient N.v) x := by
    unfold planarGradient
    apply ContDiffAt.sum
    intro i hi
    exact ((hvAt.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).smul contDiffAt_const
  have hP (i : Fin 2) : DifferentiableAt ℝ
      (fun y => matrixAction (N.leading y) (planarGradient N.v y) i) x := by
    change DifferentiableAt ℝ (fun y => ∑ j : Fin 2,
      N.leading y i j * planarGradient N.v y j) x
    apply DifferentiableAt.fun_sum
    intro j hj
    exact ((hleadAt i j).differentiableAt (by simp)).mul
      ((EuclideanSpace.proj (𝕜 := ℝ) j).differentiableAt.comp x (hgrad.differentiableAt (by simp)))
  have hfactor : ContDiffAt ℝ ∞ N.factor x :=
    (native_interior_normalized_coefficients_v475 N {x} isCompact_singleton
      (convex_singleton x) (singleton_nonempty x) (singleton_subset_iff.mpr hx)).2.2.2.2
      x (mem_singleton x)
  have hsym (i j : Fin 2) : N.leading x i j = N.leading x j i := by
    change N.h x*N.a x i j = N.h x*N.a x j i
    rw [N.elliptic.2.2.2.1 x hx i j]
  have hh := native_scalar_normalized_classical_v475 N.leading N.drift N.v N.factor x
    hsym (hfactor.differentiableAt (by simp)) hP
  change classicalL N.normalizedA N.normalizedB (fun _ => 0) N.v x = _ at hh
  rw [native_interior_divide_positive_classical_v475 N x hx,mul_zero] at hh
  exact hh

#print axioms native_interior_normalized_classical_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
