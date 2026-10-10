import NativeBoundaryToolbox
set_option maxHeartbeats 3000000
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak.BoundaryContinuation
open SeifertSurfaces.AppendixACoordinates

lemma planar_gradient_pairing (f : E2 → ℝ) (y q : E2) :
    inner ℝ (planarGradient f y) q = fderiv ℝ f y q := by
  have hq : q = q 0 • coordinateVector 2 0+q 1 • coordinateVector 2 1 := by
    ext i; fin_cases i <;> simp [coordinateVector]
  conv_rhs => rw [hq]
  rw [map_add,map_smul,map_smul]
  simp only [PiLp.inner_apply,Fin.sum_univ_two,RCLike.inner_apply,conj_trivial]
  have hg (i : Fin 2) : planarGradient f y i = fderiv ℝ f y (coordinateVector 2 i) := by
    fin_cases i <;> simp [planarGradient,coordinateVector,Fin.sum_univ_two]
  rw [hg,hg]
  simp only [smul_eq_mul]

lemma planar_gradient_linear_comp (P : E2 ≃L[ℝ] E2) (f : E2 → ℝ)
    (hf : ContDiff ℝ ∞ f) (y : E2) :
    planarGradient (fun z => f (P z)) y = P.toContinuousLinearMap.adjoint (planarGradient f (P y)) := by
  apply ext_inner_right ℝ
  intro q
  rw [planar_gradient_pairing,ContinuousLinearMap.adjoint_inner_left,planar_gradient_pairing]
  have hd := (hf.differentiable (by simp) (P y)).hasFDerivAt.comp y P.hasFDerivAt
  simp only [Function.comp_def] at hd
  rw [hd.fderiv]
  rfl

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak.BoundaryContinuation
