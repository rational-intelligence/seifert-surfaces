import NativeH1SubsetRestriction
import NativeFlatTraceLinearPullback
set_option maxHeartbeats 5000000
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak.BoundaryContinuation
open SeifertSurfaces.AppendixACoordinates BoundaryPotentialLower

lemma native_weak_divergence_restrict (U V : Set E2) (hVU : V ⊆ U)
    (a : E2 → Mat2) (e : E2 → E2) (v : E2 → ℝ) (dv : E2 → E2)
    (hw : WeakDivergenceWithData U a e (fun _ => 0) v dv) :
    WeakDivergenceWithData V a e (fun _ => 0) v dv := by
  refine ⟨h1_restrict_subset U V hVU v dv hw.1,?_⟩
  intro psi hs hc ht
  obtain ⟨hi1,hi2,heq⟩ := hw.2 psi hs hc (ht.trans hVU)
  refine ⟨hi1.mono_set hVU,hi2.mono_set hVU,?_⟩
  have hz (x : E2) (hx : x ∉ V) : planarGradient psi x = 0 :=
    planarGradient_eq_zero_off_support psi (fun hh => hx (ht hh))
  have hiU1 : (∫ y in U, inner ℝ (matrixAction (a y) (dv y)) (planarGradient psi y)) =
      ∫ y, inner ℝ (matrixAction (a y) (dv y)) (planarGradient psi y) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by rw [hz y (fun hh => hy (hVU hh)),inner_zero_right])
  have hiV1 : (∫ y in V, inner ℝ (matrixAction (a y) (dv y)) (planarGradient psi y)) =
      ∫ y, inner ℝ (matrixAction (a y) (dv y)) (planarGradient psi y) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by rw [hz y hy,inner_zero_right])
  have hiU2 : (∫ y in U, inner ℝ (e y) (planarGradient psi y)+(0:ℝ)*psi y) =
      ∫ y, inner ℝ (e y) (planarGradient psi y)+(0:ℝ)*psi y :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by rw [hz y (fun hh => hy (hVU hh)),inner_zero_right]; ring)
  have hiV2 : (∫ y in V, inner ℝ (e y) (planarGradient psi y)+(0:ℝ)*psi y) =
      ∫ y, inner ℝ (e y) (planarGradient psi y)+(0:ℝ)*psi y :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by rw [hz y hy,inner_zero_right]; ring)
  rw [hiV1,hiV2]
  rwa [hiU1,hiU2] at heq

lemma native_flat_trace_restrict (r rho : ℝ) (hrho : 0 < rho) (hrr : rho ≤ r)
    (v : E2 → ℝ) (dv : E2 → E2) (ht : FlatZeroTrace r v dv) : FlatZeroTrace rho v dv := by
  have hm : MapsTo (ContinuousLinearEquiv.refl ℝ E2) (disc rho) (disc r) := Metric.ball_subset_ball hrr
  have hh := flat_trace_linear_pullback r rho hrho (ContinuousLinearEquiv.refl ℝ E2) 1 (by norm_num)
    (fun _ => by simp) hm v dv ht
  have he : (ContinuousLinearEquiv.refl ℝ E2).toContinuousLinearMap = ContinuousLinearMap.id ℝ E2 := by ext1 x; rfl
  simpa only [ContinuousLinearEquiv.refl_apply,he,ContinuousLinearMap.adjoint_id,ContinuousLinearMap.id_apply] using hh

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak.BoundaryContinuation
