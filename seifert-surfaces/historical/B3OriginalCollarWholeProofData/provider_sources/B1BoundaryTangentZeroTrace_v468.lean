import B1NativeH1Scalar_v468
import OddH1LocalTrace
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Basic
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open ChartMetricProvider.Variational.DirectWeak
open BoundaryContinuation BoundarySupport
open ChartMetricProvider.Variational.NativeBallCapExtension
set_option maxHeartbeats 40000

/-- A zero extension of a native tangential derivative provides its own odd
H1 extension and hence every compact flat-edge H10 localization. -/
theorem native_tangent_local_zero_trace_v468
    (R q : ℝ) (hq : 0<q) (hqR : q<R) (h : E2 → ℝ)
    (hs : ContDiffOn ℝ ∞ h (halfDisc R))
    (df : E2 → E2)
    (hf : H1On (Metric.ball 0 q) (fun x => (halfDisc R).indicator (planarGradient h) x 0) df)
    (chi : E2 → ℝ) (hchi : ContDiff ℝ ∞ chi) (hc : HasCompactSupport chi)
    (ht : tsupport chi ⊆ Metric.ball 0 q) :
    H10On (halfDisc q) (fun x => chi x*planarGradient h x 0)
      (cutoffGradient chi (fun x => planarGradient h x 0)
        (planarGradient (fun x => planarGradient h x 0))) := by
  classical
  let f : E2 → ℝ := fun x => (halfDisc R).indicator (planarGradient h) x 0
  let A : E2 ≃ₗᵢ[ℝ] E2 := LinearIsometryEquiv.piLpCongrRight 2
    (fun i : Fin 2 => if i = 1 then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)
  let P : E2 ≃L[ℝ] E2 := A.toContinuousLinearEquiv
  have hP (x : E2) : P x=reflect x := by
    ext i
    fin_cases i <;> simp [P,A,reflect]
  have hpre : P ⁻¹' Metric.ball (0:E2) q=Metric.ball 0 q := by
    ext x
    simp only [mem_preimage,Metric.mem_ball,dist_zero_right]
    change ‖A x‖<q ↔ ‖x‖<q
    rw [A.norm_map]
  have hpull := linear_h1_pullback (Metric.ball 0 q) P f df hf
  rw [hpre] at hpull
  have hneg := native_h1_const_mul_v468 _ _ _ hpull (-1)
  have hsum := native_H1_sum _ _ _ _ _ hf hneg
  let odd : E2 → ℝ := fun x => f x-f (reflect x)
  let dodd : E2 → E2 := fun x => df x-P.toContinuousLinearMap.adjoint (df (reflect x))
  have hoddH : H1On (Metric.ball 0 q) odd dodd := by
    convert hsum using 1 <;> funext x <;> simp only [odd,dodd,hP,neg_one_mul,neg_one_smul,sub_eq_add_neg]
    all_goals rfl
  have hodds : (fun x => odd (reflect x)) =ᵐ[volume.restrict (Metric.ball 0 q)] (fun x => -odd x) := by
    apply Eventually.of_forall
    intro x
    dsimp [odd]
    have hr : reflect (reflect x)=x := by
      ext i
      fin_cases i <;> simp [reflect]
    rw [hr]
    ring
  have hU : IsOpen (halfDisc q) := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)
  have hsub : halfDisc q ⊆ halfDisc R :=
    fun x hx => ⟨Metric.ball_subset_ball hqR.le hx.1,hx.2⟩
  let v : E2 → ℝ := fun x => planarGradient h x 0
  have hval : odd =ᵐ[volume.restrict (halfDisc q)] v := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    have hneg : reflect x∉halfDisc R := by
      intro hn
      have hh := hn.2
      change 0 < -x 1 at hh
      linarith [hx.2]
    simp only [odd,f,indicator_of_mem (hsub hx),indicator_of_notMem hneg,PiLp.zero_apply,sub_zero,v]
  have hhalf := h1_restrict_subset (Metric.ball 0 q) (halfDisc q) (fun x hx => hx.1) odd dodd hoddH
  have hv : ContDiffOn ℝ ∞ v (halfDisc q) := by
    have hR : IsOpen (halfDisc R) := Metric.isOpen_ball.inter
      (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)
    have he : v=fun x => fderiv ℝ h x (coordinateVector 2 0) := by
      funext x
      exact QuasilinearLocalization.Helpers.gradient_apply h x 0
    rw [he]
    exact ((hs.fderiv_of_isOpen hR (m:=∞) (by simp)).clm_apply contDiffOn_const).mono hsub
  have hgrad := native_smooth_gradient_ae_v468 _ hU odd v dodd hhalf hv hval
  have htrace := (HemisphereQ.odd_H1_cutoff_H10_native_approximation q hq odd dodd hoddH hodds
    chi hchi hc ht).1
  apply native_h10_congr_ae_v468 _ _ _ _ _ htrace
  · filter_upwards [hval] with x hx
    rw [hx]
  · filter_upwards [hval,hgrad] with x hx hg
    simp only [cutoffGradient,hx,hg]
    rfl
end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.native_tangent_local_zero_trace_v468
