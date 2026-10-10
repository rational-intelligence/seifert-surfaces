import NativeBoundaryLinearQuotientFamily
import NativeBoundaryLinearTangentialEquation
import NativeBoundaryDifferentiatedForcingHolder
import NativeBoundarySchauderScalarFullGain
import NativeBoundarySchauderActualWeakGradient
import NativeA5FlatTraceBridgeV471

set_option autoImplicit false
set_option maxHeartbeats 100000
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization
open SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak

/-- A genuine derivative gain for a fixed native linear boundary equation.
The Sobolev and trace inputs of the scalar estimate come from the uniform
energy of its actual tangential quotient family. -/
theorem native_linear_tangential_C1_holder_gain
    (r κ M0 : ℝ) (hr : 0 < r) (hκ : 0 < κ) (hM0 : 0 < M0)
    (C : LinearizedCoefficients) (v : E2 → ℝ) (α : ℝ≥0)
    (hα : 0 < α) (hα1 : α < 1)
    (hv : ContDiffOn ℝ 1 v (closedHalfDisc (4 * r)))
    (ha : ContDiffOn ℝ 1 C.a (closedHalfDisc (4 * r)))
    (hd : ContDiffOn ℝ 1 C.d (closedHalfDisc (4 * r)))
    (hDa : ∃ A, HolderOnWith A α (fderivWithin ℝ C.a (closedHalfDisc (4 * r)))
      (closedHalfDisc (4 * r)))
    (hDd : ∃ A, HolderOnWith A α (fderivWithin ℝ C.d (closedHalfDisc (4 * r)))
      (closedHalfDisc (4 * r)))
    (hDv : ∃ A, HolderOnWith A α (fderivWithin ℝ v (closedHalfDisc (4 * r)))
      (closedHalfDisc (4 * r)))
    (hvi : ContDiffOn ℝ 2 v (openHalfDisc (4 * r)))
    (hz : ∀ x ∈ flatBoundary (4 * r), v x = 0)
    (hc : C.c = 0) (hb : C.b = 0) (hq : C.q = 0) (hf : C.f = 0)
    (hprincipal : ∀ x ∈ closedHalfDisc (4 * r),
      (∀ ξ : E2, κ * ‖ξ‖ ^ 2 ≤ inner ℝ (C.a x ξ) ξ) ∧ ‖C.a x‖ ≤ M0)
    (hw : LinearWeakEquation (openHalfDisc (4 * r)) C v (planarGradient v)) :
    let t := fun x => fderivWithin ℝ v (closedHalfDisc (4 * r)) x (coordinateVector 2 1)
    ContDiffOn ℝ 1 t (closedHalfDisc (r / 32)) ∧
      ∃ H, HolderOnWith H α (fderivWithin ℝ t (closedHalfDisc (r / 32)))
        (closedHalfDisc (r / 32)) := by
  let K := closedHalfDisc (4 * r)
  let U := openHalfDisc (4 * r)
  let s := r / 8
  let t := fun x => fderivWithin ℝ v K x (coordinateVector 2 1)
  let D := nativeClosedDifferentiatedLinearCoefficients K C v
  have hs : 0 < s := by dsimp [s]; positivity
  have hUK : U ⊆ K := openHalfDisc_subset_closedHalfDisc _
  have hU : IsOpen U := openHalfDisc_isOpen _
  have hsmall : openHalfDisc s ⊆ U := fun x hx =>
    ⟨Metric.ball_subset_ball (by dsimp [s]; linarith) hx.1, hx.2⟩
  have htwo : openHalfDisc (2 * s) ⊆ U := fun x hx =>
    ⟨Metric.ball_subset_ball (by dsimp [s]; linarith) hx.1, hx.2⟩
  have hcap : closedHalfDisc (2 * s) ⊆ K :=
    closedHalfDisc_mono (by dsimp [s]; linarith)
  obtain ⟨M, L, hM, hL, hfamily⟩ := native_closed_linear_uniform_quotient_family
    0 (by simp) r κ M0 hr hκ C v α hα hv ha hd hDa hDd hDv hz hc hb hq hf hprincipal hw
  have hodd : DeGiorgi.MemW1p 2 (nativeOddExtension t) (Metric.ball 0 (r / 2)) := by
    have hh := native_tangential_cap_derivative_odd_memW1p_of_uniform_family
      0 (by simp) r κ M L hr hκ hM hL v hv
      (fun h => nativeClosedLinearDifferenceCoefficients K C v h) hfamily
    simpa only [add_zero, t, K, nativeClosedBoundaryCap, closedHalfDisc] using hh
  have hoddSmall : DeGiorgi.MemW1p 2 (nativeOddExtension t) (Metric.ball 0 (2 * s)) :=
    (hodd.someWitness.restrict Metric.isOpen_ball
      (Metric.ball_subset_ball (by dsimp [s]; linarith))).memW1p
  obtain ⟨H0, hH0⟩ := native_holder_derivative_apply_const K v α hDv (coordinateVector 2 1)
  have htHolder : HolderOnWith H0 α t (closedHalfDisc (2 * s)) := hH0.mono hcap
  have htzero : ∀ x ∈ flatBoundary (2 * s), t x = 0 := by
    intro x hx
    exact native_tangential_cap_derivative_zero_trace 0 (4 * r) v hv hz x
      (Metric.ball_subset_ball (by dsimp [s]; linarith) hx.1) hx.2
  have hdt := native_closed_tangential_derivative_linear_weak U K hU
    (fun x hx => mem_of_superset (hU.mem_nhds hx) hUK) C v
    (ha.mono hUK) (hd.mono hUK) hvi hc hb hq hf hw
  have htC1 : ContDiffOn ℝ 1 t U := hdt.1
  have htTrace := (native_flat_zero_trace_of_odd_H1_holder s hs t H0 α hα hα1
    (htC1.mono htwo) htHolder htzero hoddSmall).2
  have htSob : DeGiorgi.MemW1p 2 t (openHalfDisc s) := by
    have ho := hodd.someWitness.restrict (openHalfDisc_isOpen s) (fun x hx =>
      Metric.ball_subset_ball (by dsimp [s]; linarith) hx.1)
    apply native_memW1p_congr _ (openHalfDisc_isOpen s).measurableSet
      (nativeOddExtension t) t ?_ ho.memW1p
    intro x hx
    exact if_pos (le_of_lt hx.2)
  obtain ⟨hV, hVEq⟩ := native_memW1pWitness_actual_classical_gradient (openHalfDisc s)
    (openHalfDisc_isOpen s) t (htC1.mono hsmall) htSob.someWitness
  obtain ⟨HA, A, hAEq, hAH, hAb⟩ := native_C1_principal_matrix_extension
    0 (by simp) (4 * r) κ M0 (by positivity) C.a α hα1.le ha hprincipal
  obtain ⟨B, HE, hB, e, heEq, heH, heB⟩ := native_differentiated_forcing_holder_extension
    0 (by simp) (4 * r) (by positivity) C.a C.d v α hα hDa hDd hDv
  have hDeq : EqOn e (fun x => -D.d x) K := heEq
  have hDc : ContinuousOn D.d K := by
    have hec : ContinuousOn (fun x => -e x) K := (heH.continuous hα).continuousOn.neg
    apply hec.congr
    intro x hx
    change D.d x = -e x
    rw [hDeq hx, neg_neg]
  have hdLp : MemLp D.d 2 (volume.restrict (openHalfDisc s)) :=
    (native_continuous_closed_cap_memLp 0 (4 * r) D.d hDc).mono_measure
      (Measure.restrict_mono hsmall le_rfl)
  have htweak : LinearWeakEquation (openHalfDisc s) D t hV.weakGrad := by
    rw [hVEq]
    exact native_linear_weak_restrict U (openHalfDisc s) (openHalfDisc_isOpen s)
      hsmall D t (planarGradient t) hdt.2
  have hwa := native_zero_source_linear_to_weak_divergence (openHalfDisc s)
    (openHalfDisc_isOpen s).measurableSet D (fun x => nativeMatrixOfCLM (C.a x)) t hV
    rfl rfl rfl rfl (fun x _ => nativeMatrixOfCLM_toEuclideanCLM (C.a x)) hdLp htweak
  rw [hVEq] at hwa
  have hwae : WeakDivergenceWithData (openHalfDisc s) A e (fun _ => 0) t (planarGradient t) :=
    native_zero_source_weak_divergence_coefficient_congr (openHalfDisc s)
      (openHalfDisc_isOpen s).measurableSet _ A _ e t _
      (fun x hx => hAEq (hUK (hsmall hx))) (fun x hx => hDeq (hUK (hsmall hx))) hwa
  have hgain := native_zero_source_boundary_C1_holder_gain s hs α hα hα1 A κ M0 hκ hM0
    hAb HA hAH e B hB HE heB heH t (planarGradient t)
    (htHolder.continuousOn hα |>.mono (closedHalfDisc_mono (by linarith))) hwae htTrace
  have hrad : s / 4 = r / 32 := by dsimp [s]; ring
  rw [hrad] at hgain
  exact ⟨hgain.1, native_clm_holder_of_coordinate_evaluations _ _ α hgain.2⟩

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
