import NativeBoundaryGenericTangentialSobolev

set_option autoImplicit false
set_option maxHeartbeats 50000
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization

/-- All actual native quotient inputs have common constants before the
step. Ellipticity is inherited through the actual tangential translation. -/
theorem native_closed_linear_uniform_quotient_family
    (c : E2) (hcf : c 0 = 0) (r κ M0 : ℝ) (hr : 0 < r) (hκ : 0 < κ)
    (C : LinearizedCoefficients) (v : E2 → ℝ) (α : ℝ≥0) (hα : 0 < α)
    (hv : ContDiffOn ℝ 1 v (nativeClosedBoundaryCap c (4 * r)))
    (ha : ContDiffOn ℝ 1 C.a (nativeClosedBoundaryCap c (4 * r)))
    (hd : ContDiffOn ℝ 1 C.d (nativeClosedBoundaryCap c (4 * r)))
    (hDa : ∃ A, HolderOnWith A α (fderivWithin ℝ C.a (nativeClosedBoundaryCap c (4 * r)))
      (nativeClosedBoundaryCap c (4 * r)))
    (hDd : ∃ A, HolderOnWith A α (fderivWithin ℝ C.d (nativeClosedBoundaryCap c (4 * r)))
      (nativeClosedBoundaryCap c (4 * r)))
    (hDv : ∃ A, HolderOnWith A α (fderivWithin ℝ v (nativeClosedBoundaryCap c (4 * r)))
      (nativeClosedBoundaryCap c (4 * r)))
    (hz : ∀ x ∈ Metric.ball c (4 * r) ∩ {x : E2 | x 0 = 0}, v x = 0)
    (hc : C.c = 0) (hb : C.b = 0) (hq : C.q = 0) (hf : C.f = 0)
    (hprincipal : ∀ x ∈ nativeClosedBoundaryCap c (4 * r),
      (∀ ξ : E2, κ * ‖ξ‖ ^ 2 ≤ inner ℝ (C.a x ξ) ξ) ∧ ‖C.a x‖ ≤ M0)
    (hw : LinearWeakEquation (Metric.ball c (4 * r) ∩ {x : E2 | 0 < x 0}) C v (planarGradient v)) :
    ∃ M L : ℝ, 1 ≤ M ∧ 0 ≤ L ∧ ∀ h : ℝ, h ≠ 0 → |h| < r →
      let q := differenceQuotient v 1 h
      let U := Metric.ball c (2 * r) ∩ {x : E2 | 0 < x 0}
      let D := nativeClosedLinearDifferenceCoefficients (nativeClosedBoundaryCap c (4 * r)) C v h
      ContDiffOn ℝ 1 q (nativeClosedBoundaryCap c (2 * r)) ∧
      (∀ x ∈ Metric.ball c (2 * r) ∩ {x : E2 | x 0 = 0}, q x = 0) ∧
      CoefficientBounds U D κ M ∧ CoefficientMeasurableOn U D ∧
      LinearWeakEquation U D q (planarGradient q) ∧
      (∀ x ∈ nativeClosedBoundaryCap c (2 * r), |q x| ≤ L) := by
  have hR : 2 * (2 * r) = 4 * r := by ring
  let K := nativeClosedBoundaryCap c (4 * r)
  let V := nativeClosedBoundaryCap c (2 * r)
  let Ω := Metric.ball c (4 * r) ∩ {x : E2 | 0 < x 0}
  let U := Metric.ball c (2 * r) ∩ {x : E2 | 0 < x 0}
  have hΩ : IsOpen Ω := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (0 : Fin 2)).continuous)
  have hU : IsOpen U := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (0 : Fin 2)).continuous)
  have hΩK : Ω ⊆ K := fun x hx => ⟨Metric.ball_subset_closedBall hx.1,
    by change 0 ≤ x 0; exact le_of_lt hx.2⟩
  have hUV : U ⊆ V := fun x hx => ⟨Metric.ball_subset_closedBall hx.1,
    by change 0 ≤ x 0; exact le_of_lt hx.2⟩
  have hUΩ : U ⊆ Ω := fun x hx => ⟨Metric.ball_subset_ball (by linarith) hx.1, hx.2⟩
  obtain ⟨Bd, H, hBd, hforcing⟩ := native_closed_linear_difference_forcing_uniform_holder
    c hcf (2 * r) (by positivity) C v α hα
    (by simpa only [hR, K, V] using ha)
    (by simpa only [hR, K, V] using hd)
    (by simpa only [hR, K, V] using hDa)
    (by simpa only [hR, K, V] using hDd)
    (by simpa only [hR, K, V] using hDv)
  obtain ⟨Hv, hHv⟩ := native_holder_derivative_apply_const K v α hDv (coordinateVector 2 1)
  obtain ⟨L, hL, hquot⟩ := native_tangential_quotient_holder_from_within_derivative
    c hcf (2 * r) (by positivity) v α Hv
    (by simpa only [hR, K, V] using hv)
    (by simpa only [hR, K, V] using hHv)
  let M := max (max M0 Bd) 1
  have hM : 1 ≤ M := le_max_right _ _
  refine ⟨M, L, hM, hL, ?_⟩
  intro h hne hsmall
  let D := nativeClosedLinearDifferenceCoefficients K C v h
  have hsmall2 : |h| < 2 * r := by linarith
  have hshift : MapsTo (shift 1 h) V K := by
    intro x hx
    refine ⟨?_, by change 0 ≤ shift 1 h x 0; rw [tangent_shift_normal]; exact hx.2⟩
    have hh := dist_triangle (shift 1 h x) x c
    have hdist : dist (shift 1 h x) x = |h| := by
      simp [shift, dist_eq_norm, norm_smul, QuotientHelpers.coordinate_norm]
    have hx' : dist x c ≤ 2 * r := hx.1
    change dist (shift 1 h x) c ≤ 4 * r
    linarith
  have hshiftO : MapsTo (shift 1 h) U Ω := by
    intro x hx
    refine ⟨?_, by change 0 < shift 1 h x 0; rw [tangent_shift_normal]; exact hx.2⟩
    have hh := dist_triangle (shift 1 h x) x c
    have hdist : dist (shift 1 h x) x = |h| := by
      simp [shift, dist_eq_norm, norm_smul, QuotientHelpers.coordinate_norm]
    have hx' : dist x c < 2 * r := hx.1
    change dist (shift 1 h x) c < 4 * r
    linarith
  have hdata := hforcing h hne hsmall2
  have hDb : ∀ x ∈ V, ‖D.d x‖ ≤ Bd := by
    simpa only [D, K, hR, K, V] using hdata.1
  have hDH : HolderOnWith H α D.d V := by
    simpa only [D, K, hR, K, V] using hdata.2
  have hAc : ContinuousOn D.a V := ha.continuousOn.comp
    (show ContinuousOn (shift 1 h) V by unfold shift; fun_prop) hshift
  have hbound : CoefficientBounds U D κ M := by
    refine ⟨hκ, hM, ?_, ?_⟩
    · intro x hx ξ
      exact (hprincipal _ (hshift (hUV hx))).1 ξ
    · intro x hx
      refine ⟨((hprincipal _ (hshift (hUV hx))).2).trans
        ((le_max_left M0 Bd).trans (le_max_left _ _)), ?_, ?_, ?_, ?_, ?_⟩
      · simp only [D, nativeClosedLinearDifferenceCoefficients, Pi.zero_apply, norm_zero]; linarith
      · exact (hDb x (hUV hx)).trans ((le_max_right M0 Bd).trans (le_max_left _ _))
      · simp only [D, nativeClosedLinearDifferenceCoefficients, Pi.zero_apply, norm_zero]; linarith
      · simp only [D, nativeClosedLinearDifferenceCoefficients, Pi.zero_apply, abs_zero]; linarith
      · simp only [D, nativeClosedLinearDifferenceCoefficients, Pi.zero_apply, abs_zero]; linarith
  have hmeas : CoefficientMeasurableOn U D :=
    ⟨(hAc.mono hUV).aestronglyMeasurable hU.measurableSet, by
      simpa only [D, nativeClosedLinearDifferenceCoefficients] using aestronglyMeasurable_zero,
      ((hDH.continuousOn hα).mono hUV).aestronglyMeasurable hU.measurableSet, by
      simpa only [D, nativeClosedLinearDifferenceCoefficients] using aestronglyMeasurable_zero, by
      simpa only [D, nativeClosedLinearDifferenceCoefficients] using aestronglyMeasurable_zero, by
      simpa only [D, nativeClosedLinearDifferenceCoefficients] using aestronglyMeasurable_zero⟩
  have hqC := native_tangential_cap_quotient_C1_zero_trace c (2 * r) (by positivity) v
    (by simpa only [hR, K, V] using hv)
    (by simpa only [hR, K, V] using hz) h hsmall2
  have hweak := native_closed_linear_difference_weak_equation Ω U K hΩ hU hUΩ
    (fun x hx => mem_of_superset (hΩ.mem_nhds (hUΩ hx)) hΩK)
    C v (hv.mono hΩK) hc hb hq hf hw h hne hshiftO
  refine ⟨hqC.1, hqC.2, hbound, hmeas, hweak, ?_⟩
  intro x hx
  simpa only [differenceQuotient, div_eq_mul_inv, smul_eq_mul, mul_comm, Real.norm_eq_abs] using
    (hquot h hne hsmall2).1 x hx

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
