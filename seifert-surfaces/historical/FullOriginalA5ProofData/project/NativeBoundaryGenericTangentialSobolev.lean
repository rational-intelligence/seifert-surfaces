import NativeBoundaryGenericTangentialDerivative

set_option autoImplicit false
set_option maxHeartbeats 50000
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal
namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization

/-- The uniform native quotient energy yields the odd H1 extension of the
same within tangential derivative, with no boundary extension of the solution. -/
theorem native_tangential_cap_derivative_odd_memW1p_of_uniform_family
    (c : E2) (hcf : c 0 = 0) (r κ M L : ℝ)
    (hr : 0 < r) (hκ : 0 < κ) (hM : 1 ≤ M) (hL : 0 ≤ L)
    (v0 : E2 → ℝ) (hv : ContDiffOn ℝ 1 v0 (nativeClosedBoundaryCap c (4 * r)))
    (C : ℝ → LinearizedCoefficients)
    (hfamily : ∀ h : ℝ, h ≠ 0 → |h| < r →
      let v := differenceQuotient v0 1 h
      let U := Metric.ball c (2 * r) ∩ {x : E2 | 0 < x 0}
      ContDiffOn ℝ 1 v (nativeClosedBoundaryCap c (2 * r)) ∧
      (∀ x ∈ Metric.ball c (2 * r) ∩ {x : E2 | x 0 = 0}, v x = 0) ∧
      CoefficientBounds U (C h) κ M ∧ CoefficientMeasurableOn U (C h) ∧
      LinearWeakEquation U (C h) v (planarGradient v) ∧
      (∀ x ∈ nativeClosedBoundaryCap c (2 * r), |v x| ≤ L)) :
    DeGiorgi.MemW1p 2
      (nativeOddExtension (fun x => fderivWithin ℝ v0 (nativeClosedBoundaryCap c (4 * r))
        (x + c) (coordinateVector 2 1))) (Metric.ball 0 (r / 2)) := by
  obtain ⟨E, hE, he⟩ := uniform_energy_native_zero_trace_centered_linear_solutions c hcf
    (2 * r) κ M L (by positivity) hκ hM hL
  let hseq : ℕ → ℝ := fun n => r / ((n : ℝ) + 2)
  have hpos (n : ℕ) : 0 < hseq n := by dsimp [hseq]; positivity
  have hsmall (n : ℕ) : |hseq n| < r := by
    rw [abs_of_pos (hpos n)]
    exact div_lt_self hr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hzero : Tendsto hseq atTop (𝓝 0) := by
    have ht := (tendsto_const_div_atTop_nhds_zero_nat r).comp (tendsto_add_atTop_nat 2)
    simpa [hseq, Nat.cast_add, Nat.cast_ofNat, Function.comp_def] using ht
  have hright : Tendsto hseq atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero, Eventually.of_forall hpos⟩
  let v : ℕ → E2 → ℝ := fun n => differenceQuotient v0 1 (hseq n)
  let fs : ℕ → E2 → ℝ := fun n => nativeOddExtension (fun x => v n (x + c))
  let f : E2 → ℝ := nativeOddExtension (fun x =>
    fderivWithin ℝ v0 (nativeClosedBoundaryCap c (4 * r)) (x + c) (coordinateVector 2 1))
  have hstates (n : ℕ) :
      ContDiffOn ℝ 1 (fs n) (Metric.ball 0 (2 * r)) ∧
      MemLp (planarGradient (fs n)) 2 (volume.restrict (Metric.ball 0 (r / 2))) ∧
      (∫ x in Metric.ball 0 (r / 2), ‖planarGradient (fs n) x‖ ^ 2) ≤ E := by
    obtain ⟨hv, hz, hb, hm, hw, hvalue⟩ := hfamily (hseq n) (ne_of_gt (hpos n)) (hsmall n)
    simpa only [show 2 * r / 4 = r / 2 by ring] using he (C (hseq n)) (v n) hv hz hb hm hw hvalue
  have hbound (n : ℕ) : ∀ x ∈ Metric.ball 0 (r / 2), |fs n x| ≤ L := by
    obtain ⟨_, _, _, _, _, hvalue⟩ := hfamily (hseq n) (ne_of_gt (hpos n)) (hsmall n)
    apply fun x hx => native_odd_extension_bound (2 * r) L (fun y => v n (y + c)) ?_ x
      (Metric.ball_subset_ball (by linarith) hx)
    intro y hy
    apply hvalue
    refine ⟨?_, ?_⟩
    · simpa only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_right, sub_zero] using hy.1
    · simpa only [mem_ofPred_eq, PiLp.add_apply, hcf, add_zero] using hy.2
  have hlimit : ∀ x ∈ Metric.ball 0 (r / 2), Tendsto (fun n => fs n x) atTop (𝓝 (f x)) := by
    intro x hx
    have hxOuter : ∀ y ∈ Metric.ball (0 : E2) (r / 2), y + c ∈ Metric.ball c (4 * r) := by
      intro y hy
      change dist (y + c) c < 4 * r
      have hh : dist y 0 < r / 2 := hy
      simpa only [dist_eq_norm, add_sub_cancel_right, sub_zero] using hh.trans (by linarith : r / 2 < 4 * r)
    by_cases hn : 0 ≤ x 0
    · have hn' : 0 ≤ (x + c) 0 := by simpa only [PiLp.add_apply, hcf, add_zero] using hn
      have hl := (native_tangential_cap_quotient_limit c (4 * r) v0 hv (x + c) (hxOuter x hx) hn').comp hright
      simpa only [fs, f, nativeOddExtension, ite_eq_left hn, v, Function.comp_def] using hl
    · have hxR := normalReflection_maps_ball (r / 2) hx
      have hn' : 0 ≤ (normalReflection x + c) 0 := by
        simp only [PiLp.add_apply, hcf, add_zero, normalReflection_zero]
        linarith [not_le.mp hn]
      have hl := (native_tangential_cap_quotient_limit c (4 * r) v0 hv (normalReflection x + c)
        (hxOuter _ hxR) hn').comp hright
      simpa only [fs, f, nativeOddExtension, ite_eq_right hn, v, Function.comp_def] using hl.neg
  exact native_memW1p_of_bounded_classical_energy_limit _ Metric.isOpen_ball Metric.isBounded_ball
    f fs L E hE (fun n => (hstates n).1.mono (Metric.ball_subset_ball (by linarith)))
      (fun n => (hstates n).2.1) (fun n => (hstates n).2.2) hbound hlimit


end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
