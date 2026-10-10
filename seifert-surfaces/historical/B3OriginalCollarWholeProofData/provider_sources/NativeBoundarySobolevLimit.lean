import NativeBoundaryUniformEnergy
import NativeBoundaryZeroTraceQuotientPackage
import NativeBoundaryTangentialDerivative

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization
open SeifertSurfaces.QuasilinearProviderBridge
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak.BoundaryContinuation

theorem uniform_energy_native_zero_trace_centered_linear_solutions
    (c : E2) (hcf : c 0 = 0) (ρ κ M L : ℝ)
    (hρ : 0 < ρ) (hκ : 0 < κ) (hM : 1 ≤ M) (hL : 0 ≤ L) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (C : LinearizedCoefficients) (v : E2 → ℝ),
      ContDiffOn ℝ 1 v (Metric.closedBall c ρ ∩ {x : E2 | 0 ≤ x 0}) →
      (∀ x ∈ Metric.ball c ρ ∩ {x : E2 | x 0 = 0}, v x = 0) →
      CoefficientBounds (Metric.ball c ρ ∩ {x : E2 | 0 < x 0}) C κ M →
      CoefficientMeasurableOn (Metric.ball c ρ ∩ {x : E2 | 0 < x 0}) C →
      LinearWeakEquation (Metric.ball c ρ ∩ {x : E2 | 0 < x 0}) C v (planarGradient v) →
      (∀ x ∈ Metric.closedBall c ρ ∩ {x : E2 | 0 ≤ x 0}, |v x| ≤ L) →
      ContDiffOn ℝ 1 (nativeOddExtension (fun x => v (x + c))) (Metric.ball 0 ρ) ∧
      MemLp (planarGradient (nativeOddExtension (fun x => v (x + c)))) 2
        (volume.restrict (Metric.ball 0 (ρ / 4))) ∧
      (∫ x in Metric.ball 0 (ρ / 4), ‖planarGradient (nativeOddExtension (fun x => v (x + c))) x‖ ^ 2) ≤ E := by
  obtain ⟨E, hE, he⟩ := uniform_energy_native_zero_trace_linear_solutions ρ κ M L hρ hκ hM hL
  refine ⟨E, hE, ?_⟩
  intro C v hv hz hb hm hw hvalue
  let U := Metric.ball c ρ ∩ {x : E2 | 0 < x 0}
  have hU : IsOpen U := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (0 : Fin 2)).continuous)
  have hpre := native_flat_translation_halfDisc c hcf ρ
  have hmap : MapsTo (fun x : E2 => x + c) (closedHalfDisc ρ)
      (Metric.closedBall c ρ ∩ {x : E2 | 0 ≤ x 0}) := by
    intro x hx
    refine ⟨?_, ?_⟩
    · simpa only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_right, sub_zero] using hx.1
    · simpa only [mem_ofPred_eq, PiLp.add_apply, hcf, add_zero] using hx.2
  have hvc : ContDiffOn ℝ 1 (fun x => v (x + c)) (closedHalfDisc ρ) :=
    hv.comp (contDiff_id.add contDiff_const).contDiffOn hmap
  have hzc : ∀ x ∈ flatBoundary ρ, v (x + c) = 0 := by
    intro x hx
    apply hz
    refine ⟨?_, ?_⟩
    · simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero] using hx.1
    · simpa only [mem_ofPred_eq, PiLp.add_apply, hcf, add_zero] using hx.2
  obtain ⟨hbc, hmc⟩ := native_linear_coefficients_translation U hU.measurableSet c C κ M hb hm
  have hwc := native_linear_weak_translation U hU.measurableSet c C v (planarGradient v) hw
  rw [show (fun x : E2 => x + c) ⁻¹' U = openHalfDisc ρ from hpre.1] at hbc hmc hwc
  have hgrad : (fun x => planarGradient v (x + c)) = planarGradient (fun x => v (x + c)) := by
    funext x
    exact (planar_gradient_translation v c x).symm
  rw [hgrad] at hwc
  exact he (translateLinearizedCoefficients C c) (fun x => v (x + c)) hvc hzc hbc hmc hwc
    (fun x hx => hvalue _ (hmap hx))

theorem native_memW1p_of_bounded_classical_energy_limit
    (B : Set E2) (hB : IsOpen B) (hBbd : Bornology.IsBounded B)
    (f : E2 → ℝ) (fseq : ℕ → E2 → ℝ) (L E : ℝ) (hE : 0 ≤ E)
    (hC1 : ∀ n, ContDiffOn ℝ 1 (fseq n) B)
    (hG : ∀ n, MemLp (planarGradient (fseq n)) 2 (volume.restrict B))
    (henergy : ∀ n, (∫ x in B, ‖planarGradient (fseq n) x‖ ^ 2) ≤ E)
    (hbound : ∀ n, ∀ x ∈ B, |fseq n x| ≤ L)
    (hlimit : ∀ x ∈ B, Tendsto (fun n => fseq n x) atTop (𝓝 (f x))) :
    DeGiorgi.MemW1p 2 f B := by
  haveI : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr hBbd.measure_lt_top.ne
  have hseqm (n : ℕ) : AEStronglyMeasurable (fseq n) (volume.restrict B) :=
    (hC1 n).continuousOn.aestronglyMeasurable hB.measurableSet
  have hlimAE : ∀ᵐ x ∂volume.restrict B, Tendsto (fun n => fseq n x) atTop (𝓝 (f x)) := by
    filter_upwards [ae_restrict_mem hB.measurableSet] with x hx
    exact hlimit x hx
  have hfm := aestronglyMeasurable_of_tendsto_ae atTop hseqm hlimAE
  have hf : MemLp f 2 (volume.restrict B) := by
    apply MemLp.of_bound hfm L
    filter_upwards [ae_restrict_mem hB.measurableSet] with x hx
    exact le_of_tendsto ((hlimit x hx).abs) (Eventually.of_forall (fun n => hbound n x hx))
  apply EnergyHelpers.memW1p_of_classical_energy_limit B hB f fseq hf hC1 hG E hE henergy
  intro i φ hφ hc ht
  let dφ : E2 → ℝ := fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)
  have hdφ : Continuous dφ := (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdφc : HasCompactSupport dφ := hc.fderiv_apply (𝕜 := ℝ) _
  apply tendsto_integral_of_dominated_convergence (fun x => L * ‖dφ x‖)
  · intro n
    exact (hseqm n).mul hdφ.aestronglyMeasurable
  · exact ((hdφ.integrable_of_hasCompactSupport hdφc).integrableOn.norm).const_mul L
  · intro n
    filter_upwards [ae_restrict_mem hB.measurableSet] with x hx
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hbound n x hx) (norm_nonneg _)
  · filter_upwards [ae_restrict_mem hB.measurableSet] with x hx
    exact (hlimit x hx).mul_const (dφ x)

/-- The actual tangential derivative minus its own datum derivative has an
odd Sobolev extension across the native flat edge. The energy is derived
from the native quotient equation under the original solution state. -/
theorem C1QuasilinearDirichletSolution.local_tangential_derivative_odd_memW1p
    {ρ : ℝ} (hρ : 0 < ρ) {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (c : E2) (hc : c ∈ flatBoundary ρ) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall c (4 * r) ⊆ Metric.ball 0 ρ ∧
      DeGiorgi.MemW1p 2
        (nativeOddExtension (fun x =>
          fderivWithin ℝ u (closedHalfDisc ρ) (x + c) (coordinateVector 2 1) -
            deriv g.value ((x + c) 1))) (Metric.ball 0 (r / 2)) := by
  have hcf : c 0 = 0 := hc.2
  obtain ⟨r, κ, M, L, hr, hκ, hM, hL, houter, hfamily⟩ :=
    hsolution.uniform_zero_trace_tangential_linear_package hρ c hc
  obtain ⟨E, hE, he⟩ := uniform_energy_native_zero_trace_centered_linear_solutions c hc.2
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
  let v : ℕ → E2 → ℝ := fun n => differenceQuotient (fun x => u x - g.value (x 1)) 1 (hseq n)
  let fs : ℕ → E2 → ℝ := fun n => nativeOddExtension (fun x => v n (x + c))
  let f : E2 → ℝ := nativeOddExtension (fun x =>
    fderivWithin ℝ u (closedHalfDisc ρ) (x + c) (coordinateVector 2 1) - deriv g.value ((x + c) 1))
  have hstates (n : ℕ) :
      ContDiffOn ℝ 1 (fs n) (Metric.ball 0 (2 * r)) ∧
      MemLp (planarGradient (fs n)) 2 (volume.restrict (Metric.ball 0 (r / 2))) ∧
      (∫ x in Metric.ball 0 (r / 2), ‖planarGradient (fs n) x‖ ^ 2) ≤ E := by
    obtain ⟨hv, hz, hb, hm, hw, hvalue⟩ := hfamily (hseq n) (ne_of_gt (hpos n)) (hsmall n)
    simpa only [show 2 * r / 4 = r / 2 by ring] using he _ (v n) hv hz hb hm hw hvalue
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
    have hxOuter : ∀ y ∈ Metric.ball (0 : E2) (r / 2), y + c ∈ Metric.ball 0 ρ := by
      intro y hy
      apply houter
      change dist (y + c) c ≤ 4 * r
      have hh : dist y 0 < r / 2 := hy
      simpa only [dist_eq_norm, add_sub_cancel_right, sub_zero] using hh.le.trans (by linarith : r / 2 ≤ 4 * r)
    by_cases hn : 0 ≤ x 0
    · have hn' : 0 ≤ (x + c) 0 := by simpa only [PiLp.add_apply, hcf, add_zero] using hn
      have hl := (native_tangential_quotient_limit hsolution (x + c) (hxOuter x hx) hn').comp hright
      simpa only [fs, f, nativeOddExtension, ite_eq_left hn, v, Function.comp_def] using hl
    · have hxR := normalReflection_maps_ball (r / 2) hx
      have hn' : 0 ≤ (normalReflection x + c) 0 := by
        simp only [PiLp.add_apply, hcf, add_zero, normalReflection_zero]
        linarith [not_le.mp hn]
      have hl := (native_tangential_quotient_limit hsolution (normalReflection x + c)
        (hxOuter _ hxR) hn').comp hright
      simpa only [fs, f, nativeOddExtension, ite_eq_right hn, v, Function.comp_def] using hl.neg
  refine ⟨r, hr, houter, ?_⟩
  exact native_memW1p_of_bounded_classical_energy_limit _ Metric.isOpen_ball Metric.isBounded_ball
    f fs L E hE (fun n => (hstates n).1.mono (Metric.ball_subset_ball (by linarith)))
      (fun n => (hstates n).2.1) (fun n => (hstates n).2.2) hbound hlimit

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
