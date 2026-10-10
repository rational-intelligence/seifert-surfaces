import NativeBoundaryDatumBounds
import NativeBoundaryLinearTranslation

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization

theorem native_linear_weak_congr_gradient
    (B : Set E2) (hB : MeasurableSet B) (C : LinearizedCoefficients) (v : E2 → ℝ)
    (G H : E2 → E2) (he : EqOn G H B) (hw : LinearWeakEquation B C v G) :
    LinearWeakEquation B C v H := by
  intro φ hφ hc ht
  obtain ⟨hiF, hiS, hzero⟩ := hw φ hφ hc ht
  have hae : G =ᵐ[volume.restrict B] H := by
    filter_upwards [ae_restrict_mem hB] with x hx
    exact he hx
  have hF : (fun x => inner ℝ (linearizedFlux C v G x) (planarGradient φ x)) =ᵐ[volume.restrict B]
      (fun x => inner ℝ (linearizedFlux C v H x) (planarGradient φ x)) := by
    filter_upwards [hae] with x hx
    simp only [linearizedFlux, hx]
  have hS : (fun x => linearizedSource C v G x * φ x) =ᵐ[volume.restrict B]
      (fun x => linearizedSource C v H x * φ x) := by
    filter_upwards [hae] with x hx
    simp only [linearizedSource, hx]
  refine ⟨hiF.congr hF, hiS.congr hS, ?_⟩
  exact (integral_congr_ae (hF.sub hS)).symm.trans hzero

theorem native_differenceQuotient_sub (u w : E2 → ℝ) (k : Fin 2) (h : ℝ) :
    differenceQuotient (u - w) k h = differenceQuotient u k h - differenceQuotient w k h := by
  funext x
  simp only [differenceQuotient, Pi.sub_apply]
  ring

theorem subtractDatum_coefficients_continuousOn
    (B : Set E2) (C : LinearizedCoefficients) (w : E2 → ℝ) (Gw : E2 → E2)
    (hC : coefficientsContinuousOn B C) (hw : ContinuousOn w B) (hG : ContinuousOn Gw B) :
    coefficientsContinuousOn B (subtractDatumCoefficients C w Gw) := by
  exact ⟨hC.1, hC.2.1, ((hC.1.clm_apply hG).add (hw.smul hC.2.1)).add hC.2.2.1,
    hC.2.2.2.1, hC.2.2.2.2.1,
    ((hC.2.2.2.1.clm_apply hG).add (hC.2.2.2.2.1.mul hw)).add hC.2.2.2.2.2⟩

theorem native_coefficients_measurable_of_continuousOn
    (B : Set E2) (hB : MeasurableSet B) (C : LinearizedCoefficients)
    (hC : coefficientsContinuousOn B C) : CoefficientMeasurableOn B C :=
  ⟨hC.1.aestronglyMeasurable hB, hC.2.1.aestronglyMeasurable hB,
    hC.2.2.1.aestronglyMeasurable hB, hC.2.2.2.1.aestronglyMeasurable hB,
    hC.2.2.2.2.1.aestronglyMeasurable hB, hC.2.2.2.2.2.aestronglyMeasurable hB⟩

/-- This estimate concerns the actual quotient family of the original solution
and its own datum. No quotient regularity or estimate is an input. -/
theorem C1QuasilinearDirichletSolution.uniform_zero_trace_tangential_holder
    {ρ : ℝ} (hρ : 0 < ρ) {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (c : E2) (hc : c ∈ flatBoundary ρ) :
    ∃ r δ : ℝ, ∃ K α : ℝ≥0, 0 < r ∧ 0 < δ ∧ δ < 2 * r ∧
      0 < α ∧ α < 1 ∧ Metric.closedBall c (4 * r) ⊆ Metric.ball 0 ρ ∧
      ∀ h : ℝ, h ≠ 0 → |h| < r →
        HolderOnWith K α (differenceQuotient (fun x => u x - g.value (x 1)) 1 h)
          (Metric.closedBall c δ ∩ {x : E2 | 0 ≤ x 0}) := by
  obtain ⟨r, κ, M, L, T, hr, hκ, hM, _, _, _, _, houter, hfamily⟩ :=
    hsolution.local_boundary_quotient_package hρ c hc
  obtain ⟨D, hD, hdatum⟩ := g.uniform_tangent_quotient_bounds c (4 * r) (2 * r)
    (by positivity) (by positivity) houter (by linarith)
  obtain ⟨Lu, hLu⟩ := hsolution.lipschitz_on_closedHalfDisc hρ
  let M' := M * (2 * D + 1)
  have hM' : 1 ≤ M' := by dsimp [M']; nlinarith
  have hL' : 0 ≤ (Lu : ℝ) + D := add_nonneg Lu.coe_nonneg hD
  obtain ⟨δ, K, α, hδ, hδr, hα, hα1, he⟩ :=
    uniform_holder_native_zero_trace_centered_linear_solutions c hc.2 (2 * r) κ M' ((Lu : ℝ) + D)
      (by positivity) hκ hM' hL'
  refine ⟨r, δ, K, α, hr, hδ, hδr, hα, hα1, houter, ?_⟩
  intro h hh hhr
  let B := Metric.ball c (2 * r) ∩ {x : E2 | 0 < x 0}
  let V := Metric.closedBall c (2 * r) ∩ {x : E2 | 0 ≤ x 0}
  let W := Metric.closedBall c (4 * r) ∩ {x : E2 | 0 ≤ x 0}
  let f : E2 → ℝ := fun x => g.value (x 1)
  let q := differenceQuotient u 1 h
  let d := differenceQuotient f 1 h
  let v := differenceQuotient (u - f) 1 h
  let C := averagedCoefficients Q u 1 h
  let C' := subtractDatumCoefficients C d (planarGradient d)
  obtain ⟨hqC1, hqweak, hCb, hCc, _, _⟩ := hfamily h hh hhr
  have hB : IsOpen B := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (0 : Fin 2)).continuous)
  have hVouter : V ⊆ W := fun x hx =>
    ⟨Metric.closedBall_subset_closedBall (by linarith) hx.1, hx.2⟩
  have hWclosed : W ⊆ closedHalfDisc ρ := fun x hx =>
    ⟨Metric.ball_subset_closedBall (houter hx.1), hx.2⟩
  have hWball : W ⊆ Metric.ball (0 : E2) ρ := fun x hx => houter hx.1
  have hshiftW : MapsTo (shift 1 h) V W := by
    intro x hx
    refine ⟨?_, ?_⟩
    · change dist (shift 1 h x) c ≤ 4 * r
      have hd := dist_triangle (shift 1 h x) x c
      rw [QuotientHelpers.shift_distance] at hd
      have hxD : dist x c ≤ 2 * r := hx.1
      linarith
    · simpa only [mem_ofPred_eq, tangent_shift_normal] using hx.2
  have huf : ContDiffOn ℝ 1 (u - f) W :=
    (hsolution.c1.mono hWclosed).sub ((g.smooth_extension_on_ball.mono hWball).of_le (by simp))
  have hvC1 : ContDiffOn ℝ 1 v V := by
    have heq : v = h⁻¹ • ((u - f) ∘ shift 1 h - (u - f)) := by
      funext x
      simp only [v, differenceQuotient, Pi.smul_apply, Pi.sub_apply, Function.comp_apply,
        smul_eq_mul, div_eq_mul_inv]
      ring
    rw [heq]
    exact ((huf.comp (by unfold shift; fun_prop) hshiftW).sub (huf.mono hVouter)).const_smul h⁻¹
  have hvzero : ∀ x ∈ Metric.ball c (2 * r) ∩ {x : E2 | x 0 = 0}, v x = 0 := by
    intro x hx
    have hxV : x ∈ V := ⟨Metric.ball_subset_closedBall hx.1, hx.2.ge⟩
    have hsW := hshiftW hxV
    have hxflat : x ∈ flatBoundary ρ := ⟨houter (hVouter hxV).1, hx.2⟩
    have hsflat : shift 1 h x ∈ flatBoundary ρ :=
      ⟨houter hsW.1, by simpa only [mem_ofPred_eq, tangent_shift_normal] using hx.2⟩
    simp only [v, differenceQuotient, Pi.sub_apply, f,
      hsolution.dirichlet_values x hxflat, hsolution.dirichlet_values _ hsflat, sub_self, zero_div]
  have hdC1 : ContDiffOn ℝ 1 d B := by
    have hf : ContDiffOn ℝ 1 f (Metric.ball 0 ρ) := g.smooth_extension_on_ball.of_le (by simp)
    have hBball : B ⊆ Metric.ball (0 : E2) ρ := fun x hx =>
      houter (Metric.closedBall_subset_closedBall (by linarith) (Metric.ball_subset_closedBall hx.1))
    have hsBball : MapsTo (shift 1 h) B (Metric.ball 0 ρ) := by
      intro x hx
      exact houter (hshiftW ⟨Metric.ball_subset_closedBall hx.1, show 0 ≤ x 0 from le_of_lt hx.2⟩).1
    have heq : d = h⁻¹ • (f ∘ shift 1 h - f) := by
      funext x
      simp [d, differenceQuotient, div_eq_mul_inv, mul_comm]
    rw [heq]
    exact ((hf.comp (by unfold shift; fun_prop) hsBball).sub (hf.mono hBball)).const_smul h⁻¹
  have hdcont := Helpers.gradient_continuousOn B hB d hdC1
  have hb' : CoefficientBounds B C' κ M' :=
    subtractDatum_coefficient_bounds B C κ M D hCb hD d (planarGradient d)
      (fun x hx => hdatum h hh (by linarith) x (Metric.ball_subset_closedBall hx.1))
  have hm' : CoefficientMeasurableOn B C' := native_coefficients_measurable_of_continuousOn B
    hB.measurableSet C' (subtractDatum_coefficients_continuousOn B C d (planarGradient d)
      hCc hdC1.continuousOn hdcont)
  have hveq : v = q - d := native_differenceQuotient_sub u f 1 h
  have hgradient : EqOn (planarGradient q - planarGradient d) (planarGradient v) B := by
    intro x hx
    rw [hveq]
    exact (planarGradient_sub
      ((hqC1.contDiffAt (hB.mem_nhds hx)).differentiableAt (by simp))
      ((hdC1.contDiffAt (hB.mem_nhds hx)).differentiableAt (by simp))).symm
  have hw' : LinearWeakEquation B C' v (planarGradient v) := by
    have hw := linearized_weak_equation_subtract_datum B C q d (planarGradient q)
      (planarGradient d) hqweak
    rw [← hveq] at hw
    exact native_linear_weak_congr_gradient B hB.measurableSet C' v _ _ hgradient hw
  have hvbound : ∀ x ∈ V, |v x| ≤ (Lu : ℝ) + D := by
    intro x hx
    rw [hveq]
    exact (show |q x - d x| ≤ |q x| + |d x| by simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (q x) 0 (d x)).trans (add_le_add
      (native_quotient_bound_of_lipschitz hLu 1 hh (hWclosed (hVouter hx)) (hWclosed (hshiftW hx)))
      (hdatum h hh (by linarith) x hx.1).1)
  exact he C' v hvC1 hvzero hb' hm' hw' hvbound

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
