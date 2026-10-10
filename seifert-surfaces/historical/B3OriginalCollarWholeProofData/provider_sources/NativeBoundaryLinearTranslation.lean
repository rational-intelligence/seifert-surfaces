import NativeBoundaryUniformHolder
import NativeTranslation

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak.BoundaryContinuation

def translateLinearizedCoefficients (C : LinearizedCoefficients) (c : E2) : LinearizedCoefficients where
  a x := C.a (x + c)
  c x := C.c (x + c)
  d x := C.d (x + c)
  b x := C.b (x + c)
  q x := C.q (x + c)
  f x := C.f (x + c)

theorem native_linear_weak_translation
    (U : Set E2) (hU : MeasurableSet U) (c : E2)
    (C : LinearizedCoefficients) (v : E2 → ℝ) (G : E2 → E2)
    (hw : LinearWeakEquation U C v G) :
    LinearWeakEquation ((fun x : E2 => x + c) ⁻¹' U)
      (translateLinearizedCoefficients C c) (fun x => v (x + c)) (fun x => G (x + c)) := by
  intro φ hφ hc ht
  let W := (fun x : E2 => x + c) ⁻¹' U
  let ψ : E2 → ℝ := fun y => φ (y + -c)
  have hs : ContDiff ℝ ∞ ψ := hφ.comp (contDiff_id.add contDiff_const)
  have hcompact : HasCompactSupport ψ := hc.comp_homeomorph (Homeomorph.addRight (-c))
  have ht' : tsupport ψ ⊆ U := by
    intro y hy
    have hh := ht (tsupport_comp_subset_preimage φ (continuous_id.add continuous_const) hy)
    change (y + -c) + c ∈ U at hh
    simpa only [neg_add_cancel_right] using hh
  obtain ⟨hiF, hiS, heq⟩ := hw ψ hs hcompact ht'
  have hmp : MeasurePreserving (fun x : E2 => x + c) (volume.restrict W) (volume.restrict U) :=
    (measurePreserving_add_right volume c).restrict_preimage hU
  have hemb : MeasurableEmbedding (fun x : E2 => x + c) := (Homeomorph.addRight c).measurableEmbedding
  have hg (x : E2) : planarGradient ψ (x + c) = planarGradient φ x := by
    rw [planar_gradient_translation]
    simp only [add_neg_cancel_right]
  have hF := (hmp.integrable_comp_emb hemb).mpr hiF
  have hS := (hmp.integrable_comp_emb hemb).mpr hiS
  dsimp only [Function.comp_def] at hF hS
  simp_rw [hg] at hF
  simp only [ψ, add_neg_cancel_right] at hS
  refine ⟨hF, hS, ?_⟩
  have hInt := hmp.integral_comp hemb (fun y =>
    inner ℝ (linearizedFlux C v G y) (planarGradient ψ y) - linearizedSource C v G y * ψ y)
  rw [← hInt] at heq
  simpa only [hg, ψ, add_neg_cancel_right, W, translateLinearizedCoefficients,
    linearizedFlux, linearizedSource] using heq

theorem native_linear_coefficients_translation
    (U : Set E2) (hU : MeasurableSet U) (c : E2) (C : LinearizedCoefficients)
    (κ M : ℝ) (hb : CoefficientBounds U C κ M) (hm : CoefficientMeasurableOn U C) :
    CoefficientBounds ((fun x : E2 => x + c) ⁻¹' U) (translateLinearizedCoefficients C c) κ M ∧
    CoefficientMeasurableOn ((fun x : E2 => x + c) ⁻¹' U) (translateLinearizedCoefficients C c) := by
  have hmp := (measurePreserving_add_right volume c).restrict_preimage hU
  refine ⟨⟨hb.1, hb.2.1, fun x hx => hb.2.2.1 (x + c) hx,
    fun x hx => hb.2.2.2 (x + c) hx⟩, ?_⟩
  exact ⟨hm.1.comp_measurePreserving hmp, hm.2.1.comp_measurePreserving hmp,
    hm.2.2.1.comp_measurePreserving hmp, hm.2.2.2.1.comp_measurePreserving hmp,
    hm.2.2.2.2.1.comp_measurePreserving hmp, hm.2.2.2.2.2.comp_measurePreserving hmp⟩

theorem native_flat_translation_halfDisc (c : E2) (hcf : c 0 = 0) (ρ : ℝ) :
    (fun x : E2 => x + c) ⁻¹' (Metric.ball c ρ ∩ {x : E2 | 0 < x 0}) = openHalfDisc ρ ∧
    (fun x : E2 => x + c) ⁻¹' (Metric.closedBall c ρ ∩ {x : E2 | 0 ≤ x 0}) = closedHalfDisc ρ := by
  constructor <;> ext x <;>
    simp only [mem_preimage, mem_inter_iff, Metric.mem_ball, Metric.mem_closedBall,
      dist_eq_norm, add_sub_cancel_right, sub_zero, mem_setOf_eq, PiLp.add_apply, hcf, add_zero,
      openHalfDisc, closedHalfDisc]

/-- The uniform estimate is valid at every actual flat boundary center. -/
theorem uniform_holder_native_zero_trace_centered_linear_solutions
    (c : E2) (hcf : c 0 = 0) (ρ κ M L : ℝ)
    (hρ : 0 < ρ) (hκ : 0 < κ) (hM : 1 ≤ M) (hL : 0 ≤ L) :
    ∃ δ : ℝ, ∃ K α : ℝ≥0, 0 < δ ∧ δ < ρ ∧ 0 < α ∧ α < 1 ∧
      ∀ (C : LinearizedCoefficients) (v : E2 → ℝ),
        ContDiffOn ℝ 1 v (Metric.closedBall c ρ ∩ {x : E2 | 0 ≤ x 0}) →
        (∀ x ∈ Metric.ball c ρ ∩ {x : E2 | x 0 = 0}, v x = 0) →
        CoefficientBounds (Metric.ball c ρ ∩ {x : E2 | 0 < x 0}) C κ M →
        CoefficientMeasurableOn (Metric.ball c ρ ∩ {x : E2 | 0 < x 0}) C →
        LinearWeakEquation (Metric.ball c ρ ∩ {x : E2 | 0 < x 0}) C v (planarGradient v) →
        (∀ x ∈ Metric.closedBall c ρ ∩ {x : E2 | 0 ≤ x 0}, |v x| ≤ L) →
        HolderOnWith K α v (Metric.closedBall c δ ∩ {x : E2 | 0 ≤ x 0}) := by
  obtain ⟨δ, K, α, hδ, hδρ, hα, hα1, he⟩ :=
    uniform_holder_native_zero_trace_linear_solutions ρ κ M L hρ hκ hM hL
  refine ⟨δ, K, α, hδ, hδρ, hα, hα1, ?_⟩
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
  have hvc : ContDiffOn ℝ 1 (fun x => v (x + c)) (closedHalfDisc ρ) := by
    exact hv.comp (contDiff_id.add contDiff_const).contDiffOn hmap
  have hzc : ∀ x ∈ flatBoundary ρ, v (x + c) = 0 := by
    intro x hx
    apply hz
    refine ⟨?_, ?_⟩
    · simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero] using hx.1
    · simp only [mem_setOf_eq, PiLp.add_apply, hcf, add_zero]
      exact hx.2
  obtain ⟨hbc, hmc⟩ := native_linear_coefficients_translation U hU.measurableSet c C κ M hb hm
  have hwc := native_linear_weak_translation U hU.measurableSet c C v (planarGradient v) hw
  rw [show (fun x : E2 => x + c) ⁻¹' U = openHalfDisc ρ from hpre.1] at hbc hmc hwc
  have hgrad : (fun x => planarGradient v (x + c)) = planarGradient (fun x => v (x + c)) := by
    funext x
    exact (planar_gradient_translation v c x).symm
  rw [hgrad] at hwc
  have hh := he (translateLinearizedCoefficients C c) (fun x => v (x + c)) hvc hzc hbc hmc hwc
    (fun x hx => hvalue _ (hmap hx))
  intro x hx y hy
  have hx' : x - c ∈ closedHalfDisc δ := by
    refine ⟨?_, ?_⟩
    · simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hx.1
    · simpa only [mem_setOf_eq, PiLp.sub_apply, hcf, sub_zero] using hx.2
  have hy' : y - c ∈ closedHalfDisc δ := by
    refine ⟨?_, ?_⟩
    · simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hy.1
    · simpa only [mem_setOf_eq, PiLp.sub_apply, hcf, sub_zero] using hy.2
  simpa only [sub_add_cancel, edist_dist, dist_sub_right] using hh (x - c) hx' (y - c) hy'

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
