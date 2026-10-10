import DensityWithinV487
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.Normed.Module.ContinuousInverse
import Mathlib.MeasureTheory.Constructions.Polish.Basic

noncomputable section
open Set Topology Function MeasureTheory Metric Filter IsManifold
open scoped Manifold Topology Pointwise ENNReal

namespace SeifertSurfaces.OriginalEndpoints.Section5.NativeAreaV487

variable {E V H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace H] (I : ModelWithCorners ℝ V H)
  [TopologicalSpace M] [ChartedSpace H M]

/-- Native manifold derivatives from a vector space give ordinary derivatives in
the target chart, with exactly the same tangent linear map. -/
theorem hasFDerivWithinAt_targetChart {f : E → M} {s : Set E} {x : E}
    {D : TangentSpace 𝓘(ℝ, E) x →L[ℝ] TangentSpace I (f x)}
    (h : HasMFDerivWithinAt 𝓘(ℝ, E) I f s x D) :
    HasFDerivWithinAt ((extChartAt I (f x)) ∘ f) (show E →L[ℝ] V from D) s x := by
  convert h.2 using 1 <;> simp [writtenInExtChartAt, extChartAt_model_space_eq_id,
    ModelWithCorners.range_eq_univ]
  rfl

/-- A pointwise uniqueness form needed when the target chart itself depends on the point. -/
theorem hasMFDerivWithinAt_eq_of_density {f : E → M} {s : Set E} {x : E}
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (hx : Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r))
      (𝓝[>] (0 : ℝ)) (𝓝 1))
    {D₁ D₂ : TangentSpace 𝓘(ℝ, E) x →L[ℝ] TangentSpace I (f x)}
    (h₁ : HasMFDerivWithinAt 𝓘(ℝ, E) I f s x D₁)
    (h₂ : HasMFDerivWithinAt 𝓘(ℝ, E) I f s x D₂) : D₁ = D₂ := by
  have he : (show E →L[ℝ] V from D₁) - (show E →L[ℝ] V from D₂) = 0 := by
    apply zero_derivative_eq_zero_of_density μ hx
    convert (hasFDerivWithinAt_targetChart I h₁).sub (hasFDerivWithinAt_targetChart I h₂) using 1
    ext y
    simp
  exact sub_eq_zero.mp he

variable [FiniteDimensional ℝ V]

/-- A continuous reparametrization through an injective within differential is
within differentiable on its domain, with no openness assumption on either set. -/
theorem differentiableWithinAt_transition {f g : E → M} {τ : E → E}
    {s t : Set E} {x : E} (hxs : x ∈ s)
    (hτ : ContinuousWithinAt τ s x) (hτt : MapsTo τ s t)
    (heq : EqOn (g ∘ τ) f s)
    {Df : TangentSpace 𝓘(ℝ, E) x →L[ℝ] TangentSpace I (f x)}
    {Dg : TangentSpace 𝓘(ℝ, E) (τ x) →L[ℝ] TangentSpace I (g (τ x))}
    (hf : HasMFDerivWithinAt 𝓘(ℝ, E) I f s x Df)
    (hg : HasMFDerivWithinAt 𝓘(ℝ, E) I g t (τ x) Dg)
    (hDg : Function.Injective Dg) : DifferentiableWithinAt ℝ τ s x := by
  let dg : E →L[ℝ] V := Dg
  let df : E →L[ℝ] V := Df
  obtain ⟨L, hL⟩ := ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional
    (f := dg) hDg
  have htarget : g (τ x) = f x := heq hxs
  have hgg : HasFDerivWithinAt ((extChartAt I (g (τ x))) ∘ g) dg t (τ x) :=
    hasFDerivWithinAt_targetChart I hg
  have hff : HasFDerivWithinAt ((extChartAt I (g (τ x))) ∘ f) df s x := by
    rw [htarget]
    exact hasFDerivWithinAt_targetChart I hf
  have hcomp : (((extChartAt I (g (τ x))) ∘ g) ∘ τ) =ᶠ[𝓝[s] x]
      ((extChartAt I (g (τ x))) ∘ f) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact congrArg (extChartAt I (g (τ x))) (heq hy)
  exact (HasFDerivWithinAt.of_comp_of_leftInverse
    (hτ.tendsto_nhdsWithin hτt) hgg hff hcomp hL hxs).differentiableWithinAt

/-- The native supplied derivatives satisfy the transition chain rule almost
 everywhere on an arbitrary measurable source piece. -/
theorem ae_derivative_comp_transition (μ : Measure E) [μ.IsAddHaarMeasure]
    {f g : E → M} {τ : E → E} {s t : Set E}
    (hs : MeasurableSet s) (hτ : ContinuousOn τ s) (hτt : MapsTo τ s t)
    (heq : EqOn (g ∘ τ) f s) (Df Dg : E → E →L[ℝ] V)
    (hf : ∀ x ∈ s, HasMFDerivWithinAt 𝓘(ℝ, E) I f s x (Df x))
    (hg : ∀ y ∈ t, HasMFDerivWithinAt 𝓘(ℝ, E) I g t y (Dg y))
    (hDg : ∀ y ∈ t, Function.Injective (Dg y)) :
    ∀ᵐ x ∂μ.restrict s,
      Df x = (Dg (τ x)).comp (fderivWithin ℝ τ s x) := by
  filter_upwards [Besicovitch.ae_tendsto_measure_inter_div μ s, ae_restrict_mem hs] with x hx hxs
  have hτd : DifferentiableWithinAt ℝ τ s x :=
    differentiableWithinAt_transition I hxs (hτ x hxs) hτt heq
      (hf x hxs) (hg (τ x) (hτt hxs)) (hDg (τ x) (hτt hxs))
  have hcomp := (hg (τ x) (hτt hxs)).comp x
    hτd.hasFDerivWithinAt.hasMFDerivWithinAt hτt
  have hev : f =ᶠ[𝓝[s] x] g ∘ τ := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (heq hy).symm
  have hcompf := hcomp.congr_of_eventuallyEq hev (heq hxs).symm
  have he := hasMFDerivWithinAt_eq_of_density I μ hx (hf x hxs) hcompf
  exact he

end SeifertSurfaces.OriginalEndpoints.Section5.NativeAreaV487
