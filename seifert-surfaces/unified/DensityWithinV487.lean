import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.FDeriv.Add

noncomputable section
open MeasureTheory MeasureTheory.Measure Metric Filter Set Module Asymptotics
open scoped Topology Pointwise NNReal ENNReal

namespace SeifertSurfaces.OriginalEndpoints.Section5.NativeAreaV487

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {s : Set E} {x : E}

/-- A zero function has only the zero derivative at a Lebesgue density point,
including when the measurable domain has no open neighbourhood at that point. -/
theorem zero_derivative_eq_zero_of_density (μ : Measure E) [μ.IsAddHaarMeasure]
    (hx : Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r))
      (𝓝[>] (0 : ℝ)) (𝓝 1)) (D : E →L[ℝ] F)
    (hD : HasFDerivWithinAt (fun _ : E => (0 : F)) D s x) : D = 0 := by
  ext z
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  suffices H : ∀ ε, 0 < ε → ‖D z‖ ≤ ε * (‖z‖ + ε) + ‖D‖ * ε by
    have hlim : Tendsto (fun ε : ℝ => ε * (‖z‖ + ε) + ‖D‖ * ε)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hc : Continuous (fun ε : ℝ => ε * (‖z‖ + ε) + ‖D‖ * ε) := by fun_prop
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact H ε hε
  intro ε hε
  have B₁ : ∀ᶠ r in 𝓝[>] (0 : ℝ), (s ∩ ({x} + r • closedBall z ε)).Nonempty :=
    eventually_nonempty_inter_smul_of_density_one μ s x hx _ measurableSet_closedBall
      (measure_closedBall_pos μ z hε).ne'
  obtain ⟨ρ, hρpos, hρ⟩ : ∃ ρ > 0,
      ball x ρ ∩ s ⊆ {y : E | ‖D (y - x)‖ ≤ ε * ‖y - x‖} := by
    simpa only [sub_zero, zero_sub, norm_neg] using mem_nhdsWithin_iff.1 (hD.isLittleO.def hε)
  have B₂ : ∀ᶠ r in 𝓝[>] (0 : ℝ), {x} + r • closedBall z ε ⊆ ball x ρ := by
    apply nhdsWithin_le_nhds
    exact eventually_singleton_add_smul_subset isBounded_closedBall (ball_mem_nhds x hρpos)
  obtain ⟨r, ⟨y, ⟨hys, hy⟩⟩, hrρ, hrpos⟩ : ∃ r : ℝ,
      (s ∩ ({x} + r • closedBall z ε)).Nonempty ∧
      {x} + r • closedBall z ε ⊆ ball x ρ ∧ 0 < r :=
    (B₁.and (B₂.and self_mem_nhdsWithin)).exists
  obtain ⟨a, haz, hya⟩ : ∃ a, a ∈ closedBall z ε ∧ y = x + r • a := by
    simp only [mem_smul_set, image_add_left, mem_preimage, singleton_add] at hy
    rcases hy with ⟨a, haz, ha⟩
    exact ⟨a, haz, by simp only [ha, add_neg_cancel_left]⟩
  have hnorma : ‖a‖ ≤ ‖z‖ + ε := calc
    ‖a‖ = ‖z + (a - z)‖ := by simp only [add_sub_cancel]
    _ ≤ ‖z‖ + ‖a - z‖ := norm_add_le _ _
    _ ≤ ‖z‖ + ε := add_le_add_right (mem_closedBall_iff_norm.1 haz) _
  have ha : ‖D a‖ ≤ ε * (‖z‖ + ε) := by
    have hybound := hρ ⟨hrρ hy, hys⟩
    simp only [mem_setOf_eq, hya, add_sub_cancel_left, map_smul, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg hrpos.le] at hybound
    have hcancel : ‖D a‖ ≤ ε * ‖a‖ := by
      nlinarith
    exact hcancel.trans (mul_le_mul_of_nonneg_left hnorma hε.le)
  calc
    ‖D z‖ = ‖D a + D (z - a)‖ := by rw [← map_add, add_sub_cancel]
    _ ≤ ‖D a‖ + ‖D (z - a)‖ := norm_add_le _ _
    _ ≤ ε * (‖z‖ + ε) + ‖D‖ * ‖z - a‖ := add_le_add ha (D.le_opNorm _)
    _ ≤ ε * (‖z‖ + ε) + ‖D‖ * ε := by
      gcongr
      exact mem_closedBall_iff_norm'.1 haz

/-- Within derivatives supplied on an arbitrary measurable set agree almost everywhere. -/
theorem ae_eq_of_hasFDerivWithinAt (μ : Measure E) [μ.IsAddHaarMeasure]
    (hs : MeasurableSet s) (f : E → F) (D₁ D₂ : E → E →L[ℝ] F)
    (h₁ : ∀ x ∈ s, HasFDerivWithinAt f (D₁ x) s x)
    (h₂ : ∀ x ∈ s, HasFDerivWithinAt f (D₂ x) s x) :
    D₁ =ᵐ[μ.restrict s] D₂ := by
  filter_upwards [Besicovitch.ae_tendsto_measure_inter_div μ s, ae_restrict_mem hs] with x hx hxs
  apply sub_eq_zero.mp
  apply zero_derivative_eq_zero_of_density μ hx
  convert (h₁ x hxs).sub (h₂ x hxs) using 1
  ext y
  simp

end SeifertSurfaces.OriginalEndpoints.Section5.NativeAreaV487
