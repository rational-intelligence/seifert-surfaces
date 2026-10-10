import WeakDerivativeLimit

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology BigOperators ContDiff
namespace SeifertSurfaces.QuasilinearProviderBridge.EnergyHelpers
open SeifertSurfaces.AppendixACoordinates

theorem tendsto_L2_of_uniform_bound (μ : Measure E2) [IsFiniteMeasure μ]
    (Fseq : ℕ → E2 → E2) (F : E2 → E2)
    (hseq : ∀ n, MemLp (Fseq n) 2 μ) (hF : MemLp F 2 μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hbseq : ∀ n, ∀ᵐ x ∂μ, ‖Fseq n x‖ ≤ C) (hbF : ∀ᵐ x ∂μ, ‖F x‖ ≤ C)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => Fseq n x) atTop (𝓝 (F x))) :
    Tendsto (fun n => (hseq n).toLp (Fseq n)) atTop (𝓝 (hF.toLp F)) := by
  have hint : Tendsto (fun n => ∫ x, ‖Fseq n x - F x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
    have hm (n : ℕ) : AEStronglyMeasurable (fun x => ‖Fseq n x - F x‖ ^ 2) μ :=
      (((hseq n).aestronglyMeasurable.sub hF.aestronglyMeasurable).norm.pow 2)
    have hd (n : ℕ) : ∀ᵐ x ∂μ, ‖‖Fseq n x - F x‖ ^ 2‖ ≤ (2 * C) ^ 2 := by
      filter_upwards [hbseq n, hbF] with x hx hy
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hn : ‖Fseq n x - F x‖ ≤ 2 * C := (norm_sub_le _ _).trans (by linarith)
      nlinarith [norm_nonneg (Fseq n x - F x)]
    have hp : ∀ᵐ x ∂μ, Tendsto (fun n => ‖Fseq n x - F x‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
      filter_upwards [hlim] with x hx
      simpa using ((hx.sub (tendsto_const_nhds (x := F x))).norm.pow 2)
    have hh := tendsto_integral_of_dominated_convergence (fun _ : E2 => (2 * C) ^ 2)
      hm (integrable_const _) hd hp
    simpa using hh
  have hsq (n : ℕ) : ‖(hseq n).toLp (Fseq n) - hF.toLp F‖ ^ 2 =
      ∫ x, ‖Fseq n x - F x‖ ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub ((hseq n).toLp (Fseq n)) (hF.toLp F),
      (hseq n).coeFn_toLp, hF.coeFn_toLp] with x hx hy hz
    simp only [hx, Pi.sub_apply, hy, hz, real_inner_self_eq_norm_sq]
  have hs : Tendsto (fun n => ‖(hseq n).toLp (Fseq n) - hF.toLp F‖ ^ 2) atTop (𝓝 0) := by
    simpa only [hsq] using hint
  have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  have hn' : Tendsto (fun n => ‖(hseq n).toLp (Fseq n) - hF.toLp F‖) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hn
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn'

theorem weak_strong_inner_tendsto {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u : ℕ → H) (g : H) (v : ℕ → H) (w : H) (C : ℝ)
    (hu : ∀ n, ‖u n‖ ≤ C)
    (hweak : ∀ z : H, Tendsto (fun n => inner ℝ (u n) z) atTop (𝓝 (inner ℝ g z)))
    (hstrong : Tendsto v atTop (𝓝 w)) :
    Tendsto (fun n => inner ℝ (u n) (v n)) atTop (𝓝 (inner ℝ g w)) := by
  have he : Tendsto (fun n => inner ℝ (u n) (v n - w)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hu n) (norm_nonneg _)))
    simpa using (((hstrong.sub (tendsto_const_nhds (x := w))).norm).const_mul C)
  have hh := he.add (hweak w)
  simpa only [inner_sub_right, sub_add_cancel, zero_add] using hh

end SeifertSurfaces.QuasilinearProviderBridge.EnergyHelpers
