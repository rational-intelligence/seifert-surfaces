import L2WeakStrong
import Mathlib.Analysis.InnerProductSpace.Adjoint

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology BigOperators ContDiff
namespace SeifertSurfaces.QuasilinearProviderBridge.EnergyHelpers
open SeifertSurfaces.AppendixACoordinates

section
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

set_option maxHeartbeats 800000 in
theorem integral_variable_clm_weak_limit (μ : Measure E2) [IsFiniteMeasure μ]
    (Gseq : ℕ → Lp E2 2 μ) (G : Lp E2 2 μ) (L : ℝ)
    (hGn : ∀ n, ‖Gseq n‖ ≤ L)
    (hGweak : ∀ z, Tendsto (fun n => inner ℝ (Gseq n) z) atTop (𝓝 (inner ℝ G z)))
    (Aseq : ℕ → E2 → E2 →L[ℝ] F) (A : E2 → E2 →L[ℝ] F)
    (hAmseq : ∀ n, AEStronglyMeasurable (Aseq n) μ) (hAm : AEStronglyMeasurable A μ)
    (M : ℝ) (hM : 0 ≤ M) (hAbseq : ∀ n, ∀ᵐ x ∂μ, ‖Aseq n x‖ ≤ M)
    (hAb : ∀ᵐ x ∂μ, ‖A x‖ ≤ M)
    (hAlim : ∀ᵐ x ∂μ, Tendsto (fun n => Aseq n x) atTop (𝓝 (A x)))
    (ψ : E2 → F) (hψm : AEStronglyMeasurable ψ μ) (K : ℝ) (hK : 0 ≤ K)
    (hψb : ∀ᵐ x ∂μ, ‖ψ x‖ ≤ K) :
    Tendsto (fun n => ∫ x, inner ℝ (Aseq n x (Gseq n x)) (ψ x) ∂μ) atTop
      (𝓝 (∫ x, inner ℝ (A x (G x)) (ψ x) ∂μ)) := by
  let Wseq : ℕ → E2 → E2 := fun n x => (Aseq n x).adjoint (ψ x)
  let W : E2 → E2 := fun x => (A x).adjoint (ψ x)
  have hmseq (n : ℕ) : AEStronglyMeasurable (Wseq n) μ :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (ContinuousLinearMap.adjoint.continuous.comp_aestronglyMeasurable (hAmseq n) |>.prodMk hψm)
  have hm : AEStronglyMeasurable W μ :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (ContinuousLinearMap.adjoint.continuous.comp_aestronglyMeasurable hAm |>.prodMk hψm)
  have hbseq (n : ℕ) : ∀ᵐ x ∂μ, ‖Wseq n x‖ ≤ M * K := by
    filter_upwards [hAbseq n, hψb] with x hx hψx
    exact ((Aseq n x).adjoint.le_opNorm (ψ x)).trans
      (by rw [ContinuousLinearMap.adjoint.norm_map]; exact mul_le_mul hx hψx (norm_nonneg _) hM)
  have hb : ∀ᵐ x ∂μ, ‖W x‖ ≤ M * K := by
    filter_upwards [hAb, hψb] with x hx hψx
    exact ((A x).adjoint.le_opNorm (ψ x)).trans
      (by rw [ContinuousLinearMap.adjoint.norm_map]; exact mul_le_mul hx hψx (norm_nonneg _) hM)
  have hmemseq (n : ℕ) : MemLp (Wseq n) 2 μ := MemLp.of_bound (hmseq n) (M * K) (hbseq n)
  have hmem : MemLp W 2 μ := MemLp.of_bound hm (M * K) hb
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => Wseq n x) atTop (𝓝 (W x)) := by
    filter_upwards [hAlim] with x hx
    have hA : Tendsto (fun n => (Aseq n x).adjoint) atTop
        (𝓝 ((A x).adjoint)) :=
      ContinuousLinearMap.adjoint.continuous.continuousAt.tendsto.comp hx
    change Tendsto (fun n => (Aseq n x).adjoint (ψ x)) atTop (𝓝 ((A x).adjoint (ψ x)))
    exact ((ContinuousLinearMap.apply ℝ E2 (ψ x)).continuous.tendsto ((A x).adjoint)).comp hA
  have hstrong := tendsto_L2_of_uniform_bound μ Wseq W hmemseq hmem (M * K)
    (mul_nonneg hM hK) hbseq hb hlim
  have hh := weak_strong_inner_tendsto Gseq G (fun n => (hmemseq n).toLp (Wseq n))
    (hmem.toLp W) L hGn hGweak hstrong
  have hseqeq (n : ℕ) : inner ℝ (Gseq n) ((hmemseq n).toLp (Wseq n)) =
      ∫ x, inner ℝ (Aseq n x (Gseq n x)) (ψ x) ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(hmemseq n).coeFn_toLp] with x hx
    rw [hx]
    exact (Aseq n x).adjoint_inner_right _ _
  have heq : inner ℝ G (hmem.toLp W) = ∫ x, inner ℝ (A x (G x)) (ψ x) ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hmem.coeFn_toLp] with x hx
    rw [hx]
    exact (A x).adjoint_inner_right _ _
  simpa only [hseqeq, heq] using hh

theorem integral_inner_bounded_limit (μ : Measure E2)
    (Fseq : ℕ → E2 → F) (F₀ : E2 → F)
    (hmseq : ∀ n, AEStronglyMeasurable (Fseq n) μ)
    (M : ℝ) (hbseq : ∀ n, ∀ᵐ x ∂μ, ‖Fseq n x‖ ≤ M)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => Fseq n x) atTop (𝓝 (F₀ x)))
    (ψ : E2 → F) (hψ : Integrable ψ μ) :
    Tendsto (fun n => ∫ x, inner ℝ (Fseq n x) (ψ x) ∂μ) atTop
      (𝓝 (∫ x, inner ℝ (F₀ x) (ψ x) ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => M * ‖ψ x‖)
  · intro n
    exact (hmseq n).inner hψ.aestronglyMeasurable
  · exact hψ.norm.const_mul M
  · intro n
    filter_upwards [hbseq n] with x hx
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
  · filter_upwards [hlim] with x hx
    exact hx.inner tendsto_const_nhds
end

end SeifertSurfaces.QuasilinearProviderBridge.EnergyHelpers
