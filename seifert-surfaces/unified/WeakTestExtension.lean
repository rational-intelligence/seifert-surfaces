import QuasilinearProviderBridge
import Mathlib.MeasureTheory.Function.L2Space

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology BigOperators ContDiff
namespace SeifertSurfaces.QuasilinearProviderBridge
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.QuasilinearLocalization

namespace EnergyHelpers

theorem real_inner_toLp (μ : Measure E2) {f g : E2 → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  simp [hx, hy, mul_comm]

theorem tendsto_integral_mul_of_L2 (μ : Measure E2) {f g : E2 → ℝ} {gseq : ℕ → E2 → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (hseq : ∀ n, MemLp (gseq n) 2 μ)
    (hconv : Tendsto (fun n => eLpNorm (gseq n - g) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, f x * gseq n x ∂μ) atTop (𝓝 (∫ x, f x * g x ∂μ)) := by
  have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' gseq hseq g hg).mpr hconv
  have ht' := (tendsto_const_nhds (x := hf.toLp f)).inner ht (𝕜 := ℝ)
  simpa only [real_inner_toLp] using ht'

theorem vector_component_memLp (μ : Measure E2) (F : E2 → E2)
    (hF : MemLp F 2 μ) (i : Fin 2) : MemLp (fun x => F x i) 2 μ := by
  apply hF.norm.mono' ((EuclideanSpace.proj i).continuous.comp_aestronglyMeasurable
    hF.aestronglyMeasurable)
  exact ae_of_all _ fun x => PiLp.norm_apply_le (F x) i

theorem integral_pairing_sum (μ : Measure E2) (F G : E2 → E2)
    (hF : ∀ i, MemLp (fun x => F x i) 2 μ)
    (hG : ∀ i, MemLp (fun x => G x i) 2 μ) :
    (∫ x, inner ℝ (F x) (G x) ∂μ) = ∑ i : Fin 2, ∫ x, F x i * G x i ∂μ := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mul_comm (G _ _)]
  exact integral_finsetSum _ (fun i _ => (hF i).integrable_mul (hG i))

theorem integrable_pairing (μ : Measure E2) (F G : E2 → E2)
    (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) :
    Integrable (fun x => inner ℝ (F x) (G x)) μ := by
  apply (L2.integrable_inner (𝕜 := ℝ) (hF.toLp F) (hG.toLp G)).congr
  filter_upwards [hF.coeFn_toLp, hG.coeFn_toLp] with x hx hy
  rw [hx, hy]

theorem linearized_fields_memLp (B : Set E2) (hB : IsOpen B) (hBbdd : Bornology.IsBounded B)
    (C : LinearizedCoefficients) (v : E2 → ℝ) (G : E2 → E2)
    (κ M : ℝ) (hbound : CoefficientBounds B C κ M)
    (hmeas : CoefficientMeasurableOn B C)
    (hv : MemLp v 2 (volume.restrict B)) (hG : MemLp G 2 (volume.restrict B)) :
    MemLp (linearizedFlux C v G) 2 (volume.restrict B) ∧
      MemLp (linearizedSource C v G) 2 (volume.restrict B) := by
  haveI : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr hBbdd.measure_lt_top.ne
  rcases hmeas with ⟨ha, hc, hd, hb, hq, hf⟩
  have haG : MemLp (fun x => C.a x (G x)) 2 (volume.restrict B) := by
    apply (hG.norm.const_mul M).mono' ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (ha.prodMk hG.aestronglyMeasurable))
    filter_upwards [ae_restrict_mem hB.measurableSet] with x hx
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hbound.2.2.2 x hx).1 (norm_nonneg _))
  have hvc : MemLp (fun x => v x • C.c x) 2 (volume.restrict B) := by
    apply (hv.norm.const_mul M).mono' (hv.aestronglyMeasurable.smul hc)
    filter_upwards [ae_restrict_mem hB.measurableSet] with x hx
    change ‖v x • C.c x‖ ≤ M * ‖v x‖
    rw [norm_smul]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hbound.2.2.2 x hx).2.1 (norm_nonneg _)
  have hd2 : MemLp C.d 2 (volume.restrict B) := by
    apply MemLp.of_bound hd M
    filter_upwards [ae_restrict_mem hB.measurableSet] with x hx
    exact (hbound.2.2.2 x hx).2.2.1
  have hbG : MemLp (fun x => C.b x (G x)) 2 (volume.restrict B) := by
    apply (hG.norm.const_mul M).mono' ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hb.prodMk hG.aestronglyMeasurable))
    filter_upwards [ae_restrict_mem hB.measurableSet] with x hx
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hbound.2.2.2 x hx).2.2.2.1 (norm_nonneg _))
  have hqv : MemLp (fun x => C.q x * v x) 2 (volume.restrict B) := by
    apply (hv.norm.const_mul M).mono' (hq.mul hv.aestronglyMeasurable)
    filter_upwards [ae_restrict_mem hB.measurableSet] with x hx
    simp only [Pi.mul_apply, norm_mul]
    exact mul_le_mul_of_nonneg_right (hbound.2.2.2 x hx).2.2.2.2.1 (norm_nonneg _)
  have hf2 : MemLp C.f 2 (volume.restrict B) := by
    apply MemLp.of_bound hf M
    filter_upwards [ae_restrict_mem hB.measurableSet] with x hx
    exact (hbound.2.2.2 x hx).2.2.2.2.2
  exact ⟨(haG.add hvc).add hd2, (hbG.add hqv).add hf2⟩

theorem integrable_pairing_components (μ : Measure E2) (F G : E2 → E2)
    (hF : ∀ i, MemLp (fun x => F x i) 2 μ)
    (hG : ∀ i, MemLp (fun x => G x i) 2 μ) :
    Integrable (fun x => inner ℝ (F x) (G x)) μ := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mul_comm (G _ _)]
  exact integrable_finsetSum _ (fun i _ => (hF i).integrable_mul (hG i))

end EnergyHelpers

open EnergyHelpers

theorem R2_smooth_tests_extend_to_H01
    (B : Set E2) (hB : IsOpen B) (hBbdd : Bornology.IsBounded B)
    (C : LinearizedCoefficients) (v : E2 → ℝ) (hC1 : ContDiffOn ℝ 1 v B)
    (κ M : ℝ) (hbound : CoefficientBounds B C κ M)
    (hmeas : CoefficientMeasurableOn B C)
    (hmem : DeGiorgi.MemW1p 2 v B)
    (hweak : LinearWeakEquation B C v (planarGradient v)) :
    ProviderLinearWeakEquation B C v := by
  refine ⟨hmem, ?_⟩
  intro hv φ hφ hφw
  let F := linearizedFlux C v hv.weakGrad
  let S := linearizedSource C v hv.weakGrad
  obtain ⟨hF, hS⟩ := linearized_fields_memLp B hB hBbdd C v hv.weakGrad κ M hbound
    hmeas hv.memLp hv.weakGrad_memLp
  change MemLp F 2 (volume.restrict B) at hF
  change MemLp S 2 (volume.restrict B) at hS
  have hFcomp := vector_component_memLp (volume.restrict B) F hF
  have hFφ := integrable_pairing (volume.restrict B) F hφw.weakGrad hF hφw.weakGrad_memLp
  have hSφ : Integrable (fun x => S x * φ x) (volume.restrict B) :=
    hS.integrable_mul hφw.memLp
  refine ⟨hFφ, hSφ, ?_⟩
  obtain ⟨hw, ψ, hψ, hψc, hψB, hconv, hconvD⟩ := hφ.2
  have hψLp (n : ℕ) : MemLp (ψ n) 2 (volume.restrict B) :=
    ((hψ n).continuous.memLp_of_hasCompactSupport (hψc n)).restrict B
  have hD (i : Fin 2) (n : ℕ) : MemLp
      (fun x => planarGradient (ψ n) x i) 2 (volume.restrict B) := by
    simp only [SeifertSurfaces.QuasilinearLocalization.Helpers.gradient_apply]
    exact (((hψ n).fderiv_right (show (↑(⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ↑(⊤ : ℕ∞) by simp)).clm_apply
      contDiff_const).continuous.memLp_of_hasCompactSupport
      ((hψc n).fderiv_apply (𝕜 := ℝ) _) |>.restrict B
  have hFD (n : ℕ) := integrable_pairing_components (volume.restrict B) F
    (planarGradient (ψ n)) hFcomp (fun i => hD i n)
  have hlimD (i : Fin 2) := tendsto_integral_mul_of_L2 (volume.restrict B)
    (hFcomp i) (hw.weakGrad_component_memLp i) (hD i)
    (show Tendsto (fun n => eLpNorm ((fun x => planarGradient (ψ n) x i) -
      (fun x => hw.weakGrad x i)) 2 (volume.restrict B)) atTop (𝓝 0) by
      change Tendsto (fun n => eLpNorm (fun x => planarGradient (ψ n) x i -
        hw.weakGrad x i) 2 (volume.restrict B)) atTop (𝓝 0)
      simpa only [SeifertSurfaces.QuasilinearLocalization.Helpers.gradient_apply,
        coordinateVector] using hconvD i)
  have hlimF : Tendsto (fun n => ∫ x in B, inner ℝ (F x) (planarGradient (ψ n) x))
      atTop (𝓝 (∫ x in B, inner ℝ (F x) (hw.weakGrad x))) := by
    simp_rw [integral_pairing_sum (volume.restrict B) F _ hFcomp (fun i => hD i _),
      integral_pairing_sum (volume.restrict B) F _ hFcomp hw.weakGrad_component_memLp]
    exact tendsto_finsetSum _ (fun i _ => hlimD i)
  have hlimS := tendsto_integral_mul_of_L2 (volume.restrict B) hS hw.memLp hψLp hconv
  have heq (n : ℕ) : (∫ x in B, inner ℝ (F x) (planarGradient (ψ n) x) - S x * ψ n x) = 0 := by
    rw [← (hweak (ψ n) (hψ n) (hψc n) (hψB n)).2.2]
    apply integral_congr_ae
    filter_upwards [R1_classical_weak_gradient_agrees B hB v hC1 hv] with x hx
    simp only [F, S, linearizedFlux, linearizedSource, hx]
  have hzero : (∫ x in B, inner ℝ (F x) (hw.weakGrad x)) -
      (∫ x in B, S x * φ x) = 0 := by
    apply tendsto_nhds_unique (hlimF.sub hlimS)
    have heq' (n : ℕ) : (∫ x in B, inner ℝ (F x) (planarGradient (ψ n) x)) -
        (∫ x in B, S x * ψ n x) = 0 := by
      rw [← integral_sub (hFD n) (show Integrable (fun x => S x * ψ n x)
        (volume.restrict B) from hS.integrable_mul (hψLp n))]
      exact heq n
    simpa only [heq'] using (tendsto_const_nhds (x := (0 : ℝ)) :
      Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hgrad (i : Fin 2) : (fun x => hw.weakGrad x i) =ᵐ[volume.restrict B]
      fun x => hφw.weakGrad x i :=
    (hw.isWeakGrad i).ae_eq hB (hφw.isWeakGrad i)
      ((hw.weakGrad_component_memLp i).locallyIntegrable (by norm_num))
      ((hφw.weakGrad_component_memLp i).locallyIntegrable (by norm_num))
  have heqgrad : hw.weakGrad =ᵐ[volume.restrict B] hφw.weakGrad := by
    filter_upwards [ae_all_iff.mpr hgrad] with x hx
    ext i
    exact hx i
  change (∫ x in B, inner ℝ (F x) (hφw.weakGrad x) - S x * φ x) = 0
  rw [integral_sub hFφ hSφ, ← hzero]
  congr 1
  apply integral_congr_ae
  filter_upwards [heqgrad] with x hx
  rw [hx]

end SeifertSurfaces.QuasilinearProviderBridge
