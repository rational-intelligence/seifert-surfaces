import HomogeneousTests
import SobolevLift

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology BigOperators ContDiff ENNReal
namespace SeifertSurfaces.QuasilinearProviderBridge.Helpers
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.QuasilinearLocalization

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

lemma integrable_inner_L2 {α F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] (μ : Measure α)
    (f g : α → F) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x => inner ℝ (f x) (g x)) μ := by
  apply (L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)).congr
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  rw [hx, hy]

end SeifertSurfaces.QuasilinearProviderBridge.Helpers
