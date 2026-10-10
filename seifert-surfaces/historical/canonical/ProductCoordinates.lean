import ProviderBridgeData
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology BigOperators ContDiff ENNReal
namespace SeifertSurfaces.QuasilinearProviderBridge.Helpers
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.QuasilinearLocalization

def productCLE : (E2 × ℝ) ≃L[ℝ] E3 :=
  (show (E2 × ℝ) ≃ₗ[ℝ] E3 from {
    toFun := fun p => liftedPoint p.1 p.2
    invFun := fun y => (planarPart y, y 2)
    left_inv := by
      intro p
      apply Prod.ext
      · ext i; fin_cases i <;> rfl
      · rfl
    right_inv := by intro y; ext i; fin_cases i <;> rfl
    map_add' := by intro p q; ext i; fin_cases i <;> rfl
    map_smul' := by intro c p; ext i; fin_cases i <;> rfl
  }).toContinuousLinearEquiv

lemma productCLE_apply (p : E2 × ℝ) : productCLE p = liftedPoint p.1 p.2 := rfl

lemma planarPart_lifted (x : E2) (t : ℝ) : planarPart (liftedPoint x t) = x := by
  ext i; fin_cases i <;> rfl

lemma planarPart_continuous : Continuous planarPart := by
  exact continuous_fst.comp productCLE.symm.continuous

lemma cylinder_open {B : Set E2} (hB : IsOpen B) : IsOpen (cylinder B) := by
  change IsOpen ({y : E3 | planarPart y ∈ B} ∩ {y : E3 | |y 2| < 1})
  exact (hB.preimage planarPart_continuous).inter
    (isOpen_lt ((EuclideanSpace.proj (2 : Fin 3)).continuous.abs) continuous_const)

lemma productCLE_preimage_cylinder (B : Set E2) :
    productCLE ⁻¹' cylinder B = B ×ˢ Ioo (-1 : ℝ) 1 := by
  ext p
  change (planarPart (liftedPoint p.1 p.2) ∈ B ∧ |p.2| < 1) ↔ p.1 ∈ B ∧ p.2 ∈ Ioo (-1 : ℝ) 1
  rw [planarPart_lifted]
  simp only [abs_lt, mem_Ioo]

lemma productCLE_map_cylinder {B : Set E2} (hB : IsOpen B) :
    Measure.map productCLE ((volume.restrict B).prod (volume.restrict (Ioo (-1 : ℝ) 1))) =
      volume.restrict (cylinder B) := by
  rw [Measure.prod_restrict, ← productCLE_preimage_cylinder]
  change Measure.map productCLE (volume.restrict (productCLE ⁻¹' cylinder B)) = _
  rw [← Measure.restrict_map productCLE.continuous.measurable (cylinder_open hB).measurableSet]
  exact congrArg (fun μ : Measure E3 => μ.restrict (cylinder B)) R3_liftedPoint_map_product_volume

lemma planar_pullback_memLp {B : Set E2} (hB : IsOpen B) {f : E2 → ℝ}
    (hf : MemLp f 2 (volume.restrict B)) :
    MemLp (fun y => f (planarPart y)) 2 (volume.restrict (cylinder B)) := by
  rw [← productCLE_map_cylinder hB]
  apply productCLE.toHomeomorph.measurableEmbedding.memLp_map_measure_iff.mpr
  change MemLp (fun p : E2 × ℝ => f (planarPart (productCLE p))) 2 _
  simpa only [productCLE_apply, planarPart_lifted] using
    hf.comp_fst (volume.restrict (Ioo (-1 : ℝ) 1))

lemma vertical_memLp {B : Set E2} (hB : IsOpen B) (hBbdd : Bornology.IsBounded B) :
    MemLp (fun y : E3 => y 2) 2 (volume.restrict (cylinder B)) := by
  letI : IsFiniteMeasure (volume.restrict B) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hBbdd.measure_lt_top⟩
  have ht : MemLp (fun t : ℝ => t) 2 (volume.restrict (Ioo (-1 : ℝ) 1)) := by
    apply MemLp.of_bound measurable_id.aestronglyMeasurable 1
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    simpa [Real.norm_eq_abs] using (abs_lt.mpr ht).le
  rw [← productCLE_map_cylinder hB]
  apply productCLE.toHomeomorph.measurableEmbedding.memLp_map_measure_iff.mpr
  change MemLp (fun p : E2 × ℝ => (productCLE p) 2) 2 _
  exact ht.comp_snd (volume.restrict B)

end SeifertSurfaces.QuasilinearProviderBridge.Helpers
