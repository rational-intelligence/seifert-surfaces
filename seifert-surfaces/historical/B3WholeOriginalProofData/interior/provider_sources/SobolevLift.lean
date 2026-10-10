import SmoothSlices
import L2Pairing

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology BigOperators ContDiff ENNReal
namespace SeifertSurfaces.QuasilinearProviderBridge
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.QuasilinearLocalization

namespace Helpers

lemma cylinder_finite {B : Set E2} (hB : IsOpen B) (hBbdd : Bornology.IsBounded B) :
    IsFiniteMeasure (volume.restrict (cylinder B)) := by
  letI : IsFiniteMeasure (volume.restrict B) := ⟨by
    rw [Measure.restrict_apply_univ]; exact hBbdd.measure_lt_top⟩
  rw [← productCLE_map_cylinder hB]
  infer_instance

lemma smooth_partial_memLp {ψ : E3 → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (B : Set E3) (i : Fin 3) :
    MemLp (fun y => fderiv ℝ ψ y (EuclideanSpace.single i 1)) 2 (volume.restrict B) := by
  have hd : ContDiff ℝ ∞ (fun y => fderiv ℝ ψ y (EuclideanSpace.single i 1)) :=
    (hψ.fderiv_right (m := (⊤ : ℕ∞)) (by norm_cast)).clm_apply contDiff_const
  exact (hd.continuous.memLp_of_hasCompactSupport (hc.fderiv_apply (𝕜 := ℝ) _)).restrict B

lemma horizontal_slice_partial {ψ : E3 → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (x : E2) (t : ℝ) (i : Fin 2) :
    fderiv ℝ (fun z => ψ (liftedPoint z t)) x (EuclideanSpace.single i 1) =
      fderiv ℝ ψ (liftedPoint x t) (EuclideanSpace.single (Fin.castSucc i) 1) := by
  have h := congrArg (fun p : E2 => p i) (horizontal_gradient hψ x t)
  fin_cases i <;>
    simpa [planarGradient, planarPart, gradient3, Fin.sum_univ_succ,
      coordinateVector, EuclideanSpace.single] using h

lemma horizontal_pullback_weak {B : Set E2} (hB : IsOpen B) {v g : E2 → ℝ}
    (hv : MemLp v 2 (volume.restrict B)) (hg : MemLp g 2 (volume.restrict B))
    (i : Fin 2) (hweak : DeGiorgi.HasWeakPartialDeriv i g v B) :
    DeGiorgi.HasWeakPartialDeriv (Fin.castSucc i)
      (fun y => g (planarPart y)) (fun y => v (planarPart y)) (cylinder B) := by
  intro ψ hψ hc hs
  have hpres : MeasurePreserving productCLE
      ((volume.restrict B).prod (volume.restrict (Ioo (-1 : ℝ) 1)))
      (volume.restrict (cylinder B)) := ⟨productCLE.continuous.measurable, productCLE_map_cylinder hB⟩
  have hleft : Integrable (fun y => v (planarPart y) *
      fderiv ℝ ψ y (EuclideanSpace.single (Fin.castSucc i) 1)) (volume.restrict (cylinder B)) :=
    (planar_pullback_memLp hB hv).integrable_mul (smooth_partial_memLp hψ hc _ _)
  have hψLp : MemLp ψ 2 (volume.restrict (cylinder B)) :=
    (hψ.continuous.memLp_of_hasCompactSupport hc).restrict _
  have hright : Integrable (fun y => g (planarPart y) * ψ y) (volume.restrict (cylinder B)) :=
    (planar_pullback_memLp hB hg).integrable_mul hψLp
  rw [← hpres.integral_comp productCLE.toHomeomorph.measurableEmbedding,
    ← hpres.integral_comp productCLE.toHomeomorph.measurableEmbedding]
  have hl := hpres.integrable_comp_of_integrable hleft
  have hr := hpres.integrable_comp_of_integrable hright
  change Integrable (fun p : E2 × ℝ => v (planarPart (productCLE p)) *
    fderiv ℝ ψ (productCLE p) (EuclideanSpace.single (Fin.castSucc i) 1)) _ at hl
  change Integrable (fun p : E2 × ℝ => g (planarPart (productCLE p)) * ψ (productCLE p)) _ at hr
  rw [integral_prod_symm _ hl, integral_prod_symm _ hr]
  simp only [productCLE_apply, planarPart_lifted]
  rw [← integral_neg]
  apply integral_congr_ae
  exact ae_of_all _ fun t => by
    let φ : E2 → ℝ := fun x => ψ (liftedPoint x t)
    have hφ : ContDiff ℝ ∞ φ := hψ.comp (horizontal_smooth t)
    have hφc : HasCompactSupport φ := hc.comp_isClosedEmbedding (horizontal_closed t)
    have hφs : tsupport φ ⊆ B := by
      intro x hx
      have hy := (tsupport_comp_subset_preimage ψ (horizontal_smooth t).continuous) hx
      simpa only [planarPart_lifted] using (hs hy).1
    simpa only [φ, horizontal_slice_partial hψ] using hweak φ hφ hφc hφs

lemma vertical_pullback_weak {B : Set E2} (hB : IsOpen B) {v : E2 → ℝ}
    (hv : MemLp v 2 (volume.restrict B)) :
    DeGiorgi.HasWeakPartialDeriv (2 : Fin 3) (fun _ => 0)
      (fun y => v (planarPart y)) (cylinder B) := by
  intro ψ hψ hc hs
  have hpres : MeasurePreserving productCLE
      ((volume.restrict B).prod (volume.restrict (Ioo (-1 : ℝ) 1)))
      (volume.restrict (cylinder B)) := ⟨productCLE.continuous.measurable, productCLE_map_cylinder hB⟩
  have hleft : Integrable (fun y => v (planarPart y) *
      fderiv ℝ ψ y (EuclideanSpace.single (2 : Fin 3) 1)) (volume.restrict (cylinder B)) :=
    (planar_pullback_memLp hB hv).integrable_mul (smooth_partial_memLp hψ hc _ _)
  simp only [zero_mul, integral_zero, neg_zero]
  rw [← hpres.integral_comp productCLE.toHomeomorph.measurableEmbedding]
  have hl := hpres.integrable_comp_of_integrable hleft
  change Integrable (fun p : E2 × ℝ => v (planarPart (productCLE p)) *
    fderiv ℝ ψ (productCLE p) (EuclideanSpace.single (2 : Fin 3) 1)) _ at hl
  rw [integral_prod _ hl]
  simp only [productCLE_apply, planarPart_lifted]
  have he (x : E2) : (∫ t in Ioo (-1 : ℝ) 1,
      v x * fderiv ℝ ψ (liftedPoint x t) (EuclideanSpace.single (2 : Fin 3) 1)) = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · simpa [gradient3_coordinate, coordinateVector] using vertical_integral hψ hc x (v x) 0
    · intro t ht
      have hy : liftedPoint x t ∉ tsupport ψ := by
        intro hy
        have ht' := (hs hy).2
        exact ht (abs_lt.mp ht')
      rw [fderiv_of_notMem_tsupport ℝ hy]
      simp
  simp only [he, integral_zero]

noncomputable def planarLiftWitness {B : Set E2} (hB : IsOpen B)
    {v : E2 → ℝ} (hv : DeGiorgi.MemW1pWitness 2 v B) :
    DeGiorgi.MemW1pWitness 2 (fun y => v (planarPart y)) (cylinder B) where
  memLp := planar_pullback_memLp hB hv.memLp
  weakGrad := fun y => liftedPoint (hv.weakGrad (planarPart y)) 0
  weakGrad_component_memLp := by
    intro i
    fin_cases i
    · exact planar_pullback_memLp hB (hv.weakGrad_component_memLp 0)
    · exact planar_pullback_memLp hB (hv.weakGrad_component_memLp 1)
    · exact MemLp.zero
  isWeakGrad := by
    intro i
    fin_cases i
    · exact horizontal_pullback_weak hB hv.memLp (hv.weakGrad_component_memLp 0) 0 (hv.isWeakGrad 0)
    · exact horizontal_pullback_weak hB hv.memLp (hv.weakGrad_component_memLp 1) 1 (hv.isWeakGrad 1)
    · exact vertical_pullback_weak hB hv.memLp

noncomputable def verticalWitness {B : Set E2} (hB : IsOpen B) (hBbdd : Bornology.IsBounded B) :
    DeGiorgi.MemW1pWitness 2 (fun y : E3 => y 2) (cylinder B) where
  memLp := vertical_memLp hB hBbdd
  weakGrad := fun _ => EuclideanSpace.single (2 : Fin 3) 1
  weakGrad_component_memLp := by
    letI := cylinder_finite hB hBbdd
    intro i
    exact memLp_const _
  isWeakGrad := by
    intro i
    have h := DeGiorgi.HasWeakPartialDeriv.of_contDiff (cylinder_open hB)
      (i := i) (EuclideanSpace.proj (2 : Fin 3)).contDiff
    convert h using 1
    · funext y
      have he : fderiv ℝ (fun z : E3 => z 2) y = EuclideanSpace.proj (2 : Fin 3) :=
        (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).hasFDerivAt.fderiv
      change (EuclideanSpace.single (2 : Fin 3) 1) i =
        fderiv ℝ (fun z : E3 => z 2) y (EuclideanSpace.single i 1)
      rw [he]
      simp [EuclideanSpace.single, PiLp.single_apply, eq_comm]
    · rfl


end Helpers

theorem R3_lift_memW1p
    (B : Set E2) (hB : IsOpen B) (hBbdd : Bornology.IsBounded B)
    (v : E2 → ℝ) (hv : DeGiorgi.MemW1pWitness 2 v B) :
    DeGiorgi.MemW1p 2 (liftFunction v) (cylinder B) ∧
      DeGiorgi.HasWeakGrad (liftGradient hv.weakGrad) (liftFunction v) (cylinder B) := by
  let hw := (Helpers.planarLiftWitness hB hv).add (Helpers.verticalWitness hB hBbdd)
  have he : hw.weakGrad = liftGradient hv.weakGrad := by
    funext y; ext i; fin_cases i <;>
      simp [hw, DeGiorgi.MemW1pWitness.add, Helpers.planarLiftWitness,
        Helpers.verticalWitness, liftGradient, liftedPoint, EuclideanSpace.single]
  exact ⟨hw.memW1p, he ▸ hw.isWeakGrad⟩

end SeifertSurfaces.QuasilinearProviderBridge
