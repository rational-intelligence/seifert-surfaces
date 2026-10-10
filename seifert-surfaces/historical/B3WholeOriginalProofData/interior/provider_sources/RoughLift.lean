import LinearizedL2

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology BigOperators ContDiff ENNReal
namespace SeifertSurfaces.QuasilinearProviderBridge
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.QuasilinearLocalization
open Helpers

namespace Helpers
lemma lifted_inner_formula (p : E2) (s : ℝ) (ξ : E3) :
    inner ℝ (liftedPoint p s) ξ = inner ℝ p (planarPart ξ) + s * ξ 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_succ, liftedPoint, planarPart]
  ring

lemma planar_pullback_vector_memLp {B : Set E2} (hB : IsOpen B) {F : E2 → E2}
    (hF : MemLp F 2 (volume.restrict B)) :
    MemLp (fun y => F (planarPart y)) 2 (volume.restrict (cylinder B)) := by
  apply MemLp.of_eval_piLp
  intro i
  exact planar_pullback_memLp hB (vector_component_memLp _ _ hF i)

lemma vertical_mul_pullback_memLp {B : Set E2} (hB : IsOpen B) {f : E2 → ℝ}
    (hf : MemLp f 2 (volume.restrict B)) :
    MemLp (fun y : E3 => y 2 * f (planarPart y)) 2 (volume.restrict (cylinder B)) := by
  have hp := planar_pullback_memLp hB hf
  apply hp.norm.mono' (((EuclideanSpace.proj (2 : Fin 3)).continuous.measurable.aestronglyMeasurable).mul
    hp.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem (cylinder_open hB).measurableSet] with y hy
  change ‖y 2 * f (planarPart y)‖ ≤ ‖f (planarPart y)‖
  rw [norm_mul, Real.norm_eq_abs (y 2)]
  exact mul_le_of_le_one_left (norm_nonneg _) hy.2.le
end Helpers

theorem R3_lift_provider_weak_equation
    (B : Set E2) (hB : IsOpen B) (hBbdd : Bornology.IsBounded B)
    (C : LinearizedCoefficients)
    (hmeas : CoefficientMeasurableOn B C)
    (κ M : ℝ) (hbound : CoefficientBounds B C κ M)
    (v : E2 → ℝ) (hweak : ProviderLinearWeakEquation B C v)
    (hv : DeGiorgi.MemW1pWitness 2 v B) (D : ℝ) :
    LiftWeakEquation (cylinder B) (liftMatrix C v D) (liftGradient hv.weakGrad) := by
  intro ψ hψ hc hs
  let F : E2 → E2 := linearizedFlux C v hv.weakGrad
  let S : E2 → ℝ := linearizedSource C v hv.weakGrad
  let a : E3 → ℝ := fun y => inner ℝ (F (planarPart y))
      (planarPart (gradient3 ψ y)) - S (planarPart y) * ψ y
  let b : E3 → ℝ := fun y => S (planarPart y) * ψ y +
      (D + y 2 * S (planarPart y)) * gradient3 ψ y 2
  let f : E3 → ℝ := fun y => inner ℝ
      (matrixAction (liftMatrix C v D y) (liftGradient hv.weakGrad y)) (gradient3 ψ y)
  obtain ⟨hF, hS⟩ := Helpers.linearized_fields_memLp B hB hBbdd C v hv.weakGrad κ M hbound
    hmeas hv.memLp hv.weakGrad_memLp
  have hψLp : MemLp ψ 2 (volume.restrict (cylinder B)) :=
    (hψ.continuous.memLp_of_hasCompactSupport hc).restrict _
  have hD : MemLp (fun y => gradient3 ψ y 2) 2 (volume.restrict (cylinder B)) := by
    simpa only [Helpers.gradient3_apply] using smooth_partial_memLp hψ hc (cylinder B) 2
  have hP : MemLp (fun y => planarPart (gradient3 ψ y)) 2 (volume.restrict (cylinder B)) := by
    apply MemLp.of_eval_piLp
    intro i
    fin_cases i
    · simpa [planarPart, Helpers.gradient3_apply] using
        smooth_partial_memLp hψ hc (cylinder B) 0
    · simpa [planarPart, Helpers.gradient3_apply] using
        smooth_partial_memLp hψ hc (cylinder B) 1
  have hFi := integrable_inner_L2 _ _ _ (planar_pullback_vector_memLp hB hF) hP
  have hSi := (planar_pullback_memLp hB hS).integrable_mul hψLp
  have hTi : MemLp (fun y : E3 => D + y 2 * S (planarPart y)) 2
      (volume.restrict (cylinder B)) := by
    letI := cylinder_finite hB hBbdd
    exact (memLp_const D).add (vertical_mul_pullback_memLp hB hS)
  have hai : Integrable a (volume.restrict (cylinder B)) := hFi.sub hSi
  have hbi : Integrable b (volume.restrict (cylinder B)) := hSi.add (hTi.integrable_mul hD)
  have hfeq : f = fun y => a y + b y := by
    funext y
    dsimp only [f]
    rw [R3_lift_flux_identity, lifted_inner_formula]
    dsimp [a, b, F, S, linearizedSource]
    ring
  have hfi : Integrable f (volume.restrict (cylinder B)) := by rw [hfeq]; exact hai.add hbi
  have hpres : MeasurePreserving productCLE
      ((volume.restrict B).prod (volume.restrict (Ioo (-1 : ℝ) 1)))
      (volume.restrict (cylinder B)) := ⟨productCLE.continuous.measurable, productCLE_map_cylinder hB⟩
  have hapi : Integrable (fun p : E2 × ℝ => a (productCLE p))
      ((volume.restrict B).prod (volume.restrict (Ioo (-1 : ℝ) 1))) :=
    hpres.integrable_comp_of_integrable hai
  have hbpi : Integrable (fun p : E2 × ℝ => b (productCLE p))
      ((volume.restrict B).prod (volume.restrict (Ioo (-1 : ℝ) 1))) :=
    hpres.integrable_comp_of_integrable hbi
  have hasi (t : ℝ) : (∫ x in B, a (liftedPoint x t)) = 0 := by
    let φ : E2 → ℝ := fun x => ψ (liftedPoint x t)
    have hφ : ContDiff ℝ ∞ φ := hψ.comp (horizontal_smooth t)
    have hφc : HasCompactSupport φ := hc.comp_isClosedEmbedding (horizontal_closed t)
    have hφs : tsupport φ ⊆ B := by
      intro x hx
      have hy := (tsupport_comp_subset_preimage ψ (horizontal_smooth t).continuous) hx
      simpa only [planarPart_lifted] using (hs hy).1
    have hφ01 := DeGiorgi.memW01p_of_contDiff_hasCompactSupport_subset (p := 2) hB hφ hφc hφs
    let hφw := (DeGiorgi.MemW1pWitness.ofContDiffHasCompactSupport (p := 2) hφ hφc).restrict hB (subset_univ B)
    have hφgrad : hφw.weakGrad = planarGradient φ := by
      funext x; ext i; fin_cases i <;>
        simp [hφw, DeGiorgi.MemW1pWitness.restrict, DeGiorgi.MemW1pWitness.ofContDiffHasCompactSupport,
          planarGradient, Fin.sum_univ_succ, coordinateVector, EuclideanSpace.single]
    have he := (hweak.2 hv φ hφ01 hφw).2.2
    rw [hφgrad] at he
    simpa only [a, F, S, planarPart_lifted, ← horizontal_gradient hψ, φ] using he
  have hazi : (∫ y in cylinder B, a y) = 0 := by
    rw [← hpres.integral_comp productCLE.toHomeomorph.measurableEmbedding a,
      integral_prod_symm _ hapi]
    simp only [productCLE_apply, hasi, integral_zero]
  have hbsi (x : E2) : (∫ t in Ioo (-1 : ℝ) 1, b (liftedPoint x t)) = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · have hv (t : ℝ) : (liftedPoint x t) 2 = t := rfl
      simpa only [b, planarPart_lifted, hv] using vertical_integral hψ hc x D (S x)
    · intro t ht
      have hy : liftedPoint x t ∉ tsupport ψ := by
        intro hy
        exact ht (abs_lt.mp (hs hy).2)
      simp [b, gradient3_zero hy, image_eq_zero_of_notMem_tsupport hy]
  have hbzi : (∫ y in cylinder B, b y) = 0 := by
    rw [← hpres.integral_comp productCLE.toHomeomorph.measurableEmbedding b,
      integral_prod _ hbpi]
    simp only [productCLE_apply, hbsi, integral_zero]
  refine ⟨hfi, ?_⟩
  change (∫ y in cylinder B, f y) = 0
  rw [hfeq, integral_add hai hbi, hazi, hbzi, add_zero]

end SeifertSurfaces.QuasilinearProviderBridge
