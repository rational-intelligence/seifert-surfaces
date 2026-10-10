import LiftMeasurability
import NormalizedCoefficients

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology BigOperators ContDiff ENNReal
namespace SeifertSurfaces.QuasilinearProviderBridge
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.QuasilinearLocalization

namespace Helpers

noncomputable def liftWitness {B : Set E2} (hB : IsOpen B) (hBbdd : Bornology.IsBounded B)
    {v : E2 → ℝ} (hv : DeGiorgi.MemW1pWitness 2 v B) :
    DeGiorgi.MemW1pWitness 2 (liftFunction v) (cylinder B) where
  memLp := (R3_lift_memW1p B hB hBbdd v hv).1.1
  weakGrad := liftGradient hv.weakGrad
  weakGrad_component_memLp := by
    letI := cylinder_finite hB hBbdd
    intro i
    fin_cases i
    · exact planar_pullback_memLp hB (hv.weakGrad_component_memLp 0)
    · exact planar_pullback_memLp hB (hv.weakGrad_component_memLp 1)
    · exact memLp_const 1
  isWeakGrad := (R3_lift_memW1p B hB hBbdd v hv).2

lemma liftWeakEquation_restrict {B B' : Set E3} (hsub : B' ⊆ B)
    {A : E3 → Matrix (Fin 3) (Fin 3) ℝ} {G : E3 → E3} (h : LiftWeakEquation B A G) :
    LiftWeakEquation B' A G := by
  intro ψ hψ hc hs
  have he := h ψ hψ hc (hs.trans hsub)
  refine ⟨he.1.mono_set hsub, ?_⟩
  have hz (y : E3) (hy : y ∉ B') : inner ℝ (matrixAction (A y) (G y)) (gradient3 ψ y) = 0 := by
    rw [gradient3_zero (fun h => hy (hs h)), inner_zero_right]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := B) (fun y hy =>
      hz y (fun h => hy (hsub h)))]
  exact he.2

lemma liftWeakEquation_scale_ae {B : Set E3} {A A' : E3 → Matrix (Fin 3) (Fin 3) ℝ}
    {G : E3 → E3} (c : ℝ) (hA : A' =ᵐ[volume.restrict B] (fun y => c • A y))
    (h : LiftWeakEquation B A G) : LiftWeakEquation B A' G := by
  intro ψ hψ hc hs
  have he := h ψ hψ hc hs
  have hi : (fun y => inner ℝ (matrixAction (A' y) (G y)) (gradient3 ψ y)) =ᵐ[volume.restrict B]
      (fun y => c * inner ℝ (matrixAction (A y) (G y)) (gradient3 ψ y)) := by
    filter_upwards [hA] with y hy
    rw [hy, matrixAction_smul, inner_smul_left]
    simp
  refine ⟨(he.1.const_mul c).congr hi.symm, ?_⟩
  rw [integral_congr_ae hi, integral_const_mul, he.2, mul_zero]

end Helpers

theorem R3_lift_homogeneous_on_ball
    (B : Set E2) (hB : IsOpen B) (hBbdd : Bornology.IsBounded B)
    (C : LinearizedCoefficients)
    (v : E2 → ℝ) (κ M L : ℝ) (hκ : 0 < κ) (hM : 1 ≤ M) (hL : 0 ≤ L)
    (hmeas : CoefficientMeasurableOn B C)
    (hbound : CoefficientBounds B C κ M) (hvbound : ∀ x ∈ B, |v x| ≤ L)
    (hweak : ProviderLinearWeakEquation B C v)
    (center : E3) (R : ℝ) (hR : 0 < R) (hball : Metric.ball center R ⊆ cylinder B) :
    ∃ A : DeGiorgi.NormalizedEllipticCoeff 3 (Metric.ball center R),
      A.1.Λ = liftLambda κ M L ∧
      (∀ y ∉ Metric.ball center R, A.1.a y = 1) ∧
      (∀ᵐ y ∂(volume.restrict (Metric.ball center R)), ∀ i j : Fin 3,
        A.1.a y i j = (min (κ / 2) 1)⁻¹ * liftMatrix C v (liftD κ M L) y i j) ∧
      ProviderHomogeneousEquation (Metric.ball center R) A.1 (liftFunction v) ∧
      IntegrableOn (fun y => |liftFunction v y| ^ (2 : ℝ)) (Metric.ball center R) := by
  let hv := hweak.1.someWitness
  have hmeas3 : ∀ i j : Fin 3, AEMeasurable (fun y => liftMatrix C v (liftD κ M L) y i j)
      (volume.restrict (Metric.ball center R)) := by
    intro i j
    exact (Helpers.liftMatrix_aemeasurable hB C v (liftD κ M L) hmeas hv.memLp i j).mono_measure
      (Measure.restrict_mono_set volume hball)
  obtain ⟨A, hΛ, hexterior, hae⟩ := R3_normalized_coefficients_on_three_ball B hB C v κ M L hκ hM hL
    hbound hvbound center R hR hball hmeas3
  let hV := (Helpers.liftWitness hB hBbdd hv).restrict Metric.isOpen_ball hball
  have hA : A.1.a =ᵐ[volume.restrict (Metric.ball center R)]
      (fun y => (min (κ / 2) 1)⁻¹ • liftMatrix C v (liftD κ M L) y) := by
    filter_upwards [hae] with y hy
    ext i j
    exact hy i j
  have hraw := R3_lift_provider_weak_equation B hB hBbdd C hmeas κ M hbound v hweak hv (liftD κ M L)
  have hsmall := Helpers.liftWeakEquation_restrict hball hraw
  have hnormalized := Helpers.liftWeakEquation_scale_ae (min (κ / 2) 1)⁻¹ hA hsmall
  refine ⟨A, hΛ, hexterior, hae, ?_, ?_⟩
  · exact R3_smooth_homogeneous_tests_extend_to_H01 (Metric.ball center R) Metric.isOpen_ball
      Metric.isBounded_ball A.1 (liftFunction v) hV hnormalized
  · simpa [IntegrableOn, Real.norm_eq_abs] using hV.memLp.integrable_norm_rpow (by norm_num) (by norm_num)

end SeifertSurfaces.QuasilinearProviderBridge
