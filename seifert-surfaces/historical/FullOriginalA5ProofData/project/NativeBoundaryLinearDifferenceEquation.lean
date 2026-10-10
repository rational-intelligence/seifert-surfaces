import NativeBoundaryFiniteNormalGain
import QuotientBasic

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization

def nativeLinearDifferenceCoefficients
    (C : LinearizedCoefficients) (v : E2 → ℝ) (k : Fin 2) (h : ℝ) : LinearizedCoefficients where
  a x := C.a (shift k h x)
  c := 0
  d x := h⁻¹ • (C.d (shift k h x) - C.d x) +
    (h⁻¹ • (C.a (shift k h x) - C.a x)) (planarGradient v x)
  b := 0
  q := 0
  f := 0

theorem native_linear_difference_flux
    (C : LinearizedCoefficients) (v : E2 → ℝ)
    (hc : C.c = 0) (k : Fin 2) (h : ℝ) (x : E2)
    (hgradient : planarGradient (differenceQuotient v k h) x =
      h⁻¹ • (planarGradient v (shift k h x) - planarGradient v x)) :
    linearizedFlux (nativeLinearDifferenceCoefficients C v k h)
      (differenceQuotient v k h) (planarGradient (differenceQuotient v k h)) x =
      h⁻¹ • (linearizedFlux C v (planarGradient v) (shift k h x) -
        linearizedFlux C v (planarGradient v) x) := by
  simp only [linearizedFlux, nativeLinearDifferenceCoefficients, hc, Pi.zero_apply,
    smul_zero, add_zero, hgradient, map_smul, map_sub, smul_apply, sub_apply]
  simp only [smul_sub]
  module

theorem native_linear_difference_weak_equation
    (Ω B : Set E2) (hΩ : IsOpen Ω) (hB : IsOpen B) (hsub : B ⊆ Ω)
    (C : LinearizedCoefficients) (v : E2 → ℝ)
    (hv : ContDiffOn ℝ 1 v Ω)
    (hc : C.c = 0) (hb : C.b = 0) (hq : C.q = 0) (hf : C.f = 0)
    (hw : LinearWeakEquation Ω C v (planarGradient v))
    (k : Fin 2) (h : ℝ) (hne : h ≠ 0) (hshift : MapsTo (shift k h) B Ω) :
    LinearWeakEquation B (nativeLinearDifferenceCoefficients C v k h)
      (differenceQuotient v k h) (planarGradient (differenceQuotient v k h)) := by
  let z := h • coordinateVector 2 k
  have hwT := native_linear_weak_translation Ω hΩ.measurableSet z C v (planarGradient v) hw
  have hpre : B ⊆ (fun x : E2 => x + z) ⁻¹' Ω := hshift
  have hwS := native_linear_weak_restrict _ B hB hpre _ _ _ hwT
  have hwO := native_linear_weak_restrict Ω B hB hsub C v (planarGradient v) hw
  have hsource (x : E2) : linearizedSource C v (planarGradient v) x = 0 := by
    simp [linearizedSource, hb, hq, hf]
  have hsourceS (x : E2) :
      linearizedSource (translateLinearizedCoefficients C z) (fun y => v (y + z))
        (fun y => planarGradient v (y + z)) x = 0 := by
    change linearizedSource C v (planarGradient v) (x + z) = 0
    exact hsource _
  intro φ hs hcompact ht
  obtain ⟨hiS, _, hzS⟩ := hwS φ hs hcompact ht
  obtain ⟨hiO, _, hzO⟩ := hwO φ hs hcompact ht
  have hnewsource (x : E2) :
      linearizedSource (nativeLinearDifferenceCoefficients C v k h)
        (differenceQuotient v k h) (planarGradient (differenceQuotient v k h)) x = 0 := by
    simp [linearizedSource, nativeLinearDifferenceCoefficients]
  have hflux (x : E2) (hx : x ∈ B) := native_linear_difference_flux C v hc k h x
    (R2_differenceQuotient_gradient Ω hΩ v hv k h hne x (hsub hx) (hshift hx))
  let fS := fun x => inner ℝ
    (linearizedFlux (translateLinearizedCoefficients C z) (fun y => v (y + z))
      (fun y => planarGradient v (y + z)) x) (planarGradient φ x)
  let fO := fun x => inner ℝ (linearizedFlux C v (planarGradient v) x) (planarGradient φ x)
  have hInt : IntegrableOn (fun x => h⁻¹ * (fS x - fO x)) B :=
    (hiS.sub hiO).const_mul h⁻¹
  have hEq : (fun x => inner ℝ
      (linearizedFlux (nativeLinearDifferenceCoefficients C v k h)
        (differenceQuotient v k h) (planarGradient (differenceQuotient v k h)) x)
      (planarGradient φ x)) =ᵐ[volume.restrict B]
      (fun x => h⁻¹ * (fS x - fO x)) := by
    filter_upwards [ae_restrict_mem hB.measurableSet] with x hx
    rw [hflux x hx, real_inner_smul_left, inner_sub_left]
    rfl
  refine ⟨hInt.congr hEq.symm, by simp only [hnewsource, zero_mul]; exact integrable_zero _ _ _, ?_⟩
  simp only [hsourceS, zero_mul, sub_zero] at hzS
  simp only [hsource, zero_mul, sub_zero] at hzO
  simp only [hnewsource, zero_mul, sub_zero]
  rw [integral_congr_ae hEq, integral_const_mul, integral_sub hiS hiO]
  change h⁻¹ * ((∫ x in B, fS x) - (∫ x in B, fO x)) = 0
  rw [show (∫ x in B, fS x) = 0 from hzS, show (∫ x in B, fO x) = 0 from hzO]
  simp

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
