import NativeBoundaryOddGradient
import WeakTestExtension

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization
open SeifertSurfaces.QuasilinearProviderBridge.EnergyHelpers

/-- Native C1 is enough to construct the actual reflected weak equation.
The flux/source L2 hypotheses are discharged from the actual bounded
coefficients and the compact closed half-disc C1 state. -/
theorem native_c1_zero_trace_reflected_linear_equation
    (ρ κ M : ℝ) (hρ : 0 < ρ) (C : LinearizedCoefficients) (v : E2 → ℝ)
    (hv : ContDiffOn ℝ 1 v (closedHalfDisc ρ))
    (hz : ∀ x ∈ flatBoundary ρ, v x = 0)
    (hb : CoefficientBounds (openHalfDisc ρ) C κ M)
    (hm : CoefficientMeasurableOn (openHalfDisc ρ) C)
    (hw : LinearWeakEquation (openHalfDisc ρ) C v (planarGradient v)) :
    ContDiffOn ℝ 1 (nativeOddExtension v) (Metric.ball 0 ρ) ∧
      CoefficientBounds (Metric.ball 0 ρ) (reflectLinearizedCoefficients C κ) κ (M + κ) ∧
      LinearWeakEquation (Metric.ball 0 ρ) (reflectLinearizedCoefficients C κ)
        (nativeOddExtension v) (planarGradient (nativeOddExtension v)) := by
  let U := openHalfDisc ρ
  let G := planarGradientWithin v (closedHalfDisc ρ)
  have hU : IsOpen U := openHalfDisc_isOpen ρ
  have hsub : U ⊆ closedHalfDisc ρ := openHalfDisc_subset_closedHalfDisc ρ
  have hUbd : Bornology.IsBounded U := Metric.isBounded_ball.subset (fun x hx => hx.1)
  haveI : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hUbd.measure_lt_top.ne
  obtain ⟨V, hV⟩ := (closedHalfDisc_isCompact ρ).exists_bound_of_continuousOn hv.continuousOn
  have hcG := continuousOn_planarGradientWithin_closedHalfDisc hρ hv
  obtain ⟨D, hD⟩ := (closedHalfDisc_isCompact ρ).exists_bound_of_continuousOn hcG
  have hv2 : MemLp v 2 (volume.restrict U) := by
    apply MemLp.of_bound ((hv.continuousOn.mono hsub).aestronglyMeasurable hU.measurableSet) V
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    exact hV x (hsub hx)
  have hG2 : MemLp G 2 (volume.restrict U) := by
    apply MemLp.of_bound ((hcG.mono hsub).aestronglyMeasurable hU.measurableSet) D
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    exact hD x (hsub hx)
  have hGeq : ∀ x ∈ U, G x = planarGradient v x :=
    fun x hx => planarGradientWithin_closedHalfDisc_eq v hx
  have hwG : LinearWeakEquation U C v G := by
    intro φ hs hc ht
    have heF : ∀ x ∈ U, linearizedFlux C v G x = linearizedFlux C v (planarGradient v) x :=
      fun x hx => by simp only [linearizedFlux, hGeq x hx]
    have heS : ∀ x ∈ U, linearizedSource C v G x = linearizedSource C v (planarGradient v) x :=
      fun x hx => by simp only [linearizedSource, hGeq x hx]
    obtain ⟨hiF, hiS, heq⟩ := hw φ hs hc ht
    refine ⟨hiF.congr_fun (fun x hx => by rw [heF x hx]) hU.measurableSet,
      hiS.congr_fun (fun x hx => by rw [heS x hx]) hU.measurableSet, ?_⟩
    calc
      _ = ∫ x in U, inner ℝ (linearizedFlux C v (planarGradient v) x) (planarGradient φ x) -
          linearizedSource C v (planarGradient v) x * φ x := by
        apply setIntegral_congr_fun hU.measurableSet
        intro x hx
        dsimp only
        rw [heF x hx, heS x hx]
      _ = 0 := heq
  obtain ⟨hF, hS⟩ := linearized_fields_memLp U hU hUbd C v G κ M hb hm hv2 hG2
  have hwR := native_linearized_equation_odd_reflection 0 (by simp) ρ κ C v G hF hS hwG
  obtain ⟨hcR, hGR⟩ := native_odd_extension_actual_gradient hρ hv hz
  refine ⟨hcR, native_reflected_coefficient_bounds 0 (by simp) ρ κ M C hb, ?_⟩
  intro φ hs hc ht
  have heG : ∀ x ∈ Metric.ball 0 ρ, planarGradient (nativeOddExtension v) x = nativeOddGradient G x := hGR
  obtain ⟨hiF, hiS, heq⟩ := hwR φ hs hc ht
  have heF : ∀ x ∈ Metric.ball 0 ρ,
      linearizedFlux (reflectLinearizedCoefficients C κ) (nativeOddExtension v)
        (planarGradient (nativeOddExtension v)) x =
      linearizedFlux (reflectLinearizedCoefficients C κ) (nativeOddExtension v) (nativeOddGradient G) x :=
    fun x hx => by simp only [linearizedFlux, heG x hx]
  have heS : ∀ x ∈ Metric.ball 0 ρ,
      linearizedSource (reflectLinearizedCoefficients C κ) (nativeOddExtension v)
        (planarGradient (nativeOddExtension v)) x =
      linearizedSource (reflectLinearizedCoefficients C κ) (nativeOddExtension v) (nativeOddGradient G) x :=
    fun x hx => by simp only [linearizedSource, heG x hx]
  refine ⟨hiF.congr_fun (fun x hx => by rw [heF x hx]) Metric.isOpen_ball.measurableSet,
    hiS.congr_fun (fun x hx => by rw [heS x hx]) Metric.isOpen_ball.measurableSet, ?_⟩
  calc
    _ = ∫ x in Metric.ball 0 ρ,
      inner ℝ (linearizedFlux (reflectLinearizedCoefficients C κ) (nativeOddExtension v) (nativeOddGradient G) x)
          (planarGradient φ x) -
        linearizedSource (reflectLinearizedCoefficients C κ) (nativeOddExtension v) (nativeOddGradient G) x * φ x := by
      apply setIntegral_congr_fun Metric.isOpen_ball.measurableSet
      intro x hx
      dsimp only
      rw [heF x hx, heS x hx]
    _ = 0 := heq

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
