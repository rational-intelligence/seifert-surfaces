import NativeBoundaryReflectedCoefficients

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization

theorem native_odd_extension_actual_gradient
    {ρ : ℝ} (hρ : 0 < ρ) {v : E2 → ℝ}
    (hv : ContDiffOn ℝ 1 v (closedHalfDisc ρ))
    (hz : ∀ x ∈ flatBoundary ρ, v x = 0) :
    ContDiffOn ℝ 1 (nativeOddExtension v) (Metric.ball 0 ρ) ∧
      ∀ x ∈ Metric.ball 0 ρ,
        planarGradient (nativeOddExtension v) x =
          nativeOddGradient (planarGradientWithin v (closedHalfDisc ρ)) x := by
  obtain ⟨hc, _, hd⟩ := c1_native_odd_extension hρ hv hz
  refine ⟨hc, ?_⟩
  intro x hx
  by_cases hp : 0 ≤ x 0
  · simp only [planarGradient, hd x hx, ite_eq_left hp, nativeOddGradient, planarGradientWithin]
  · simp only [planarGradient, hd x hx, ite_eq_right hp, nativeOddGradient]
    ext i
    fin_cases i
    · simp [planarGradientWithin, Fin.sum_univ_two, coordinateVector, normalReflection,
        show PiLp.single 2 (0 : Fin 2) (-1 : ℝ) = -EuclideanSpace.single 0 1 from by
          ext j; fin_cases j <;> simp]
    · simp [planarGradientWithin, Fin.sum_univ_two, coordinateVector, normalReflection]

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
