import QuasilinearLocalization

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology BigOperators ContDiff

namespace SeifertSurfaces.QuasilinearLocalization
open SeifertSurfaces.AppendixACoordinates

theorem R2_differenceQuotient_gradient
    (Ω : Set E2) (hΩ : IsOpen Ω) (u : E2 → ℝ) (hC1 : ContDiffOn ℝ 1 u Ω)
    (k : Fin 2) (h : ℝ) (hh : h ≠ 0) (x : E2)
    (hx : x ∈ Ω) (hxshift : shift k h x ∈ Ω) :
    planarGradient (differenceQuotient u k h) x =
      (h⁻¹) • (planarGradient u (shift k h x) - planarGradient u x) := by
  have hxderiv := (hC1.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)
  have hsderiv := (hC1.contDiffAt (hΩ.mem_nhds hxshift)).differentiableAt (by simp)
  have hshift : HasFDerivAt (shift k h) (ContinuousLinearMap.id ℝ E2) x :=
    (hasFDerivAt_id x).add_const _
  have hd : HasFDerivAt (differenceQuotient u k h)
      (h⁻¹ • (fderiv ℝ u (shift k h x) - fderiv ℝ u x)) x := by
    have heq : differenceQuotient u k h = h⁻¹ • (u ∘ shift k h - u) := by
      funext y
      simp [differenceQuotient, div_eq_mul_inv, mul_comm]
    rw [heq]
    simpa using
      ((hsderiv.hasFDerivAt.comp x hshift).sub hxderiv.hasFDerivAt).const_smul h⁻¹
  apply (InnerProductSpace.toDual ℝ E2).injective
  simp only [Helpers.gradient_dual, map_smul, map_sub]
  exact hd.fderiv

end SeifertSurfaces.QuasilinearLocalization
