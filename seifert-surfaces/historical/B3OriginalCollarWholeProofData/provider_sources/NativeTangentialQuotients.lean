import NativeBoundaryTrace
import NativeBoundaryJetTube

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization

theorem tangent_shift_norm_le (h : ℝ) (x : E2) :
    ‖shift 1 h x‖ ≤ ‖x‖ + |h| := by
  simpa only [shift, norm_smul, Real.norm_eq_abs,
    QuotientHelpers.coordinate_norm, mul_one] using norm_add_le x (h • coordinateVector 2 1)

theorem tangent_shift_normal (h : ℝ) (x : E2) : shift 1 h x 0 = x 0 := by
  simp [shift, PiLp.add_apply, PiLp.smul_apply, coordinateVector, EuclideanSpace.single]

theorem tangent_shift_maps_openHalfDisc {ρ r h : ℝ} (hh : |h| < ρ - r) :
    MapsTo (shift 1 h) (openHalfDisc r) (openHalfDisc ρ) := by
  intro x hx
  have hxn : ‖x‖ < r := by simpa only [Metric.mem_ball, dist_zero_right] using hx.1
  refine ⟨?_, ?_⟩
  · apply Metric.mem_ball.mpr
    rw [dist_zero_right]
    exact (tangent_shift_norm_le h x).trans_lt (by linarith)
  · simpa only [mem_setOf_eq, tangent_shift_normal] using hx.2

theorem tangent_shift_maps_closedHalfDisc {ρ r h : ℝ} (hh : |h| < ρ - r) :
    MapsTo (shift 1 h) (closedHalfDisc r) (closedHalfDisc ρ) := by
  intro x hx
  have hxn : ‖x‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx.1
  refine ⟨?_, ?_⟩
  · apply Metric.mem_closedBall.mpr
    rw [dist_zero_right]
    exact ((tangent_shift_norm_le h x).trans_lt (by linarith)).le
  · simpa only [mem_setOf_eq, tangent_shift_normal] using hx.2

theorem tangent_shift_maps_flatBoundary {ρ r h : ℝ} (hh : |h| < ρ - r) :
    MapsTo (shift 1 h) (flatBoundary r) (flatBoundary ρ) := by
  intro x hx
  have hxn : ‖x‖ < r := by simpa only [Metric.mem_ball, dist_zero_right] using hx.1
  refine ⟨?_, ?_⟩
  · apply Metric.mem_ball.mpr
    rw [dist_zero_right]
    exact (tangent_shift_norm_le h x).trans_lt (by linarith)
  · simpa only [mem_setOf_eq, tangent_shift_normal] using hx.2

theorem C1QuasilinearDirichletSolution.tangent_quotient_C1
    {ρ r h : ℝ} {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u) (hh : |h| < ρ - r) :
    ContDiffOn ℝ 1 (differenceQuotient u 1 h) (closedHalfDisc r) := by
  have hrρ : r < ρ := by linarith [abs_nonneg h]
  have hs : ContDiff ℝ 1 (shift 1 h) := by unfold shift; fun_prop
  have huc := (hsolution.c1.comp hs.contDiffOn (tangent_shift_maps_closedHalfDisc hh)).sub
    (hsolution.c1.mono (closedHalfDisc_mono hrρ.le))
  have heq : differenceQuotient u 1 h = h⁻¹ • (u ∘ shift 1 h - u) := by
    funext x
    simp [differenceQuotient, div_eq_mul_inv, mul_comm]
  rw [heq]
  exact huc.const_smul h⁻¹

/-- The native tangential quotient of the solution after subtracting its own
smooth boundary datum has exactly zero flat trace. The quotient family has
actual C1 regularity before any limiting derivative is introduced. -/
theorem C1QuasilinearDirichletSolution.zero_trace_tangent_quotient
    {ρ r h : ℝ} {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u) (hh : |h| < ρ - r) :
    ContDiffOn ℝ 1
      (differenceQuotient (fun x => u x - g.value (x 1)) 1 h) (closedHalfDisc r) ∧
      (∀ x ∈ flatBoundary r,
        differenceQuotient (fun x => u x - g.value (x 1)) 1 h x = 0) := by
  have hrρ : r < ρ := by linarith [abs_nonneg h]
  let s := (ρ + r + |h|) / 2
  have hrs : r < s := by dsimp [s]; linarith [abs_nonneg h]
  have hsρ : s < ρ := by dsimp [s]; linarith
  have hhs : |h| < s - r := by dsimp [s]; linarith
  have hzero := hsolution.zero_trace_subtraction hsρ
  have hsmooth : ContDiff ℝ 1 (shift 1 h) := by unfold shift; fun_prop
  have huc := (hzero.1.comp hsmooth.contDiffOn (tangent_shift_maps_closedHalfDisc hhs)).sub
    (hzero.1.mono (closedHalfDisc_mono hrs.le))
  have heq : differenceQuotient (fun x => u x - g.value (x 1)) 1 h =
      h⁻¹ • ((fun x => u x - g.value (x 1)) ∘ shift 1 h - (fun x => u x - g.value (x 1))) := by
    funext x
    simp [differenceQuotient, div_eq_mul_inv, mul_comm]
  refine ⟨by rw [heq]; exact huc.const_smul h⁻¹, ?_⟩
  intro x hx
  have h0 := hsolution.dirichlet_values x
    ⟨Metric.ball_subset_ball hrρ.le hx.1, hx.2⟩
  have h1 := hsolution.dirichlet_values (shift 1 h x) (tangent_shift_maps_flatBoundary hh hx)
  simp only [differenceQuotient, h0, h1, sub_self, zero_div]

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
