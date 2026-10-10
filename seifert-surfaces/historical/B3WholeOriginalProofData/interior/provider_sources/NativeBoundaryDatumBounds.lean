import NativeBoundaryDirichletLinearization
import NativeBoundaryUniformHolder

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization

theorem native_smooth_gradient_on_open
    (U : Set E2) (hU : IsOpen U) (f : E2 → ℝ)
    (hf : ContDiffOn ℝ ∞ f U) : ContDiffOn ℝ ∞ (planarGradient f) U := by
  unfold planarGradient
  apply ContDiffOn.sum
  intro i hi
  exact ((hf.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const).smul
    contDiffOn_const

theorem SmoothDirichletDatum.smooth_extension_on_ball
    {ρ : ℝ} (g : SmoothDirichletDatum ρ) :
    ContDiffOn ℝ ∞ (fun x : E2 => g.value (x 1)) (Metric.ball 0 ρ) := by
  apply g.smooth.comp (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff.contDiffOn
  intro x hx
  have hn : ‖x‖ < ρ := by simpa only [Metric.mem_ball, dist_zero_right] using hx
  have hcl : |x 1| ≤ ‖x‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x (1 : Fin 2) (p := 2)
  have hc : |x 1| < ρ := hcl.trans_lt hn
  exact abs_lt.mp hc

/-- The original smooth datum supplies a uniform bound for both its actual
tangential quotient and its ordinary gradient, before the quotient step. -/
theorem SmoothDirichletDatum.uniform_tangent_quotient_bounds
    {ρ : ℝ} (g : SmoothDirichletDatum ρ) (c : E2) (s r : ℝ)
    (_hs : 0 < s) (_hr : 0 ≤ r) (hK : Metric.closedBall c s ⊆ Metric.ball 0 ρ) (hrs : r < s) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ h : ℝ, h ≠ 0 → |h| < s - r →
      ∀ x ∈ Metric.closedBall c r,
        |differenceQuotient (fun x : E2 => g.value (x 1)) 1 h x| ≤ D ∧
        ‖planarGradient (differenceQuotient (fun x : E2 => g.value (x 1)) 1 h) x‖ ≤ D := by
  let f : E2 → ℝ := fun x => g.value (x 1)
  have hf := g.smooth_extension_on_ball
  obtain ⟨L, hL⟩ := (hf.mono hK).exists_lipschitzOnWith (by simp)
    (convex_closedBall _ _) (isCompact_closedBall _ _)
  obtain ⟨G, hG⟩ := ((native_smooth_gradient_on_open _ Metric.isOpen_ball f hf).mono hK).exists_lipschitzOnWith
    (by simp) (convex_closedBall _ _) (isCompact_closedBall _ _)
  refine ⟨max (L : ℝ) (G : ℝ), L.coe_nonneg.trans (le_max_left _ _), ?_⟩
  intro h hh hhr x hx
  have hxS : x ∈ Metric.closedBall c s := Metric.closedBall_subset_closedBall hrs.le hx
  have hshiftS : shift 1 h x ∈ Metric.closedBall c s := by
    change dist (shift 1 h x) c ≤ s
    calc
      dist (shift 1 h x) c ≤ dist (shift 1 h x) x + dist x c := dist_triangle _ _ _
      _ ≤ |h| + r := by
        rw [QuotientHelpers.shift_distance]
        have : dist x c ≤ r := by simpa [Metric.mem_closedBall, dist_comm c] using hx
        linarith
      _ ≤ s := by linarith
  refine ⟨(native_quotient_bound_of_lipschitz hL 1 hh hxS hshiftS).trans (le_max_left _ _), ?_⟩
  rw [R2_differenceQuotient_gradient (Metric.ball 0 ρ) Metric.isOpen_ball f
    (hf.of_le (by simp)) 1 h hh x (hK hxS) (hK hshiftS), norm_smul, Real.norm_eq_abs, abs_inv]
  have hd := hG.dist_le_mul (shift 1 h x) hshiftS x hxS
  rw [dist_eq_norm, QuotientHelpers.shift_distance] at hd
  have hm : |h|⁻¹ * ‖planarGradient f (shift 1 h x) - planarGradient f x‖ ≤ G := by
    calc
      _ ≤ |h|⁻¹ * ((G : ℝ) * |h|) := mul_le_mul_of_nonneg_left hd (by positivity)
      _ = G := by field_simp
  exact hm.trans (le_max_right _ _)

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
