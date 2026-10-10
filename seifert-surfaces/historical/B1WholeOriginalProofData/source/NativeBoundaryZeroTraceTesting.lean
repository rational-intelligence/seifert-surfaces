import NativeBoundaryOddExtension
import SmoothFlatZeroH10
import PlanarGradientLinearComp

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak.BoundaryContinuation

theorem coordinateSwap_zero (x : E2) : coordinateSwap x 0 = x 1 := by
  simp [coordinateSwap]

theorem coordinateSwap_one (x : E2) : coordinateSwap x 1 = x 0 := by
  simp [coordinateSwap]

theorem coordinateSwap_involutive (x : E2) : coordinateSwap (coordinateSwap x) = x := by
  ext i
  fin_cases i <;> simp [coordinateSwap]

theorem coordinateSwap_adjoint (x : E2) :
    coordinateSwap.toContinuousLinearEquiv.toContinuousLinearMap.adjoint x = coordinateSwap x := by
  rw [show coordinateSwap.toContinuousLinearEquiv.toContinuousLinearMap =
    (coordinateSwap : E2 →L[ℝ] E2) from rfl, coordinateSwap.adjoint_eq_symm]
  apply coordinateSwap.injective
  change coordinateSwap (coordinateSwap.symm x) = coordinateSwap (coordinateSwap x)
  rw [coordinateSwap.apply_symm_apply, coordinateSwap_involutive]

theorem coordinateSwap_gradient (ψ : E2 → ℝ) (hψ : ContDiff ℝ ∞ ψ) (x : E2) :
    planarGradient (fun y => ψ (coordinateSwap y)) x =
      coordinateSwap (planarGradient ψ (coordinateSwap x)) := by
  exact (planar_gradient_linear_comp coordinateSwap.toContinuousLinearEquiv ψ hψ x).trans
    (coordinateSwap_adjoint _)

/-- The paid zero-trace approximation, transported to the actual normal
coordinate 0 with both the function and its actual gradient. -/
theorem native_smooth_flat_zero_h10 (ρ : ℝ) (ψ : E2 → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (ht : tsupport ψ ⊆ Metric.ball 0 ρ)
    (hflat : ∀ x : E2, x 0 = 0 → ψ x = 0) :
    H10On (openHalfDisc ρ) ψ (planarGradient ψ) := by
  let P := coordinateSwap.toContinuousLinearEquiv
  let ψs : E2 → ℝ := fun y => ψ (coordinateSwap y)
  have hs : ContDiff ℝ ∞ ψs := hψ.comp P.contDiff
  have hcs : HasCompactSupport ψs := hc.comp_homeomorph P.toHomeomorph
  have hts : tsupport ψs ⊆ disc ρ := by
    rw [show ψs = ψ ∘ P.toHomeomorph from rfl, tsupport_comp_eq_preimage]
    intro y hy
    have hh := ht hy
    change coordinateSwap y ∈ Metric.ball 0 ρ at hh
    change dist y 0 < ρ
    simpa only [Metric.mem_ball, dist_zero_right, coordinateSwap.norm_map] using hh
  have hfs : ∀ y : E2, y 1 = 0 → ψs y = 0 := by
    intro y hy
    exact hflat _ (by rw [coordinateSwap_zero]; exact hy)
  have hh := linear_h10_pullback (halfDisc ρ) P ψs (planarGradient ψs)
    (smooth_flat_zero_h10 ρ ψs hs hcs hts hfs)
  have hpre : P ⁻¹' halfDisc ρ = openHalfDisc ρ := by
    ext x
    simp only [mem_preimage, halfDisc, disc, openHalfDisc, mem_setOf_eq,
      mem_inter_iff, Metric.mem_ball, dist_zero_right]
    change (‖coordinateSwap x‖ < ρ ∧ 0 < coordinateSwap x 1) ↔
      (‖x‖ < ρ ∧ 0 < x 0)
    rw [coordinateSwap.norm_map, coordinateSwap_one]
  have hf : (fun y => ψs (P y)) = ψ := by
    funext y
    exact congrArg ψ (coordinateSwap_involutive y)
  have hg : (fun y => P.toContinuousLinearMap.adjoint (planarGradient ψs (P y))) =
      planarGradient ψ := by
    funext y
    rw [show planarGradient ψs (P y) = coordinateSwap
      (planarGradient ψ (coordinateSwap (coordinateSwap y))) from coordinateSwap_gradient ψ hψ _,
      coordinateSwap_involutive]
    exact (coordinateSwap_adjoint _).trans (coordinateSwap_involutive _)
  rw [hpre, hf, hg] at hh
  exact hh

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
