import NativeBoundaryGenericCoefficientFields

set_option autoImplicit false
set_option maxHeartbeats 50000
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity

theorem native_differentiated_forcing_holder_extension
    (c : E2) (hcf : c 0 = 0) (r : ℝ) (hr : 0 < r)
    (a : E2 → E2 →L[ℝ] E2) (d : E2 → E2) (v : E2 → ℝ)
    (α : ℝ≥0) (hα : 0 < α)
    (hDa : ∃ C, HolderOnWith C α (fderivWithin ℝ a (nativeClosedBoundaryCap c r))
      (nativeClosedBoundaryCap c r))
    (hDd : ∃ C, HolderOnWith C α (fderivWithin ℝ d (nativeClosedBoundaryCap c r))
      (nativeClosedBoundaryCap c r))
    (hDv : ∃ C, HolderOnWith C α (fderivWithin ℝ v (nativeClosedBoundaryCap c r))
      (nativeClosedBoundaryCap c r)) :
    ∃ B : ℝ, ∃ H : ℝ≥0, 0 ≤ B ∧ ∃ e : E2 → E2,
      EqOn e (fun x => -(
        fderivWithin ℝ a (nativeClosedBoundaryCap c r) x (coordinateVector 2 1)
          (planarGradientWithin v (nativeClosedBoundaryCap c r) x) +
        fderivWithin ℝ d (nativeClosedBoundaryCap c r) x (coordinateVector 2 1)))
        (nativeClosedBoundaryCap c r) ∧
      HolderWith H α e ∧ (∀ x, ‖e x‖ ≤ B) := by
  let K := nativeClosedBoundaryCap c r
  let A := fun x => fderivWithin ℝ a K x (coordinateVector 2 1)
  let D := fun x => fderivWithin ℝ d K x (coordinateVector 2 1)
  let G := planarGradientWithin v K
  let f := fun x => A x (G x) + D x
  have hK : IsCompact K := (isCompact_closedBall c r).inter_right
    (isClosed_le continuous_const (EuclideanSpace.proj (0 : Fin 2)).continuous)
  obtain ⟨Ca, hCa⟩ := native_holder_derivative_apply_const K a α hDa (coordinateVector 2 1)
  obtain ⟨Cd, hCd⟩ := native_holder_derivative_apply_const K d α hDd (coordinateVector 2 1)
  obtain ⟨Cg, hCg⟩ := native_holder_planarGradientWithin K v α hDv
  obtain ⟨Cp, hCp⟩ := native_compact_holder_clm_apply_exists K hK A G α hα ⟨Ca, hCa⟩ ⟨Cg, hCg⟩
  let H := Cp + Cd
  have hf : HolderOnWith H α f K := native_holder_add K _ D Cp Cd α hCp hCd
  obtain ⟨B0, hB0⟩ := hK.exists_bound_of_continuousOn (hf.continuousOn hα)
  let B := max B0 0
  have hn : HolderOnWith H α (fun x => -f x) K := by
    intro x hx y hy
    simpa only [edist_neg_neg] using hf x hx y hy
  obtain ⟨e, heq, heH, heB⟩ := native_holder_field_extension_on_cap c r hr.le hcf.ge
    (fun x => -f x) H α B hn (by
      intro x hx
      rw [norm_neg]
      exact (hB0 x hx).trans (le_max_left _ _))
  exact ⟨B, H, le_max_right _ _, e, heq, heH, heB⟩

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
