import NativeBoundarySchauderScalarFullGain

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity

theorem native_boundary_derivative_holder_translation
    (c : E2) (hcf : c 0 = 0) (r : ℝ) (hr : 0 < r) (v0 : E2 → ℝ)
    (hv : ContDiffOn ℝ 1 (fun x => v0 (x + c)) (closedHalfDisc r))
    (α : ℝ≥0)
    (hH : ∀ i, ∃ C : ℝ≥0, HolderOnWith C α
      (fun x => fderivWithin ℝ (fun y => v0 (y + c)) (closedHalfDisc r) x
        (coordinateVector 2 i)) (closedHalfDisc r)) :
    ContDiffOn ℝ 1 v0 (nativeClosedBoundaryCap c r) ∧
      ∀ i, ∃ C : ℝ≥0, HolderOnWith C α
        (fun x => fderivWithin ℝ v0 (nativeClosedBoundaryCap c r) x (coordinateVector 2 i))
        (nativeClosedBoundaryCap c r) := by
  let K := nativeClosedBoundaryCap c r
  let V := closedHalfDisc r
  let v := fun x => v0 (x + c)
  have hpre := (native_flat_translation_halfDisc c hcf r).2
  have hmap : MapsTo (fun x : E2 => x + -c) K V := by
    intro x hx
    exact (Set.ext_iff.mp hpre (x + -c)).mp
      (show (x + -c) + c ∈ nativeClosedBoundaryCap c r by
        simpa only [neg_add_cancel_right] using hx)
  have hC : ContDiffOn ℝ 1 v0 K := by
    simpa only [Function.comp_def, id_eq, neg_add_cancel_right] using
      hv.comp (contDiff_id.add contDiff_const).contDiffOn hmap
  refine ⟨hC, ?_⟩
  intro i
  obtain ⟨C, hC⟩ := hH i
  have hformula : ∀ x ∈ K,
      fderivWithin ℝ v0 K x (coordinateVector 2 i) =
        fderivWithin ℝ v V (x + -c) (coordinateVector 2 i) := by
    intro x hx
    have hp : HasFDerivAt (fun x : E2 => x + -c) (ContinuousLinearMap.id ℝ E2) x :=
      (hasFDerivAt_id x).add_const _
    have hEq : (v ∘ (fun x : E2 => x + -c)) = v0 := by
      funext x
      simp only [Function.comp_def, v, neg_add_cancel_right]
    have hvdiff : DifferentiableWithinAt ℝ v V (x + -c) :=
      hv.differentiableOn (by norm_num) _ (hmap hx)
    have hder := fderivWithin_comp x hvdiff
      hp.differentiableAt.differentiableWithinAt hmap
      (nativeClosedBoundaryCap_uniqueDiffOn c r hr hcf x hx)
    have hpder := hp.hasFDerivWithinAt.fderivWithin
      (nativeClosedBoundaryCap_uniqueDiffOn c r hr hcf x hx)
    rw [hEq, hpder] at hder
    exact congrArg (fun L : E2 →L[ℝ] ℝ => L (coordinateVector 2 i)) hder
  refine ⟨C, ?_⟩
  intro x hx y hy
  have hh := hC (x + -c) (hmap hx) (y + -c) (hmap hy)
  change edist ((fderivWithin ℝ v0 K x) (coordinateVector 2 i))
      ((fderivWithin ℝ v0 K y) (coordinateVector 2 i)) ≤ _
  rw [hformula x hx, hformula y hy]
  simpa only [edist_add_right] using hh

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
