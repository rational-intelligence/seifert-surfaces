import NativeBoundaryFiniteHolderCalculus

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity

/-- Translation preserves every actual finite within-cap Holder jet. -/
theorem NativeCapHolder.translate
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (c : E2) (hcf : c 0 = 0) (r : ℝ) (hr : 0 < r)
    {α : ℝ≥0} {n : ℕ} {f : E2 → F}
    (hf : NativeCapHolder (nativeClosedBoundaryCap c r) α n f) :
    NativeCapHolder (closedHalfDisc r) α n (fun x => f (x + c)) := by
  let K := nativeClosedBoundaryCap c r
  let V := closedHalfDisc r
  have hpre := (native_flat_translation_halfDisc c hcf r).2
  have hmap : MapsTo (fun x : E2 => x + c) V K := by
    intro x hx
    exact (Set.ext_iff.mp hpre x).mpr hx
  induction n generalizing f with
  | zero =>
    obtain ⟨A, hA⟩ := hf
    refine ⟨A, ?_⟩
    intro x hx y hy
    simpa only [edist_add_right] using hA (x + c) (hmap hx) (y + c) (hmap hy)
  | succ n ih =>
    refine ⟨hf.1.comp (contDiff_id.add contDiff_const).contDiffOn hmap, ?_⟩
    intro i
    apply (ih (hf.2 i)).congr
    intro x hx
    dsimp only
    have hp : HasFDerivAt (fun x : E2 => x + c) (ContinuousLinearMap.id ℝ E2) x :=
      (hasFDerivAt_id x).add_const _
    have hpdiff : DifferentiableWithinAt ℝ (fun x : E2 => x + c) V x :=
      hp.differentiableAt.differentiableWithinAt
    have hfdiff : DifferentiableWithinAt ℝ f K (x + c) :=
      hf.1.differentiableOn (by simp) _ (hmap hx)
    have hd := fderivWithin_comp x hfdiff hpdiff hmap (closedHalfDisc_uniqueDiffOn hr x hx)
    have hpder := hp.hasFDerivWithinAt.fderivWithin (closedHalfDisc_uniqueDiffOn hr x hx)
    rw [hpder] at hd
    simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using
      congrArg (fun L : E2 →L[ℝ] F => L (coordinateVector 2 i)) hd

theorem NativeCapHolder.translate_back
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (c : E2) (hcf : c 0 = 0) (r : ℝ) (hr : 0 < r)
    {α : ℝ≥0} {n : ℕ} {f : E2 → F}
    (hf : NativeCapHolder (closedHalfDisc r) α n (fun x => f (x + c))) :
    NativeCapHolder (nativeClosedBoundaryCap c r) α n f := by
  let K := nativeClosedBoundaryCap c r
  let V := closedHalfDisc r
  have hpre := (native_flat_translation_halfDisc c hcf r).2
  have hmap : MapsTo (fun x : E2 => x + -c) K V := by
    intro x hx
    exact (Set.ext_iff.mp hpre (x + -c)).mp
      (show (x + -c) + c ∈ nativeClosedBoundaryCap c r by
        simpa only [neg_add_cancel_right] using hx)
  induction n generalizing f with
  | zero =>
    obtain ⟨A, hA⟩ := hf
    refine ⟨A, ?_⟩
    intro x hx y hy
    simpa only [neg_add_cancel_right, edist_add_right] using
      hA (x + -c) (hmap hx) (y + -c) (hmap hy)
  | succ n ih =>
    have hC : ContDiffOn ℝ ((n + 1 : ℕ) : ℕ∞ω) f K := by
      simpa only [Function.comp_def, id_eq, neg_add_cancel_right] using
        hf.1.comp (contDiff_id.add contDiff_const).contDiffOn hmap
    refine ⟨hC, ?_⟩
    intro i
    apply ih
    apply (hf.2 i).congr
    intro x hx
    dsimp only
    have hp : HasFDerivAt (fun x : E2 => x + c) (ContinuousLinearMap.id ℝ E2) x :=
      (hasFDerivAt_id x).add_const _
    have hmaps : MapsTo (fun x : E2 => x + c) V K := by
      intro y hy
      exact (Set.ext_iff.mp hpre y).mpr hy
    have hpdiff : DifferentiableWithinAt ℝ (fun x : E2 => x + c) V x :=
      hp.differentiableAt.differentiableWithinAt
    have hfdiff : DifferentiableWithinAt ℝ f K (x + c) :=
      hC.differentiableOn (by simp) _ (hmaps hx)
    have hd := fderivWithin_comp x hfdiff hpdiff hmaps (closedHalfDisc_uniqueDiffOn hr x hx)
    have hpder := hp.hasFDerivWithinAt.fderivWithin (closedHalfDisc_uniqueDiffOn hr x hx)
    rw [hpder] at hd
    simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using
      (congrArg (fun L : E2 →L[ℝ] F => L (coordinateVector 2 i)) hd).symm

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
