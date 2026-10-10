import NativeBoundaryFiniteHolderCalculus

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity

universe u

theorem NativeCapHolder.clm_apply
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (c : E2) (r : ℝ) (hr : 0 < r) (hcf : c 0 = 0)
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α ≤ 1) {n : ℕ}
    {a : E2 → F →L[ℝ] G} {v : E2 → F}
    (ha : NativeCapHolder (nativeClosedBoundaryCap c r) α n a)
    (hv : NativeCapHolder (nativeClosedBoundaryCap c r) α n v) :
    NativeCapHolder (nativeClosedBoundaryCap c r) α n (fun x => a x (v x)) := by
  let K := nativeClosedBoundaryCap c r
  have hKD := nativeClosedBoundaryCap_uniqueDiffOn c r hr hcf
  induction n generalizing a v with
  | zero =>
    have hK : IsCompact K := (isCompact_closedBall c r).inter_right
      (isClosed_le continuous_const (EuclideanSpace.proj (0 : Fin 2)).continuous)
    exact native_compact_holder_clm_apply_exists K hK a v α hα ha hv
  | succ n ih =>
    refine ⟨ha.1.clm_apply hv.1, ?_⟩
    intro i
    have hp := ih (ha.lower c r hr hα1) (hv.2 i)
    have hq := ih (ha.2 i) (hv.lower c r hr hα1)
    apply (hp.add hKD hq).congr
    intro x hx
    dsimp only
    rw [fderivWithin_clm_apply (hKD x hx) (ha.1.differentiableOn (by simp) x hx)
      (hv.1.differentiableOn (by simp) x hx), add_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]

theorem NativeCapHolder.of_contDiffOn_succ
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (c : E2) (r : ℝ) (hr : 0 < r) (hcf : c 0 = 0)
    {α : ℝ≥0} (hα1 : α ≤ 1) {n : ℕ} {f : E2 → F}
    (hf : ContDiffOn ℝ ((n + 1 : ℕ) : ℕ∞ω) f (nativeClosedBoundaryCap c r)) :
    NativeCapHolder (nativeClosedBoundaryCap c r) α n f := by
  induction n generalizing f with
  | zero => exact native_contDiffOn_cap_holder c r hr f α hα1 hf
  | succ n ih =>
    refine ⟨hf.of_le (by exact_mod_cast Nat.le_succ (n + 1)), ?_⟩
    intro i
    exact ih ((hf.fderivWithin (nativeClosedBoundaryCap_uniqueDiffOn c r hr hcf)
      (by simp)).clm_apply contDiffOn_const)

/-- Smooth composition preserves the exact finite within-cap Holder jets.
The attained image lies in a genuine compact convex subset of the original
open smoothness domain. -/
theorem NativeCapHolder.comp_smooth
    {F G : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (c : E2) (r : ℝ) (hr : 0 < r) (hcf : c 0 = 0)
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α ≤ 1) {n : ℕ}
    (J T : Set F) (hJ : IsOpen J) (hT : IsCompact T) (hTc : Convex ℝ T) (hTJ : T ⊆ J)
    (f : F → G) (hf : ContDiffOn ℝ ∞ f J) (g : E2 → F)
    (hg : NativeCapHolder (nativeClosedBoundaryCap c r) α n g)
    (hmap : MapsTo g (nativeClosedBoundaryCap c r) T) :
    NativeCapHolder (nativeClosedBoundaryCap c r) α n (fun x => f (g x)) := by
  let K := nativeClosedBoundaryCap c r
  have hKD := nativeClosedBoundaryCap_uniqueDiffOn c r hr hcf
  induction n generalizing G f g with
  | zero =>
    obtain ⟨A, hA⟩ := hg
    obtain ⟨L, hL⟩ := (hf.mono hTJ).exists_lipschitzOnWith (by simp) hTc hT
    refine ⟨L * A, ?_⟩
    simpa only [Function.comp_def, NNReal.coe_one, NNReal.rpow_one, one_mul] using
      hL.holderOnWith.comp hA hmap
  | succ n ih =>
    refine ⟨(hf.of_le (by simp)).comp hg.1 (fun x hx => hTJ (hmap hx)), ?_⟩
    intro i
    have hDf : ContDiffOn ℝ ∞ (fderiv ℝ f) J := hf.fderiv_of_isOpen hJ (by simp)
    have hA := ih (fderiv ℝ f) hDf g (hg.lower c r hr hα1) hmap
    apply (hA.clm_apply c r hr hcf hα hα1 (hg.2 i)).congr
    intro x hx
    dsimp only
    have hh := fderiv_comp_fderivWithin x
      ((hf.contDiffAt (hJ.mem_nhds (hTJ (hmap hx)))).differentiableAt (by simp))
      (hg.1.differentiableOn (by simp) x hx) (hKD x hx)
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply] using
      congrArg (fun L : E2 →L[ℝ] G => L (coordinateVector 2 i)) hh

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
