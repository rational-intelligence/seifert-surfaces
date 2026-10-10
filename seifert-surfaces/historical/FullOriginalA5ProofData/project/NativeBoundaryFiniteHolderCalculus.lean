import NativeBoundaryC1HolderOperations

set_option autoImplicit false
set_option maxHeartbeats 100000
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity

/-- Finite boundary regularity, using only derivatives within the actual
closed cap. The recursion records Holder control at the final order. -/
def NativeCapHolder {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : Set E2) (α : ℝ≥0) : ℕ → (E2 → F) → Prop
  | 0, f => ∃ A, HolderOnWith A α f K
  | n + 1, f => ContDiffOn ℝ ((n + 1 : ℕ) : ℕ∞ω) f K ∧
      ∀ i : Fin 2, NativeCapHolder K α n (fun x => fderivWithin ℝ f K x (coordinateVector 2 i))

theorem NativeCapHolder.contDiffOn
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set E2} {α : ℝ≥0} (hα : 0 < α) {n : ℕ} {f : E2 → F}
    (hf : NativeCapHolder K α n f) : ContDiffOn ℝ n f K := by
  cases n with
  | zero => obtain ⟨A, hA⟩ := hf; exact contDiffOn_zero.mpr (hA.continuousOn hα)
  | succ n => exact hf.1

theorem NativeCapHolder.congr
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set E2} {α : ℝ≥0} {n : ℕ} {f g : E2 → F}
    (hf : NativeCapHolder K α n f) (he : EqOn g f K) : NativeCapHolder K α n g := by
  induction n generalizing f g with
  | zero =>
    obtain ⟨A, hA⟩ := hf
    exact ⟨A, fun x hx y hy => by rw [he hx, he hy]; exact hA x hx y hy⟩
  | succ n ih =>
    refine ⟨hf.1.congr he, fun i => ih (hf.2 i) ?_⟩
    intro x hx
    dsimp only
    rw [fderivWithin_congr' he hx]

theorem NativeCapHolder.restrict
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K V : Set E2} {α : ℝ≥0} {n : ℕ} {f : E2 → F}
    (hsub : V ⊆ K) (hVD : UniqueDiffOn ℝ V)
    (hf : NativeCapHolder K α n f) : NativeCapHolder V α n f := by
  induction n generalizing f with
  | zero => obtain ⟨A, hA⟩ := hf; exact ⟨A, hA.mono hsub⟩
  | succ n ih =>
    refine ⟨hf.1.mono hsub, ?_⟩
    intro i
    apply (ih (hf.2 i)).congr
    intro x hx
    dsimp only
    rw [fderivWithin_subset hsub (hVD x hx)
      (hf.1.differentiableOn (by simp) x (hsub hx))]

theorem NativeCapHolder.add
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set E2} (hKD : UniqueDiffOn ℝ K) {α : ℝ≥0} {n : ℕ} {f g : E2 → F}
    (hf : NativeCapHolder K α n f) (hg : NativeCapHolder K α n g) :
    NativeCapHolder K α n (fun x => f x + g x) := by
  induction n generalizing f g with
  | zero =>
    obtain ⟨A, hA⟩ := hf
    obtain ⟨B, hB⟩ := hg
    exact ⟨A + B, native_holder_add K f g A B α hA hB⟩
  | succ n ih =>
    refine ⟨hf.1.add hg.1, ?_⟩
    intro i
    apply (ih (hf.2 i) (hg.2 i)).congr
    intro x hx
    dsimp only
    rw [fderivWithin_fun_add (hKD x hx) (hf.1.differentiableOn (by simp) x hx)
      (hg.1.differentiableOn (by simp) x hx), add_apply]

theorem NativeCapHolder.comp_linear
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {K : Set E2} (hKD : UniqueDiffOn ℝ K) {α : ℝ≥0} {n : ℕ} {f : E2 → F}
    (hf : NativeCapHolder K α n f) (L : F →L[ℝ] G) :
    NativeCapHolder K α n (fun x => L (f x)) := by
  induction n generalizing f with
  | zero =>
    obtain ⟨A, hA⟩ := hf
    exact ⟨‖L‖₊ * A, native_holder_comp_linear K f A α hA L⟩
  | succ n ih =>
    refine ⟨L.contDiff.comp_contDiffOn hf.1, ?_⟩
    intro i
    apply (ih (hf.2 i)).congr
    intro x hx
    have hd := L.hasFDerivAt.comp_hasFDerivWithinAt x
      ((hf.1.differentiableOn (by simp) x hx).hasFDerivWithinAt)
    exact congrArg (fun A : E2 →L[ℝ] G => A (coordinateVector 2 i)) (hd.fderivWithin (hKD x hx))

theorem NativeCapHolder.lower
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (c : E2) (r : ℝ) (hr : 0 < r) {α : ℝ≥0} (hα1 : α ≤ 1)
    {n : ℕ} {f : E2 → F} (hf : NativeCapHolder (nativeClosedBoundaryCap c r) α (n + 1) f) :
    NativeCapHolder (nativeClosedBoundaryCap c r) α n f := by
  induction n generalizing f with
  | zero => exact native_contDiffOn_cap_holder c r hr f α hα1 hf.1
  | succ n ih =>
    refine ⟨hf.1.of_le (by exact_mod_cast Nat.le_succ (n + 1)), fun i => ih (hf.2 i)⟩

/-- The recursive C1 notion is exactly the full within derivative Holder
condition already used by the paid linear boundary gain. -/
theorem nativeCapHolder_one_iff
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : Set E2) (α : ℝ≥0) (f : E2 → F) :
    NativeCapHolder K α 1 f ↔ ContDiffOn ℝ 1 f K ∧
      ∃ A, HolderOnWith A α (fderivWithin ℝ f K) K := by
  constructor
  · intro h
    exact ⟨h.1, native_clm_holder_of_coordinate_evaluations K _ α h.2⟩
  · rintro ⟨hc, hH⟩
    exact ⟨hc, fun i => native_holder_derivative_apply_const K f α hH (coordinateVector 2 i)⟩

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
