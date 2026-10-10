import NativeBoundaryFiniteHolderProducts
import NativeBoundaryFiniteHolderDerivatives

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity

theorem NativeCapHolder.neg
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set E2} (hKD : UniqueDiffOn ℝ K) {α : ℝ≥0} {n : ℕ} {f : E2 → F}
    (hf : NativeCapHolder K α n f) : NativeCapHolder K α n (fun x => -f x) := by
  simpa only [neg_one_smul, neg_apply, smul_apply, ContinuousLinearMap.id_apply] using
    hf.comp_linear hKD ((-1 : ℝ) • ContinuousLinearMap.id ℝ F)

theorem NativeCapHolder.sub
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set E2} (hKD : UniqueDiffOn ℝ K) {α : ℝ≥0} {n : ℕ} {f g : E2 → F}
    (hf : NativeCapHolder K α n f) (hg : NativeCapHolder K α n g) :
    NativeCapHolder K α n (fun x => f x - g x) := by
  simpa only [sub_eq_add_neg] using hf.add hKD (hg.neg hKD)

theorem NativeCapHolder.smul_const
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set E2} (hKD : UniqueDiffOn ℝ K) {α : ℝ≥0} {n : ℕ} {f : E2 → ℝ}
    (hf : NativeCapHolder K α n f) (v : F) :
    NativeCapHolder K α n (fun x => f x • v) := by
  simpa only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply] using
    hf.comp_linear hKD ((ContinuousLinearMap.id ℝ ℝ).smulRight v)

theorem NativeCapHolder.mul
    (c : E2) (r : ℝ) (hr : 0 < r) (hcf : c 0 = 0)
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α ≤ 1) {n : ℕ} {f g : E2 → ℝ}
    (hf : NativeCapHolder (nativeClosedBoundaryCap c r) α n f)
    (hg : NativeCapHolder (nativeClosedBoundaryCap c r) α n g) :
    NativeCapHolder (nativeClosedBoundaryCap c r) α n (fun x => f x * g x) := by
  have hh := (hf.comp_linear (nativeClosedBoundaryCap_uniqueDiffOn c r hr hcf)
    (ContinuousLinearMap.mul ℝ ℝ)).clm_apply c r hr hcf hα hα1 hg
  simpa only [ContinuousLinearMap.mul_apply'] using hh

theorem NativeCapHolder.inv_positive
    (c : E2) (r κ : ℝ) (hr : 0 < r) (hcf : c 0 = 0) (hκ : 0 < κ)
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α ≤ 1) {n : ℕ} {f : E2 → ℝ}
    (hf : NativeCapHolder (nativeClosedBoundaryCap c r) α n f)
    (hpos : ∀ x ∈ nativeClosedBoundaryCap c r, κ ≤ f x) :
    NativeCapHolder (nativeClosedBoundaryCap c r) α n (fun x => (f x)⁻¹) := by
  let K := nativeClosedBoundaryCap c r
  have hK : IsCompact K := (isCompact_closedBall c r).inter_right
    (isClosed_le continuous_const (EuclideanSpace.proj (0 : Fin 2)).continuous)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hf.contDiffOn hα).continuousOn
  have hmap : MapsTo f K (Icc κ M) := fun x hx =>
    ⟨hpos x hx, (le_abs_self (f x)).trans (by simpa only [Real.norm_eq_abs] using hM x hx)⟩
  have hTJ : Icc κ M ⊆ ({0}ᶜ : Set ℝ) := by
    intro x hx
    exact (hκ.trans_le hx.1).ne'
  exact hf.comp_smooth c r hr hcf hα hα1 {0}ᶜ (Icc κ M) isOpen_compl_singleton
    isCompact_Icc (convex_Icc κ M) hTJ Inv.inv (contDiffOn_inv (𝕜 := ℝ)) f hmap

theorem NativeCapHolder.div_positive
    (c : E2) (r κ : ℝ) (hr : 0 < r) (hcf : c 0 = 0) (hκ : 0 < κ)
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α ≤ 1) {n : ℕ} {f g : E2 → ℝ}
    (hf : NativeCapHolder (nativeClosedBoundaryCap c r) α n f)
    (hg : NativeCapHolder (nativeClosedBoundaryCap c r) α n g)
    (hpos : ∀ x ∈ nativeClosedBoundaryCap c r, κ ≤ g x) :
    NativeCapHolder (nativeClosedBoundaryCap c r) α n (fun x => f x / g x) := by
  simpa only [div_eq_mul_inv] using
    hf.mul c r hr hcf hα hα1 (hg.inv_positive c r κ hr hcf hκ hα hα1 hpos)

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
