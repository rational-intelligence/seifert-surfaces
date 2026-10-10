import NativeBoundaryHolderDerivativeAssembly

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity

theorem native_holder_prodMk
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (K : Set E2) (f : E2 → F) (g : E2 → G) (A B α : ℝ≥0)
    (hf : HolderOnWith A α f K) (hg : HolderOnWith B α g K) :
    HolderOnWith (A + B) α (fun x => (f x, g x)) K := by
  apply native_holder_of_norm_distance_bound
  intro x hx y hy
  have hf' : ‖f x - f y‖ ≤ (A : ℝ) * dist x y ^ (α : ℝ) := by
    simpa only [dist_eq_norm] using hf.dist_le hx hy
  have hg' : ‖g x - g y‖ ≤ (B : ℝ) * dist x y ^ (α : ℝ) := by
    simpa only [dist_eq_norm] using hg.dist_le hx hy
  simp only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, NNReal.coe_add]
  have hp : 0 ≤ dist x y ^ (α : ℝ) := Real.rpow_nonneg dist_nonneg _
  exact max_le (hf'.trans (by nlinarith [B.coe_nonneg])) (hg'.trans (by nlinarith [A.coe_nonneg]))

theorem native_holder_smul_const
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : Set E2) (f : E2 → ℝ) (C α : ℝ≥0) (hf : HolderOnWith C α f K) (z : F) :
    ∃ A, HolderOnWith A α (fun x => f x • z) K := by
  let L : ℝ →L[ℝ] F := (ContinuousLinearMap.id ℝ ℝ).smulRight z
  exact ⟨‖L‖₊ * C, native_holder_comp_linear K f C α hf L⟩

theorem native_holder_const
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : Set E2) (z : F) (α : ℝ≥0) : HolderOnWith 0 α (fun _ => z) K := by
  intro x hx y hy
  simp only [edist_self, ENNReal.coe_zero, zero_mul, le_refl]

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
