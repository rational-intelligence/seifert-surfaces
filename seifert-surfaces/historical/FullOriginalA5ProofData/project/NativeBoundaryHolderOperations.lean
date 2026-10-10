import NativeBoundaryJetHolder

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity

section
variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem native_holder_add (V : Set E2) (f g : E2 → F) (A B α : ℝ≥0)
    (hf : HolderOnWith A α f V) (hg : HolderOnWith B α g V) :
    HolderOnWith (A + B) α (fun x => f x + g x) V := by
  apply native_holder_of_norm_distance_bound
  intro x hx y hy
  have ha := hf.dist_le hx hy
  have hb := hg.dist_le hx hy
  calc
    _ = ‖(f x - f y) + (g x - g y)‖ := by congr 1; abel
    _ ≤ ‖f x - f y‖ + ‖g x - g y‖ := norm_add_le _ _
    _ ≤ (A : ℝ) * dist x y ^ (α : ℝ) + (B : ℝ) * dist x y ^ (α : ℝ) :=
      add_le_add (by simpa only [dist_eq_norm] using ha) (by simpa only [dist_eq_norm] using hb)
    _ = _ := by rw [NNReal.coe_add]; ring

theorem native_holder_clm_apply (V : Set E2) (a : E2 → F →L[ℝ] G) (v : E2 → F)
    (A B Ma Mv α : ℝ≥0) (ha : HolderOnWith A α a V) (hv : HolderOnWith B α v V)
    (hMa : ∀ x ∈ V, ‖a x‖ ≤ (Ma : ℝ)) (hMv : ∀ x ∈ V, ‖v x‖ ≤ (Mv : ℝ)) :
    HolderOnWith (A * Mv + Ma * B) α (fun x => a x (v x)) V := by
  apply native_holder_of_norm_distance_bound
  intro x hx y hy
  have hA : ‖a x - a y‖ ≤ (A : ℝ) * dist x y ^ (α : ℝ) := by simpa only [dist_eq_norm] using ha.dist_le hx hy
  have hB : ‖v x - v y‖ ≤ (B : ℝ) * dist x y ^ (α : ℝ) := by simpa only [dist_eq_norm] using hv.dist_le hx hy
  calc
    _ = ‖(a x - a y) (v x) + a y (v x - v y)‖ := by congr 1; simp only [sub_apply, map_sub]; abel
    _ ≤ ‖(a x - a y) (v x)‖ + ‖a y (v x - v y)‖ := norm_add_le _ _
    _ ≤ ‖a x - a y‖ * ‖v x‖ + ‖a y‖ * ‖v x - v y‖ :=
      add_le_add ((a x - a y).le_opNorm _) ((a y).le_opNorm _)
    _ ≤ ((A : ℝ) * dist x y ^ (α : ℝ)) * Mv + (Ma : ℝ) * ((B : ℝ) * dist x y ^ (α : ℝ)) := by
      gcongr
      · exact hMv x hx
      · exact hMa y hy
    _ = _ := by simp only [NNReal.coe_add, NNReal.coe_mul]; ring

theorem native_holder_comp_linear (V : Set E2) (f : E2 → F) (A α : ℝ≥0)
    (hf : HolderOnWith A α f V) (L : F →L[ℝ] G) :
    HolderOnWith (‖L‖₊ * A) α (fun x => L (f x)) V := by
  have hh := L.lipschitz.holderWith.comp_holderOnWith hf
  simpa only [NNReal.coe_one, NNReal.rpow_one, one_mul, Function.comp_def] using hh

end

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
