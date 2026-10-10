import NativeBoundaryHolderOperations

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity

theorem native_holder_neg (V : Set E2) (f : E2 → ℝ) (C α : ℝ≥0)
    (hf : HolderOnWith C α f V) : HolderOnWith C α (fun x => -f x) V := by
  intro x hx y hy
  simpa only [edist_neg_neg] using hf x hx y hy

theorem native_holder_sub (V : Set E2) (f g : E2 → ℝ) (A B α : ℝ≥0)
    (hf : HolderOnWith A α f V) (hg : HolderOnWith B α g V) :
    HolderOnWith (A + B) α (fun x => f x - g x) V := by
  simpa only [sub_eq_add_neg] using
    native_holder_add V f (fun x => -g x) A B α hf (native_holder_neg V g B α hg)

theorem native_holder_mul (V : Set E2) (f g : E2 → ℝ) (A B Mf Mg α : ℝ≥0)
    (hf : HolderOnWith A α f V) (hg : HolderOnWith B α g V)
    (hMf : ∀ x ∈ V, |f x| ≤ (Mf : ℝ)) (hMg : ∀ x ∈ V, |g x| ≤ (Mg : ℝ)) :
    HolderOnWith (A * Mg + Mf * B) α (fun x => f x * g x) V := by
  apply native_holder_of_real_distance_bound
  intro x hx y hy
  have ha : |f x - f y| ≤ (A : ℝ) * dist x y ^ (α : ℝ) := by
    simpa only [Real.dist_eq] using hf.dist_le hx hy
  have hb : |g x - g y| ≤ (B : ℝ) * dist x y ^ (α : ℝ) := by
    simpa only [Real.dist_eq] using hg.dist_le hx hy
  calc
    _ = |(f x - f y) * g x + f y * (g x - g y)| := by congr 1; ring
    _ ≤ |(f x - f y) * g x| + |f y * (g x - g y)| := abs_add_le _ _
    _ = |f x - f y| * |g x| + |f y| * |g x - g y| := by rw [abs_mul, abs_mul]
    _ ≤ ((A : ℝ) * dist x y ^ (α : ℝ)) * Mg +
        (Mf : ℝ) * ((B : ℝ) * dist x y ^ (α : ℝ)) := by
      gcongr
      · exact hMg x hx
      · exact hMf y hy
    _ = _ := by simp only [NNReal.coe_add, NNReal.coe_mul]; ring

theorem native_holder_inv_positive (V : Set E2) (f : E2 → ℝ) (C α : ℝ≥0)
    (κ : ℝ) (hκ : 0 < κ) (hf : HolderOnWith C α f V)
    (hpos : ∀ x ∈ V, κ ≤ f x) :
    HolderOnWith (C / Real.toNNReal (κ ^ 2)) α (fun x => (f x)⁻¹) V := by
  apply native_holder_of_real_distance_bound
  intro x hx y hy
  have hxpos : 0 < f x := hκ.trans_le (hpos x hx)
  have hypos : 0 < f y := hκ.trans_le (hpos y hy)
  have hden : κ ^ 2 ≤ f x * f y := by
    calc
      κ ^ 2 = κ * κ := by ring
      _ ≤ f x * f y := mul_le_mul (hpos x hx) (hpos y hy) hκ.le hxpos.le
  have hd : |f x - f y| ≤ (C : ℝ) * dist x y ^ (α : ℝ) := by
    simpa only [Real.dist_eq] using hf.dist_le hx hy
  calc
    _ = |f x - f y| / (f x * f y) := by
      rw [inv_sub_inv hxpos.ne' hypos.ne', abs_div, abs_sub_comm,
        abs_of_pos (mul_pos hxpos hypos)]
    _ ≤ ((C : ℝ) * dist x y ^ (α : ℝ)) / (κ ^ 2) := by
      exact div_le_div₀ (mul_nonneg C.coe_nonneg (Real.rpow_nonneg dist_nonneg _)) hd
        (by positivity) hden
    _ = _ := by
      rw [NNReal.coe_div, Real.coe_toNNReal _ (by positivity)]
      ring

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
