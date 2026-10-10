import CurveComplexGenusTwo.Topology.CompletedJordan
import Mathlib
open Set Schoenflies
/-- Plane version: an axis-aligned short support region is disjoint from every nonzero
full lattice translate. -/
theorem plane_narrow_box_lattice_disjoint
    (K : Set Plane) (T a b w h : ℝ) (hT : 0 < T)
    (hw : w < T) (hh : h < T)
    (hbox : ∀ z ∈ K, a ≤ z 0 ∧ z 0 ≤ a+w ∧ b ≤ z 1 ∧ z 1 ≤ b+h) :
    ∀ v : ℤ × ℤ, v ≠ 0 → Disjoint K
      ((fun z : Plane => z + Plane.mk ((v.1:ℝ)*T) ((v.2:ℝ)*T)) '' K) := by
  intro v hv
  apply Set.disjoint_left.mpr
  intro z hz hzv
  obtain ⟨q,hq,rfl⟩ := hzv
  have hzbox := hbox (q + Plane.mk ((v.1:ℝ)*T) ((v.2:ℝ)*T)) hz
  change a ≤ q 0 + (v.1:ℝ)*T ∧ q 0 + (v.1:ℝ)*T ≤ a+w ∧
    b ≤ q 1 + (v.2:ℝ)*T ∧ q 1 + (v.2:ℝ)*T ≤ b+h at hzbox
  have hqbox := hbox q hq
  have hv1 : v.1 ≠ 0 ∨ v.2 ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hv (Prod.ext hn.1 hn.2)
  rcases hv1 with hv1 | hv2
  · have hvabs : (1:ℝ) ≤ |(v.1:ℝ)| := by
      exact_mod_cast (Int.one_le_abs hv1)
    have hlt : |(v.1:ℝ)*T| < T := by
      rw [abs_lt]
      constructor <;> linarith [hzbox.1, hzbox.2.1, hqbox.1, hqbox.2.1]
    rw [abs_mul, abs_of_pos hT] at hlt
    nlinarith [mul_le_mul_of_nonneg_right hvabs hT.le]
  · have hvabs : (1:ℝ) ≤ |(v.2:ℝ)| := by
      exact_mod_cast (Int.one_le_abs hv2)
    have hlt : |(v.2:ℝ)*T| < T := by
      rw [abs_lt]
      constructor <;> linarith [hzbox.2.1, hzbox.2.2, hqbox.2.1, hqbox.2.2]
    rw [abs_mul, abs_of_pos hT] at hlt
    nlinarith [mul_le_mul_of_nonneg_right hvabs hT.le]
#print axioms plane_narrow_box_lattice_disjoint
