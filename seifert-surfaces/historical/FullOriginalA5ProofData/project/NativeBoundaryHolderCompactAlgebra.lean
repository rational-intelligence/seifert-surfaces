import NativeBoundaryHigherJetComposition

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity

theorem native_compact_holder_mul_exists (K : Set E2) (hK : IsCompact K)
    (f g : E2 → ℝ) (α : ℝ≥0) (hα : 0 < α)
    (hf : ∃ A, HolderOnWith A α f K) (hg : ∃ B, HolderOnWith B α g K) :
    ∃ C, HolderOnWith C α (fun x => f x * g x) K := by
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  obtain ⟨Mf, hMf⟩ := hK.exists_bound_of_continuousOn (hA.continuousOn hα)
  obtain ⟨Mg, hMg⟩ := hK.exists_bound_of_continuousOn (hB.continuousOn hα)
  refine ⟨A * Real.toNNReal Mg + Real.toNNReal Mf * B, ?_⟩
  exact native_holder_mul K f g A B (Real.toNNReal Mf) (Real.toNNReal Mg) α hA hB
    (fun x hx => by simpa only [Real.norm_eq_abs] using (hMf x hx).trans (Real.le_coe_toNNReal Mf))
    (fun x hx => by simpa only [Real.norm_eq_abs] using (hMg x hx).trans (Real.le_coe_toNNReal Mg))

theorem native_compact_holder_sub_exists (K : Set E2) (f g : E2 → ℝ) (α : ℝ≥0)
    (hf : ∃ A, HolderOnWith A α f K) (hg : ∃ B, HolderOnWith B α g K) :
    ∃ C, HolderOnWith C α (fun x => f x - g x) K := by
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  exact ⟨A + B, native_holder_sub K f g A B α hA hB⟩

theorem native_compact_holder_div_exists (K : Set E2) (hK : IsCompact K)
    (f g : E2 → ℝ) (α : ℝ≥0) (hα : 0 < α)
    (κ : ℝ) (hκ : 0 < κ) (hpos : ∀ x ∈ K, κ ≤ g x)
    (hf : ∃ A, HolderOnWith A α f K) (hg : ∃ B, HolderOnWith B α g K) :
    ∃ C, HolderOnWith C α (fun x => f x / g x) K := by
  obtain ⟨B, hB⟩ := hg
  simpa only [div_eq_mul_inv] using native_compact_holder_mul_exists K hK f
    (fun x => (g x)⁻¹) α hα hf
    ⟨B / Real.toNNReal (κ ^ 2), native_holder_inv_positive K g B α κ hκ hB hpos⟩

theorem native_derivative_holder_cap_restrict
    (c : E2) (hcf : c 0 = 0) (r s : ℝ) (hs : 0 < s) (hsr : s ≤ r)
    (f : E2 → ℝ) (hf : ContDiffOn ℝ 1 f (nativeClosedBoundaryCap c r)) (α : ℝ≥0)
    (hH : ∀ i, ∃ C, HolderOnWith C α
      (fun x => fderivWithin ℝ f (nativeClosedBoundaryCap c r) x (coordinateVector 2 i))
      (nativeClosedBoundaryCap c r)) :
    ∀ i, ∃ C, HolderOnWith C α
      (fun x => fderivWithin ℝ f (nativeClosedBoundaryCap c s) x (coordinateVector 2 i))
      (nativeClosedBoundaryCap c s) := by
  have hsub : nativeClosedBoundaryCap c s ⊆ nativeClosedBoundaryCap c r := fun x hx =>
    ⟨Metric.closedBall_subset_closedBall hsr hx.1, hx.2⟩
  have hEq (x : E2) (hx : x ∈ nativeClosedBoundaryCap c s) :
      fderivWithin ℝ f (nativeClosedBoundaryCap c s) x =
      fderivWithin ℝ f (nativeClosedBoundaryCap c r) x :=
    fderivWithin_subset hsub (nativeClosedBoundaryCap_uniqueDiffOn c s hs hcf x hx)
      (hf.differentiableOn (by norm_num) x (hsub hx))
  intro i
  obtain ⟨C, hC⟩ := hH i
  refine ⟨C, ?_⟩
  intro x hx y hy
  change edist ((fderivWithin ℝ f (nativeClosedBoundaryCap c s) x) (coordinateVector 2 i))
      ((fderivWithin ℝ f (nativeClosedBoundaryCap c s) y) (coordinateVector 2 i)) ≤ _
  rw [hEq x hx, hEq y hy]
  exact hC x (hsub hx) y (hsub hy)

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
