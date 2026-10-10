import ActualJordanLineCutFactoryV807

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Topology
open Schoenflies
noncomputable section
namespace CompressionActualNestedCrosscutCellLabelsV808

/-- Each inner cell belongs to exactly one outer cell. Both labels occur:
    the common chord approaches both outer cells inside the inner domain.
    This derives compatible labels rather than assuming an annular tiling. -/
theorem nested_cell_labels
    (U V K U₁ U₂ V₁ V₂ : Set Plane)
    (hU : IsOpen U) (hUV : U ⊆ V)
    (hUc : U \ K = U₁ ∪ U₂) (hVc : V \ K = V₁ ∪ V₂)
    (hU₁ : IsConnected U₁) (hU₂ : IsConnected U₂)
    (hV₁ : IsOpen V₁) (hV₂ : IsOpen V₂) (hVsep : Disjoint V₁ V₂)
    (y : Plane) (hy : y ∈ U)
    (hy₁ : y ∈ closure V₁) (hy₂ : y ∈ closure V₂) :
    (U₁ ⊆ V₁ ∧ U₂ ⊆ V₂) ∨ (U₁ ⊆ V₂ ∧ U₂ ⊆ V₁) := by
  have hsub (i : Set Plane) (hi : i ⊆ U₁ ∪ U₂) : i ⊆ V₁ ∪ V₂ := by
    intro x hx
    have hxin : x ∈ U \ K := hUc.symm ▸ hi hx
    exact hVc ▸ (show x ∈ V \ K from ⟨hUV hxin.1,hxin.2⟩)
  have h₁ := hU₁.isPreconnected.subset_or_subset hV₁ hV₂ hVsep
    (hsub U₁ subset_union_left)
  have h₂ := hU₂.isPreconnected.subset_or_subset hV₁ hV₂ hVsep
    (hsub U₂ subset_union_right)
  have hboth₁ : ¬ (U₁ ⊆ V₁ ∧ U₂ ⊆ V₁) := by
    rintro ⟨ha,hb⟩
    obtain ⟨z,hzU,hz₂⟩ := mem_closure_iff.mp hy₂ U hU hy
    have hzVK : z ∈ V \ K := hVc.symm ▸ (Or.inr hz₂)
    have hzUK : z ∈ U \ K := ⟨hzU,hzVK.2⟩
    have hz₁ : z ∈ V₁ := (union_subset ha hb) (hUc ▸ hzUK)
    exact disjoint_left.mp hVsep hz₁ hz₂
  have hboth₂ : ¬ (U₁ ⊆ V₂ ∧ U₂ ⊆ V₂) := by
    rintro ⟨ha,hb⟩
    obtain ⟨z,hzU,hz₁⟩ := mem_closure_iff.mp hy₁ U hU hy
    have hzVK : z ∈ V \ K := hVc.symm ▸ (Or.inl hz₁)
    have hzUK : z ∈ U \ K := ⟨hzU,hzVK.2⟩
    have hz₂ : z ∈ V₂ := (union_subset ha hb) (hUc ▸ hzUK)
    exact disjoint_left.mp hVsep hz₁ hz₂
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · exact False.elim (hboth₁ ⟨h₁,h₂⟩)
  · exact Or.inl ⟨h₁,h₂⟩
  · exact Or.inr ⟨h₁,h₂⟩
  · exact False.elim (hboth₂ ⟨h₁,h₂⟩)

/-- The same labelling also controls whole closed cells, including every
    boundary point, by monotonicity of closure. -/
theorem nested_closed_cell_labels
    (U V K U₁ U₂ V₁ V₂ : Set Plane)
    (hU : IsOpen U) (hUV : U ⊆ V)
    (hUc : U \ K = U₁ ∪ U₂) (hVc : V \ K = V₁ ∪ V₂)
    (hU₁ : IsConnected U₁) (hU₂ : IsConnected U₂)
    (hV₁ : IsOpen V₁) (hV₂ : IsOpen V₂) (hVsep : Disjoint V₁ V₂)
    (y : Plane) (hy : y ∈ U)
    (hy₁ : y ∈ closure V₁) (hy₂ : y ∈ closure V₂) :
    (closure U₁ ⊆ closure V₁ ∧ closure U₂ ⊆ closure V₂) ∨
      (closure U₁ ⊆ closure V₂ ∧ closure U₂ ⊆ closure V₁) := by
  rcases nested_cell_labels U V K U₁ U₂ V₁ V₂ hU hUV hUc hVc
      hU₁ hU₂ hV₁ hV₂ hVsep y hy hy₁ hy₂ with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · exact Or.inl ⟨closure_mono h₁,closure_mono h₂⟩
  · exact Or.inr ⟨closure_mono h₁,closure_mono h₂⟩

#print axioms nested_cell_labels
#print axioms nested_closed_cell_labels
end CompressionActualNestedCrosscutCellLabelsV808
