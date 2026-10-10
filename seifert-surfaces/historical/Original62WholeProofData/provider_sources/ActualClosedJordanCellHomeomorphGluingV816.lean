import ActualSquareAnnularStripFactoryV814

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Topology
open Schoenflies
noncomputable section
namespace CompressionActualClosedJordanCellHomeomorphGluingV816

/-- Glue two closed-region homeomorphisms. Exact matching of the whole
    overlap, rather than just its endpoints, pays inverse agreement. -/
theorem glue_closed_regions
    {S₁ S₂ T₁ T₂ : Set Plane} {f₁ f₂ g₁ g₂ : Plane → Plane}
    (hS₁ : IsClosed S₁) (hS₂ : IsClosed S₂) (hT₁ : IsClosed T₁) (hT₂ : IsClosed T₂)
    (h₁ : IsHomeoOn f₁ g₁ S₁ T₁) (h₂ : IsHomeoOn f₂ g₂ S₂ T₂)
    (hagree : EqOn f₁ f₂ (S₁ ∩ S₂))
    (hmatch : f₁ '' (S₁ ∩ S₂) = T₁ ∩ T₂) :
    ∃ F G : Plane → Plane, IsHomeoOn F G (S₁ ∪ S₂) (T₁ ∪ T₂) ∧
      EqOn F f₁ S₁ ∧ EqOn F f₂ S₂ ∧ EqOn G g₁ T₁ ∧ EqOn G g₂ T₂ := by
  classical
  let F := S₁.piecewise f₁ f₂
  let G := T₁.piecewise g₁ g₂
  have hf₁ : EqOn F f₁ S₁ := fun x hx => Set.piecewise_eq_of_mem _ _ _ hx
  have hf₂ : EqOn F f₂ S₂ := by
    intro x hx
    by_cases hx₁ : x ∈ S₁
    · exact (hf₁ hx₁).trans (hagree ⟨hx₁,hx⟩)
    · exact Set.piecewise_eq_of_notMem _ _ _ hx₁
  have hgagree : EqOn g₁ g₂ (T₁ ∩ T₂) := by
    intro y hy
    obtain ⟨x,hx,he⟩ := hmatch.symm ▸ hy
    have he₂ : f₂ x = y := (hagree hx).symm.trans he
    have hg₁ : g₁ y = x := he ▸ h₁.invOn.1 hx.1
    have hg₂ : g₂ y = x := he₂ ▸ h₂.invOn.1 hx.2
    exact hg₁.trans hg₂.symm
  have hg₁ : EqOn G g₁ T₁ := fun y hy => Set.piecewise_eq_of_mem _ _ _ hy
  have hg₂ : EqOn G g₂ T₂ := by
    intro y hy
    by_cases hy₁ : y ∈ T₁
    · exact (hg₁ hy₁).trans (hgagree ⟨hy₁,hy⟩)
    · exact Set.piecewise_eq_of_notMem _ _ _ hy₁
  have hcF : ContinuousOn F (S₁ ∪ S₂) :=
    (h₁.continuousOn.congr hf₁).union_of_isClosed (h₂.continuousOn.congr hf₂) hS₁ hS₂
  have hcG : ContinuousOn G (T₁ ∪ T₂) :=
    (h₁.continuousOn_inv.congr hg₁).union_of_isClosed (h₂.continuousOn_inv.congr hg₂) hT₁ hT₂
  have hmapF : MapsTo F (S₁ ∪ S₂) (T₁ ∪ T₂) := by
    rintro x (hx | hx)
    · rw [hf₁ hx]
      exact Or.inl (h₁.mapsTo hx)
    · rw [hf₂ hx]
      exact Or.inr (h₂.mapsTo hx)
  have hmapG : MapsTo G (T₁ ∪ T₂) (S₁ ∪ S₂) := by
    rintro y (hy | hy)
    · rw [hg₁ hy]
      exact Or.inl (h₁.mapsTo_inv hy)
    · rw [hg₂ hy]
      exact Or.inr (h₂.mapsTo_inv hy)
  have hleft : LeftInvOn G F (S₁ ∪ S₂) := by
    rintro x (hx | hx)
    · rw [hf₁ hx,hg₁ (h₁.mapsTo hx)]
      exact h₁.invOn.1 hx
    · rw [hf₂ hx,hg₂ (h₂.mapsTo hx)]
      exact h₂.invOn.1 hx
  have hright : RightInvOn G F (T₁ ∪ T₂) := by
    rintro y (hy | hy)
    · rw [hg₁ hy,hf₁ (h₁.mapsTo_inv hy)]
      exact h₁.invOn.2 hy
    · rw [hg₂ hy,hf₂ (h₂.mapsTo_inv hy)]
      exact h₂.invOn.2 hy
  exact ⟨F,G,⟨hmapF,hmapG,hcF,hcG,hleft,hright⟩,hf₁,hf₂,hg₁,hg₂⟩

/-- Extend both prescribed Jordan boundary maps to their whole closed
    cells, then glue them. The supplied common arcs are the exact whole
    intersections of the closed cells on both sides. -/
theorem extend_and_glue_jordan_cells
    {C₁ C₂ D₁ D₂ P Q : Set Plane} {f₁ f₂ g₁ g₂ : Plane → Plane}
    (hC₁ : IsJordanCurve C₁) (hC₂ : IsJordanCurve C₂)
    (hD₁ : IsJordanCurve D₁) (hD₂ : IsJordanCurve D₂)
    (h₁ : IsHomeoOn f₁ g₁ C₁ D₁) (h₂ : IsHomeoOn f₂ g₂ C₂ D₂)
    (hPi : P ⊆ C₁ ∩ C₂)
    (hsource : closure (inside C₁) ∩ closure (inside C₂) = P)
    (htarget : closure (inside D₁) ∩ closure (inside D₂) = Q)
    (hagree : EqOn f₁ f₂ P) (hmatch : f₁ '' P = Q) :
    ∃ F G : Plane → Plane,
      IsHomeoOn F G (closure (inside C₁) ∪ closure (inside C₂))
        (closure (inside D₁) ∪ closure (inside D₂)) ∧
      EqOn F f₁ C₁ ∧ EqOn F f₂ C₂ := by
  obtain ⟨F₁,G₁,hH₁,he₁⟩ := closed_interior_extension squareExtension hC₁ hD₁ h₁
  obtain ⟨F₂,G₂,hH₂,he₂⟩ := closed_interior_extension squareExtension hC₂ hD₂ h₂
  have hcloseC₁ : C₁ ∪ inside C₁ = closure (inside C₁) := by
    rw [(IsRegionOf.inside _).closure_eq (jordan_curve_theorem hC₁),union_comm]
  have hcloseC₂ : C₂ ∪ inside C₂ = closure (inside C₂) := by
    rw [(IsRegionOf.inside _).closure_eq (jordan_curve_theorem hC₂),union_comm]
  have hcloseD₁ : D₁ ∪ inside D₁ = closure (inside D₁) := by
    rw [(IsRegionOf.inside _).closure_eq (jordan_curve_theorem hD₁),union_comm]
  have hcloseD₂ : D₂ ∪ inside D₂ = closure (inside D₂) := by
    rw [(IsRegionOf.inside _).closure_eq (jordan_curve_theorem hD₂),union_comm]
  rw [hcloseC₁,hcloseD₁] at hH₁
  rw [hcloseC₂,hcloseD₂] at hH₂
  have hagree' : EqOn F₁ F₂ (closure (inside C₁) ∩ closure (inside C₂)) := by
    intro x hx
    have hp : x ∈ P := hsource ▸ hx
    exact (he₁ (hPi hp).1).trans ((hagree hp).trans (he₂ (hPi hp).2).symm)
  have hmatch' : F₁ '' (closure (inside C₁) ∩ closure (inside C₂)) =
      closure (inside D₁) ∩ closure (inside D₂) := by
    rw [hsource,htarget]
    exact (Set.EqOn.image_eq (he₁.mono (hPi.trans inter_subset_left))).trans hmatch
  obtain ⟨F,G,hFG,hF₁,hF₂,-,-⟩ := glue_closed_regions
    isClosed_closure isClosed_closure isClosed_closure isClosed_closure hH₁ hH₂ hagree' hmatch'
  refine ⟨F,G,hFG,?_,?_⟩
  · intro x hx
    exact (hF₁ ((IsRegionOf.inside _).subset_closure (jordan_curve_theorem hC₁) hx)).trans (he₁ hx)
  · intro x hx
    exact (hF₂ ((IsRegionOf.inside _).subset_closure (jordan_curve_theorem hC₂) hx)).trans (he₂ hx)

#print axioms glue_closed_regions
#print axioms extend_and_glue_jordan_cells
end CompressionActualClosedJordanCellHomeomorphGluingV816
