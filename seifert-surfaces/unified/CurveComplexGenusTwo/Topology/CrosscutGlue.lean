import Schoenflies.JordanSchoenflies

open Set

namespace CurveComplex

open Schoenflies

/-- Paste two compatible homeomorphisms of closed planar pieces. The image
condition on the overlap ensures that the inverse paste uses the matching
piece. -/
theorem glue_closed_homeoOn
    {D₁ D₂ E₁ E₂ : Set Plane} {F₁ G₁ F₂ G₂ : Plane → Plane}
    (hD₁ : IsClosed D₁) (hD₂ : IsClosed D₂)
    (hE₁ : IsClosed E₁) (hE₂ : IsClosed E₂)
    (h₁ : IsHomeoOn F₁ G₁ D₁ E₁)
    (h₂ : IsHomeoOn F₂ G₂ D₂ E₂)
    (hagree : ∀ x ∈ D₁ ∩ D₂, F₁ x = F₂ x)
    (himage : F₁ '' (D₁ ∩ D₂) = E₁ ∩ E₂) :
    ∃ F G : Plane → Plane,
      IsHomeoOn F G (D₁ ∪ D₂) (E₁ ∪ E₂) ∧
      (∀ x ∈ D₁, F x = F₁ x) ∧
      (∀ x ∈ D₂, F x = F₂ x) := by
  classical
  let F : Plane → Plane := fun x => if x ∈ D₁ then F₁ x else F₂ x
  let G : Plane → Plane := fun y => if y ∈ E₁ then G₁ y else G₂ y
  have hFD₁ : ∀ x ∈ D₁, F x = F₁ x := by
    intro x hx
    simp [F, hx]
  have hFD₂ : ∀ x ∈ D₂, F x = F₂ x := by
    intro x hxD₂
    by_cases hxD₁ : x ∈ D₁
    · simp [F, hxD₁, hagree x ⟨hxD₁, hxD₂⟩]
    · simp [F, hxD₁]
  have hGagree : ∀ y ∈ E₁ ∩ E₂, G₁ y = G₂ y := by
    intro y hy
    have hyImage : y ∈ F₁ '' (D₁ ∩ D₂) := by rw [himage]; exact hy
    obtain ⟨x, hx, hxy⟩ := hyImage
    have hxy₂ : F₂ x = y := (hagree x hx).symm.trans hxy
    calc
      G₁ y = G₁ (F₁ x) := by rw [hxy]
      _ = x := h₁.invOn.1 hx.1
      _ = G₂ (F₂ x) := (h₂.invOn.1 hx.2).symm
      _ = G₂ y := by rw [hxy₂]
  have hGE₁ : ∀ y ∈ E₁, G y = G₁ y := by
    intro y hy
    simp [G, hy]
  have hGE₂ : ∀ y ∈ E₂, G y = G₂ y := by
    intro y hyE₂
    by_cases hyE₁ : y ∈ E₁
    · simp [G, hyE₁, hGagree y ⟨hyE₁, hyE₂⟩]
    · simp [G, hyE₁]
  have hFmaps : MapsTo F (D₁ ∪ D₂) (E₁ ∪ E₂) := by
    intro x hx
    rcases hx with hxD₁ | hxD₂
    · rw [hFD₁ x hxD₁]
      exact Or.inl (h₁.mapsTo hxD₁)
    · rw [hFD₂ x hxD₂]
      exact Or.inr (h₂.mapsTo hxD₂)
  have hGmaps : MapsTo G (E₁ ∪ E₂) (D₁ ∪ D₂) := by
    intro y hy
    rcases hy with hyE₁ | hyE₂
    · rw [hGE₁ y hyE₁]
      exact Or.inl (h₁.mapsTo_inv hyE₁)
    · rw [hGE₂ y hyE₂]
      exact Or.inr (h₂.mapsTo_inv hyE₂)
  have hFcont : ContinuousOn F (D₁ ∪ D₂) :=
    Plane.continuousOn_union_of_isClosed hD₁ hD₂
      (h₁.continuousOn.congr (fun x hx => hFD₁ x hx))
      (h₂.continuousOn.congr (fun x hx => hFD₂ x hx))
  have hGcont : ContinuousOn G (E₁ ∪ E₂) :=
    Plane.continuousOn_union_of_isClosed hE₁ hE₂
      (h₁.continuousOn_inv.congr (fun y hy => hGE₁ y hy))
      (h₂.continuousOn_inv.congr (fun y hy => hGE₂ y hy))
  have hleft : ∀ x ∈ D₁ ∪ D₂, G (F x) = x := by
    intro x hx
    rcases hx with hxD₁ | hxD₂
    · rw [hFD₁ x hxD₁, hGE₁ (F₁ x) (h₁.mapsTo hxD₁)]
      exact h₁.invOn.1 hxD₁
    · rw [hFD₂ x hxD₂, hGE₂ (F₂ x) (h₂.mapsTo hxD₂)]
      exact h₂.invOn.1 hxD₂
  have hright : ∀ y ∈ E₁ ∪ E₂, F (G y) = y := by
    intro y hy
    rcases hy with hyE₁ | hyE₂
    · rw [hGE₁ y hyE₁, hFD₁ (G₁ y) (h₁.mapsTo_inv hyE₁)]
      exact h₁.invOn.2 hyE₁
    · rw [hGE₂ y hyE₂, hFD₂ (G₂ y) (h₂.mapsTo_inv hyE₂)]
      exact h₂.invOn.2 hyE₂
  exact ⟨F, G, ⟨hFmaps, hGmaps, hFcont, hGcont, hleft, hright⟩,
    hFD₁, hFD₂⟩

#print axioms glue_closed_homeoOn

end CurveComplex
