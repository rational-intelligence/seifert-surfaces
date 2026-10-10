import ActualOriginalSurgeryPointIdentificationV922

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set Topology
open SeifertSurfaces.Foundations
noncomputable section
namespace CompressionActualSupportedAmbientRoundingCompositionV924

theorem supported_ambient_rounding_composition
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    (I₀ I₁ : TopologicalAmbientIsotopy M) (V₀ V₁ : Set M)
    (hV₀ : IsOpen V₀) (hV₁ : IsOpen V₁)
    (hoff₀ : ∀ t x,x ∉ V₀ → I₀.stage t x = x)
    (hoff₁ : ∀ t x,x ∉ V₁ → I₁.stage t x = x)
    (hbd₀ : ∀ t x,x ∈ (𝓡∂ 3).boundary M → I₀.stage t x = x)
    (hbd₁ : ∀ t x,x ∈ (𝓡∂ 3).boundary M → I₁.stage t x = x) :
    ∃ I : TopologicalAmbientIsotopy M,
      IsOpen (V₀ ∪ V₁) ∧
      (∀ t x,I.stage t x = I₁.stage t (I₀.stage t x)) ∧
      (∀ t x,x ∉ V₀ ∪ V₁ → I.stage t x = x) ∧
      ∀ t x,x ∈ (𝓡∂ 3).boundary M → I.stage t x = x := by
  let I : TopologicalAmbientIsotopy M := {
    stage := fun t => (I₀.stage t).trans (I₁.stage t)
    continuous_family := I₁.continuous_family.comp
      (continuous_fst.prodMk I₀.continuous_family)
    initial := by intro x; change I₁.stage 0 (I₀.stage 0 x) = x; rw [I₀.initial,I₁.initial]
    boundary_setwise := by
      intro t
      change (I₁.stage t ∘ I₀.stage t) '' _ = _
      rw [Set.image_comp,I₀.boundary_setwise,I₁.boundary_setwise] }
  refine ⟨I,hV₀.union hV₁,fun _ _ => rfl,?_,?_⟩
  · intro t x hx
    change I₁.stage t (I₀.stage t x) = x
    rw [hoff₀ t x (fun h => hx (Or.inl h)),hoff₁ t x (fun h => hx (Or.inr h))]
  · intro t x hx
    change I₁.stage t (I₀.stage t x) = x
    rw [hbd₀ t x hx,hbd₁ t x hx]

#print axioms supported_ambient_rounding_composition
end CompressionActualSupportedAmbientRoundingCompositionV924
