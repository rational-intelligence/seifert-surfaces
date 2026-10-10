import ActualAnnularStripAmbientChartSupportV878

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped Manifold ContDiff
open Set Topology
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
noncomputable section
namespace CompressionActualDisjointSupportedAmbientCompositionV881

theorem preserves_support
    {M : Type} [TopologicalSpace M] (g : M ≃ₜ M) (V : Set M)
    (hg : ∀ x,x ∉ V → g x = x) {x : M} (hx : x ∈ V) : g x ∈ V := by
  by_contra ho
  have he : g x = g (g x) := (hg _ ho).symm
  exact ho ((g.injective he) ▸ hx)

/-- Two disjoint supported ambient isotopies compose simultaneously and
    retain either exact stage map on the complement of the other support. -/
theorem disjoint_supported_isotopy_composition
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    (I₀ I₁ : TopologicalAmbientIsotopy M) (V₀ V₁ : Set M)
    (hV₀ : IsOpen V₀) (hV₁ : IsOpen V₁)
    (hc₀ : IsCompact (closure V₀)) (hc₁ : IsCompact (closure V₁))
    (hd : Disjoint V₀ V₁)
    (hoff₀ : ∀ t x,x ∉ V₀ → I₀.stage t x = x)
    (hoff₁ : ∀ t x,x ∉ V₁ → I₁.stage t x = x)
    (hbd₀ : ∀ t x,x ∈ (𝓡∂ 3).boundary M → I₀.stage t x = x)
    (hbd₁ : ∀ t x,x ∈ (𝓡∂ 3).boundary M → I₁.stage t x = x) :
    ∃ I : TopologicalAmbientIsotopy M,
      IsOpen (V₀ ∪ V₁) ∧ IsCompact (closure (V₀ ∪ V₁)) ∧
      (∀ t x,x ∉ V₀ ∪ V₁ → I.stage t x = x) ∧
      (∀ t x,x ∈ (𝓡∂ 3).boundary M → I.stage t x = x) ∧
      (∀ t x,x ∉ V₁ → I.stage t x = I₀.stage t x) ∧
      ∀ t x,x ∉ V₀ → I.stage t x = I₁.stage t x := by
  let I : TopologicalAmbientIsotopy M := {
    stage := fun t => (I₀.stage t).trans (I₁.stage t)
    continuous_family := I₁.continuous_family.comp
      (continuous_fst.prodMk I₀.continuous_family)
    initial := by intro x; change I₁.stage 0 (I₀.stage 0 x) = x; rw [I₀.initial,I₁.initial]
    boundary_setwise := by
      intro t
      change (I₁.stage t ∘ I₀.stage t) '' _ = _
      rw [Set.image_comp,I₀.boundary_setwise,I₁.boundary_setwise] }
  refine ⟨I,hV₀.union hV₁,?_,?_,?_,?_,?_⟩
  · rw [closure_union]
    exact hc₀.union hc₁
  · intro t x hx
    change I₁.stage t (I₀.stage t x) = x
    rw [hoff₀ t x (fun h => hx (Or.inl h)),hoff₁ t x (fun h => hx (Or.inr h))]
  · intro t x hx
    change I₁.stage t (I₀.stage t x) = x
    rw [hbd₀ t x hx,hbd₁ t x hx]
  · intro t x hx
    change I₁.stage t (I₀.stage t x) = I₀.stage t x
    apply hoff₁
    by_cases hx₀ : x ∈ V₀
    · exact fun h => disjoint_left.mp hd (preserves_support (I₀.stage t) V₀ (hoff₀ t) hx₀) h
    · rwa [hoff₀ t x hx₀]
  · intro t x hx
    change I₁.stage t (I₀.stage t x) = I₁.stage t x
    rw [hoff₀ t x hx]

#print axioms disjoint_supported_isotopy_composition
end CompressionActualDisjointSupportedAmbientCompositionV881
