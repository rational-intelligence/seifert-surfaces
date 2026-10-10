import ActualEmbeddedImageIdentificationV921

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped Manifold ContDiff
open Set Topology
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
noncomputable section
namespace CompressionActualSupportedSurfaceRemainderHomeomorphV923

/-- The actual ambient surface and removed-region image maps determine
    the full remainder homeomorphism, with native boundary and fixed
    exterior marking identities derived pointwise. -/
theorem supported_surface_remainder_homeomorph
    {S : CompactOrientedSurface.{0}} {M : Type}
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    (f : NeatEmbedding S M) {D : InteriorCompressingDisk f}
    (A B : CompressionAnnulus D) (g : M ≃ₜ M)
    (hS : g '' range f.toFun = range f.toFun)
    (hRemoved : g '' (f.toFun '' A.removed) = f.toFun '' B.removed)
    (hbd : ∀ y,y ∈ (𝓡∂ 3).boundary M → g y = y)
    (V : Set M) (hoff : ∀ y,y ∉ V → g y = y) :
    ∃ r : A.Remainder ≃ₜ B.Remainder,
      (∀ x,f.toFun (r x).val = g (f.toFun x.val)) ∧
      (∀ x,(r x).val ∈ S.boundary ↔ x.val ∈ S.boundary) ∧
      ∀ x,f.toFun x.val ∉ V → (r x).val = x.val := by
  obtain ⟨h,hh⟩ := CompressionActualEmbeddedImageIdentificationV921.embedded_image_identification
    f.toFun f.smoothEmbedding.isEmbedding f.toFun f.smoothEmbedding.isEmbedding g hS
  have hRemovedIff (x : S) : x ∈ A.removed ↔ h x ∈ B.removed := by
    constructor
    · intro hx
      have hy : g (f.toFun x) ∈ f.toFun '' B.removed := hRemoved ▸ ⟨f.toFun x,⟨x,hx,rfl⟩,rfl⟩
      obtain ⟨y,hy,hye⟩ := hy
      have he : y = h x := f.smoothEmbedding.isEmbedding.injective (hye.trans (hh x).symm)
      exact he ▸ hy
    · intro hx
      have hy : f.toFun (h x) ∈ g '' (f.toFun '' A.removed) := hRemoved.symm ▸ ⟨h x,hx,rfl⟩
      obtain ⟨y,⟨p,hp,rfl⟩,hye⟩ := hy
      have he : p = x := f.smoothEmbedding.isEmbedding.injective (g.injective (hye.trans (hh x)))
      exact he ▸ hp
  let r : A.Remainder ≃ₜ B.Remainder := h.subtype (fun x => not_congr (hRemovedIff x))
  have hr (x : A.Remainder) : f.toFun (r x).val = g (f.toFun x.val) := hh x.val
  have hbdiff (y : M) : g y ∈ (𝓡∂ 3).boundary M ↔ y ∈ (𝓡∂ 3).boundary M := by
    constructor
    · intro hy
      have he : y = g y := g.injective (hbd _ hy).symm
      exact he.symm ▸ hy
    · intro hy
      rwa [hbd y hy]
  refine ⟨r,hr,?_,?_⟩
  · intro x
    change (r x).val ∈ S.boundary ↔ x.val ∈ S.boundary
    rw [← f.boundary_preimage]
    change f.toFun (r x).val ∈ (𝓡∂ 3).boundary M ↔ f.toFun x.val ∈ (𝓡∂ 3).boundary M
    rw [hr]
    exact hbdiff _
  · intro x hx
    apply f.smoothEmbedding.isEmbedding.injective
    rw [hr,hoff _ hx]

#print axioms supported_surface_remainder_homeomorph
end CompressionActualSupportedSurfaceRemainderHomeomorphV923
