import ActualOriginalAnnulusSurfaceNormalStraighteningV918

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Topology
noncomputable section
namespace CompressionActualEmbeddedImageIdentificationV921

/-- A concrete ambient image equality induces the exact domain
    homeomorphism, retaining every point label by embedding injectivity. -/
theorem embedded_image_identification
    {X Y M : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace M]
    (f : X → M) (hf : IsEmbedding f) (h : Y → M) (hh : IsEmbedding h)
    (g : M ≃ₜ M) (heq : g '' range f = range h) :
    ∃ q : X ≃ₜ Y,∀ x,h (q x) = g (f x) := by
  have hiff (z : M) : z ∈ range f ↔ g z ∈ range h := by
    constructor
    · intro hz
      exact heq ▸ ⟨z,hz,rfl⟩
    · intro hz
      obtain ⟨w,hw,hwe⟩ := heq.symm ▸ hz
      exact g.injective hwe ▸ hw
  let q : X ≃ₜ Y := hf.toHomeomorph.trans ((g.subtype hiff).trans hh.toHomeomorph.symm)
  refine ⟨q,?_⟩
  intro x
  have hp := hh.toHomeomorph.apply_symm_apply ((g.subtype hiff) (hf.toHomeomorph x))
  exact congrArg Subtype.val hp

#print axioms embedded_image_identification
end CompressionActualEmbeddedImageIdentificationV921
