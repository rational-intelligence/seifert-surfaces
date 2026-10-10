import ActualOriginalAnnulusRegionNormalStraighteningV930

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped Manifold ContDiff
open Set Topology
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
noncomputable section
namespace CompressionActualRestrictedNativeNormalChartV938

theorem restricted_native_normal_chart
    {n : ℕ} {L : OrientedLink n} {T : TubularNeighborhood L}
    (E : SmoothExterior T) (F : LinkSpanningSurface.{0} E)
    (u : ℝ) (hu : 0 < u) (W : Set F.surface) (hW : IsOpen W)
    (β : PartialDiffeomorph (𝓘(ℝ,ℝ).prod (𝓡∂ 2)) (𝓡∂ 3) (ℝ × F.surface) E.Carrier ∞)
    (hwide : Icc (-u) u ×ˢ W ⊆ β.source)
    (hzero : ∀ x ∈ W,β (0,x) = F.embedding.toFun x)
    (hdetect : ∀ p ∈ Icc (-u) u ×ˢ W,β p ∈ F.image ↔ p.1 = 0)
    (G : E.Carrier ≃ₜ E.Carrier)
    (hG : ∀ x,G x ∈ F.image ↔ x ∈ F.image)
    (hGfix : ∀ x ∈ F.image,G x = x) :
    ∃ N : OpenPartialHomeomorph (ℝ × F.surface) E.Carrier,
      (∀ p,N p = G (β p)) ∧
      (∀ x ∈ W,(0,x) ∈ N.source) ∧
      (∀ x ∈ W,N (0,x) = F.embedding.toFun x) ∧
      (∀ p,p ∈ N.source → (N p ∈ F.image ↔ p.1 = 0)) ∧
      ∀ p,p ∈ Ioo (-u) u ×ˢ W → p ∈ N.source := by
  let N : OpenPartialHomeomorph (ℝ × F.surface) E.Carrier :=
    (β.toOpenPartialHomeomorph.restrOpen (Ioo (-u) u ×ˢ W) (isOpen_Ioo.prod hW)).transHomeomorph G
  have hformula (p : ℝ × F.surface) : N p = G (β p) := rfl
  have hsource (p : ℝ × F.surface) (hp : p ∈ Ioo (-u) u ×ˢ W) : p ∈ N.source :=
    ⟨hwide ⟨⟨hp.1.1.le,hp.1.2.le⟩,hp.2⟩,hp⟩
  refine ⟨N,hformula,?_,?_,?_,hsource⟩
  · intro x hx
    exact hsource (0,x) ⟨⟨by linarith,hu⟩,hx⟩
  · intro x hx
    rw [hformula,hzero x hx,hGfix _ (mem_range_self _)]
  · intro p hp
    change p ∈ β.source ∩ (Ioo (-u) u ×ˢ W) at hp
    rw [hformula,hG]
    exact hdetect p ⟨⟨hp.2.1.1.le,hp.2.1.2.le⟩,hp.2.2⟩

#print axioms restricted_native_normal_chart
end CompressionActualRestrictedNativeNormalChartV938
