import ActualContainedAnnulusCoordinatesV778
import ActualAnnulusWholeFamilyWithSideChoiceV780

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Topology
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
noncomputable section
namespace CompressionActualContainedToOriginalAnnulusFamilyV781

/-- Transition from the entire contained band to the ENTIRE literal original
    arbitrary band, confined to that original band and fixing all core labels.
    The optional reflection is derived and recorded in the exact first endpoint. -/
theorem contained_to_literal_original_annulus_family
    {n : ℕ} {L : OrientedLink n} {T : TubularNeighborhood L}
    (E : SmoothExterior T) (F : LinkSpanningSurface.{0} E)
    (D : InteriorCompressingDisk F.embedding) (A B : CompressionAnnulus D)
    (hBA : range B.band ⊆ A.removed) :
    ∃ R : Circle × Time ≃ₜ Circle × Time,
      (R = Homeomorph.refl _ ∨ R = CompressionActualAnnulusTimeReflectionV779.reflection) ∧
      (∀ z,R (z,middleTime) = (z,middleTime)) ∧
      ∃ H : C(Time × (Circle × Time),F.surface),
        (∀ s,IsEmbedding (fun p => H (s,p))) ∧
        (∀ p,H (0,p) = B.band (R p)) ∧ (∀ p,H (1,p) = A.band p) ∧
        (∀ s z,H (s,(z,middleTime)) = D.surfaceLoop z) ∧
        (range H ⊆ range A.band) ∧
        ∀ s p,H (s,p) ∈ range D.surfaceLoop ↔ p.2 = middleTime := by
  obtain ⟨β,hβ,hβval,hβcore,hβopen⟩ :=
    CompressionActualContainedAnnulusCoordinatesV778.contained_annulus_coordinates E F D A B hBA
  obtain ⟨R,hR,hRc,G,hG,hG0,hG1,hGc⟩ :=
    CompressionActualAnnulusWholeFamilyWithSideChoiceV780.whole_annulus_relative_family_with_side_choice
      β hβ hβcore hβopen
  let H : C(Time × (Circle × Time),F.surface) := ⟨A.band ∘ G,A.band.continuous.comp G.continuous⟩
  have hHcore (s : Time) (z : Circle) : H (s,(z,middleTime)) = D.surfaceLoop z := by
    change A.band (G (s,(z,middleTime))) = _
    rw [hGc,A.center]
  refine ⟨R,hR,hRc,H,fun s => A.embedded.comp (hG s),?_,?_,hHcore,?_,?_⟩
  · intro p
    change A.band (G (0,p)) = _
    rw [hG0,hβval]
  · intro p
    change A.band (G (1,p)) = _
    rw [hG1]
  · rintro x ⟨p,rfl⟩
    exact mem_range_self (G p)
  · intro s p
    constructor
    · rintro ⟨z,hz⟩
      have he : H (s,p) = H (s,(z,middleTime)) := hz.symm.trans (hHcore s z).symm
      have hp : p = (z,middleTime) := (A.embedded.comp (hG s)).injective he
      exact congrArg (fun q : Circle × Time => q.2) hp
    · intro hp
      have he : p = (p.1,middleTime) := Prod.ext rfl hp
      rw [he,hHcore]
      exact mem_range_self p.1

end CompressionActualContainedToOriginalAnnulusFamilyV781
