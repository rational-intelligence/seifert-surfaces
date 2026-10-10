import ActualAnnulusHalfRestrictionV773
import ActualAnnulusFullFamilyGluingV774
import ActualAnnulusHalfRelativeFamilyV769

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Topology
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
open CompressionActualAnnulusHalfCoordinatesV772
noncomputable section
namespace CompressionActualAnnulusWholeRelativeFamilyV775

/-- A side-preserving whole annulus embedding fixing the literal core has a
    confined whole embedding family to identity with exact endpoints. -/
theorem whole_annulus_relative_embedding_family
    (β : C(Circle × Time,Circle × Time)) (hβ : IsEmbedding β)
    (hcore : ∀ z,β (z,middleTime) = (z,middleTime))
    (hside : ∀ k p,side k (β (half k p))) :
    ∃ G : C(Time × (Circle × Time),Circle × Time),
      (∀ s,IsEmbedding (fun p => G (s,p))) ∧
      (∀ p,G (0,p) = β p) ∧ (∀ p,G (1,p) = p) ∧
      ∀ s z,G (s,(z,middleTime)) = (z,middleTime) := by
  classical
  choose βh hhalf hβh hβhcore hβhpos using fun k =>
    CompressionActualAnnulusHalfRestrictionV773.annulus_half_restriction β hβ hcore k (hside k)
  choose Γ hΓ hΓ0 hΓ1 hΓcore hΓpos using fun k =>
    CompressionActualAnnulusHalfRelativeFamilyV769.annulus_half_relative_embedding_family
      (βh k) (hβh k) (hβhcore k) (hβhpos k)
  obtain ⟨G,hGhalf,hG,hGcore⟩ :=
    CompressionActualAnnulusFullFamilyGluingV774.full_family_gluing Γ hΓ hΓcore
  refine ⟨G,hG,?_,?_,hGcore⟩
  · intro p
    obtain ⟨k,q,rfl⟩ := CompressionActualAnnulusFullFamilyGluingV774.half_cover p
    rw [hGhalf,hΓ0,hhalf]
  · intro p
    obtain ⟨k,q,rfl⟩ := CompressionActualAnnulusFullFamilyGluingV774.half_cover p
    rw [hGhalf,hΓ1]

end CompressionActualAnnulusWholeRelativeFamilyV775
