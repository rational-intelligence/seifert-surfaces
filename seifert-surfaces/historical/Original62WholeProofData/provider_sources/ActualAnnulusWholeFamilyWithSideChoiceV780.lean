import ActualAnnulusOppositeSidesV777
import ActualAnnulusTimeReflectionV779
import ActualAnnulusWholeRelativeFamilyV775

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Topology
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
open CompressionActualAnnulusHalfCoordinatesV772
open CompressionActualAnnulusTimeReflectionV779
noncomputable section
namespace CompressionActualAnnulusWholeFamilyWithSideChoiceV780

/-- The side choice is derived from the literal open annulus embedding.
    The only reparameterization is identity or time reflection, and the
    resulting full family is confined and fixes every original core point. -/
theorem whole_annulus_relative_family_with_side_choice
    (β : C(Circle × Time,Circle × Time)) (hβ : IsEmbedding β)
    (hcore : ∀ z,β (z,middleTime) = (z,middleTime))
    (hopen : IsOpen (β '' (univ ×ˢ Ioo (0:Time) 1))) :
    ∃ R : Circle × Time ≃ₜ Circle × Time,
      (R = Homeomorph.refl _ ∨ R = reflection) ∧
      (∀ z,R (z,middleTime) = (z,middleTime)) ∧
      ∃ G : C(Time × (Circle × Time),Circle × Time),
        (∀ s,IsEmbedding (fun p => G (s,p))) ∧
        (∀ p,G (0,p) = β (R p)) ∧ (∀ p,G (1,p) = p) ∧
        ∀ s z,G (s,(z,middleTime)) = (z,middleTime) := by
  classical
  obtain ⟨π,hπ⟩ :=
    CompressionActualAnnulusOppositeSidesV777.annulus_half_side_permutation β hβ hcore hopen
  by_cases hπ0 : π 0 = 0
  · have hπ1 : π 1 = 1 := Fin.eq_one_of_ne_zero _ (by
      intro he
      have h := π.injective (he.trans hπ0.symm)
      norm_num at h)
    have hside (k : Fin 2) (p : Circle × Time) : side k (β (half k p)) := by
      fin_cases k
      · change side 0 (β (half 0 p))
        simpa only [hπ0] using hπ 0 p
      · change side 1 (β (half 1 p))
        simpa only [hπ1] using hπ 1 p
    obtain ⟨G,hG,hG0,hG1,hGc⟩ :=
      CompressionActualAnnulusWholeRelativeFamilyV775.whole_annulus_relative_embedding_family β hβ hcore hside
    exact ⟨Homeomorph.refl _,Or.inl rfl,fun _ => rfl,G,hG,hG0,hG1,hGc⟩
  · have hπ0' : π 0 = 1 := Fin.eq_one_of_ne_zero _ hπ0
    have hπ1 : π 1 = 0 := by
      by_contra hn
      have he := Fin.eq_one_of_ne_zero (π 1) hn
      have h := π.injective (he.trans hπ0'.symm)
      norm_num at h
    let β' : C(Circle × Time,Circle × Time) := ⟨β ∘ reflection,β.continuous.comp reflection.continuous⟩
    have hβ' : IsEmbedding β' := hβ.comp reflection.isEmbedding
    have hc' (z : Circle) : β' (z,middleTime) = (z,middleTime) := by
      change β (reflection (z,middleTime)) = _
      rw [reflection_core,hcore]
    have hside (k : Fin 2) (p : Circle × Time) : side k (β' (half k p)) := by
      change side k (β (reflection (half k p)))
      fin_cases k
      · change side 0 (β (reflection (half 0 p)))
        rw [reflection_half_zero]
        simpa only [hπ1] using hπ 1 p
      · change side 1 (β (reflection (half 1 p)))
        rw [reflection_half_one]
        simpa only [hπ0'] using hπ 0 p
    obtain ⟨G,hG,hG0,hG1,hGc⟩ :=
      CompressionActualAnnulusWholeRelativeFamilyV775.whole_annulus_relative_embedding_family β' hβ' hc' hside
    exact ⟨reflection,Or.inr rfl,reflection_core,G,hG,hG0,hG1,hGc⟩

end CompressionActualAnnulusWholeFamilyWithSideChoiceV780
