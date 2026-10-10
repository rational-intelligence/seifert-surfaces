import ActualAnnulusOppositeSidesV777
import ActualAnnulusTimeReflectionV779
import ActualOriginalAnnulusAmbientExtensionV868

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Topology
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
open CompressionActualAnnulusHalfCoordinatesV772
open CompressionActualAnnulusTimeReflectionV779
noncomputable section
namespace CompressionActualAnnulusSideNormalizationV869

/-- Normalize the two half labels by the identity or time reflection;
    the opposite-side choice is derived from the literal open core embedding. -/
theorem annulus_side_normalization
    (β : C(Circle × Time,Circle × Time)) (hβ : IsEmbedding β)
    (hcore : ∀ z,β (z,middleTime) = (z,middleTime))
    (hopen : IsOpen (β '' (univ ×ˢ Ioo (0:Time) 1))) :
    ∃ R : Circle × Time ≃ₜ Circle × Time,
      (R = Homeomorph.refl _ ∨ R = reflection) ∧
      (∀ z,R (z,middleTime) = (z,middleTime)) ∧
      ∀ k p,side k (β (R (half k p))) := by
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
    exact ⟨Homeomorph.refl _,Or.inl rfl,fun _ => rfl,hside⟩
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
    exact ⟨reflection,Or.inr rfl,reflection_core,hside⟩

#print axioms annulus_side_normalization

end CompressionActualAnnulusSideNormalizationV869
