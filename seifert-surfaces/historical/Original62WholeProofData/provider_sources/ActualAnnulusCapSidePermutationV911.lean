import ActualAnnulusTimeReflectionV779

set_option autoImplicit false
open Set Topology
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
open CompressionActualAnnulusTimeReflectionV779
noncomputable section
namespace CompressionActualAnnulusCapSidePermutationV911

theorem cap_side_permutation
    (R : Circle × Time ≃ₜ Circle × Time)
    (hR : R = Homeomorph.refl _ ∨ R = reflection) :
    ∃ π : Fin 2 ≃ Fin 2,∀ k,
      (R ((1:Circle),CompressionAnnulus.sideTime k)).2 = CompressionAnnulus.sideTime (π k) := by
  rcases hR with rfl | rfl
  · exact ⟨Equiv.refl _,fun _ => rfl⟩
  · refine ⟨Equiv.swap 0 1,?_⟩
    intro k
    apply Subtype.ext
    fin_cases k <;> norm_num [reflection,reverseTimeHomeomorph,reverseTime,
      CompressionAnnulus.sideTime,Equiv.swap_apply_def]

#print axioms cap_side_permutation
end CompressionActualAnnulusCapSidePermutationV911
