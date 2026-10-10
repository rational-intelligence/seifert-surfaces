import ActualAnnulusHalfGlobalFamilyV896
import ActualAnnulusFullFamilyGluingV774
import ActualAnnulusHalfRestrictionV773

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Topology Metric
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
open CompressionActualPlanarWholeDiskExtensionV756
open CompressionActualAnnulusHalfPolarModelV768
open CompressionActualAnnulusHalfCoordinatesV772
noncomputable section
namespace CompressionActualAnnulusWholeGlobalFamilyV897

/-- Retain the actual two global plane families behind the SAME whole
    confined annulus deformation, with all parameter labels matched. -/
theorem whole_annulus_relative_global_family
    (β : C(Circle × Time,Circle × Time)) (hβ : IsEmbedding β)
    (hcore : ∀ z,β (z,middleTime) = (z,middleTime))
    (hside : ∀ k p,side k (β (half k p))) :
    ∃ H : C(Time × (Circle × Time),Circle × Time),
      (∀ s,IsEmbedding (fun p => H (s,p))) ∧
      (∀ p,H (0,p) = β p) ∧ (∀ p,H (1,p) = p) ∧
      (∀ s z,H (s,(z,middleTime)) = (z,middleTime)) ∧
      ∃ Γ : Fin 2 → C(Time × (Circle × Time),Circle × Time),
      ∃ G : Fin 2 → Time → Plane ≃ₜ Plane,
        (∀ k,Continuous (fun p : Time × Plane => G k p.1 p.2)) ∧
        (∀ k,Continuous (fun p : Time × Plane => (G k p.1).symm p.2)) ∧
        (∀ k x,G k 1 x = x) ∧ (∀ k s x,‖x‖ ≤ 1 → G k s x = x) ∧
        (∀ k s x,‖x‖ ≤ 2 → ‖G k s x‖ ≤ 2) ∧
        (∀ k s p,polar (Γ k (s,p)) = G k s (polar p)) ∧
        ∀ k s p,H (s,half k p) = half k (Γ k (s,p)) := by
  classical
  choose βh hhalf hβh hβhcore hβhpos using fun k =>
    CompressionActualAnnulusHalfRestrictionV773.annulus_half_restriction β hβ hcore k (hside k)
  choose Γ hΓ hΓ0 hΓ1 hΓcore hΓpos G hG hGi hG1 hGfix hGbound hΓpolar using fun k =>
    CompressionActualAnnulusHalfGlobalFamilyV896.annulus_half_global_embedding_family
      (βh k) (hβh k) (hβhcore k) (hβhpos k)
  obtain ⟨H,hHhalf,hH,hHcore⟩ :=
    CompressionActualAnnulusFullFamilyGluingV774.full_family_gluing Γ hΓ hΓcore
  refine ⟨H,hH,?_,?_,hHcore,Γ,G,hG,hGi,hG1,hGfix,hGbound,hΓpolar,hHhalf⟩
  · intro p
    obtain ⟨k,q,rfl⟩ := CompressionActualAnnulusFullFamilyGluingV774.half_cover p
    rw [hHhalf,hΓ0,hhalf]
  · intro p
    obtain ⟨k,q,rfl⟩ := CompressionActualAnnulusFullFamilyGluingV774.half_cover p
    rw [hHhalf,hΓ1]

#print axioms whole_annulus_relative_global_family
end CompressionActualAnnulusWholeGlobalFamilyV897
