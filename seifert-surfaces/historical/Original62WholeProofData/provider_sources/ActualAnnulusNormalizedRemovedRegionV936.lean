import ActualAnnulusSideNormalizationV869

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Set Topology
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
open CompressionActualAnnulusTimeReflectionV779
noncomputable section
namespace CompressionActualAnnulusNormalizedRemovedRegionV936

theorem normalized_time_open_middle
    (R : Circle × Time ≃ₜ Circle × Time)
    (hR : R = Homeomorph.refl _ ∨ R = reflection) :
    R '' {p : Circle × Time | 0 < p.2.val ∧ p.2.val < 1} =
      {p : Circle × Time | 0 < p.2.val ∧ p.2.val < 1} := by
  rcases hR with rfl | rfl
  · exact image_id _
  · apply Subset.antisymm
    · rintro p ⟨q,hq,rfl⟩
      change 0 < 1-q.2.val ∧ 1-q.2.val < 1
      exact ⟨by linarith [hq.2],by linarith [hq.1]⟩
    · intro p hp
      refine ⟨reflection p,?_,?_⟩
      · change 0 < 1-p.2.val ∧ 1-p.2.val < 1
        exact ⟨by linarith [hp.2],by linarith [hp.1]⟩
      · exact Prod.ext rfl (reverseTime_reverse p.2)

theorem contained_normalized_removed_region
    {S : CompactOrientedSurface.{0}} {M : Type}
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    {f : NeatEmbedding S M} {D : InteriorCompressingDisk f}
    (A B : CompressionAnnulus D)
    (β : C(Circle × Time,Circle × Time))
    (hβ : ∀ p,A.band (β p) = B.band p)
    (R : Circle × Time ≃ₜ Circle × Time)
    (hR : R = Homeomorph.refl _ ∨ R = reflection) :
    A.band '' ((β ∘ R) '' {p : Circle × Time | 0 < p.2.val ∧ p.2.val < 1}) = B.removed := by
  rw [image_comp,normalized_time_open_middle R hR,image_image]
  change (A.band ∘ β) '' _ = B.band '' _
  congr 1
  exact funext hβ

#print axioms normalized_time_open_middle
#print axioms contained_normalized_removed_region
end CompressionActualAnnulusNormalizedRemovedRegionV936
