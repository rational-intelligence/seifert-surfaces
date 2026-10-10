import ActualOriginalAnnulusFullDiskProductV790

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped Manifold ContDiff
open Set Topology Manifold
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
noncomputable section
namespace CompressionActualOriginalAnnulusUnroundedQuotientV793

/-- Literal original-A full product and unrounded quotient, with exact
    remainder/cap maps, full original D center, and all attachment disjointness. -/
theorem given_original_disk_arbitrary_annulus_unrounded_quotient
    {n : ℕ} {L : OrientedLink n} {T : TubularNeighborhood L}
    (E : SmoothExterior T) (F : LinkSpanningSurface.{0} E)
    (D : InteriorCompressingDisk F.embedding) (A : CompressionAnnulus D) :
    ∃ P : ClosedDisk ≃ₜ D.disk,
      (∀ z,P (CompressionAnnulus.capEdge z) = D.boundaryCircle.toFun z) ∧
      ∃ J : C(ClosedDisk × Time,E.Carrier),IsEmbedding J ∧
        (∀ x,J (x,middleTime) = D.toFun (P x)) ∧
        (∀ z t,J (CompressionAnnulus.capEdge z,t) = F.embedding.toFun (A.band (z,t))) ∧
        (range J ⊆ (𝓡∂ 3).interior E.Carrier) ∧
        (range J ∩ F.image = range (fun p : Circle × Time => F.embedding.toFun (A.band p))) ∧
        ∃ R : C(A.SurgerySpace,E.Carrier),IsEmbedding R ∧
          (∀ x : A.Remainder,R (A.remainderInclusion x) = F.embedding.toFun x) ∧
          (∀ k x,R (A.capInclusion k x) = J (x,CompressionAnnulus.sideTime k)) ∧
          Disjoint
            (range (fun x : ClosedDisk => J (x,CompressionAnnulus.sideTime 0)))
            (range (fun x : ClosedDisk => J (x,CompressionAnnulus.sideTime 1))) ∧
          (∀ k : Fin 2,Disjoint
            (range (fun x : ClosedDisk => J (x,CompressionAnnulus.sideTime k))) (range D.toFun)) ∧
          (∀ k : Fin 2,
            range (fun x : ClosedDisk => J (x,CompressionAnnulus.sideTime k)) ∩
              (F.embedding.toFun '' A.removedᶜ) =
            range (fun z : Circle => F.embedding.toFun (A.band (z,CompressionAnnulus.sideTime k)))) := by
  obtain ⟨P,hP,J,hJ,hcenter,hlateral,hinterior,hinter⟩ :=
    CompressionActualOriginalAnnulusFullDiskProductV790.given_original_disk_arbitrary_annulus_full_product E F D A
  exact ⟨P,hP,J,hJ,hcenter,hlateral,hinterior,hinter,
    CompressionActualExactLateralQuotient.actual_unrounded_quotient_of_exact_lateral_product
      E F D A P J hJ hcenter hlateral hinter⟩

#print axioms given_original_disk_arbitrary_annulus_unrounded_quotient
end CompressionActualOriginalAnnulusUnroundedQuotientV793
