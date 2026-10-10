import ActualEmbeddedImageIdentificationV921

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Topology
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
noncomputable section
namespace CompressionActualOriginalSurgeryPointIdentificationV922

theorem surgery_point_cases
    {S : CompactOrientedSurface.{0}} {M : Type}
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    {f : NeatEmbedding S M} {D : InteriorCompressingDisk f}
    (A : CompressionAnnulus D) (q : A.SurgerySpace) :
    (∃ x : A.Remainder,A.remainderInclusion x = q) ∨
    ∃ k x,A.capInclusion k x = q := by
  induction q using Quot.inductionOn with
  | _ p =>
    rcases p with x | ⟨k,x⟩
    · exact Or.inl ⟨x,rfl⟩
    · exact Or.inr ⟨k,x,rfl⟩

/-- Every literal original quotient point is identified by the actual
    remainder and whole disk-cap point maps. No image equality is assumed. -/
theorem original_surgery_point_identification
    {S : CompactOrientedSurface.{0}} {M : Type}
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    {f : NeatEmbedding S M} {D : InteriorCompressingDisk f}
    (A B : CompressionAnnulus D)
    (RA : C(A.SurgerySpace,M)) (hRA : IsEmbedding RA)
    (RB : C(B.SurgerySpace,M)) (hRB : IsEmbedding RB)
    (g : M ≃ₜ M) (r : A.Remainder ≃ₜ B.Remainder) (π : Fin 2 ≃ Fin 2)
    (hrem : ∀ x,g (RA (A.remainderInclusion x)) = RB (B.remainderInclusion (r x)))
    (hcap : ∀ k x,g (RA (A.capInclusion k x)) = RB (B.capInclusion (π k) x)) :
    ∃ q : A.SurgerySpace ≃ₜ B.SurgerySpace,
      (∀ x,RB (q x) = g (RA x)) ∧
      (∀ x,q (A.remainderInclusion x) = B.remainderInclusion (r x)) ∧
      ∀ k x,q (A.capInclusion k x) = B.capInclusion (π k) x := by
  have heq : g '' range RA = range RB := by
    apply Subset.antisymm
    · rintro y ⟨u,⟨x,rfl⟩,rfl⟩
      rcases surgery_point_cases A x with ⟨p,rfl⟩ | ⟨k,p,rfl⟩
      · rw [hrem]
        exact mem_range_self _
      · rw [hcap]
        exact mem_range_self _
    · rintro y ⟨x,rfl⟩
      rcases surgery_point_cases B x with ⟨p,rfl⟩ | ⟨k,p,rfl⟩
      · refine ⟨RA (A.remainderInclusion (r.symm p)),mem_range_self _,?_⟩
        rw [hrem,r.apply_symm_apply]
      · refine ⟨RA (A.capInclusion (π.symm k) p),mem_range_self _,?_⟩
        rw [hcap,π.apply_symm_apply]
  obtain ⟨q,hq⟩ := CompressionActualEmbeddedImageIdentificationV921.embedded_image_identification RA hRA RB hRB g heq
  refine ⟨q,hq,?_,?_⟩
  · intro x
    apply hRB.injective
    exact (hq _).trans (hrem x)
  · intro k x
    apply hRB.injective
    exact (hq _).trans (hcap k x)

end CompressionActualOriginalSurgeryPointIdentificationV922
