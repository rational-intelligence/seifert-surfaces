import NativeGeometryReplayV763

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Topology
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
noncomputable section
namespace CompressionActualContainedAnnulusCoordinatesV778

/-- Coordinates of the whole contained annulus in the caller's original
    arbitrary annulus, with literal core labels and derived open middle. -/
theorem contained_annulus_coordinates
    {n : ℕ} {L : OrientedLink n} {T : TubularNeighborhood L}
    (E : SmoothExterior T) (F : LinkSpanningSurface.{0} E)
    (D : InteriorCompressingDisk F.embedding) (A B : CompressionAnnulus D)
    (hBA : range B.band ⊆ A.removed) :
    ∃ β : C(Circle × Time,Circle × Time),IsEmbedding β ∧
      (∀ p,A.band (β p) = B.band p) ∧
      (∀ z,β (z,middleTime) = (z,middleTime)) ∧
      IsOpen (β '' (univ ×ˢ Ioo (0:Time) 1)) := by
  let H := A.embedded.toHomeomorph
  let b : Circle × Time → range A.band :=
    fun p => ⟨B.band p,image_subset_range A.band _ (hBA (mem_range_self p))⟩
  have hb : Continuous b := B.band.continuous.subtype_mk _
  let β : C(Circle × Time,Circle × Time) := ⟨H.symm ∘ b,H.symm.continuous.comp hb⟩
  have hβval (p : Circle × Time) : A.band (β p) = B.band p :=
    congrArg Subtype.val (H.apply_symm_apply (b p))
  have hβinj : Function.Injective β := by
    intro p q he
    have h := congrArg A.band he
    rw [hβval,hβval] at h
    exact B.embedded.injective h
  have hβcore (z : Circle) : β (z,middleTime) = (z,middleTime) := by
    apply A.embedded.injective
    rw [hβval,B.center,A.center]
  have himage : β '' (univ ×ˢ Ioo (0:Time) 1) = A.band ⁻¹' B.removed := by
    ext q
    constructor
    · rintro ⟨p,hp,rfl⟩
      refine ⟨p,?_,(hβval p).symm⟩
      exact hp.2
    · rintro ⟨p,hp,he⟩
      refine ⟨p,⟨mem_univ _,hp⟩,?_⟩
      apply A.embedded.injective
      exact (hβval p).trans he
  refine ⟨β,(β.continuous.isClosedEmbedding hβinj).isEmbedding,hβval,hβcore,?_⟩
  rw [himage]
  exact B.open_middle.preimage A.band.continuous

end CompressionActualContainedAnnulusCoordinatesV778
