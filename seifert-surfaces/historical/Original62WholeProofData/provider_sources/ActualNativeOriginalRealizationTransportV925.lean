import ActualSupportedAmbientRoundingCompositionV924
import ActualSupportedSurfaceRemainderHomeomorphV923
import OriginalSection62

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped Manifold ContDiff
open Set Filter Topology Manifold
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
open SeifertSurfaces.OriginalEndpoints
noncomputable section
namespace CompressionActualNativeOriginalRealizationTransportV925

/-- Assemble the literal original-A strong native realization from the
    SAME full original product, actual whole-cap straightening, and actual
    remainder homeomorphism. Every quotient point and positive untouched
    remainder orientation are retained; no chosen-annulus substitution. -/
theorem native_original_realization_transport
    {n : ℕ} {L : OrientedLink n} {T : TubularNeighborhood L}
    (E : SmoothExterior T) (F : LinkSpanningSurface.{0} E)
    (D : InteriorCompressingDisk F.embedding) (A B : CompressionAnnulus D)
    (PB : SmoothCompressionSurface B) (CB : ActualCompressionRealization E F B PB)
    (P : ClosedDisk ≃ₜ D.disk)
    (hP : ∀ z,P (CompressionAnnulus.capEdge z) = D.boundaryCircle.toFun z)
    (J : C(ClosedDisk × Time,E.Carrier)) (hJ : IsEmbedding J)
    (hcenter : ∀ x,J (x,middleTime) = D.toFun (P x))
    (hlateral : ∀ z t,J (CompressionAnnulus.capEdge z,t) = F.embedding.toFun (A.band (z,t)))
    (hinterior : range J ⊆ (𝓡∂ 3).interior E.Carrier)
    (hintersection : range J ∩ F.image = range (fun p : Circle × Time => F.embedding.toFun (A.band p)))
    (I : TopologicalAmbientIsotopy E.Carrier) (V : Set E.Carrier)
    (hV : IsOpen V) (hVD : Disjoint (closure V) (range D.toFun))
    (hVbd : Disjoint (closure V) ((𝓡∂ 3).boundary E.Carrier))
    (hseam : ∀ k z,F.embedding.toFun (A.band (z,CompressionAnnulus.sideTime k)) ∈ V)
    (hoff : ∀ t x,x ∉ V → I.stage t x = x)
    (hIbd : ∀ t x,x ∈ (𝓡∂ 3).boundary E.Carrier → I.stage t x = x)
    (π : Fin 2 ≃ Fin 2)
    (hcap : ∀ k x,I.stage 1 (J (x,CompressionAnnulus.sideTime k)) =
      CB.thickening (x,CompressionAnnulus.sideTime (π k)))
    (hS : F.surface ≃ₜ F.surface)
    (hSpoint : ∀ x,F.embedding.toFun (hS x) = I.stage 1 (F.embedding.toFun x))
    (r : A.Remainder ≃ₜ B.Remainder) (hr : ∀ x,(r x).val = hS x.val) :
    ∃ PA : SmoothCompressionSurface A,Nonempty (ActualCompressionRealization E F A PA) := by
  classical
  obtain ⟨RA,hRA,hRArem,hRAcap,hcaps,havoid,hattach⟩ :=
    CompressionActualExactLateralQuotient.actual_unrounded_quotient_of_exact_lateral_product
      E F D A P J hJ hcenter hlateral hintersection
  have hrem (x : A.Remainder) : I.stage 1 (RA (A.remainderInclusion x)) =
      CB.unrounded (B.remainderInclusion (r x)) := by
    rw [hRArem,CB.unrounded_remainder,hr,hSpoint]
  have hcapsMap (k : Fin 2) (x : ClosedDisk) : I.stage 1 (RA (A.capInclusion k x)) =
      CB.unrounded (B.capInclusion (π k) x) := by
    rw [hRAcap,CB.unrounded_caps,hcap]
  obtain ⟨q,hq,hqrem,hqcap⟩ :=
    CompressionActualOriginalSurgeryPointIdentificationV922.original_surgery_point_identification
      A B RA hRA CB.unrounded CB.unrounded_embedded (I.stage 1) r π hrem hcapsMap
  let real : PB.surface ≃ₜ A.SurgerySpace := PB.realization.trans q.symm
  have hRealRem (x : A.Remainder) : real.symm (A.remainderInclusion x) =
      PB.realization.symm (B.remainderInclusion (r x)) := by
    change PB.realization.symm (q (A.remainderInclusion x)) = _
    rw [hqrem]
  have hRealCap (k : Fin 2) (x : ClosedDisk) : real.symm (A.capInclusion k x) =
      PB.realization.symm (B.capInclusion (π k) x) := by
    change PB.realization.symm (q (A.capInclusion k x)) = _
    rw [hqcap]
  have hSfix (x : F.surface) (hx : F.embedding.toFun x ∉ V) : hS x = x := by
    apply F.embedding.smoothEmbedding.isEmbedding.injective
    rw [hSpoint,hoff _ _ hx]
  have hSbd (x : F.surface) (hx : x ∈ F.surface.boundary) : hS x = x := by
    apply F.embedding.smoothEmbedding.isEmbedding.injective
    rw [hSpoint,hIbd]
    change x ∈ F.embedding.toFun ⁻¹' (𝓡∂ 3).boundary E.Carrier
    rwa [F.embedding.boundary_preimage]
  have hrbd (x : A.Remainder) : (r x).val ∈ F.surface.boundary ↔ x.val ∈ F.surface.boundary := by
    rw [hr]
    constructor
    · intro hx
      have he : x.val = hS x.val := hS.injective (hSbd _ hx).symm
      exact he.symm ▸ hx
    · intro hx
      rwa [hSbd x.val hx]
  let PA : SmoothCompressionSurface A := {
    surface := PB.surface
    realization := real
    boundary_matches := fun x => by rw [hRealRem,PB.boundary_matches]; exact hrbd x
    caps_interior := fun k x => by rw [hRealCap]; exact PB.caps_interior (π k) x }
  let K : Set F.surface := (F.embedding.toFun ⁻¹' closure V) ∪ closure CB.seamNeighborhood
  have hKc : IsCompact K :=
    (isClosed_closure.preimage F.embedding.smoothEmbedding.isEmbedding.continuous).isCompact.union isClosed_closure.isCompact
  have hKb : K ⊆ F.surface.boundaryᶜ := by
    rintro x (hx | hx) hb
    · apply disjoint_left.mp hVbd hx
      change x ∈ F.embedding.toFun ⁻¹' (𝓡∂ 3).boundary E.Carrier
      rwa [F.embedding.boundary_preimage]
    · exact disjoint_left.mp CB.seam_closure_away_boundary hx hb
  have hbdclosed : IsClosed F.surface.boundary :=
    (𝓡∂ 2).isClosed_boundary (M := F.surface) (n := ∞) (by decide)
  obtain ⟨U,hU,hKU,hUbd⟩ := hKc.exists_isOpen_closure_subset (hbdclosed.isOpen_compl.mem_nhdsSet.mpr hKb)
  have hUV (x : F.surface) (hx : x ∉ U) : F.embedding.toFun x ∉ closure V :=
    fun hv => hx (hKU (Or.inl hv))
  have hUB (x : F.surface) (hx : x ∉ U) : x ∉ CB.seamNeighborhood :=
    fun hs => hx (hKU (Or.inr (subset_closure hs)))
  have hfixU (x : F.surface) (hx : x ∉ U) : hS x = x :=
    hSfix x (fun hv => hUV x hx (subset_closure hv))
  have hnotRemovedB (x : F.surface) (hx : x ∉ U) (hxa : x ∉ A.removed) : x ∉ B.removed := by
    have hh : (r ⟨x,hxa⟩).val = x := (hr _).trans (hfixU x hx)
    exact hh ▸ (r ⟨x,hxa⟩).property
  obtain ⟨Rnd,hRndOpen,hRnd,hRndOff,hRndBd⟩ :=
    CompressionActualSupportedAmbientRoundingCompositionV924.supported_ambient_rounding_composition
      I CB.rounding V CB.roundingSupport hV CB.roundingSupport_open hoff CB.rounding_fixed_outside hIbd CB.rounding_boundary_fixed
  have hRndD : Disjoint (closure (V ∪ CB.roundingSupport)) (range D.toFun) := by
    rw [closure_union]
    exact hVD.sup_left CB.roundingSupport_away_centralDisk
  have hRndB : Disjoint (closure (V ∪ CB.roundingSupport)) ((𝓡∂ 3).boundary E.Carrier) := by
    rw [closure_union]
    exact hVbd.sup_left CB.roundingSupport_away_boundary
  have hRounded (x : A.SurgerySpace) : CB.embedding.toFun (real.symm x) = Rnd.stage 1 (RA x) := by
    change CB.embedding.toFun (PB.realization.symm (q x)) = _
    rw [CB.rounded_identification,hq,hRnd]
  let EC : EmbeddedCompression E F D A PA := {
    embedding := CB.embedding
    seamNeighborhood := U
    seam_open := hU
    seam_contains := fun k z => hKU (Or.inl (subset_closure (hseam k z)))
    unchanged := fun x hx => by
      change CB.embedding.toFun (real.symm (A.remainderInclusion x)) = _
      rw [hRealRem,CB.unchanged (r x) (by rw [hr,hfixU x.val hx]; exact hUB x.val hx),hr,hfixU x.val hx]
    boundary_fixed := fun x hx => by
      change CB.embedding.toFun (real.symm (A.remainderInclusion x)) = _
      rw [hRealRem,CB.boundary_fixed (r x) ((hrbd x).mpr hx),hr,hSbd x.val hx]
    seam_away_boundary := disjoint_left.mpr (fun x hx hb => hUbd (subset_closure hx) hb) }
  let marking : F.surface → PA.surface := CB.remainderMarking ∘ hS
  have hMarkEq (x : A.Remainder) : marking x.val = PA.realization.symm (A.remainderInclusion x) := by
    change CB.remainderMarking (hS x.val) = real.symm (A.remainderInclusion x)
    rw [← hr x,CB.remainderMarking_eq,hRealRem]
  have hMarkLocal (x : F.surface) (hx : x ∉ U) : marking =ᶠ[𝓝 x] CB.remainderMarking := by
    have hO : IsOpen (F.embedding.toFun ⁻¹' (closure V)ᶜ) :=
      isClosed_closure.isOpen_compl.preimage F.embedding.smoothEmbedding.isEmbedding.continuous
    filter_upwards [hO.mem_nhds (hUV x hx)] with y hy
    change CB.remainderMarking (hS y) = CB.remainderMarking y
    rw [hSfix y (fun hv => hy (subset_closure hv))]
  let CA : ActualCompressionRealization E F A PA := {
    toEmbeddedCompression := EC
    diskParam := P
    diskParam_boundary := hP
    thickening := J
    thickening_embedded := hJ
    thickening_center := hcenter
    thickening_lateral := hlateral
    thickening_interior := hinterior
    thickening_surface_intersection := hintersection
    caps_disjoint := hcaps
    caps_avoid_suppliedDisk := havoid
    caps_meet_remainder_only_at_attachment := hattach
    unrounded := RA
    unrounded_embedded := hRA
    unrounded_remainder := hRArem
    unrounded_caps := hRAcap
    rounding := Rnd
    roundingSupport := V ∪ CB.roundingSupport
    roundingSupport_open := hRndOpen
    roundingSupport_contains_seams := fun k z => Or.inl (hseam k z)
    roundingSupport_away_boundary := hRndB
    roundingSupport_away_centralDisk := hRndD
    rounding_fixed_outside := hRndOff
    rounding_boundary_fixed := hRndBd
    rounded_identification := hRounded
    seam_closure_away_boundary := disjoint_left.mpr (fun x hx hb => hUbd hx hb)
    remainderMarking := marking
    remainderMarking_eq := hMarkEq
    remainderMarking_smooth := fun x hx hxa =>
      (CB.remainderMarking_smooth x (hUB x hx) (hnotRemovedB x hx hxa)).congr_of_eventuallyEq (hMarkLocal x hx)
    remainder_orientation := by
      intro x hx hxa v hv
      rw [(hMarkLocal x hx).eq_of_nhds,(hMarkLocal x hx).mfderiv_eq]
      exact CB.remainder_orientation x (hUB x hx) (hnotRemovedB x hx hxa) v hv }
  exact ⟨PA,⟨CA⟩⟩

#print axioms native_original_realization_transport
end CompressionActualNativeOriginalRealizationTransportV925
