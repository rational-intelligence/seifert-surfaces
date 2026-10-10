import ActualNativeOriginalRealizationTransportV925
import ActualSupportedSurfaceRemainderHomeomorphV923

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped Manifold ContDiff
open Set Topology
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
open SeifertSurfaces.OriginalEndpoints
noncomputable section
namespace CompressionActualNativeOriginalMatchedRegionConsumerV937

theorem native_original_realization_from_matched_regions
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
    (hImage : I.stage 1 '' F.image = F.image)
    (hRemoved : I.stage 1 '' (F.embedding.toFun '' A.removed) = F.embedding.toFun '' B.removed) :
    ∃ PA : SmoothCompressionSurface A,Nonempty (ActualCompressionRealization E F A PA) := by
  obtain ⟨hS,hSpoint⟩ := CompressionActualEmbeddedImageIdentificationV921.embedded_image_identification
    F.embedding.toFun F.embedding.smoothEmbedding.isEmbedding
    F.embedding.toFun F.embedding.smoothEmbedding.isEmbedding (I.stage 1) hImage
  obtain ⟨r,hrpoint,hrbd,hroff⟩ :=
    CompressionActualSupportedSurfaceRemainderHomeomorphV923.supported_surface_remainder_homeomorph
      F.embedding A B (I.stage 1) hImage hRemoved (hIbd 1) V (hoff 1)
  have hr (x : A.Remainder) : (r x).val = hS x.val := by
    apply F.embedding.smoothEmbedding.isEmbedding.injective
    rw [hrpoint,hSpoint]
  exact CompressionActualNativeOriginalRealizationTransportV925.native_original_realization_transport
    E F D A B PB CB P hP J hJ hcenter hlateral hinterior hintersection
    I V hV hVD hVbd hseam hoff hIbd π hcap hS hSpoint r hr

#print axioms native_original_realization_from_matched_regions
end CompressionActualNativeOriginalMatchedRegionConsumerV937
