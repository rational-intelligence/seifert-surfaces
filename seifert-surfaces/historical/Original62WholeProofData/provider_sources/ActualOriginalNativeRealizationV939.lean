import ActualOriginalFullMatchedSurfaceProductV935
import ActualNativeOriginalMatchedRegionConsumerV937

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped Manifold ContDiff
open Set Topology
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
open SeifertSurfaces.OriginalEndpoints
noncomputable section
namespace CompressionActualOriginalNativeRealizationV939

/-- The supplied arbitrary annulus and the complete original disk admit the
    literal native realization, retaining every quotient and lateral label. -/
theorem given_original_annulus_native_realization
    {n : ℕ} {L : OrientedLink n} {T : TubularNeighborhood L}
    (E : SmoothExterior T) (F : LinkSpanningSurface.{0} E)
    (D : InteriorCompressingDisk F.embedding) (A : CompressionAnnulus D) :
    ∃ P : SmoothCompressionSurface A,Nonempty (ActualCompressionRealization E F A P) := by
  obtain ⟨B,hBA,P,hP,JB,hJB,hJBcenter,hJBlateral,PB,CB,hCBP,hCBJ,
    J,hJ,hcenter,hlateral,hinterior,hintersection,π,I,V,hV,hVc,hVD,hVbd,hseam,hoff,hIbd,hImage,hRemoved,hcap⟩ :=
    CompressionActualOriginalFullMatchedSurfaceProductV935.given_original_full_matched_surface_product E F D A
  have hcapCB (k : Fin 2) (x : ClosedDisk) :
      I.stage 1 (J (x,CompressionAnnulus.sideTime k)) = CB.thickening (x,CompressionAnnulus.sideTime (π k)) := by
    rw [hCBJ]
    exact hcap k x
  exact CompressionActualNativeOriginalMatchedRegionConsumerV937.native_original_realization_from_matched_regions
    E F D A B PB CB P hP J hJ hcenter hlateral hinterior hintersection
    I V hV hVD hVbd hseam hoff hIbd π hcapCB (hImage 1) hRemoved

#print axioms given_original_annulus_native_realization
end CompressionActualOriginalNativeRealizationV939
