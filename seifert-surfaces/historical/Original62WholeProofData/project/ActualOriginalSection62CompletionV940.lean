import ActualOriginalNativeRealizationV939
import NativeEndpointReadyReplayV947

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Set Topology
open scoped Manifold ContDiff
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
open SeifertSurfaces.OriginalEndpoints
namespace CompressionActualOriginalSection62CompletionV940
variable {n : ℕ} {L : OrientedLink n} {T : TubularNeighborhood L}
    (E : SmoothExterior T)

theorem original_6_2_with_actual_original_annulus_realization
    (Q : LinkCoordinates L) (hL : LinkIsLinkingIndecomposable L Q)
 :
    (∀ F : LinkSpanningSurface.{0} E, ConnectedSpace F.surface →
      ∀ D : InteriorCompressingDisk F.embedding,
        Nonempty (CompressionAnnulus D) ∧
        (∀ A : CompressionAnnulus D,
          ∃ P : SmoothCompressionSurface A,
            Nonempty (ActualCompressionRealization E F A P)) ∧
        (∀ (A : CompressionAnnulus D) (P : SmoothCompressionSurface A)
          (J : ActualCompressionRealization E F A P),
          CompressionConclusion E F A P J)) ∧
    (∀ G F : LinkSpanningSurface.{0} E, RetainedCompressionStep E G F →
      surfaceGenus G.surface < surfaceGenus F.surface) ∧
    WellFounded (RetainedCompressionStep E) ∧
    (¬ ∃ S : ℕ → LinkSpanningSurface.{0} E,
      ∀ k, RetainedCompressionStep E (S (k + 1)) (S k)) ∧
    (∀ (m : ℕ) (S : Fin (m + 1) → LinkSpanningSurface.{0} E),
      (∀ i : Fin m, RetainedCompressionStep E (S i.succ) (S i.castSucc)) →
      m ≤ surfaceGenus (S 0).surface) := by
  exact original_6_2_from_actual_realization_exists E Q hL
    (fun F _ D A => CompressionActualOriginalNativeRealizationV939.given_original_annulus_native_realization E F D A)

#print axioms original_6_2_with_actual_original_annulus_realization
end CompressionActualOriginalSection62CompletionV940
