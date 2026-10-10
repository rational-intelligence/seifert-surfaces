import EndpointActualHistory
import EndpointAnnulusConstruction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology
open scoped Manifold ContDiff
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
namespace SeifertSurfaces.OriginalEndpoints
variable {n : ℕ} {L : OrientedLink n} {T : TubularNeighborhood L}
    (E : SmoothExterior T)

/-- Whole original endpoint with annulus and all conclusions paid. The sole
remaining input is the approved actual compression realization producer. -/
theorem original_6_2_from_actual_realization_exists
    (Q : LinkCoordinates L) (hL : LinkIsLinkingIndecomposable L Q)
    (hactual : ∀ F : LinkSpanningSurface.{0} E, ConnectedSpace F.surface →
      ∀ (D : InteriorCompressingDisk F.embedding) (A : CompressionAnnulus D),
        ∃ P : SmoothCompressionSurface A, Nonempty (ActualCompressionRealization E F A P)) :
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
  obtain ⟨hwf,hno,hbound⟩ := actual_retained_compression_histories E Q hL
  refine ⟨?_,actual_retained_step_genus_drop E Q hL,hwf,hno,hbound⟩
  intro F hF D
  refine ⟨compression_annulus_exists (E := E) F D,hactual F hF D,?_⟩
  intro A P J
  let _ := hF
  exact compressionConclusion_of_actual E Q hL F D A P J

end SeifertSurfaces.OriginalEndpoints
