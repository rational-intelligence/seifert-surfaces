import project.OriginalSection62
import GeometrySupportV510
import EndpointSupportV510
import PaidClosureSupportV510

set_option autoImplicit false
noncomputable section
open Set Topology
open scoped Manifold ContDiff BigOperators
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
namespace SeifertSurfaces.OriginalEndpoints
variable {n : ℕ}

/-- Lemma 6.2 in full, with successive steps restricted to actual disk surgery. -/
theorem original_6_2 (L : OrientedLink n) {T : TubularNeighborhood L}
    (E : SmoothExterior T) (Q : LinkCoordinates L)
    (hL : LinkIsLinkingIndecomposable L Q) :
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


end SeifertSurfaces.OriginalEndpoints

open Lean Elab Command in
run_cmd do
  let (approved,_) ← liftIO <| readModuleData "/home/caoyichuan/test/seifert-surfaces/target/Original62WholeProofData/objects/OriginalSection62.olean"
  let env := (← getEnv).setExporting false
  let n := `SeifertSurfaces.OriginalEndpoints.original_6_2
  let some original := approved.constants.find? (fun c => c.name == n) | throwError "Original root absent"
  let some actual := env.constants.find? n | throwError "Completed root absent"
  unless actual.levelParams == original.levelParams && Expr.equal actual.type original.type && ExprStructEq.mk actual.type == ExprStructEq.mk original.type do throwError "Full original root raw type changed"
  logInfo "PASS full original root raw type literal"

#print axioms SeifertSurfaces.OriginalEndpoints.original_6_2
