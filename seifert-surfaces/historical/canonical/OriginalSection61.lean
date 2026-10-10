import LinkingHomology

/-!
# Original Lemma 6.1
Source: references/seifert-surfaces.txt, lines 956–957 and 972–991.
The implicit no-closed-components convention is the native
LinkSpanningSurface.no_closed_components field (SOURCE_ISSUES.md SF-08).
The universal quantifier includes the spanning outputs of Lemma 4.9;
the construction and its spanning-output guarantee belong to Lemma 4.9.
-/

set_option autoImplicit false
noncomputable section
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
open scoped BigOperators

namespace SeifertSurfaces.OriginalEndpoints

/-- Every spanning surface for a linking-indecomposable link is connected
and has exactly n boundary curves, including the spanning frontier outputs
of Lemma 4.9. Linking is the native homological oriented linking number,
with total linking to the opposite sublink in every nontrivial cut. -/
theorem original_6_1 {n : ℕ} (L : OrientedLink n)
    {T : TubularNeighborhood L} (E : SmoothExterior T)
    (Q : LinkCoordinates L) (hL : LinkIsLinkingIndecomposable L Q) :
    ∀ F : LinkSpanningSurface.{0} E,
      ConnectedSpace F.surface ∧ boundaryCount F.surface = n := by
  intro F
  exact spanning_boundary_count_and_connected L E Q hL F

end SeifertSurfaces.OriginalEndpoints
