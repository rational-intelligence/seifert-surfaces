import NativeGeometryReplayV763
import ActualWholeNativeOrientedCombinerV750

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped Manifold ContDiff
open Set Filter Topology TopologicalSpace Manifold
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
open CompressionNativeSignedQuotientSeam CompressionLocalPiecesSupport
open CompressionPieceChartsSupport
noncomputable section
namespace CompressionActualWholeNativeOrientedRealizationV766

/-- The full actual product, quotient, rounding and native atlas construct the
approved strong realization on the chosen smooth internal annulus. The supplied
arbitrary annulus remains present in the containment bound. -/
theorem given_original_disk_whole_native_oriented_realization
    {n : ℕ} {L : OrientedLink n} {T : TubularNeighborhood L}
    (E : SmoothExterior T) (F : LinkSpanningSurface.{0} E)
    (D : InteriorCompressingDisk F.embedding) (A : CompressionAnnulus D) :
    ∃ B : CompressionAnnulus D,range B.band ⊆ A.removed ∧
      ∃ Pout : SmoothCompressionSurface B,
        Nonempty (SeifertSurfaces.OriginalEndpoints.ActualCompressionRealization E F B Pout) := by
  exact CompressionActualWholeNativeOrientedCombinerV750.whole_native_oriented_realization_of_given_whole_smooth_witness
    E F D A (CompressionActualWholeNativeSmoothQuotient.given_original_disk_whole_native_smooth_quotient E F D A)

#print axioms given_original_disk_whole_native_oriented_realization
end CompressionActualWholeNativeOrientedRealizationV766
