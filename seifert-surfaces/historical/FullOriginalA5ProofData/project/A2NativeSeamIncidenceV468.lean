import OriginalA25SourceDefinitionsV464
import A5NativeSeamSector
import A5SectorProjectedInverse
import A5NativeLocalCover
import NativeSeamProducerProofsProbe

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology MeasureTheory
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
universe u
variable {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)

/-- Whole S1–S5 arc construction from the native source category only.
Source A2 proof lines 1147–1159 and ROUTE.md S2–S4. No incidence, lifted
regularity, collar, minimizer, stationarity or conormal balance is assumed. -/
theorem native_adjacent_arc_producer (G : A7.SourceGeometry E)
    {S : CompactOrientedSurface.{u}}
    (Fprime : GeometricPiecewiseSurface S E.Carrier)
    (a : Fin Fprime.seam.arcCount) (s : Time)
    (hleft : 0 < (s : ℝ)) (hright : (s : ℝ) < 1) :
    Nonempty (AdjacentArcData E G Fprime a s) := by
  exact native_adjacent_arc_construction_v468 E G Fprime a s hleft hright

/-- The entire circle construction with its exact centered output local clock. -/
theorem native_adjacent_circle_producer (G : A7.SourceGeometry E)
    {S : CompactOrientedSurface.{u}}
    (Fprime : GeometricPiecewiseSurface S E.Carrier)
    (a : Fin Fprime.seam.circleCount) (s : Circle) :
    Nonempty (AdjacentCircleData E G Fprime a s) := by
  exact native_adjacent_circle_construction_v468 E G Fprime a s

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
