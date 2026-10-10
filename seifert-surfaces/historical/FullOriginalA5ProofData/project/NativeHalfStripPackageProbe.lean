import NativeHalfStripTemplateProbe
import A2NativeSeamDefinitionsV468

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set Topology Filter
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
universe u
variable {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)

/-- The regular native sector template fills every approved halfstrip field,
with the exact same shortened boundary lift. -/
def nativeHalfStripOfTemplate
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count) (q : ℝ → Euc 2)
    (C : SectorHalfStripTemplate ((F.domain i).chart j).model q)
    (d : ℝ) (hd : 0 < d) (hdC : d ≤ C.scaleBound) :
    NativeSeamHalfStrip E F i j (fun t => q (d * (t : ℝ))) := by
  have hcalc := affineSeamCoordinates_c1_rank (q 0) C.tangent C.inward
    (fun t => C.clock (d * t)) C.height C.tangent_unit C.inward_unit C.orthogonal
    (C.clock_c1 d hd hdC) (C.clock_regular d hd hdC)
  refine {
    height := C.height
    height_pos := C.height_pos
    origin := q 0
    tangent := C.tangent
    inward := C.inward
    tangent_unit := C.tangent_unit
    inward_unit := C.inward_unit
    frame_orthogonal := C.orthogonal
    clock := fun t => C.clock (d * t)
    clock_c1 := C.clock_c1 d hd hdC
    clock_regular := fun t => C.clock_regular d hd hdC t t.property
    exact_boundary_lift := ?_
    planar_c1 := hcalc.1
    planar_embedding := affineSeamCoordinates_embedding (q 0) C.tangent C.inward
      (fun t => C.clock (d * t)) C.height C.tangent_unit C.inward_unit C.orthogonal
      (C.clock_embedding d hd hdC)
    planar_rank := hcalc.2
    maps_to_sector := ?_
    positive_sector_interior := ?_
    source_embedding := native_halfstrip_template_source_embedding E F i j q C d hd hdC
    positive_piece_interior := native_halfstrip_template_positive_piece_interior E F i j q C d hd hdC
  }
  · intro t
    simpa only [nativeHalfStripCoordinates, zero_smul, add_zero] using C.exact_lift d hd hdC t t.property
  · change MapsTo (affineSeamCoordinates (q 0) C.tangent C.inward (fun t => C.clock (d * t)))
      (seamHalfstrip C.height) ((F.domain i).chart j).map.target
    rw [((F.domain i).chart j).target_eq]
    exact C.maps_to_sector d hd hdC
  · change MapsTo (affineSeamCoordinates (q 0) C.tangent C.inward (fun t => C.clock (d * t)))
      (Ioo (-1 : ℝ) 1 ×ˢ Ioo (0 : ℝ) C.height) (interior ((F.domain i).chart j).map.target)
    rw [((F.domain i).chart j).target_eq]
    exact C.positive_interior d hd hdC

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
