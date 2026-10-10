import OriginalA25SourceDefinitionsV464
import A5NativeSeamSector
import A5SectorProjectedInverse
import A5NativeLocalCover

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology MeasureTheory
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
universe u
variable {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)

open Lean Elab Command
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def pieceSphereCoordinate {S : CompactOrientedSurface.{u}}
    (Fprime : GeometricPiecewiseSurface S E.Carrier) (i : Fin Fprime.pieceCount)
    (j : Fin (Fprime.domain i).count) : Euc 2 → ThreeSphere :=
  E.toSphere ∘ Fprime.map ∘ Fprime.parametrization i ∘
    ((Fprime.domain i).chart j).map.symm

/-- Actual tangential metric trace div_P X, in the chart centred at the
piece image point. Every tangent and metric coefficient is derived from
that image, with within-differentiation on the genuine closed sector. -/


abbrev SeamLocalTime := Set.Ioo (-1 : ℝ) 1

/-- Actual conormal of a selected closed piece chart, transported along the
exact image equality to the actual common seam point. -/


def actualPieceConormal {S : CompactOrientedSurface.{u}}
    (Fprime : GeometricPiecewiseSurface S E.Carrier) (i : Fin Fprime.pieceCount)
    (j : Fin (Fprime.domain i).count) (y v : Euc 2) (p : ThreeSphere)
    (heq : pieceSphereCoordinate E Fprime i j y = p) : TangentSpace (𝓡 3) p :=
  heq ▸ mfderivWithin 𝓘(ℝ, Euc 2) (𝓡 3) (pieceSphereCoordinate E Fprime i j)
    ((Fprime.domain i).chart j).map.target y v

/-- The two actual adjacent C1 closed pieces near an interior seam point.
All incidence, boundary charts and outward metric unit conormals are output
construction data. Neither smooth sheet removal nor balance is assumed. -/



def nativeHalfStripDomain (height : ℝ) : Set (ℝ × ℝ) :=
  Ioo (-1 : ℝ) 1 ×ˢ Ico (0 : ℝ) height

def nativeHalfStripPositiveDomain (height : ℝ) : Set (ℝ × ℝ) :=
  Ioo (-1 : ℝ) 1 ×ˢ Ioo (0 : ℝ) height

def nativeHalfStripCoordinates (origin e m : Euc 2) (clock : ℝ → ℝ)
    (z : ℝ × ℝ) : Euc 2 := origin + clock z.1 • e + z.2 • m

/-- A real affine straight-sector halfstrip with the SAME boundary clock.
Only the boundary clock is C1; no smooth bulk reparametrization is required.
The source embedding is topological. All data and regularity are outputs. -/
structure NativeSeamHalfStrip {S : CompactOrientedSurface.{u}}
    (Fprime : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin Fprime.pieceCount) (j : Fin (Fprime.domain i).count)
    (lift : SeamLocalTime → Euc 2) where
  height : ℝ
  height_pos : 0 < height
  origin : Euc 2
  tangent : Euc 2
  inward : Euc 2
  tangent_unit : ‖tangent‖ = 1
  inward_unit : ‖inward‖ = 1
  frame_orthogonal : inner ℝ tangent inward = 0
  clock : ℝ → ℝ
  clock_c1 : ContDiffOn ℝ 1 clock (Ioo (-1 : ℝ) 1)
  clock_regular : ∀ t : SeamLocalTime, deriv clock (t : ℝ) ≠ 0
  exact_boundary_lift : ∀ t : SeamLocalTime,
    lift t = nativeHalfStripCoordinates origin tangent inward clock (t, 0)
  planar_c1 : ContDiffOn ℝ 1 (nativeHalfStripCoordinates origin tangent inward clock)
    (nativeHalfStripDomain height)
  planar_embedding : IsEmbedding (fun z : nativeHalfStripDomain height =>
    nativeHalfStripCoordinates origin tangent inward clock z)
  planar_rank : ∀ z ∈ nativeHalfStripDomain height,
    Function.Injective (fderiv ℝ (nativeHalfStripCoordinates origin tangent inward clock) z)
  maps_to_sector : MapsTo (nativeHalfStripCoordinates origin tangent inward clock)
    (nativeHalfStripDomain height) ((Fprime.domain i).chart j).map.target
  positive_sector_interior : MapsTo (nativeHalfStripCoordinates origin tangent inward clock)
    (nativeHalfStripPositiveDomain height) (interior ((Fprime.domain i).chart j).map.target)
  source_embedding : IsEmbedding (fun z : nativeHalfStripDomain height =>
    Fprime.parametrization i (((Fprime.domain i).chart j).map.symm
      (nativeHalfStripCoordinates origin tangent inward clock z)))
  positive_piece_interior : MapsTo
    (fun z => ((Fprime.domain i).chart j).map.symm
      (nativeHalfStripCoordinates origin tangent inward clock z))
    (nativeHalfStripPositiveDomain height) (Fprime.domain i).interior

/-- Literal original arc fields except balance, followed by construction support. -/
structure AdjacentArcData (G : A7.SourceGeometry E)
    {S : CompactOrientedSurface.{u}} (Fprime : GeometricPiecewiseSurface S E.Carrier)
    (a : Fin Fprime.seam.arcCount) (s : Time) where
  radius : ℝ
  radius_pos : 0 < radius
  left_bound : 0 < (s : ℝ) - radius
  right_bound : (s : ℝ) + radius < 1
  parameter : SeamLocalTime → Time
  parameter_formula : ∀ t : SeamLocalTime, (parameter t : ℝ) = (s : ℝ) + radius * (t : ℝ)
  edge : ℝ → ThreeSphere
  edge_formula : ∀ t : SeamLocalTime,
    edge t = E.toSphere (Fprime.map (Fprime.seam.arc a (parameter t)))
  edge_smooth : ContMDiffOn 𝓘(ℝ) (𝓡 3) ∞ edge (Ioo (-1 : ℝ) 1)
  edge_regular : ∀ t : SeamLocalTime, mfderiv 𝓘(ℝ) (𝓡 3) edge (t : ℝ) 1 ≠ 0
  one : Fin Fprime.pieceCount
  two : Fin Fprime.pieceCount
  chartOne : Fin (Fprime.domain one).count
  chartTwo : Fin (Fprime.domain two).count
  liftOne : SeamLocalTime → Euc 2
  liftTwo : SeamLocalTime → Euc 2
  liftOne_boundary : ∀ t : SeamLocalTime, liftOne t ∈ ((Fprime.domain one).chart chartOne).map.target ∩
    frontier ((Fprime.domain one).chart chartOne).map.target
  liftTwo_boundary : ∀ t : SeamLocalTime, liftTwo t ∈ ((Fprime.domain two).chart chartTwo).map.target ∩
    frontier ((Fprime.domain two).chart chartTwo).map.target
  imageOne : ∀ t : SeamLocalTime, pieceSphereCoordinate E Fprime one chartOne (liftOne t) = edge t
  imageTwo : ∀ t : SeamLocalTime, pieceSphereCoordinate E Fprime two chartTwo (liftTwo t) = edge t
  outwardOne : SeamLocalTime → Euc 2
  outwardTwo : SeamLocalTime → Euc 2
  outwardOne_direction : ∀ t : SeamLocalTime, ∃ ε : ℝ, 0 < ε ∧ ∀ b ∈ Ioo (0 : ℝ) ε,
    liftOne t - b • outwardOne t ∈ interior ((Fprime.domain one).chart chartOne).map.target ∧
    liftOne t + b • outwardOne t ∉ ((Fprime.domain one).chart chartOne).map.target
  outwardTwo_direction : ∀ t : SeamLocalTime, ∃ ε : ℝ, 0 < ε ∧ ∀ b ∈ Ioo (0 : ℝ) ε,
    liftTwo t - b • outwardTwo t ∈ interior ((Fprime.domain two).chart chartTwo).map.target ∧
    liftTwo t + b • outwardTwo t ∉ ((Fprime.domain two).chart chartTwo).map.target
  conormalOne_unit : ∀ t : SeamLocalTime, G.extension.inner (edge t)
    (actualPieceConormal E Fprime one chartOne (liftOne t) (outwardOne t) (edge t) (imageOne t))
    (actualPieceConormal E Fprime one chartOne (liftOne t) (outwardOne t) (edge t) (imageOne t)) = 1
  conormalTwo_unit : ∀ t : SeamLocalTime, G.extension.inner (edge t)
    (actualPieceConormal E Fprime two chartTwo (liftTwo t) (outwardTwo t) (edge t) (imageTwo t))
    (actualPieceConormal E Fprime two chartTwo (liftTwo t) (outwardTwo t) (edge t) (imageTwo t)) = 1
  conormalOne_orthogonal : ∀ t : SeamLocalTime, G.extension.inner (edge t)
    (actualPieceConormal E Fprime one chartOne (liftOne t) (outwardOne t) (edge t) (imageOne t))
    (mfderiv 𝓘(ℝ) (𝓡 3) edge (t : ℝ) 1) = 0
  conormalTwo_orthogonal : ∀ t : SeamLocalTime, G.extension.inner (edge t)
    (actualPieceConormal E Fprime two chartTwo (liftTwo t) (outwardTwo t) (edge t) (imageTwo t))
    (mfderiv 𝓘(ℝ) (𝓡 3) edge (t : ℝ) 1) = 0
  neighbourhood : Set ThreeSphere
  neighbourhood_open : IsOpen neighbourhood
  contains_point : E.toSphere (Fprime.map (Fprime.seam.arc a s)) ∈ neighbourhood
  covers_two_sheets : E.toSphere '' Fprime.image ∩ neighbourhood =
    ((E.toSphere ∘ Fprime.map ∘ Fprime.parametrization one) ''
      ((Fprime.domain one).chart chartOne).map.source ∪
    (E.toSphere ∘ Fprime.map ∘ Fprime.parametrization two) ''
      ((Fprime.domain two).chart chartTwo).map.source) ∩ neighbourhood
  otherwise_disjoint :
    ((E.toSphere ∘ Fprime.map ∘ Fprime.parametrization one) ''
      ((Fprime.domain one).chart chartOne).map.source ∩
    (E.toSphere ∘ Fprime.map ∘ Fprime.parametrization two) ''
      ((Fprime.domain two).chart chartTwo).map.source) ∩ neighbourhood =
    (edge '' Ioo (-1 : ℝ) 1) ∩ neighbourhood
  one_ne_two : one ≠ two
  incident_exact : ∀ t : SeamLocalTime, ∀ i : Fin Fprime.pieceCount,
    Fprime.seam.arc a (parameter t) ∈ range (Fprime.parametrization i) ↔ i = one ∨ i = two
  coreRadius : ℝ
  coreRadius_pos : 0 < coreRadius
  coreRadius_lt_one : coreRadius < 1
  core_edge_closure_in_neighbourhood :
    closure (edge '' Ioo (-coreRadius) coreRadius) ⊆ neighbourhood
  halfStripOne : NativeSeamHalfStrip E Fprime one chartOne liftOne
  halfStripTwo : NativeSeamHalfStrip E Fprime two chartTwo liftTwo
  outwardOne_continuous : Continuous outwardOne
  outwardTwo_continuous : Continuous outwardTwo
  conormalOne_continuous : Continuous (fun t : SeamLocalTime =>
    Bundle.TotalSpace.mk' (Euc 3) (edge t)
      (actualPieceConormal E Fprime one chartOne (liftOne t) (outwardOne t) (edge t) (imageOne t)))
  conormalTwo_continuous : Continuous (fun t : SeamLocalTime =>
    Bundle.TotalSpace.mk' (Euc 3) (edge t)
      (actualPieceConormal E Fprime two chartTwo (liftTwo t) (outwardTwo t) (edge t) (imageTwo t)))

/-- Literal original circle fields except balance, followed by construction support. -/
structure AdjacentCircleData (G : A7.SourceGeometry E)
    {S : CompactOrientedSurface.{u}} (Fprime : GeometricPiecewiseSurface S E.Carrier)
    (a : Fin Fprime.seam.circleCount) (s : Circle) where
  parameter : SeamLocalTime → Circle
  parameter_embedding : IsEmbedding parameter
  parameter_open_range : IsOpen (Set.range parameter)
  parameter_center : parameter ⟨0, neg_one_lt_zero, zero_lt_one⟩ = s
  edge : ℝ → ThreeSphere
  edge_formula : ∀ t : SeamLocalTime,
    edge t = E.toSphere (Fprime.map (Fprime.seam.circle a (parameter t)))
  edge_smooth : ContMDiffOn 𝓘(ℝ) (𝓡 3) ∞ edge (Ioo (-1 : ℝ) 1)
  edge_regular : ∀ t : SeamLocalTime, mfderiv 𝓘(ℝ) (𝓡 3) edge (t : ℝ) 1 ≠ 0
  one : Fin Fprime.pieceCount
  two : Fin Fprime.pieceCount
  chartOne : Fin (Fprime.domain one).count
  chartTwo : Fin (Fprime.domain two).count
  liftOne : SeamLocalTime → Euc 2
  liftTwo : SeamLocalTime → Euc 2
  liftOne_boundary : ∀ t : SeamLocalTime, liftOne t ∈ ((Fprime.domain one).chart chartOne).map.target ∩
    frontier ((Fprime.domain one).chart chartOne).map.target
  liftTwo_boundary : ∀ t : SeamLocalTime, liftTwo t ∈ ((Fprime.domain two).chart chartTwo).map.target ∩
    frontier ((Fprime.domain two).chart chartTwo).map.target
  imageOne : ∀ t : SeamLocalTime, pieceSphereCoordinate E Fprime one chartOne (liftOne t) = edge t
  imageTwo : ∀ t : SeamLocalTime, pieceSphereCoordinate E Fprime two chartTwo (liftTwo t) = edge t
  outwardOne : SeamLocalTime → Euc 2
  outwardTwo : SeamLocalTime → Euc 2
  outwardOne_direction : ∀ t : SeamLocalTime, ∃ ε : ℝ, 0 < ε ∧ ∀ b ∈ Ioo (0 : ℝ) ε,
    liftOne t - b • outwardOne t ∈ interior ((Fprime.domain one).chart chartOne).map.target ∧
    liftOne t + b • outwardOne t ∉ ((Fprime.domain one).chart chartOne).map.target
  outwardTwo_direction : ∀ t : SeamLocalTime, ∃ ε : ℝ, 0 < ε ∧ ∀ b ∈ Ioo (0 : ℝ) ε,
    liftTwo t - b • outwardTwo t ∈ interior ((Fprime.domain two).chart chartTwo).map.target ∧
    liftTwo t + b • outwardTwo t ∉ ((Fprime.domain two).chart chartTwo).map.target
  conormalOne_unit : ∀ t : SeamLocalTime, G.extension.inner (edge t)
    (actualPieceConormal E Fprime one chartOne (liftOne t) (outwardOne t) (edge t) (imageOne t))
    (actualPieceConormal E Fprime one chartOne (liftOne t) (outwardOne t) (edge t) (imageOne t)) = 1
  conormalTwo_unit : ∀ t : SeamLocalTime, G.extension.inner (edge t)
    (actualPieceConormal E Fprime two chartTwo (liftTwo t) (outwardTwo t) (edge t) (imageTwo t))
    (actualPieceConormal E Fprime two chartTwo (liftTwo t) (outwardTwo t) (edge t) (imageTwo t)) = 1
  conormalOne_orthogonal : ∀ t : SeamLocalTime, G.extension.inner (edge t)
    (actualPieceConormal E Fprime one chartOne (liftOne t) (outwardOne t) (edge t) (imageOne t))
    (mfderiv 𝓘(ℝ) (𝓡 3) edge (t : ℝ) 1) = 0
  conormalTwo_orthogonal : ∀ t : SeamLocalTime, G.extension.inner (edge t)
    (actualPieceConormal E Fprime two chartTwo (liftTwo t) (outwardTwo t) (edge t) (imageTwo t))
    (mfderiv 𝓘(ℝ) (𝓡 3) edge (t : ℝ) 1) = 0
  neighbourhood : Set ThreeSphere
  neighbourhood_open : IsOpen neighbourhood
  contains_point : E.toSphere (Fprime.map (Fprime.seam.circle a s)) ∈ neighbourhood
  covers_two_sheets : E.toSphere '' Fprime.image ∩ neighbourhood =
    ((E.toSphere ∘ Fprime.map ∘ Fprime.parametrization one) ''
      ((Fprime.domain one).chart chartOne).map.source ∪
    (E.toSphere ∘ Fprime.map ∘ Fprime.parametrization two) ''
      ((Fprime.domain two).chart chartTwo).map.source) ∩ neighbourhood
  otherwise_disjoint :
    ((E.toSphere ∘ Fprime.map ∘ Fprime.parametrization one) ''
      ((Fprime.domain one).chart chartOne).map.source ∩
    (E.toSphere ∘ Fprime.map ∘ Fprime.parametrization two) ''
      ((Fprime.domain two).chart chartTwo).map.source) ∩ neighbourhood =
    (edge '' Ioo (-1 : ℝ) 1) ∩ neighbourhood

  one_ne_two : one ≠ two
  incident_exact : ∀ t : SeamLocalTime, ∀ i : Fin Fprime.pieceCount,
    Fprime.seam.circle a (parameter t) ∈ range (Fprime.parametrization i) ↔ i = one ∨ i = two
  coreRadius : ℝ
  coreRadius_pos : 0 < coreRadius
  coreRadius_lt_one : coreRadius < 1
  core_edge_closure_in_neighbourhood :
    closure (edge '' Ioo (-coreRadius) coreRadius) ⊆ neighbourhood
  halfStripOne : NativeSeamHalfStrip E Fprime one chartOne liftOne
  halfStripTwo : NativeSeamHalfStrip E Fprime two chartTwo liftTwo
  outwardOne_continuous : Continuous outwardOne
  outwardTwo_continuous : Continuous outwardTwo
  conormalOne_continuous : Continuous (fun t : SeamLocalTime =>
    Bundle.TotalSpace.mk' (Euc 3) (edge t)
      (actualPieceConormal E Fprime one chartOne (liftOne t) (outwardOne t) (edge t) (imageOne t)))
  conormalTwo_continuous : Continuous (fun t : SeamLocalTime =>
    Bundle.TotalSpace.mk' (Euc 3) (edge t)
      (actualPieceConormal E Fprime two chartTwo (liftTwo t) (outwardTwo t) (edge t) (imageTwo t)))

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
