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
run_cmd do
  let source := System.FilePath.mk (← getFileName)
  let path := source.parent.getD "." / "ProofData" / "ApprovedOriginalA2V464.olean"
  let (data,_) ← liftIO <| readModuleData path
  let all := data.constants.foldl (fun m ci => m.insert ci.name ci) ({} : Std.HashMap Name ConstantInfo)
  let pref := `SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
  let roots := #[pref ++ `pieceSphereCoordinate,pref ++ `SeamLocalTime,pref ++ `actualPieceConormal]
  let mut todo := roots
  let mut required : NameSet := {}
  let mut j := 0
  let initial := (← getEnv).setExporting false
  while j < todo.size do
    let n := todo[j]!
    j := j+1
    if required.contains n then continue
    required := required.insert n
    if (initial.find? n).isSome then continue
    let some ci := all[n]? | throwError "approved native dependency absent {n}"
    if n == pref ++ `A2_original then throwError "unpaid original root cannot be replayed"
    todo := todo ++ ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque := true) then todo := todo ++ v.getUsedConstants
  let mut pending := data.constants.filter (fun ci => required.contains ci.name && (initial.find? ci.name).isNone)
  while !pending.isEmpty do
    let mut next := #[]
    let mut progress := false
    for ci in pending do
      let env := (← getEnv).setExporting false
      let some value := ci.value? (allowOpaque := true) | throwError "unreplayable native primitive {ci.name}"
      let deps := ci.type.getUsedConstantsAsSet.union value.getUsedConstantsAsSet
      if deps.toArray.any (fun n => (env.find? n).isNone) then next := next.push ci; continue
      match ci with
      | .defnInfo d => liftCoreM <| addDecl (.defnDecl d)
      | .thmInfo d => liftCoreM <| addDecl (.thmDecl d)
      | .opaqueInfo d => liftCoreM <| addDecl (.opaqueDecl d)
      | _ => throwError "unexpected native declaration kind {ci.name}"
      let some stored := ((← getEnv).setExporting false).find? ci.name | throwError "native replay absent"
      unless ci == stored && ci.levelParams == stored.levelParams &&
          Expr.equal ci.type stored.type && ExprStructEq.mk ci.type == ExprStructEq.mk stored.type &&
          (match stored.value? (allowOpaque := true) with
           | some v => Expr.equal value v && ExprStructEq.mk value == ExprStructEq.mk v
           | none => false) do throwError "native raw replay drift {ci.name}"
      progress := true
    unless progress do throwError "native replay dependency stall {next.map ConstantInfo.name}"
    pending := next
  logInfo m!"APPROVED_NATIVE_REPLAY_PASS {required.toArray.size} dependency names"


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
