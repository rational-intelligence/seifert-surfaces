import OriginalA25SourceDefinitionsV464
import A2NativeSeamIncidenceV468
import NativeHalfStripRelativeWindowProbe
import DifferentialGeometry.Analysis.ODE.Flow.CompactSupport
import SectorRegularityHelpers
import B1FiniteRefinement
import Mathlib.Geometry.Manifold.VectorField.Pullback
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import OriginalA4GeometryBridges
import A2NativeNormalProjection
import A2NormalSmoothProbe
import A2EuclideanRetractionProbe
import A2MetricFluxV468
import A2AffineHalfboxV470
import A2OutwardSignProbe
import A2NativeHalfstripClosedBoxProbe
import A2NativeAffineVolumeProbe
import A2PositiveGramRankReadyV469
import A2NativeIncidenceSupportV469
import DifferentialGeometry.Topology.InvarianceOfDomainManifold
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology MeasureTheory Matrix Filter
open DifferentialGeometry.Analysis.ODE
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
universe u
variable {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)

/-- A smooth ambient field compactly supported in the actual exterior interior.
Interior-supported fields on the exterior have the equivalent smooth zero
extension to the two-sided ambient sphere. No flow or variation identity is input. -/
structure InteriorSmoothVectorField where
  field : ∀ p : ThreeSphere, TangentSpace (𝓡 3) p
  smooth : ContMDiff (𝓡 3) (𝓡 3).tangent ∞
    (fun p => Bundle.TotalSpace.mk' (Euc 3) p (field p))
  compact_support : IsCompact (closure {p | field p ≠ 0})
  support_interior : closure {p | field p ≠ 0} ⊆
    E.toSphere '' (𝓡∂ 3).interior E.Carrier

/-- Actual coordinate vector of the supplied field in the actual ambient chart. -/
def fieldCoordinate (X : InteriorSmoothVectorField E) (p : ThreeSphere)
    (z : Euc 3) : Euc 3 :=
  let e := extChartAt (𝓡 3) p
  (NormedSpace.fromTangentSpace (e (e.symm z)))
    (mfderiv (𝓡 3) 𝓘(ℝ, Euc 3) e (e.symm z) (X.field (e.symm z)))

/-- Levi-Civita covariant derivative of that same field, from the actual metric's
Christoffel formula and ordinary coordinate derivative. -/
def covariantFieldCoordinate (G : A7.SourceGeometry E)
    (X : InteriorSmoothVectorField E) (p : ThreeSphere) (z v : Euc 3) : Euc 3 :=
  let g := MetricInChart (𝓡 3) G.extension p
  let x := fieldCoordinate E X p
  fderiv ℝ x z v + ∑ a : Fin 3,
    (∑ b : Fin 3, ∑ c : Fin 3, ChristoffelCoordinate g z a b c * v b * x z c) •
      EuclideanSpace.single a 1

/- The actual two-sided ambient parametrization is imported byte-exact from the paid seam definitions. -/


open Lean Elab Command
set_option maxHeartbeats 0
set_option maxRecDepth 100000
run_cmd do
  let source := System.FilePath.mk (← getFileName)
  let path := source.parent.getD "." / "A2ProofData" / "ApprovedOriginalA2V464.olean"
  let (data,_) ← liftIO <| readModuleData path
  let all := data.constants.foldl (fun m ci => m.insert ci.name ci) ({} : Std.HashMap Name ConstantInfo)
  let pref := `SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
  let roots := #[pref ++ `pieceTangentialDivergence,pref ++ `pieceDivergenceSum,pref ++ `PiecesMinimal]
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


/- The actual conormal definition is imported byte-exact from the paid seam definitions. -/


/-- The two actual adjacent C1 closed pieces near an interior seam point.
All incidence, boundary charts and outward metric unit conormals are output
construction data. Neither smooth sheet removal nor balance is assumed. -/
structure OppositePieceConormals (G : A7.SourceGeometry E)
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
  balance : ∀ t : SeamLocalTime,
    actualPieceConormal E Fprime one chartOne (liftOne t) (outwardOne t) (edge t) (imageOne t) +
    actualPieceConormal E Fprime two chartTwo (liftTwo t) (outwardTwo t) (edge t) (imageTwo t) = 0

/-- The same literal opposite-conormal conclusion on each circle component
of the proper graph, using an output smooth local circle trace. -/
structure OppositeCirclePieceConormals (G : A7.SourceGeometry E)
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
  balance : ∀ t : SeamLocalTime,
    actualPieceConormal E Fprime one chartOne (liftOne t) (outwardOne t) (edge t) (imageOne t) +
    actualPieceConormal E Fprime two chartTwo (liftTwo t) (outwardTwo t) (edge t) (imageTwo t) = 0

private theorem area_nonnegative {S : CompactOrientedSurface.{u}}
    (g : SmoothMetric E.Carrier) (F : GeometricPiecewiseSurface S E.Carrier) :
    0 ≤ geometricArea g F := by
  classical
  apply Finset.sum_nonneg
  intro i hi
  unfold sectorArea sectorPartitionArea
  apply Finset.sum_nonneg
  intro j hj
  exact MeasureTheory.integral_nonneg (fun _ => Real.sqrt_nonneg _)
private theorem minimum_compare {S R Q : CompactOrientedSurface.{u}}
    (g : SmoothMetric E.Carrier)
    (F : GeometricPiecewiseSurface S E.Carrier)
    (Fprime : GeometricPiecewiseSurface R E.Carrier)
    (h : FixedBoundaryMinimizer E g F Fprime)
    (C : GeometricPiecewiseSurface Q E.Carrier)
    (hc : FixedBoundaryImageIsotopic E F C) :
    geometricArea g Fprime ≤ geometricArea g C := by
  rw [h.attainment]
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro a ⟨P, H, _, rfl⟩
    exact area_nonnegative E g H
  · exact ⟨Q, C, hc, rfl⟩
private theorem field_zero_outside (X : InteriorSmoothVectorField E)
    {p : ThreeSphere} (hp : p ∉ E.toSphere '' (𝓡∂ 3).interior E.Carrier) :
    X.field p = 0 := by
  by_contra h
  exact hp (X.support_interior (subset_closure h))
private theorem field_tsupport_compact (X : InteriorSmoothVectorField E) :
    IsCompact (tsupport X.field) := by
  exact X.compact_support
private theorem field_complete (X : InteriorSmoothVectorField E) :
    ∀ p : ThreeSphere, ∃ γ : ℝ → ThreeSphere,
      γ 0 = p ∧ IsMIntegralCurve γ X.field := by
  apply DifferentialGeometry.Analysis.ODE.exists_globalIntegralCurve_of_compactSupport
  · exact X.smooth
  · exact field_tsupport_compact E X
private theorem field_flow_joint (X : InteriorSmoothVectorField E) :
    ContMDiff (𝓘(ℝ).prod (𝓡 3)) (𝓡 3) ∞
      (fun q : ℝ × ThreeSphere => curveAt X.field (field_complete E X) q.2 q.1) := by
  exact DifferentialGeometry.Analysis.ODE.contMDiff_curveAt
    X.field X.smooth (field_complete E X)
private theorem field_flow_diffeomorph (X : InteriorSmoothVectorField E) (t : ℝ) :
    ∃ d : Diffeomorph (𝓡 3) (𝓡 3) ThreeSphere ThreeSphere ∞,
      (∀ p, d p = curveAt X.field (field_complete E X) p t) ∧
      (∀ p, d.symm p = curveAt X.field (field_complete E X) p (-t)) := by
  exact DifferentialGeometry.Analysis.ODE.globalFlow_diffeomorph_of_complete
    X.field X.smooth (field_complete E X) t
private theorem field_flow_fixed (X : InteriorSmoothVectorField E)
    {p : ThreeSphere} (hp : p ∉ E.toSphere '' (𝓡∂ 3).interior E.Carrier) (t : ℝ) :
    curveAt X.field (field_complete E X) p t = p := by
  apply DifferentialGeometry.Analysis.ODE.curveAt_eq_self_of_eq_zero
  · exact X.smooth.of_le (by simp)
  · exact field_zero_outside E X hp
private theorem field_flow_preserves_range (X : InteriorSmoothVectorField E)
    (p : ThreeSphere) (hp : p ∈ Set.range E.toSphere) (t : ℝ) :
    curveAt X.field (field_complete E X) p t ∈ Set.range E.toSphere := by
  by_contra h
  have hnot : curveAt X.field (field_complete E X) p t ∉
      E.toSphere '' (𝓡∂ 3).interior E.Carrier := by
    intro he
    obtain ⟨q, _, heq⟩ := he
    exact h ⟨q, heq⟩
  have hfix := field_flow_fixed E X hnot (-t)
  rw [← curveAt_add X.field (X.smooth.of_le (by simp)) (field_complete E X),
    add_neg_cancel, curveAt_zero] at hfix
  exact h (hfix ▸ hp)
private def field_flow_homeomorph (X : InteriorSmoothVectorField E) (t : ℝ) :
    E.Carrier ≃ₜ E.Carrier := by
  let f : E.Carrier → E.Carrier := fun p =>
    ⟨curveAt X.field (field_complete E X) (E.toSphere p) t,
      by
        obtain ⟨q, hq⟩ := field_flow_preserves_range E X _ ⟨p, rfl⟩ t
        exact hq ▸ q.property⟩
  let g : E.Carrier → E.Carrier := fun p =>
    ⟨curveAt X.field (field_complete E X) (E.toSphere p) (-t),
      by
        obtain ⟨q, hq⟩ := field_flow_preserves_range E X _ ⟨p, rfl⟩ (-t)
        exact hq ▸ q.property⟩
  refine {
    toFun := f
    invFun := g
    left_inv := ?_
    right_inv := ?_
    continuous_toFun := ?_
    continuous_invFun := ?_ }
  · intro p
    apply Subtype.ext
    change curveAt X.field (field_complete E X)
      (curveAt X.field (field_complete E X) (E.toSphere p) t) (-t) = E.toSphere p
    rw [← curveAt_add X.field (X.smooth.of_le (by simp)) (field_complete E X),
      add_neg_cancel, curveAt_zero]
  · intro p
    apply Subtype.ext
    change curveAt X.field (field_complete E X)
      (curveAt X.field (field_complete E X) (E.toSphere p) (-t)) t = E.toSphere p
    rw [← curveAt_add X.field (X.smooth.of_le (by simp)) (field_complete E X),
      neg_add_cancel, curveAt_zero]
  · apply Continuous.subtype_mk
    exact (field_flow_joint E X).continuous.comp
      (continuous_const.prodMk continuous_subtype_val)
  · apply Continuous.subtype_mk
    exact (field_flow_joint E X).continuous.comp
      (continuous_const.prodMk continuous_subtype_val)
private def field_flow_exterior_diffeomorph (X : InteriorSmoothVectorField E) (t : ℝ) :
    Diffeomorph (𝓡∂ 3) (𝓡∂ 3) E.Carrier E.Carrier ∞ := by
  let h := field_flow_homeomorph E X t
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  refine {
    toEquiv := h.toEquiv
    contMDiff_toFun := ?_
    contMDiff_invFun := ?_ }
  · apply (ContMDiff.iff_comp_isImmersion hinc.isImmersion).mpr
    refine ⟨h.continuous, ?_⟩
    exact (field_flow_joint E X).comp
      (contMDiff_const.prodMk hinc.contMDiff)
  · apply (ContMDiff.iff_comp_isImmersion hinc.isImmersion).mpr
    refine ⟨h.symm.continuous, ?_⟩
    exact (field_flow_joint E X).comp
      (contMDiff_const.prodMk hinc.contMDiff)

private theorem diffeo_derivative_injective
    (d : Diffeomorph (𝓡∂ 3) (𝓡∂ 3) E.Carrier E.Carrier ∞) (p : E.Carrier) :
    Function.Injective (mfderiv (𝓡∂ 3) (𝓡∂ 3) d p) := by
  exact (d.mfderivToContinuousLinearEquiv (by simp) p).injective
private def transformed_seam {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier)
    (d : Diffeomorph (𝓡∂ 3) (𝓡∂ 3) E.Carrier E.Carrier ∞) :
    SeamGraph S (d ∘ F.map) where
  arcCount := F.seam.arcCount
  circleCount := F.seam.circleCount
  arc := F.seam.arc
  circle := F.seam.circle
  arc_embedding := F.seam.arc_embedding
  circle_embedding := F.seam.circle_embedding
  arc_smooth_image := fun i => d.contMDiff.comp (F.seam.arc_smooth_image i)
  arc_differential_injective := by
    intro i x
    rw [show (d ∘ ⇑F.map) ∘ ⇑(F.seam.arc i) = d ∘ (F.map ∘ F.seam.arc i) from rfl,
      mfderiv_comp x (d.mdifferentiable (by simp) _) 
        ((F.seam.arc_smooth_image i).mdifferentiable (by simp) x)]
    exact (diffeo_derivative_injective E d _).comp (F.seam.arc_differential_injective i x)
  circle_smooth_image := fun i => d.contMDiff.comp (F.seam.circle_smooth_image i)
  circle_differential_injective := by
    intro i x
    rw [show (d ∘ ⇑F.map) ∘ ⇑(F.seam.circle i) = d ∘ (F.map ∘ F.seam.circle i) from rfl,
      mfderiv_comp x (d.mdifferentiable (by simp) _)
        ((F.seam.circle_smooth_image i).mdifferentiable (by simp) x)]
    exact (diffeo_derivative_injective E d _).comp (F.seam.circle_differential_injective i x)
  arc_boundary := F.seam.arc_boundary
  circle_off_boundary := F.seam.circle_off_boundary
  arc_intersections := F.seam.arc_intersections
  circle_intersections := F.seam.circle_intersections
  arc_circle_disjoint := F.seam.arc_circle_disjoint
private def transformed_surface {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier)
    (d : Diffeomorph (𝓡∂ 3) (𝓡∂ 3) E.Carrier E.Carrier ∞) :
    GeometricPiecewiseSurface S E.Carrier where
  map := ⟨d ∘ F.map, d.continuous.comp F.map.continuous⟩
  embedding := d.toHomeomorph.isEmbedding.comp F.embedding
  boundary_preimage := by
    change F.map ⁻¹' (d ⁻¹' (𝓡∂ 3).boundary E.Carrier) = S.boundary
    rw [d.preimage_boundary (by simp), F.boundary_preimage]
  seam := transformed_seam E F d
  smooth_off_seam := by
    intro x hx
    obtain ⟨c, hc, hsub⟩ := F.smooth_off_seam x hx
    refine ⟨{
      chart := c.chart
      source_open := c.source_open
      target_open := c.target_open
      cInfinity := d.contMDiff.comp_contMDiffOn c.cInfinity
      differential_injective := ?_
      boundary_image := c.boundary_image }, hc, hsub⟩
    intro y hy
    rw [mfderivWithin_of_mem_nhds (c.target_open.mem_nhds hy)]
    change Function.Injective (mfderiv (𝓡∂ 2) (𝓡∂ 3) (d ∘ (F.map ∘ c.chart.symm)) y)
    rw [mfderiv_comp y (d.mdifferentiable (by simp) _)
        ((c.cInfinity.contMDiffAt (c.target_open.mem_nhds hy)).mdifferentiableAt (by simp))]
    apply (diffeo_derivative_injective E d _).comp
    have hc := c.differential_injective y hy
    rw [mfderivWithin_of_mem_nhds (c.target_open.mem_nhds hy)] at hc
    exact fun v w h => hc h
  pieceCount := F.pieceCount
  domain := F.domain
  parametrization := F.parametrization
  parametrization_embedding := F.parametrization_embedding
  piece_c1 := fun i j => (d.contMDiff.of_le (by simp)).comp_contMDiffOn (F.piece_c1 i j)
  piece_topological_embedding := fun i => d.toHomeomorph.isEmbedding.comp (F.piece_topological_embedding i)
  piece_differential_injective := by
    intro i j y hy
    change Function.Injective (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 3)
      (d ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j)
      ((F.domain i).chart j).map.target y)
    rw [mfderiv_comp_mfderivWithin y (d.mdifferentiable (by simp) _)
      (((F.piece_c1 i j).mdifferentiableOn (by simp)) y hy) ?_]
    · exact (diffeo_derivative_injective E d _).comp (F.piece_differential_injective i j y hy)
    · apply UniqueDiffWithinAt.uniqueMDiffWithinAt
      have hUD : UniqueDiffOn ℝ ((F.domain i).chart j).map.target := by
        rw [((F.domain i).chart j).target_eq]
        exact SectorModel.uniqueDiffOn_domain _
      exact hUD y hy
  piece_smooth_interior := fun i j => d.contMDiff.comp_contMDiffOn (F.piece_smooth_interior i j)
  piece_edges_smooth := fun i j t ht => d.contMDiff.comp_contMDiffOn (F.piece_edges_smooth i j t ht)
  piece_interior_component := F.piece_interior_component
  pieces_distinct := F.pieces_distinct
  piece_closure := F.piece_closure
  covers := F.covers
  piece_boundary := F.piece_boundary
private def transformed_source_map {S R : CompactOrientedSurface.{u}}
    {F : GeometricPiecewiseSurface S E.Carrier}
    {G : GeometricPiecewiseSurface R E.Carrier} {f : S → R}
    (H : GeometricSourceMap F G f)
    (d0 d1 : Diffeomorph (𝓡∂ 3) (𝓡∂ 3) E.Carrier E.Carrier ∞) :
    GeometricSourceMap (transformed_surface E F d0) (transformed_surface E G d1) f where
  count := H.count
  domain := H.domain
  parametrization := H.parametrization
  embedding := H.embedding
  covers := H.covers
  source_c1 := fun i => (d0.contMDiff.of_le (by simp)).comp (H.source_c1 i)
  source_injective := by
    intro i q
    change Function.Injective (mfderiv CornerModel (𝓡∂ 3)
      (d0 ∘ (F.map ∘ H.parametrization i)) q)
    rw [mfderiv_comp q (d0.mdifferentiable (by simp) _)
      ((H.source_c1 i).mdifferentiable (by simp) q)]
    exact (diffeo_derivative_injective E d0 _).comp (H.source_injective i q)
  source_smooth_interior := fun i => d0.contMDiff.comp_contMDiffOn (H.source_smooth_interior i)
  target_c1 := fun i => (d1.contMDiff.of_le (by simp)).comp (H.target_c1 i)
  target_injective := by
    intro i q
    change Function.Injective (mfderiv CornerModel (𝓡∂ 3)
      (d1 ∘ (G.map ∘ f ∘ H.parametrization i)) q)
    rw [mfderiv_comp q (d1.mdifferentiable (by simp) _)
      ((H.target_c1 i).mdifferentiable (by simp) q)]
    exact (diffeo_derivative_injective E d1 _).comp (H.target_injective i q)
  target_smooth_interior := fun i => d1.contMDiff.comp_contMDiffOn (H.target_smooth_interior i)
private theorem exterior_flow_joint (X : InteriorSmoothVectorField E) :
    ContMDiff (𝓘(ℝ).prod (𝓡∂ 3)) (𝓡∂ 3) ∞
      (fun q : ℝ × E.Carrier => field_flow_exterior_diffeomorph E X q.1 q.2) := by
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  apply (ContMDiff.iff_comp_isImmersion hinc.isImmersion).mpr
  refine ⟨?_, ?_⟩
  · apply Continuous.subtype_mk
    exact (field_flow_joint E X).continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  · exact (field_flow_joint E X).comp
      (contMDiff_fst.prodMk (hinc.contMDiff.comp contMDiff_snd))
private theorem exterior_flow_fixed_boundary (X : InteriorSmoothVectorField E)
    (t : ℝ) (p : E.Carrier) (hp : p ∈ (𝓡∂ 3).boundary E.Carrier) :
    field_flow_exterior_diffeomorph E X t p = p := by
  apply Subtype.ext
  apply field_flow_fixed E X
  rintro ⟨q, hq, heq⟩
  have hqp : q = p := Subtype.ext heq
  subst q
  exact (𝓡∂ 3).disjoint_interior_boundary (M := E.Carrier) |>.le_bot ⟨hq, hp⟩
private def flow_graph_homeomorph (X : InteriorSmoothVectorField E) (ε : ℝ) :
    (Time × E.Carrier) ≃ₜ (Time × E.Carrier) where
  toFun q := (q.1, field_flow_exterior_diffeomorph E X (ε * (q.1 : ℝ)) q.2)
  invFun q := (q.1, field_flow_exterior_diffeomorph E X (-(ε * (q.1 : ℝ))) q.2)
  left_inv := by
    intro q
    refine Prod.ext ?_ ?_
    · rfl
    apply Subtype.ext
    change curveAt X.field (field_complete E X)
      (curveAt X.field (field_complete E X) (E.toSphere q.2) (ε * (q.1 : ℝ)))
      (-(ε * (q.1 : ℝ))) = E.toSphere q.2
    rw [← curveAt_add X.field (X.smooth.of_le (by simp)) (field_complete E X),
      add_neg_cancel, curveAt_zero]
  right_inv := by
    intro q
    refine Prod.ext ?_ ?_
    · rfl
    apply Subtype.ext
    change curveAt X.field (field_complete E X)
      (curveAt X.field (field_complete E X) (E.toSphere q.2) (-(ε * (q.1 : ℝ))))
      (ε * (q.1 : ℝ)) = E.toSphere q.2
    rw [← curveAt_add X.field (X.smooth.of_le (by simp)) (field_complete E X),
      neg_add_cancel, curveAt_zero]
  continuous_toFun := continuous_fst.prodMk ((exterior_flow_joint E X).continuous.comp
    ((continuous_const.mul (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd))
  continuous_invFun := continuous_fst.prodMk ((exterior_flow_joint E X).continuous.comp
    ((continuous_const.mul (continuous_subtype_val.comp continuous_fst)).neg.prodMk continuous_snd))
private def flow_graph_diffeomorph (X : InteriorSmoothVectorField E) (ε : ℝ) :
    Diffeomorph ((𝓡∂ 1).prod (𝓡∂ 3)) ((𝓡∂ 1).prod (𝓡∂ 3))
      (Time × E.Carrier) (Time × E.Carrier) ∞ where
  toEquiv := (flow_graph_homeomorph E X ε).toEquiv
  contMDiff_toFun := by
    apply contMDiff_fst.prodMk
    exact (exterior_flow_joint E X).comp (f := fun q : Time × E.Carrier =>
      (ε * (q.1 : ℝ), q.2))
      ((contMDiff_const.mul (contMDiff_subtypeVal_Icc.comp contMDiff_fst)).prodMk contMDiff_snd)
  contMDiff_invFun := by
    apply contMDiff_fst.prodMk
    exact (exterior_flow_joint E X).comp (f := fun q : Time × E.Carrier =>
      (-(ε * (q.1 : ℝ)), q.2))
      ((contMDiff_const.mul (contMDiff_subtypeVal_Icc.comp contMDiff_fst)).neg.prodMk contMDiff_snd)
private def transformed_track {S : CompactOrientedSurface.{u}}
    {F : GeometricPiecewiseSurface S E.Carrier} {track : Time × S → E.Carrier}
    (H : GeometricTrack F track) (X : InteriorSmoothVectorField E) (ε : ℝ) :
    GeometricTrack F (fun q => field_flow_exterior_diffeomorph E X (ε * (q.1 : ℝ)) (track q)) where
  count := H.count
  prism := H.prism
  parametrization := H.parametrization
  embedding := H.embedding
  covers := H.covers
  source_c1 := H.source_c1
  source_injective := H.source_injective
  source_smooth_interior := H.source_smooth_interior
  target_c1 := fun i => ((flow_graph_diffeomorph E X ε).contMDiff.of_le (by simp)).comp (H.target_c1 i)
  target_injective := by
    intro i q
    change Function.Injective (mfderiv (modelWithCornersEuclideanQuadrant 3)
      ((𝓡∂ 1).prod (𝓡∂ 3))
      (flow_graph_diffeomorph E X ε ∘
        (fun q => ((H.parametrization i q).1, track (H.parametrization i q)))) q)
    rw [mfderiv_comp q ((flow_graph_diffeomorph E X ε).mdifferentiable (by simp) _)
      ((H.target_c1 i).mdifferentiable (by simp) q)]
    exact ((flow_graph_diffeomorph E X ε).mfderivToContinuousLinearEquiv (by simp) _).injective.comp
      (H.target_injective i q)
  target_smooth_interior := fun i => (flow_graph_diffeomorph E X ε).contMDiff.comp_contMDiffOn
    (H.target_smooth_interior i)
private theorem flow_admissible {S R : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier)
    (G : GeometricPiecewiseSurface R E.Carrier)
    (h : FixedBoundaryImageIsotopic E F G) (X : InteriorSmoothVectorField E) (ε : ℝ) :
    FixedBoundaryImageIsotopic E F
      (transformed_surface E G (field_flow_exterior_diffeomorph E X ε)) := by
  classical
  obtain ⟨e, stage, hcont, ⟨htrack⟩, hzero, hone, hbdry⟩ := h
  let dt := field_flow_exterior_diffeomorph E X
  let stage' : Time → GeometricPiecewiseSurface S E.Carrier :=
    fun t => transformed_surface E (stage t) (dt (ε * (t : ℝ)))
  let e' : GeometricSourceHomeomorph F (transformed_surface E G (dt ε)) := {
    homeomorph := e.homeomorph
    forward := transformed_source_map E e.forward (Diffeomorph.refl (𝓡∂ 3) E.Carrier ∞) (dt ε)
    backward := transformed_source_map E e.backward (dt ε) (Diffeomorph.refl (𝓡∂ 3) E.Carrier ∞)
    boundary_image := e.boundary_image }
  refine ⟨e', stage', ?_, ⟨transformed_track E htrack X ε⟩, ?_, ?_, ?_⟩
  · exact (exterior_flow_joint E X).continuous.comp
      ((continuous_const.mul (continuous_subtype_val.comp continuous_fst)).prodMk hcont)
  · ext x
    change dt (ε * (0 : ℝ)) ((stage 0).map x) = F.map x
    rw [mul_zero, hzero]
    apply Subtype.ext
    exact curveAt_zero _ _ _
  · ext x
    change dt (ε * (1 : ℝ)) ((stage 1).map x) = dt ε (G.map (e.homeomorph x))
    rw [mul_one, hone]
    rfl
  · intro t x hx
    change dt (ε * (t : ℝ)) ((stage t).map x) = F.map x
    rw [hbdry t x hx]
    apply exterior_flow_fixed_boundary E X
    rw [← F.boundary_preimage] at hx
    exact hx
private theorem flow_area_is_global_minimum {S R : CompactOrientedSurface.{u}}
    (g : SmoothMetric E.Carrier) (F : GeometricPiecewiseSurface S E.Carrier)
    (G : GeometricPiecewiseSurface R E.Carrier) (h : FixedBoundaryMinimizer E g F G)
    (X : InteriorSmoothVectorField E) :
    ∀ t : ℝ, geometricArea g G ≤
      geometricArea g (transformed_surface E G (field_flow_exterior_diffeomorph E X t)) := by
  intro t
  exact minimum_compare E g F G h _ (flow_admissible E F G h.in_class X t)
private theorem native_piece_smooth_and_rank {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier) (i : Fin F.pieceCount)
    (j : Fin (F.domain i).count) :
    ContMDiffOn 𝓘(ℝ, Euc 2) (𝓡 3) ∞ (pieceSphereCoordinate E F i j)
      (interior ((F.domain i).chart j).map.target) ∧
    ∀ y ∈ interior ((F.domain i).chart j).map.target,
      Function.Injective (mfderiv 𝓘(ℝ, Euc 2) (𝓡 3) (pieceSphereCoordinate E F i j) y) := by
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  refine ⟨hinc.contMDiff.comp_contMDiffOn (F.piece_smooth_interior i j), ?_⟩
  intro y hy
  change Function.Injective (mfderiv 𝓘(ℝ, Euc 2) (𝓡 3)
    (E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j) y)
  rw [mfderiv_comp y (hinc.contMDiff.mdifferentiableAt (by simp))
    (((F.piece_smooth_interior i j).contMDiffAt (isOpen_interior.mem_nhds hy)).mdifferentiableAt (by simp))]
  apply (hinc.isImmersion.mfderiv_injective (by simp) _).comp
  have h := F.piece_differential_injective i j y (interior_subset hy)
  rw [mfderivWithin_of_mem_nhds
    (Filter.mem_of_superset (isOpen_interior.mem_nhds hy) interior_subset)] at h
  exact fun v w hvw => h hvw
private theorem flow_zero_map {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier) (X : InteriorSmoothVectorField E) :
    (transformed_surface E F (field_flow_exterior_diffeomorph E X 0)).map = F.map := by
  ext p
  apply Subtype.ext
  exact curveAt_zero _ _ _
private theorem flow_area_at_zero {S : CompactOrientedSurface.{u}}
    (g : SmoothMetric E.Carrier) (F : GeometricPiecewiseSurface S E.Carrier)
    (X : InteriorSmoothVectorField E) :
    geometricArea g (transformed_surface E F (field_flow_exterior_diffeomorph E X 0)) =
      geometricArea g F := by
  apply piecewiseArea_same_image
  dsimp [GeometricPiecewiseSurface.image]
  rw [flow_zero_map E F X]
private theorem flow_area_local_minimum {S R : CompactOrientedSurface.{u}}
    (g : SmoothMetric E.Carrier) (F : GeometricPiecewiseSurface S E.Carrier)
    (G : GeometricPiecewiseSurface R E.Carrier) (h : FixedBoundaryMinimizer E g F G)
    (X : InteriorSmoothVectorField E) :
    IsLocalMin (fun t : ℝ => geometricArea g
      (transformed_surface E G (field_flow_exterior_diffeomorph E X t))) 0 := by
  apply Filter.Eventually.of_forall
  intro t
  change geometricArea g (transformed_surface E G (field_flow_exterior_diffeomorph E X 0)) ≤ _
  rw [flow_area_at_zero E g G X]
  exact flow_area_is_global_minimum E g F G h X t

open scoped BigOperators
private theorem metric_christoffel_matches (g : MetricTensor)
    (hsym : ∀ z a b, g z a b = g z b a) (y : E3) (a b k : Fin 3) :
    ChristoffelCoordinate g y k a b = christoffel g y a b k := by
  unfold ChristoffelCoordinate christoffel partial3
  apply congrArg ((1 / 2 : ℝ) * ·)
  apply Finset.sum_congr rfl
  intro l hl
  have hb : (fun z => g z b l) = (fun z => g z l b) := funext (fun z => hsym z b l)
  have ha : (fun z => g z a l) = (fun z => g z l a) := funext (fun z => hsym z a l)
  rw [hb, ha]
  rfl
private theorem lowered_christoffel_formula (g : MetricTensor) (y : E3) (hg : IsUnit (g y).det)
    (hsym : ∀ z a b, g z a b = g z b a) (u v w : E3) :
    coordinateInner g y
      (∑ k : Fin 3, (∑ a : Fin 3, ∑ b : Fin 3,
        christoffel g y a b k * u a * v b) • coordinateVector 3 k) w =
      (1 / 2 : ℝ) *
        ((∑ a : Fin 3, ∑ b : Fin 3,fderiv ℝ (fun z => g z a b) y u * v a * w b) +
         (∑ a : Fin 3, ∑ b : Fin 3,fderiv ℝ (fun z => g z a b) y v * u a * w b) -
         (∑ a : Fin 3, ∑ b : Fin 3,fderiv ℝ (fun z => g z a b) y w * u a * v b)) := by
  classical
  have hLower (g : MetricTensor) (y : E3) (hg : IsUnit (g y).det)
      (hsym : ∀ a b, g y a b = g y b a) (u v w : E3) :
      coordinateInner g y
        (∑ k : Fin 3, (∑ a : Fin 3, ∑ b : Fin 3,
          christoffel g y a b k * u a * v b) • coordinateVector 3 k) w =
        (1 / 2 : ℝ) * (∑ a : Fin 3, ∑ b : Fin 3, ∑ l : Fin 3,
          (partial3 (fun z => g z l b) y a + partial3 (fun z => g z l a) y b -
            partial3 (fun z => g z a b) y l) * u a * v b * w l) := by
    classical
    have hlower (a b l : Fin 3) :
        (∑ k : Fin 3, g y l k * christoffel g y a b k) =
          (1 / 2 : ℝ) * (partial3 (fun z => g z l b) y a +
            partial3 (fun z => g z l a) y b - partial3 (fun z => g z a b) y l) := by
      let R : Fin 3 → ℝ := fun m => partial3 (fun z => g z m b) y a +
        partial3 (fun z => g z m a) y b - partial3 (fun z => g z a b) y m
      change (∑ k : Fin 3, g y l k * ((1 / 2 : ℝ) * ∑ m : Fin 3, (g y)⁻¹ k m * R m)) =
        (1 / 2 : ℝ) * R l
      calc
        _ = (1 / 2 : ℝ) * ∑ m : Fin 3, (g y * (g y)⁻¹) l m * R m := by
          simp only [Matrix.mul_apply,Fin.sum_univ_three]
          ring
        _ = _ := by
          rw [Matrix.mul_nonsing_inv _ hg]
          change (1 / 2 : ℝ) * (∑ m : Fin 3, (if l = m then 1 else 0) * R m) = _
          simp
    have hcoord (s : Fin 3 → ℝ) (k : Fin 3) :
        (∑ i : Fin 3,s i • coordinateVector 3 i) k = s k := by
      simp [coordinateVector,EuclideanSpace.single,Pi.single_apply]
    simp only [coordinateInner,hcoord]
    calc
      _ = ∑ a : Fin 3, ∑ b : Fin 3, ∑ l : Fin 3,
          (∑ k : Fin 3,g y l k * christoffel g y a b k) * u a * v b * w l := by
        simp only [Fin.sum_univ_three,hsym]
        ring
      _ = _ := by
        simp only [hlower,Fin.sum_univ_three]
        ring
  rw [hLower g y hg (hsym y)]
  have hsum (v : E3) : (∑ i : Fin 3,v i • coordinateVector 3 i) = v := by
    ext j
    simp [coordinateVector,EuclideanSpace.single,Pi.single_apply]
  have hexpand (F : E3 → ℝ) (d : E3) : fderiv ℝ F y d =
      ∑ i : Fin 3,partial3 F y i * d i := by
    conv_lhs => rw [← hsum d]
    simp only [map_sum,map_smul,smul_eq_mul,partial3]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hdsym (a i j : Fin 3) : partial3 (fun z => g z i j) y a =
      partial3 (fun z => g z j i) y a := by
    have he : (fun z => g z i j) = (fun z => g z j i) := funext (fun z => hsym z i j)
    rw [he]
  simp only [hexpand,Fin.sum_univ_three,hdsym]
  ring
private theorem gram_density_hasDerivAt
    (A : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (B : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : (A 0).PosDef) (hB : ∀ i j, HasDerivAt (fun t => A t i j) (B i j) 0) :
    HasDerivAt (fun t => Real.sqrt (A t).det)
      ((1 / 2 : ℝ) * Real.sqrt (A 0).det *
        (∑ i : Fin 2, ∑ j : Fin 2, (A 0)⁻¹ i j * B j i)) 0 := by
  have hdet : HasDerivAt (fun t => (A t).det)
      (B 0 0 * A 0 1 1 + A 0 0 0 * B 1 1 -
        (B 0 1 * A 0 1 0 + A 0 0 1 * B 1 0)) 0 := by
    convert! ((hB 0 0).mul (hB 1 1)).sub ((hB 0 1).mul (hB 1 0)) using 1
    ext t
    exact Matrix.det_fin_two (A t)
  have hs := hdet.sqrt (ne_of_gt hA.det_pos)
  convert hs using 1
  have hroot : 0 < Real.sqrt (A 0).det := Real.sqrt_pos.2 hA.det_pos
  have hsq : Real.sqrt (A 0).det ^ 2 = (A 0).det := Real.sq_sqrt hA.det_pos.le
  rw [Matrix.inv_def, Matrix.adjugate_fin_two]
  simp only [Ring.inverse_eq_inv, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.head_fin_const]
  field_simp [ne_of_gt hroot, ne_of_gt hA.det_pos]
  rw [hsq]
  ring
private def coordinateConnection (g : MetricTensor) (y u v : E3) : E3 :=
  ∑ k : Fin 3, (∑ a : Fin 3, ∑ b : Fin 3,
    ChristoffelCoordinate g y k a b * u a * v b) • coordinateVector 3 k
private theorem coordinate_metric_symmetric (g : MetricTensor)
    (hsym : ∀ z a b, g z a b = g z b a) (y u v : E3) :
    coordinateInner g y u v = coordinateInner g y v u := by
  simp only [coordinateInner, Fin.sum_univ_three, hsym]
  ring
private theorem lowered_native_connection (g : MetricTensor) (y : E3)
    (hg : IsUnit (g y).det) (hsym : ∀ z a b, g z a b = g z b a) (u v w : E3) :
    coordinateInner g y (coordinateConnection g y u v) w =
      (1 / 2 : ℝ) *
        ((∑ a : Fin 3, ∑ b : Fin 3, fderiv ℝ (fun z => g z a b) y u * v a * w b) +
         (∑ a : Fin 3, ∑ b : Fin 3, fderiv ℝ (fun z => g z a b) y v * u a * w b) -
         (∑ a : Fin 3, ∑ b : Fin 3, fderiv ℝ (fun z => g z a b) y w * u a * v b)) := by
  unfold coordinateConnection
  simp_rw [metric_christoffel_matches g hsym]
  exact lowered_christoffel_formula g y hg hsym u v w
private theorem native_metric_connection_compatibility (g : MetricTensor) (y : E3)
    (hg : IsUnit (g y).det) (hsym : ∀ z a b, g z a b = g z b a) (u v w : E3) :
    coordinateInner g y (coordinateConnection g y u v) w +
      coordinateInner g y v (coordinateConnection g y u w) =
      ∑ a : Fin 3, ∑ b : Fin 3, fderiv ℝ (fun z => g z a b) y u * v a * w b := by
  rw [coordinate_metric_symmetric g hsym y v (coordinateConnection g y u w),
    lowered_native_connection g y hg hsym,
    lowered_native_connection g y hg hsym]
  have hmdsym (d a b : E3) :
      (∑ i : Fin 3, ∑ j : Fin 3, fderiv ℝ (fun z => g z i j) y d * a i * b j) =
      ∑ i : Fin 3, ∑ j : Fin 3, fderiv ℝ (fun z => g z i j) y d * b i * a j := by
    have hd (i j : Fin 3) : fderiv ℝ (fun z => g z i j) y =
        fderiv ℝ (fun z => g z j i) y := by
      congr 1
      exact funext (fun z => hsym z i j)
    simp only [Fin.sum_univ_three, hd]
    ring
  rw [hmdsym u w v, hmdsym v u w, hmdsym w u v]
  ring
private theorem native_christoffel_symmetric (g : MetricTensor)
    (hsym : ∀ z a b, g z a b = g z b a) (y : E3) (k a b : Fin 3) :
    ChristoffelCoordinate g y k a b = ChristoffelCoordinate g y k b a := by
  unfold ChristoffelCoordinate
  have he : (fun z => g z a b) = (fun z => g z b a) := funext (fun z => hsym z a b)
  simp only [he, add_comm]
private theorem coordinate_connection_symmetric (g : MetricTensor)
    (hsym : ∀ z a b, g z a b = g z b a) (y u v : E3) :
    coordinateConnection g y u v = coordinateConnection g y v u := by
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  simp only [Fin.sum_univ_three, native_christoffel_symmetric g hsym]
  ring
private theorem coordinate_metric_add_right (g : MetricTensor) (y u v w : E3) :
    coordinateInner g y u (v + w) = coordinateInner g y u v + coordinateInner g y u w := by
  simp only [coordinateInner, PiLp.add_apply, mul_add, Finset.sum_add_distrib]
private theorem covariant_gram_density_variation (g : MetricTensor) (y x : E3)
    (hg : IsUnit (g y).det) (hsym : ∀ z a b, g z a b = g z b a)
    (A : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hA : (A 0).PosDef)
    (v W : Fin 2 → E3)
    (hD : ∀ i j, HasDerivAt (fun t => A t i j)
      ((∑ a : Fin 3, ∑ b : Fin 3, fderiv ℝ (fun z => g z a b) y x * v i a * v j b) +
        coordinateInner g y (W i) (v j) + coordinateInner g y (v i) (W j)) 0) :
    HasDerivAt (fun t => Real.sqrt (A t).det)
      (Real.sqrt (A 0).det * (∑ i : Fin 2, ∑ j : Fin 2, (A 0)⁻¹ i j *
        coordinateInner g y (W i + coordinateConnection g y (v i) x) (v j))) 0 := by
  let C : Fin 2 → E3 := fun i => W i + coordinateConnection g y (v i) x
  have he (i j : Fin 2) :
      (∑ a : Fin 3, ∑ b : Fin 3, fderiv ℝ (fun z => g z a b) y x * v i a * v j b) +
        coordinateInner g y (W i) (v j) + coordinateInner g y (v i) (W j) =
      coordinateInner g y (C i) (v j) + coordinateInner g y (v i) (C j) := by
    dsimp [C]
    rw [coordinateInner_add_left, coordinate_metric_add_right,
      coordinate_connection_symmetric g hsym y (v i) x,
      coordinate_connection_symmetric g hsym y (v j) x]
    have h := native_metric_connection_compatibility g y hg hsym x (v i) (v j)
    linarith
  have hD' : ∀ i j, HasDerivAt (fun t => A t i j)
      (coordinateInner g y (C i) (v j) + coordinateInner g y (v i) (C j)) 0 := by
    intro i j
    rw [← he i j]
    exact hD i j
  convert! gram_density_hasDerivAt A _ hA hD' using 1
  change Real.sqrt (A 0).det * (∑ i : Fin 2, ∑ j : Fin 2, (A 0)⁻¹ i j *
      coordinateInner g y (C i) (v j)) = _
  have hi (i j : Fin 2) : (A 0)⁻¹ i j = (A 0)⁻¹ j i := by
    simpa only [star_trivial] using (hA.isHermitian.inv.apply j i)
  simp only [Fin.sum_univ_two, coordinate_metric_symmetric g hsym y,
    hi 1 0]
  ring

set_option backward.isDefEq.respectTransparency false in
private theorem native_coordinate_metric_inner (h : AmbientMetric ThreeSphere)
    (p : ThreeSphere) (z u v : E3) :
    coordinateInner (MetricInChart (𝓡 3) h p) z u v =
      h.inner ((extChartAt (𝓡 3) p).symm z)
        (mfderivWithin 𝓘(ℝ, E3) (𝓡 3) (extChartAt (𝓡 3) p).symm
          (Set.range (𝓡 3)) z u)
        (mfderivWithin 𝓘(ℝ, E3) (𝓡 3) (extChartAt (𝓡 3) p).symm
          (Set.range (𝓡 3)) z v) := by
  let L : E3 →L[ℝ] TangentSpace (𝓡 3) ((extChartAt (𝓡 3) p).symm z) :=
    mfderivWithin 𝓘(ℝ, E3) (𝓡 3) (extChartAt (𝓡 3) p).symm
    (Set.range (𝓡 3)) z
  have hsum (w : E3) : (∑ i : Fin 3, w i • coordinateVector 3 i) = w := by
    ext j
    simp [coordinateVector, EuclideanSpace.single, Pi.single_apply]
  have hL (w : E3) : L w = ∑ i : Fin 3, w i • L (coordinateVector 3 i) := by
    calc
      L w = L (∑ i : Fin 3, w i • coordinateVector 3 i) := congrArg L (hsum w).symm
      _ = _ := by rw [map_sum]; simp only [map_smul]
  change coordinateInner (MetricInChart (𝓡 3) h p) z u v =
    h.inner ((extChartAt (𝓡 3) p).symm z) (L u) (L v)
  change (∑ i : Fin 3, ∑ j : Fin 3,
    h.inner ((extChartAt (𝓡 3) p).symm z) (L (coordinateVector 3 i))
      (L (coordinateVector 3 j)) * u i * v j) = _
  rw [hL u, hL v, map_sum]
  simp only [map_smul, _root_.sum_apply, _root_.smul_apply, map_sum, smul_eq_mul]
  simp only [Fin.sum_univ_three]
  ring
private theorem native_coordinate_metric_symmetric (h : AmbientMetric ThreeSphere)
    (p : ThreeSphere) :
    ∀ z i j, MetricInChart (𝓡 3) h p z i j = MetricInChart (𝓡 3) h p z j i := by
  intro z i j
  exact h.symm _ _ _
set_option backward.isDefEq.respectTransparency false in
private theorem native_chart_metric_positive (h : AmbientMetric ThreeSphere)
    (p : ThreeSphere) {z : E3} (hz : z ∈ (extChartAt (𝓡 3) p).target) :
    (MetricInChart (𝓡 3) h p z).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · apply Matrix.IsHermitian.ext
    intro i j
    simpa only [star_trivial] using (native_coordinate_metric_symmetric h p z j i)
  · intro ξ hξ
    let w : E3 := WithLp.toLp 2 ξ
    have hw : w ≠ 0 := fun he => hξ (WithLp.toLp_injective 2 he)
    let L : E3 →L[ℝ] TangentSpace (𝓡 3) ((extChartAt (𝓡 3) p).symm z) :=
      mfderivWithin 𝓘(ℝ, E3) (𝓡 3) (extChartAt (𝓡 3) p).symm (Set.range (𝓡 3)) z
    have hLi : Function.Injective L := by
      obtain ⟨d, hd⟩ := isInvertible_mfderivWithin_extChartAt_symm (I := 𝓡 3) hz
      dsimp only [L]
      rw [← hd]
      exact d.injective
    have hLp : L w ≠ 0 := fun he => hw (hLi (he.trans (map_zero L).symm))
    have hpos : 0 < coordinateInner (MetricInChart (𝓡 3) h p) z w w := by
      calc
        coordinateInner (MetricInChart (𝓡 3) h p) z w w =
            h.inner ((extChartAt (𝓡 3) p).symm z) (L w) (L w) :=
          native_coordinate_metric_inner h p z w w
        _ > 0 := h.pos _ _ hLp
    convert! hpos using 1
    simp only [coordinateInner, dotProduct, Matrix.mulVec, Fin.sum_univ_three,
      Pi.star_apply, star_trivial]
    dsimp [w]
    ring
private theorem native_chart_metric_smooth (h : AmbientMetric ThreeSphere)
    (p : ThreeSphere) :
    ∀ a b, ContDiffOn ℝ ∞ (fun z => MetricInChart (𝓡 3) h p z a b)
      (extChartAt (𝓡 3) p).target := by
  let e := extChartAt (𝓡 3) p
  have hvector (v : E3) :
      ContMDiffOn 𝓘(ℝ, E3) (𝓡 3).tangent ∞
        (fun z => Bundle.TotalSpace.mk' E3 (e.symm z)
          (mfderivWithin 𝓘(ℝ, E3) (𝓡 3) e.symm (Set.range (𝓡 3)) z v)) e.target := by
    have hconst : ContMDiff 𝓘(ℝ, E3) (𝓘(ℝ, E3).tangent) ∞
        (fun z : E3 => Bundle.TotalSpace.mk' E3 z
          ((NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm v)) := by
      apply contMDiff_vectorSpace_iff_contDiff.mpr
      change ContDiff ℝ ∞ (fun _ : E3 => v)
      exact contDiff_const
    have htm := (contMDiffOn_extChartAt_symm (I := 𝓡 3) (n := ∞) p).contMDiffOn_tangentMapWithin
      (m := ∞) (by simp) (isOpen_extChartAt_target (I := 𝓡 3) p).uniqueMDiffOn
    have hv := htm.comp (f := fun z : E3 => Bundle.TotalSpace.mk' E3 z
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm v)) hconst.contMDiffOn
      (s := e.target) (by intro z hz; exact hz)
    apply hv.congr
    intro z hz
    change Bundle.TotalSpace.mk' E3 (e.symm z)
      (mfderivWithin 𝓘(ℝ, E3) (𝓡 3) e.symm (Set.range (𝓡 3)) z v) =
      Bundle.TotalSpace.mk' E3 (e.symm z)
        (mfderivWithin 𝓘(ℝ, E3) (𝓡 3) e.symm e.target z v)
    rw [(𝓡 3).range_eq_univ, mfderivWithin_univ,
      mfderivWithin_of_mem_nhds ((isOpen_extChartAt_target (I := 𝓡 3) p).mem_nhds hz)]
  intro a b z hz
  have hh : ContMDiffWithinAt 𝓘(ℝ, E3) ((𝓡 3).prod 𝓘(ℝ)) ∞
      (fun z => Bundle.TotalSpace.mk' ℝ (E := Bundle.Trivial ThreeSphere ℝ) (e.symm z)
        (MetricInChart (𝓡 3) h p z a b)) e.target z := by
    apply ContMDiffWithinAt.clm_bundle_apply₂ (F₁ := E3) (F₂ := E3)
    · exact h.contMDiff.contMDiffAt.comp_contMDiffWithinAt z
        (contMDiffOn_extChartAt_symm (I := 𝓡 3) (n := ∞) p z hz)
    · exact hvector (coordinateVector 3 a) z hz
    · exact hvector (coordinateVector 3 b) z hz
  exact (Bundle.contMDiffWithinAt_totalSpace.mp hh).2.contDiffWithinAt

private theorem native_patch_metric_covariance (h : AmbientMetric ThreeSphere)
    (p : ThreeSphere) (f : Euc 2 → ThreeSphere) (D : Set (Euc 2)) (y u v : Euc 2)
    (hu : UniqueMDiffWithinAt 𝓘(ℝ, Euc 2) D y)
    (hf : MDifferentiableWithinAt 𝓘(ℝ, Euc 2) (𝓡 3) f D y)
    (hsrc : f y ∈ (extChartAt (𝓡 3) p).source) :
    coordinateInner (MetricInChart (𝓡 3) h p) (extChartAt (𝓡 3) p (f y))
      (fderivWithin ℝ ((extChartAt (𝓡 3) p) ∘ f) D y u)
      (fderivWithin ℝ ((extChartAt (𝓡 3) p) ∘ f) D y v) =
      h.inner (f y) (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡 3) f D y u)
        (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡 3) f D y v) := by
  let e := extChartAt (𝓡 3) p
  have hemd : MDifferentiableAt (𝓡 3) 𝓘(ℝ, Euc 3) e (f y) :=
    mdifferentiableAt_extChartAt (I := 𝓡 3) (by simpa only [extChartAt_source] using hsrc)
  have hcomp := mfderivWithin_comp y hemd.mdifferentiableWithinAt hf
    (s := D) (u := univ) (by simp) hu
  rw [mfderivWithin_univ, mfderivWithin_eq_fderivWithin] at hcomp
  have hd (w : Euc 2) :
      (mfderivWithin 𝓘(ℝ, Euc 3) (𝓡 3) e.symm (range (𝓡 3)) (e (f y)))
        (fderivWithin ℝ (e ∘ f) D y w) =
      mfderivWithin 𝓘(ℝ, Euc 2) (𝓡 3) f D y w := by
    have hc := congrArg (fun A => A w) hcomp
    change fderivWithin ℝ (e ∘ f) D y w =
      mfderiv (𝓡 3) 𝓘(ℝ, Euc 3) e (f y)
        (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡 3) f D y w) at hc
    rw [hc]
    have hi := congrArg (fun A => A
      (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡 3) f D y w))
      (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (I := 𝓡 3) hsrc)
    exact hi
  have hn := native_coordinate_metric_inner h p (e (f y))
    (fderivWithin ℝ (e ∘ f) D y u) (fderivWithin ℝ (e ∘ f) D y v)
  change _ = h.inner (e.symm (e (f y))) _ _ at hn
  rw [hd u, hd v] at hn
  convert! hn using 1
  rw [e.left_inv hsrc]

private theorem native_piece_gram_metric_covariance (G : SeifertSurfaces.OriginalEndpoints.A7.SourceGeometry E)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count) (y : Euc 2)
    (hy : y ∈ ((F.domain i).chart j).map.target) (a b : Fin 2) :
    let f := pieceSphereCoordinate E F i j
    let p := f y
    let e := extChartAt (𝓡 3) p
    coordinateInner (MetricInChart (𝓡 3) G.extension p) (e p)
      (fderivWithin ℝ (e ∘ f) ((F.domain i).chart j).map.target y (EuclideanSpace.single a 1))
      (fderivWithin ℝ (e ∘ f) ((F.domain i).chart j).map.target y (EuclideanSpace.single b 1)) =
    sectorCoordinateGram G.metric (F.map ∘ F.parametrization i) j y a b := by
  let D := ((F.domain i).chart j).map.target
  let f := sectorCoordinateMap (F.map ∘ F.parametrization i) j
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  have hud : UniqueMDiffWithinAt 𝓘(ℝ, Euc 2) D y := by
    dsimp only [D]
    rw [((F.domain i).chart j).target_eq]
    exact (SectorModel.uniqueDiffOn_domain ((F.domain i).chart j).model y
      (by simpa only [((F.domain i).chart j).target_eq] using hy)).uniqueMDiffWithinAt
  have hf : MDifferentiableWithinAt 𝓘(ℝ, Euc 2) (𝓡∂ 3) f D y :=
    (F.piece_c1 i j y hy).mdifferentiableWithinAt one_ne_zero
  have hfc : MDifferentiableWithinAt 𝓘(ℝ, Euc 2) (𝓡 3) (E.toSphere ∘ f) D y :=
    hinc.contMDiff.mdifferentiableAt (by simp) |>.comp_mdifferentiableWithinAt y hf
  have hc := native_patch_metric_covariance G.extension (E.toSphere (f y))
    (E.toSphere ∘ f) D y (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)
    hud hfc (mem_extChartAt_source (E.toSphere (f y)))
  refine hc.trans ?_
  have hd := mfderivWithin_comp y
    (hinc.contMDiff.mdifferentiableAt (by simp)).mdifferentiableWithinAt hf
    (u := univ) (by simp) hud
  rw [mfderivWithin_univ] at hd
  rw [hd]
  exact (G.metric_restriction (f y)
    (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 3) f D y (EuclideanSpace.single a 1))
    (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 3) f D y (EuclideanSpace.single b 1))).symm

set_option backward.isDefEq.respectTransparency false in
private theorem native_sector_gram_positive
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] (g : SmoothMetric M)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S M)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count) (y : Euc 2)
    (hy : y ∈ ((F.domain i).chart j).map.target) :
    (sectorCoordinateGram g (F.map ∘ F.parametrization i) j y).PosDef := by
  let f := sectorCoordinateMap (F.map ∘ F.parametrization i) j
  let L : Euc 2 →L[ℝ] TangentSpace (𝓡∂ 3) (f y) :=
    (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 3) f ((F.domain i).chart j).map.target y).comp
      (tangentSpaceCastModel 𝓘(ℝ, Euc 2) y).symm.toContinuousLinearMap
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · apply Matrix.IsHermitian.ext
    intro a b
    change g.inner (f y) (L (EuclideanSpace.single b 1)) (L (EuclideanSpace.single a 1)) =
      g.inner (f y) (L (EuclideanSpace.single a 1)) (L (EuclideanSpace.single b 1))
    exact g.symm _ _ _
  · intro ξ hξ
    let w : Euc 2 := WithLp.toLp 2 ξ
    have hw : w ≠ 0 := fun he => hξ (WithLp.toLp_injective 2 he)
    have hL : Function.Injective L :=
      (F.piece_differential_injective i j y hy).comp
        (tangentSpaceCastModel 𝓘(ℝ, Euc 2) y).symm.injective
    have hp : L w ≠ 0 := fun he => hw (hL (he.trans (map_zero L).symm))
    have hpos := g.pos (f y) (L w) hp
    have hsum : (∑ a : Fin 2, w a • EuclideanSpace.single a 1) = w := by
      ext k
      fin_cases k <;> simp [EuclideanSpace.single, Pi.single_apply]
    have hvec : L w = ∑ a : Fin 2, w a • L (EuclideanSpace.single a 1) := by
      calc
        L w = L (∑ a : Fin 2, w a • EuclideanSpace.single a 1) := congrArg L hsum.symm
        _ = _ := by rw [map_sum]; simp only [map_smul]
    rw [hvec, map_sum] at hpos
    simp only [map_smul, _root_.sum_apply, _root_.smul_apply, map_sum, smul_eq_mul] at hpos
    change 0 < star ξ ⬝ᵥ (fun a b => g.inner (f y)
      (L (EuclideanSpace.single a 1)) (L (EuclideanSpace.single b 1))) *ᵥ ξ
    convert! hpos using 1
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Pi.star_apply, star_trivial]
    dsimp only [w]
    ring

set_option backward.isDefEq.respectTransparency false in
private theorem field_coordinate_eq_pullback (X : InteriorSmoothVectorField E)
    (p : ThreeSphere) {z : Euc 3} (hz : z ∈ (extChartAt (𝓡 3) p).target) :
    fieldCoordinate E X p z =
      VectorField.mpullbackWithin 𝓘(ℝ, Euc 3) (𝓡 3)
        (extChartAt (𝓡 3) p).symm X.field (range (𝓡 3)) z := by
  have heq := ContinuousLinearMap.inverse_eq
    (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt (I := 𝓡 3) hz)
    (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := 𝓡 3) hz)
  exact congrArg (fun A => A (X.field ((extChartAt (𝓡 3) p).symm z))) heq.symm
set_option backward.isDefEq.respectTransparency false in
private theorem field_coordinate_smooth_center (X : InteriorSmoothVectorField E)
    (p : ThreeSphere) :
    ContDiffAt ℝ ∞ (fieldCoordinate E X p) (extChartAt (𝓡 3) p p) := by
  have h := VectorField.contMDiffWithinAt_mpullbackWithin_extChartAt_symm
    (I := 𝓡 3) (n := ∞) (m := ∞)
    (s := univ) (X.smooth.contMDiffAt.contMDiffWithinAt (x := p))
    (uniqueMDiffOn_univ) (mem_univ p) (by simp)
  simp only [preimage_univ, inter_univ] at h
  have hc := contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt.mp h
  have he : (extChartAt (𝓡 3) p).target ∈ 𝓝 (extChartAt (𝓡 3) p p) :=
    (isOpen_extChartAt_target (I := 𝓡 3) p).mem_nhds (mem_extChartAt_target p)
  apply (hc.contDiffAt he).congr_of_eventuallyEq
  filter_upwards [he] with z hz
  exact field_coordinate_eq_pullback E X p hz
set_option backward.isDefEq.respectTransparency false in
private theorem integral_curve_coordinate_derivative (X : InteriorSmoothVectorField E)
    (p : ThreeSphere) (γ : ℝ → ThreeSphere) (hγ : IsMIntegralCurve γ X.field)
    (t : ℝ) (hsrc : γ t ∈ (extChartAt (𝓡 3) p).source) :
    HasDerivAt ((extChartAt (𝓡 3) p) ∘ γ)
      (fieldCoordinate E X p (extChartAt (𝓡 3) p (γ t))) t := by
  let e := extChartAt (𝓡 3) p
  have hmd : MDifferentiableAt (𝓡 3) 𝓘(ℝ, Euc 3) e (γ t) :=
    mdifferentiableAt_extChartAt (I := 𝓡 3) (by simpa only [extChartAt_source] using hsrc)
  have hd := hasMFDerivAt_iff_hasFDerivAt.mp (hmd.hasMFDerivAt.comp t (hγ t))
  apply hasDerivAt_iff_hasFDerivAt.mpr
  apply hd.congr_fderiv
  apply ContinuousLinearMap.ext
  intro r
  change ℝ at r
  change (NormedSpace.fromTangentSpace (e (γ t)))
    (mfderiv (𝓡 3) 𝓘(ℝ, Euc 3) e (γ t) (r • X.field (γ t))) =
    r • fieldCoordinate E X p (e (γ t))
  rw [map_smul, map_smul]
  congr 1
  change _ = (NormedSpace.fromTangentSpace (e (e.symm (e (γ t)))))
    (mfderiv (𝓡 3) 𝓘(ℝ, Euc 3) e (e.symm (e (γ t)))
      (X.field (e.symm (e (γ t)))))
  rw [e.left_inv hsrc]

private def native_coordinate_flow (X : InteriorSmoothVectorField E) (p : ThreeSphere)
    (q : ℝ × Euc 3) : Euc 3 :=
  (extChartAt (𝓡 3) p)
    (curveAt X.field (field_complete E X) ((extChartAt (𝓡 3) p).symm q.2) q.1)
set_option backward.isDefEq.respectTransparency false in
private theorem native_coordinate_flow_smooth (X : InteriorSmoothVectorField E)
    (p : ThreeSphere) : ContDiffAt ℝ ∞ (native_coordinate_flow E X p)
      (0, extChartAt (𝓡 3) p p) := by
  let e := extChartAt (𝓡 3) p
  have hinv : ContMDiffAt 𝓘(ℝ, Euc 3) (𝓡 3) ∞ e.symm (e p) :=
    (contMDiffOn_extChartAt_symm (I := 𝓡 3) (n := ∞) p).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 3) p).mem_nhds (mem_extChartAt_target p))
  have hpair : ContMDiffAt (𝓘(ℝ).prod 𝓘(ℝ, Euc 3)) (𝓘(ℝ).prod (𝓡 3)) ∞
      (fun q : ℝ × Euc 3 => (q.1, e.symm q.2)) (0, e p) :=
    contMDiffAt_fst.prodMk (hinv.comp (0, e p) (f := Prod.snd) contMDiffAt_snd)
  have hflow := (field_flow_joint E X).contMDiffAt.comp (0, e p) hpair
  have he : ContMDiffAt (𝓡 3) 𝓘(ℝ, Euc 3) ∞ e p :=
    contMDiffAt_extChartAt (I := 𝓡 3) (n := ∞)
  have he' : ContMDiffAt (𝓡 3) 𝓘(ℝ, Euc 3) ∞ e
      (curveAt X.field (field_complete E X) (e.symm (e p)) 0) := by
    simpa only [curveAt_zero, e.left_inv (mem_extChartAt_source p)] using he
  have hc := he'.comp (0, e p) hflow
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hc
  exact hc.contDiffAt

private theorem spatial_slice_derivative (Φ : ℝ × E3 → E3) (t : ℝ) (z : E3)
    (hΦ : DifferentiableAt ℝ Φ (t,z)) :
    fderiv ℝ (fun y => Φ (t,y)) z =
      (fderiv ℝ Φ (t,z)).comp (ContinuousLinearMap.inr ℝ ℝ E3) := by
  have hi : HasFDerivAt (fun y : E3 => (t,y)) (ContinuousLinearMap.inr ℝ ℝ E3) z :=
    (hasFDerivAt_const t z).prodMk (hasFDerivAt_id z)
  exact (hΦ.hasFDerivAt.comp z hi).fderiv
private theorem temporal_slice_derivative (Φ : ℝ × E3 → E3) (t : ℝ) (z : E3)
    (hΦ : DifferentiableAt ℝ Φ (t,z)) :
    deriv (fun s => Φ (s,z)) t = fderiv ℝ Φ (t,z) (1,0) := by
  have hi : HasDerivAt (fun s : ℝ => (s,z)) (1,0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t z)
  exact (hΦ.hasFDerivAt.comp_hasDerivAt t hi).deriv
private theorem mixed_flow_jet (Φ : ℝ × E3 → E3) (z v : E3)
    (hΦ : ContDiffAt ℝ 2 Φ (0,z)) :
    HasDerivAt (fun t => fderiv ℝ (fun y => Φ (t,y)) z v)
      (fderiv ℝ (fun y => deriv (fun t => Φ (t,y)) 0) z v) 0 := by
  have hD : DifferentiableAt ℝ (fderiv ℝ Φ) (0,z) :=
    (hΦ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hdiff : ∀ᶠ q in 𝓝 (0,z), DifferentiableAt ℝ Φ q :=
    (hΦ.eventually (by norm_num)).mono (fun _ h => h.differentiableAt two_ne_zero)
  have htD : HasDerivAt (fun t : ℝ => fderiv ℝ Φ (t,z))
      (fderiv ℝ (fderiv ℝ Φ) (0,z) (1,0)) 0 :=
    hD.hasFDerivAt.comp_hasDerivAt 0
      ((hasDerivAt_id 0).prodMk (hasDerivAt_const 0 z))
  have htV := htD.clm_apply (hasDerivAt_const 0 (0,v))
  have heT : (fun t : ℝ => fderiv ℝ (fun y => Φ (t,y)) z v) =ᶠ[𝓝 0]
      (fun t : ℝ => fderiv ℝ Φ (t,z) (0,v)) := by
    filter_upwards [((continuous_id.prodMk continuous_const).continuousAt :
      ContinuousAt (fun t : ℝ => (t,z)) 0) hdiff] with t ht
    rw [spatial_slice_derivative Φ t z ht]
    rfl
  have hyD : HasFDerivAt (fun y : E3 => fderiv ℝ Φ (0,y))
      ((fderiv ℝ (fderiv ℝ Φ) (0,z)).comp (ContinuousLinearMap.inr ℝ ℝ E3)) z :=
    hD.hasFDerivAt.comp z ((hasFDerivAt_const (0 : ℝ) z).prodMk (hasFDerivAt_id z))
  have hyV := hyD.clm_apply (hasFDerivAt_const (𝕜 := ℝ) ((1,0) : ℝ × E3) z)
  have heY : (fun y : E3 => deriv (fun t => Φ (t,y)) 0) =ᶠ[𝓝 z]
      (fun y : E3 => fderiv ℝ Φ (0,y) (1,0)) := by
    filter_upwards [((continuous_const.prodMk continuous_id).continuousAt :
      ContinuousAt (fun y : E3 => ((0 : ℝ),y)) z) hdiff] with y hy
    exact temporal_slice_derivative Φ 0 y hy
  have hyEq := heY.fderiv_eq (𝕜 := ℝ)
  have hs := hΦ.isSymmSndFDerivAt (by norm_num) (1,0) (0,v)
  apply (htV.congr_of_eventuallyEq heT).congr_deriv
  rw [hyEq, hyV.fderiv]
  simpa [ContinuousLinearMap.flip_apply] using hs

set_option backward.isDefEq.respectTransparency false in
private theorem native_coordinate_flow_velocity (X : InteriorSmoothVectorField E)
    (p : ThreeSphere) {z : Euc 3} (hz : z ∈ (extChartAt (𝓡 3) p).target) :
    HasDerivAt (fun t => native_coordinate_flow E X p (t,z))
      (fieldCoordinate E X p z) 0 := by
  let e := extChartAt (𝓡 3) p
  have hγ := curveAt_integralCurve X.field (field_complete E X) (e.symm z)
  have hc := integral_curve_coordinate_derivative E X p
    (curveAt X.field (field_complete E X) (e.symm z)) hγ 0
    (by simpa only [curveAt_zero] using e.map_target hz)
  simp only [curveAt_zero] at hc
  change HasDerivAt (fun t => native_coordinate_flow E X p (t,z))
    (fieldCoordinate E X p (e (e.symm z))) 0 at hc
  rw [e.right_inv hz] at hc
  exact hc
private theorem native_coordinate_flow_tangent_velocity (X : InteriorSmoothVectorField E)
    (p : ThreeSphere) (v : Euc 3) :
    HasDerivAt (fun t => fderiv ℝ (fun z => native_coordinate_flow E X p (t,z))
      (extChartAt (𝓡 3) p p) v)
      (fderiv ℝ (fieldCoordinate E X p) (extChartAt (𝓡 3) p p) v) 0 := by
  have hm := mixed_flow_jet (native_coordinate_flow E X p)
    (extChartAt (𝓡 3) p p) v ((native_coordinate_flow_smooth E X p).of_le (by simp))
  have he : (fun z => deriv (fun t => native_coordinate_flow E X p (t,z)) 0) =ᶠ[
      𝓝 (extChartAt (𝓡 3) p p)] (fieldCoordinate E X p) := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓡 3) p).mem_nhds
      (mem_extChartAt_target p)] with z hz
    exact (native_coordinate_flow_velocity E X p hz).deriv
  simpa only [he.fderiv_eq (𝕜 := ℝ)] using hm
private theorem native_coordinate_flow_initial_differential (X : InteriorSmoothVectorField E)
    (p : ThreeSphere) :
    fderiv ℝ (fun z => native_coordinate_flow E X p (0,z))
      (extChartAt (𝓡 3) p p) = ContinuousLinearMap.id ℝ (Euc 3) := by
  have he : (fun z => native_coordinate_flow E X p (0,z)) =ᶠ[
      𝓝 (extChartAt (𝓡 3) p p)] id := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓡 3) p).mem_nhds
      (mem_extChartAt_target p)] with z hz
    change (extChartAt (𝓡 3) p)
      (curveAt X.field (field_complete E X) ((extChartAt (𝓡 3) p).symm z) 0) = z
    rw [curveAt_zero, (extChartAt (𝓡 3) p).right_inv hz]
  rw [he.fderiv_eq (𝕜 := ℝ), fderiv_id]

private theorem coordinate_inner_curve_derivative (g : MetricTensor)
    (Z V W : ℝ → E3) (x v w : E3)
    (hg : ∀ a b, DifferentiableAt ℝ (fun z => g z a b) (Z 0))
    (hZ : HasDerivAt Z x 0) (hV : HasDerivAt V v 0) (hW : HasDerivAt W w 0) :
    HasDerivAt (fun t => coordinateInner g (Z t) (V t) (W t))
      ((∑ a : Fin 3, ∑ b : Fin 3,
          fderiv ℝ (fun z => g z a b) (Z 0) x * V 0 a * W 0 b) +
        coordinateInner g (Z 0) v (W 0) + coordinateInner g (Z 0) (V 0) w) 0 := by
  have he (a b : Fin 3) : HasDerivAt (fun t => g (Z t) a b * V t a * W t b)
      ((fderiv ℝ (fun z => g z a b) (Z 0) x * V 0 a + g (Z 0) a b * v a) * W 0 b +
        (g (Z 0) a b * V 0 a) * w b) 0 := by
    have hga := (hg a b).hasFDerivAt.comp_hasDerivAt 0 hZ
    have hVa := (EuclideanSpace.proj a).hasFDerivAt.comp_hasDerivAt 0 hV
    have hWb := (EuclideanSpace.proj b).hasFDerivAt.comp_hasDerivAt 0 hW
    exact (hga.mul hVa).mul hWb
  convert! HasDerivAt.sum (u := Finset.univ) (fun a _ => HasDerivAt.sum (u := Finset.univ) (fun b _ => he a b)) using 1
  simp only [coordinateInner, Fin.sum_univ_three]
  ring


private theorem native_flow_gram_density_variation (G : A7.SourceGeometry E)
    (X : InteriorSmoothVectorField E) (p : ThreeSphere) (v : Fin 2 → Euc 3)
    (hgram : Matrix.PosDef (fun i j => coordinateInner (MetricInChart (𝓡 3) G.extension p)
      (extChartAt (𝓡 3) p p) (v i) (v j))) :
    let z := extChartAt (𝓡 3) p p
    let g := MetricInChart (𝓡 3) G.extension p
    let Φ := native_coordinate_flow E X p
    let V := fun t i => fderiv ℝ (fun w => Φ (t,w)) z (v i)
    let A : ℝ → Matrix (Fin 2) (Fin 2) ℝ :=
      fun t i j => coordinateInner g (Φ (t,z)) (V t i) (V t j)
    HasDerivAt (fun t => Real.sqrt (A t).det)
      (Real.sqrt (A 0).det * (∑ i : Fin 2, ∑ j : Fin 2, (A 0)⁻¹ i j *
        coordinateInner g z (covariantFieldCoordinate E G X p z (v i)) (v j))) 0 := by
  let z := extChartAt (𝓡 3) p p
  let g := MetricInChart (𝓡 3) G.extension p
  let Φ := native_coordinate_flow E X p
  let V := fun t i => fderiv ℝ (fun w => Φ (t,w)) z (v i)
  let A : ℝ → Matrix (Fin 2) (Fin 2) ℝ :=
    fun t i j => coordinateInner g (Φ (t,z)) (V t i) (V t j)
  change HasDerivAt (fun t => Real.sqrt (A t).det)
    (Real.sqrt (A 0).det * (∑ i : Fin 2, ∑ j : Fin 2, (A 0)⁻¹ i j *
      coordinateInner g z (covariantFieldCoordinate E G X p z (v i)) (v j))) 0
  have hZ : Φ (0,z) = z := by
    change (extChartAt (𝓡 3) p)
      (curveAt X.field (field_complete E X) ((extChartAt (𝓡 3) p).symm z) 0) = z
    rw [curveAt_zero, (extChartAt (𝓡 3) p).right_inv (mem_extChartAt_target p)]
  have hV (i : Fin 2) : V 0 i = v i := by
    dsimp only [V, Φ, z]
    rw [native_coordinate_flow_initial_differential E X p]
    rfl
  have hA : (A 0).PosDef := by
    simpa only [A, hZ, hV] using hgram
  have hgm : (g z).PosDef := native_chart_metric_positive G.extension p
    (mem_extChartAt_target p)
  have hunit : IsUnit (g z).det := isUnit_iff_ne_zero.mpr (ne_of_gt hgm.det_pos)
  have hD (i j : Fin 2) : HasDerivAt (fun t => A t i j)
      ((∑ a : Fin 3, ∑ b : Fin 3, fderiv ℝ (fun w => g w a b) z
        (fieldCoordinate E X p z) * v i a * v j b) +
        coordinateInner g z (fderiv ℝ (fieldCoordinate E X p) z (v i)) (v j) +
        coordinateInner g z (v i) (fderiv ℝ (fieldCoordinate E X p) z (v j))) 0 := by
    have hg (a b : Fin 3) : DifferentiableAt ℝ (fun w => g w a b) (Φ (0,z)) := by
      rw [hZ]
      exact ((native_chart_metric_smooth G.extension p a b).contDiffAt
        ((isOpen_extChartAt_target (I := 𝓡 3) p).mem_nhds (mem_extChartAt_target p))).differentiableAt (by simp)
    have hr := coordinate_inner_curve_derivative g (fun t => Φ (t,z))
      (fun t => V t i) (fun t => V t j)
      (fieldCoordinate E X p z)
      (fderiv ℝ (fieldCoordinate E X p) z (v i))
      (fderiv ℝ (fieldCoordinate E X p) z (v j)) hg
      (native_coordinate_flow_velocity E X p (mem_extChartAt_target p))
      (native_coordinate_flow_tangent_velocity E X p (v i))
      (native_coordinate_flow_tangent_velocity E X p (v j))
    simpa only [hZ, hV] using hr
  exact covariant_gram_density_variation g z (fieldCoordinate E X p z) hunit
    (native_coordinate_metric_symmetric G.extension p) A hA v
    (fun i => fderiv ℝ (fieldCoordinate E X p) z (v i)) hD


private theorem native_piece_flow_density_variation (G : A7.SourceGeometry E)
    (X : InteriorSmoothVectorField E) {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier) (i : Fin F.pieceCount)
    (j : Fin (F.domain i).count) (y : Euc 2)
    (hy : y ∈ ((F.domain i).chart j).map.target) :
    let f := pieceSphereCoordinate E F i j
    let p := f y
    let e := extChartAt (𝓡 3) p
    let z := e p
    let v := fun a : Fin 2 => fderivWithin ℝ (e ∘ f)
      ((F.domain i).chart j).map.target y (EuclideanSpace.single a 1)
    let g := MetricInChart (𝓡 3) G.extension p
    let Φ := native_coordinate_flow E X p
    let V := fun t a => fderiv ℝ (fun w => Φ (t,w)) z (v a)
    let A : ℝ → Matrix (Fin 2) (Fin 2) ℝ :=
      fun t a b => coordinateInner g (Φ (t,z)) (V t a) (V t b)
    HasDerivAt (fun t => Real.sqrt (A t).det)
      (pieceTangentialDivergence E G F X i j y *
        sectorCoordinateDensity G.metric (F.map ∘ F.parametrization i) j y) 0 := by
  let f := pieceSphereCoordinate E F i j
  let p := f y
  let e := extChartAt (𝓡 3) p
  let z := e p
  let v := fun a : Fin 2 => fderivWithin ℝ (e ∘ f)
    ((F.domain i).chart j).map.target y (EuclideanSpace.single a 1)
  let g := MetricInChart (𝓡 3) G.extension p
  let Φ := native_coordinate_flow E X p
  let V := fun t a => fderiv ℝ (fun w => Φ (t,w)) z (v a)
  let A : ℝ → Matrix (Fin 2) (Fin 2) ℝ :=
    fun t a b => coordinateInner g (Φ (t,z)) (V t a) (V t b)
  let H : Matrix (Fin 2) (Fin 2) ℝ := fun a b => coordinateInner g z (v a) (v b)
  have hH : H = sectorCoordinateGram G.metric (F.map ∘ F.parametrization i) j y := by
    ext a b
    exact native_piece_gram_metric_covariance E G F i j y hy a b
  have hpos : H.PosDef := by rw [hH]; exact native_sector_gram_positive G.metric F i j y hy
  have hr := native_flow_gram_density_variation E G X p v hpos
  have hZ : Φ (0,z) = z := by
    change e (curveAt X.field (field_complete E X) (e.symm z) 0) = z
    rw [curveAt_zero, e.right_inv (mem_extChartAt_target p)]
  have hV (a : Fin 2) : V 0 a = v a := by
    dsimp only [V, Φ, z, e]
    rw [native_coordinate_flow_initial_differential E X p]
    rfl
  have hA : A 0 = H := by
    ext a b
    change coordinateInner g (Φ (0,z)) (V 0 a) (V 0 b) = _
    rw [hZ, hV, hV]
  change HasDerivAt (fun t => Real.sqrt (A t).det)
    (pieceTangentialDivergence E G F X i j y *
      sectorCoordinateDensity G.metric (F.map ∘ F.parametrization i) j y) 0
  apply hr.congr_deriv
  change Real.sqrt (A 0).det * (∑ a : Fin 2, ∑ b : Fin 2, (A 0)⁻¹ a b *
    coordinateInner g z (covariantFieldCoordinate E G X p z (v a)) (v b)) = _
  rw [hA]
  change Real.sqrt H.det * pieceTangentialDivergence E G F X i j y = _
  rw [hH]
  change sectorCoordinateDensity G.metric (F.map ∘ F.parametrization i) j y *
    pieceTangentialDivergence E G F X i j y = _
  ring

private theorem native_piece_gram_in_fixed_chart (G : SeifertSurfaces.OriginalEndpoints.A7.SourceGeometry E)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count) (y : Euc 2)
    (hy : y ∈ ((F.domain i).chart j).map.target) (q : ThreeSphere)
    (hsrc : pieceSphereCoordinate E F i j y ∈ (extChartAt (𝓡 3) q).source) (a b : Fin 2) :
    let f := pieceSphereCoordinate E F i j
    let e := extChartAt (𝓡 3) q
    coordinateInner (MetricInChart (𝓡 3) G.extension q) (e (f y))
      (fderivWithin ℝ (e ∘ f) ((F.domain i).chart j).map.target y (EuclideanSpace.single a 1))
      (fderivWithin ℝ (e ∘ f) ((F.domain i).chart j).map.target y (EuclideanSpace.single b 1)) =
    sectorCoordinateGram G.metric (F.map ∘ F.parametrization i) j y a b := by
  let D := ((F.domain i).chart j).map.target
  let f := sectorCoordinateMap (F.map ∘ F.parametrization i) j
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  have hud : UniqueMDiffWithinAt 𝓘(ℝ, Euc 2) D y := by
    dsimp only [D]
    rw [((F.domain i).chart j).target_eq]
    exact (SectorModel.uniqueDiffOn_domain ((F.domain i).chart j).model y
      (by simpa only [((F.domain i).chart j).target_eq] using hy)).uniqueMDiffWithinAt
  have hf : MDifferentiableWithinAt 𝓘(ℝ, Euc 2) (𝓡∂ 3) f D y :=
    (F.piece_c1 i j y hy).mdifferentiableWithinAt one_ne_zero
  have hfc : MDifferentiableWithinAt 𝓘(ℝ, Euc 2) (𝓡 3) (E.toSphere ∘ f) D y :=
    hinc.contMDiff.mdifferentiableAt (by simp) |>.comp_mdifferentiableWithinAt y hf
  have hc := native_patch_metric_covariance G.extension q
    (E.toSphere ∘ f) D y (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)
    hud hfc hsrc
  refine hc.trans ?_
  have hd := mfderivWithin_comp y
    (hinc.contMDiff.mdifferentiableAt (by simp)).mdifferentiableWithinAt hf
    (u := univ) (by simp) hud
  rw [mfderivWithin_univ] at hd
  rw [hd]
  exact (G.metric_restriction (f y)
    (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 3) f D y (EuclideanSpace.single a 1))
    (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 3) f D y (EuclideanSpace.single b 1))).symm



private theorem native_piece_chart_differentiable (X : InteriorSmoothVectorField E)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count) (y : Euc 2)
    (hy : y ∈ ((F.domain i).chart j).map.target) :
    DifferentiableWithinAt ℝ
      ((extChartAt (𝓡 3) (pieceSphereCoordinate E F i j y)) ∘ pieceSphereCoordinate E F i j)
      ((F.domain i).chart j).map.target y := by
  let f := sectorCoordinateMap (F.map ∘ F.parametrization i) j
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  have hE : ContMDiffWithinAt 𝓘(ℝ, Euc 2) (𝓡 3) 1 (E.toSphere ∘ f)
      ((F.domain i).chart j).map.target y :=
    (hinc.contMDiff.of_le (by simp)).contMDiffAt.comp_contMDiffWithinAt y (F.piece_c1 i j y hy)
  have hchart : ContMDiffAt (𝓡 3) 𝓘(ℝ, Euc 3) 1
      (extChartAt (𝓡 3) (E.toSphere (f y))) (E.toSphere (f y)) :=
    contMDiffAt_extChartAt (I := 𝓡 3) (n := 1)
  exact (hchart.comp_contMDiffWithinAt y hE).contDiffWithinAt.differentiableWithinAt one_ne_zero
private theorem native_flow_piece_sphere_map (X : InteriorSmoothVectorField E)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count) (t : ℝ) :
    pieceSphereCoordinate E (transformed_surface E F (field_flow_exterior_diffeomorph E X t)) i j =
      (fun y => curveAt X.field (field_complete E X) (pieceSphereCoordinate E F i j y) t) := by
  rfl


private theorem native_flow_piece_chart_derivative (X : InteriorSmoothVectorField E)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count) (y : Euc 2)
    (hy : y ∈ ((F.domain i).chart j).map.target) :
    let f := pieceSphereCoordinate E F i j
    let p := f y
    let e := extChartAt (𝓡 3) p
    let z := e p
    ∀ᶠ t in 𝓝 (0 : ℝ),
      fderivWithin ℝ (e ∘ pieceSphereCoordinate E
        (transformed_surface E F (field_flow_exterior_diffeomorph E X t)) i j)
        ((F.domain i).chart j).map.target y =
      (fderiv ℝ (fun w => native_coordinate_flow E X p (t,w)) z).comp
        (fderivWithin ℝ (e ∘ f) ((F.domain i).chart j).map.target y) := by
  let D := ((F.domain i).chart j).map.target
  let f := pieceSphereCoordinate E F i j
  let p := f y
  let e := extChartAt (𝓡 3) p
  let z := e p
  have hud : UniqueDiffWithinAt ℝ D y := by
    dsimp only [D]
    rw [((F.domain i).chart j).target_eq]
    exact SectorModel.uniqueDiffOn_domain ((F.domain i).chart j).model y
      (by simpa only [((F.domain i).chart j).target_eq] using hy)
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  have hf : MDifferentiableWithinAt 𝓘(ℝ, Euc 2) (𝓡 3) f D y :=
    (hinc.contMDiff.mdifferentiableAt (by simp)).comp_mdifferentiableWithinAt y
      ((F.piece_c1 i j y hy).mdifferentiableWithinAt one_ne_zero)
  have hs : ∀ᶠ q in 𝓝[D] y, f q ∈ e.source :=
    hf.continuousWithinAt ((isOpen_extChartAt_source p).mem_nhds (mem_extChartAt_source p))
  have hdiff : ∀ᶠ q in 𝓝 ((0 : ℝ),z), DifferentiableAt ℝ (native_coordinate_flow E X p) q :=
    (((native_coordinate_flow_smooth E X p).of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually
      (by simp)).mono (fun _ h => h.differentiableAt one_ne_zero)
  have ht := ((continuous_id.prodMk continuous_const).continuousAt :
      ContinuousAt (fun t : ℝ => (t,z)) 0) hdiff
  filter_upwards [ht] with t ht
  have hd : DifferentiableAt ℝ (fun w => native_coordinate_flow E X p (t,w)) z :=
    ht.comp z ((differentiableAt_const t).prodMk differentiableAt_id)
  have he : (e ∘ pieceSphereCoordinate E
        (transformed_surface E F (field_flow_exterior_diffeomorph E X t)) i j) =ᶠ[𝓝[D] y]
      (fun q => native_coordinate_flow E X p (t, e (f q))) := by
    filter_upwards [hs] with q hq
    change e (curveAt X.field (field_complete E X) (f q) t) =
      e (curveAt X.field (field_complete E X) (e.symm (e (f q))) t)
    rw [e.left_inv hq]
  rw [he.fderivWithin_eq_of_mem (𝕜 := ℝ) hy]
  exact fderiv_comp_fderivWithin y hd (native_piece_chart_differentiable E X F i j y hy) hud


private theorem native_sector_density_first_variation (G : A7.SourceGeometry E)
    (X : InteriorSmoothVectorField E) {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier) (i : Fin F.pieceCount)
    (j : Fin (F.domain i).count) (y : Euc 2)
    (hy : y ∈ ((F.domain i).chart j).map.target) :
    HasDerivAt (fun t => sectorCoordinateDensity G.metric
      ((transformed_surface E F (field_flow_exterior_diffeomorph E X t)).map ∘
        (transformed_surface E F (field_flow_exterior_diffeomorph E X t)).parametrization i) j y)
      (pieceTangentialDivergence E G F X i j y *
        sectorCoordinateDensity G.metric (F.map ∘ F.parametrization i) j y) 0 := by
  let f := pieceSphereCoordinate E F i j
  let p := f y
  let e := extChartAt (𝓡 3) p
  let z := e p
  let v := fun a : Fin 2 => fderivWithin ℝ (e ∘ f)
    ((F.domain i).chart j).map.target y (EuclideanSpace.single a 1)
  let g := MetricInChart (𝓡 3) G.extension p
  let Φ := native_coordinate_flow E X p
  let V := fun t a => fderiv ℝ (fun w => Φ (t,w)) z (v a)
  let A : ℝ → Matrix (Fin 2) (Fin 2) ℝ :=
    fun t a b => coordinateInner g (Φ (t,z)) (V t a) (V t b)
  let Ft := fun t => transformed_surface E F (field_flow_exterior_diffeomorph E X t)
  have hγ : ContinuousAt (fun t => curveAt X.field (field_complete E X) p t) 0 :=
    (curveAt_integralCurve (I := 𝓡 3) X.field (field_complete E X) p).continuous.continuousAt
  have hs : ∀ᶠ t in 𝓝 (0 : ℝ), pieceSphereCoordinate E (Ft t) i j y ∈ e.source := by
    have he := hγ (by simpa only [curveAt_zero] using
      ((isOpen_extChartAt_source (I := 𝓡 3) p).mem_nhds (mem_extChartAt_source (I := 𝓡 3) p)))
    exact he
  have hd := native_flow_piece_chart_derivative E X F i j y hy
  have heq : (fun t => sectorCoordinateDensity G.metric
      ((Ft t).map ∘ (Ft t).parametrization i) j y) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => Real.sqrt (A t).det) := by
    filter_upwards [hs, hd] with t ht hdt
    have hm : A t = sectorCoordinateGram G.metric ((Ft t).map ∘ (Ft t).parametrization i) j y := by
      ext a b
      have hc := native_piece_gram_in_fixed_chart E G (Ft t) i j y hy p ht a b
      have hz : Φ (t,z) = e (pieceSphereCoordinate E (Ft t) i j y) := by
        change e (curveAt X.field (field_complete E X) (e.symm (e p)) t) =
          e (curveAt X.field (field_complete E X) p t)
        rw [e.left_inv (mem_extChartAt_source p)]
      change fderivWithin ℝ (e ∘ pieceSphereCoordinate E (Ft t) i j)
        ((F.domain i).chart j).map.target y =
        (fderiv ℝ (fun w => Φ (t,w)) z).comp
          (fderivWithin ℝ (e ∘ f) ((F.domain i).chart j).map.target y) at hdt
      have hva : fderivWithin ℝ (e ∘ pieceSphereCoordinate E (Ft t) i j)
          ((F.domain i).chart j).map.target y (EuclideanSpace.single a 1) = V t a :=
        congrArg (fun L => L (EuclideanSpace.single a 1)) hdt
      have hvb : fderivWithin ℝ (e ∘ pieceSphereCoordinate E (Ft t) i j)
          ((F.domain i).chart j).map.target y (EuclideanSpace.single b 1) = V t b :=
        congrArg (fun L => L (EuclideanSpace.single b 1)) hdt
      change coordinateInner g (e (pieceSphereCoordinate E (Ft t) i j y))
        (fderivWithin ℝ (e ∘ pieceSphereCoordinate E (Ft t) i j)
          ((F.domain i).chart j).map.target y (EuclideanSpace.single a 1))
        (fderivWithin ℝ (e ∘ pieceSphereCoordinate E (Ft t) i j)
          ((F.domain i).chart j).map.target y (EuclideanSpace.single b 1)) = _ at hc
      change coordinateInner g (Φ (t,z)) (V t a) (V t b) = _
      rw [hz]
      exact (hva ▸ hvb ▸ hc)
    exact congrArg (fun H : Matrix (Fin 2) (Fin 2) ℝ => Real.sqrt H.det) hm.symm
  exact (native_piece_flow_density_variation E G X F i j y hy).congr_of_eventuallyEq heq


open B1Bridges in
private theorem native_sector_cell_density_integrable (G : A7.SourceGeometry E)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (α : SectorCellIndex F) :
    IntegrableOn (sectorCoordinateDensity G.metric (F.map ∘ F.parametrization α.1)
      (sectorCellChart F α))
      (((F.domain α.1).chart (sectorCellChart F α)).map '' sectorCellSet F α) := by
  classical
  let c := ((F.domain α.1).chart (sectorCellChart F α)).map
  let clean := sectorCellSet F α ∩ (F.domain α.1).interior ∩
    (F.parametrization α.1) ⁻¹' F.seam.carrierᶜ
  have hr := same_image_mixed_integrability_and_row_assembly G.metric F F
    (Homeomorph.refl S) (by intro x; rfl) rfl
  have hm := same_image_mixed_refinement_metadata F F
    (Homeomorph.refl S) (by intro x; rfl) rfl
  have hu : (⋃ β : SectorCellIndex F,
      c '' mixedSectorCell F F (Homeomorph.refl S) α β) = c '' clean := by
    rw [← image_iUnion]
    exact congrArg (c '' ·) (hm.2.2.1 α)
  have hi : IntegrableOn
      (sectorCoordinateDensity G.metric (F.map ∘ F.parametrization α.1) (sectorCellChart F α))
      (c '' clean) := by
    rw [← hu]
    exact integrableOn_finite_iUnion.mpr (fun β => (hr.1 α β).1)
  have hn := own_sector_exclusions_separately_null F α.1 (sectorCellChart F α)
  have hsub : c '' clean ⊆ c '' sectorCellSet F α := image_mono
    (fun q hq => hq.1.1)
  have hnull : volume (c '' sectorCellSet F α \ c '' clean) = 0 := by
    apply measure_mono_null (t :=
      c '' ((F.domain α.1).boundary ∩ c.source) ∪
        c '' ((F.parametrization α.1) ⁻¹' F.seam.carrier ∩ c.source))
    · rintro z ⟨⟨q, hq, rfl⟩, hnot⟩
      have hsrc : q ∈ c.source := (canonicalSectorPartition (F.domain α.1)).subordinate α.2 hq
      by_cases hqi : q ∈ (F.domain α.1).interior
      · by_cases hqs : F.parametrization α.1 q ∈ F.seam.carrier
        · exact Or.inr ⟨q, ⟨hqs,hsrc⟩,rfl⟩
        · exact False.elim (hnot ⟨q,⟨⟨hq,hqi⟩,hqs⟩,rfl⟩)
      · exact Or.inl ⟨q,⟨by simpa only [CompactSectorPiece.interior,mem_compl_iff,not_not] using hqi,hsrc⟩,rfl⟩
    · exact measure_union_null hn.1 hn.2.1
  have he : (c '' sectorCellSet F α) =ᵐ[volume] (c '' clean) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with z hz
    exact propext ⟨fun h => by by_contra hc; exact hz ⟨h,hc⟩,fun h => hsub h⟩
  exact (integrableOn_congr_set_ae he).mpr hi


open B1Bridges in
private theorem native_flow_sector_cell_density_integrable (G : A7.SourceGeometry E)
    (X : InteriorSmoothVectorField E) {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier) (α : SectorCellIndex F) (t : ℝ) :
    IntegrableOn (sectorCoordinateDensity G.metric
      ((transformed_surface E F (field_flow_exterior_diffeomorph E X t)).map ∘
        (transformed_surface E F (field_flow_exterior_diffeomorph E X t)).parametrization α.1)
      (sectorCellChart F α))
      (((F.domain α.1).chart (sectorCellChart F α)).map '' sectorCellSet F α) := by
  exact native_sector_cell_density_integrable E G
    (transformed_surface E F (field_flow_exterior_diffeomorph E X t)) α
open B1Bridges in
private theorem native_sector_cell_coordinates_measurable
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (α : SectorCellIndex F) :
    MeasurableSet (((F.domain α.1).chart (sectorCellChart F α)).map '' sectorCellSet F α) := by
  letI : MetricSpace (F.domain α.1) := TopologicalSpace.metrizableSpaceMetric (F.domain α.1)
  letI : BorelSpace (F.domain α.1) := ⟨rfl⟩
  let c := ((F.domain α.1).chart (sectorCellChart F α)).map
  have hs : MeasurableSet (sectorCellSet F α) := (canonicalSectorPartition (F.domain α.1)).measurable α.2
  have hsub : sectorCellSet F α ⊆ c.source := (canonicalSectorPartition (F.domain α.1)).subordinate α.2
  exact hs.image_of_continuousOn_injOn (c.continuousOn.mono hsub) (c.injOn.mono hsub)


set_option backward.isDefEq.respectTransparency false in
private theorem native_coordinate_flow_smooth_at (X : InteriorSmoothVectorField E)
    (p : ThreeSphere) (t : ℝ) (z : Euc 3)
    (hz : z ∈ (extChartAt (𝓡 3) p).target)
    (hsrc : curveAt X.field (field_complete E X) ((extChartAt (𝓡 3) p).symm z) t ∈
      (extChartAt (𝓡 3) p).source) :
    ContDiffAt ℝ ∞ (native_coordinate_flow E X p) (t,z) := by
  let e := extChartAt (𝓡 3) p
  have hinv : ContMDiffAt 𝓘(ℝ, Euc 3) (𝓡 3) ∞ e.symm z :=
    (contMDiffOn_extChartAt_symm (I := 𝓡 3) (n := ∞) p).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 3) p).mem_nhds hz)
  have hpair : ContMDiffAt (𝓘(ℝ).prod 𝓘(ℝ, Euc 3)) (𝓘(ℝ).prod (𝓡 3)) ∞
      (fun q : ℝ × Euc 3 => (q.1, e.symm q.2)) (t,z) :=
    contMDiffAt_fst.prodMk (hinv.comp (t,z) (f := Prod.snd) contMDiffAt_snd)
  have hflow := (field_flow_joint E X).contMDiffAt.comp (t,z) hpair
  have he : ContMDiffAt (𝓡 3) 𝓘(ℝ, Euc 3) ∞ e
      (curveAt X.field (field_complete E X) (e.symm z) t) :=
    contMDiffAt_extChartAt' (I := 𝓡 3) (n := ∞)
      (by convert! hsrc using 1; rw [extChartAt_source])
  have hc := he.comp (t,z) hflow
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hc
  exact hc.contDiffAt


private def native_flow_jet_gram (G : A7.SourceGeometry E)
    (X : InteriorSmoothVectorField E) (p : ThreeSphere)
    (q : (ℝ × Euc 3) × (Fin 2 → Euc 3)) : Matrix (Fin 2) (Fin 2) ℝ :=
  let Φ := native_coordinate_flow E X p
  let v := fun a => fderiv ℝ Φ q.1 (0,q.2 a)
  fun a b => coordinateInner (MetricInChart (𝓡 3) G.extension p) (Φ q.1) (v a) (v b)
set_option maxHeartbeats 400000 in
private theorem native_flow_jet_density_smooth (G : A7.SourceGeometry E)
    (X : InteriorSmoothVectorField E) (p : ThreeSphere)
    (q : (ℝ × Euc 3) × (Fin 2 → Euc 3))
    (hz : q.1.2 ∈ (extChartAt (𝓡 3) p).target)
    (hsrc : curveAt X.field (field_complete E X) ((extChartAt (𝓡 3) p).symm q.1.2) q.1.1 ∈
      (extChartAt (𝓡 3) p).source)
    (hpos : (native_flow_jet_gram E G X p q).PosDef) :
    ContDiffAt ℝ ∞ (fun r => Real.sqrt (native_flow_jet_gram E G X p r).det) q := by
  let Φ := native_coordinate_flow E X p
  let e := extChartAt (𝓡 3) p
  have hΦ : ContDiffAt ℝ ∞ Φ q.1 := native_coordinate_flow_smooth_at E X p q.1.1 q.1.2 hz hsrc
  have hD : ContDiffAt ℝ ∞ (fun r : (ℝ × Euc 3) × (Fin 2 → Euc 3) =>
      fderiv ℝ Φ r.1) q :=
    (hΦ.fderiv_right (m := ∞) (by simp)).comp q contDiffAt_fst
  have hZ : ContDiffAt ℝ ∞ (fun r : (ℝ × Euc 3) × (Fin 2 → Euc 3) => Φ r.1) q :=
    hΦ.comp q contDiffAt_fst
  have ht : Φ q.1 ∈ e.target := e.map_source hsrc
  have hv (a : Fin 2) : ContDiffAt ℝ ∞
      (fun r : (ℝ × Euc 3) × (Fin 2 → Euc 3) => fderiv ℝ Φ r.1 (0,r.2 a)) q := by
    apply hD.clm_apply
    exact contDiffAt_const.prodMk ((contDiffAt_apply ℝ (Euc 3) a q.2).comp q contDiffAt_snd)
  have hm (a b : Fin 2) : ContDiffAt ℝ ∞ (fun r => native_flow_jet_gram E G X p r a b) q := by
    change ContDiffAt ℝ ∞ (fun r : (ℝ × Euc 3) × (Fin 2 → Euc 3) =>
      ∑ k : Fin 3, ∑ l : Fin 3,
        MetricInChart (𝓡 3) G.extension p (Φ r.1) k l *
          (fderiv ℝ Φ r.1 (0,r.2 a)) k * (fderiv ℝ Φ r.1 (0,r.2 b)) l) q
    apply ContDiffAt.sum
    intro k hk
    apply ContDiffAt.sum
    intro l hl
    have hga : ContDiffAt ℝ ∞
        (fun w : Euc 3 => MetricInChart (𝓡 3) G.extension p w k l) (Φ q.1) :=
      (native_chart_metric_smooth G.extension p k l).contDiffAt
        ((isOpen_extChartAt_target (I := 𝓡 3) p).mem_nhds ht)
    have hg : ContDiffAt ℝ ∞ (fun r : (ℝ × Euc 3) × (Fin 2 → Euc 3) =>
        MetricInChart (𝓡 3) G.extension p (Φ r.1) k l) q := by
      convert! hga.comp q hZ using 1
    exact (hg.mul ((EuclideanSpace.proj k).contDiff.comp_contDiffAt q (hv a))).mul
      ((EuclideanSpace.proj l).contDiff.comp_contDiffAt q (hv b))
  have hdet : ContDiffAt ℝ ∞ (fun r => (native_flow_jet_gram E G X p r).det) q := by
    simpa only [Matrix.det_fin_two] using ((hm 0 0).mul (hm 1 1)).sub ((hm 0 1).mul (hm 1 0))
  exact hdet.sqrt (ne_of_gt hpos.det_pos)


private theorem native_flow_jet_density_time_derivative_smooth (G : A7.SourceGeometry E)
    (X : InteriorSmoothVectorField E) (p : ThreeSphere)
    (q : (ℝ × Euc 3) × (Fin 2 → Euc 3))
    (hz : q.1.2 ∈ (extChartAt (𝓡 3) p).target)
    (hsrc : curveAt X.field (field_complete E X) ((extChartAt (𝓡 3) p).symm q.1.2) q.1.1 ∈
      (extChartAt (𝓡 3) p).source)
    (hpos : (native_flow_jet_gram E G X p q).PosDef) :
    ContDiffAt ℝ ∞ (fun r => fderiv ℝ
      (fun r => Real.sqrt (native_flow_jet_gram E G X p r).det) r
        (((1 : ℝ), (0 : Euc 3)), (0 : Fin 2 → Euc 3))) q := by
  exact ((native_flow_jet_density_smooth E G X p q hz hsrc hpos).fderiv_right
    (m := ∞) (by simp)).clm_apply contDiffAt_const
set_option backward.isDefEq.respectTransparency false in
private theorem native_piece_jet_continuous_in_chart
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count) (p : ThreeSphere)
    (y : Euc 2) (hy : y ∈ ((F.domain i).chart j).map.target)
    (hsrc : pieceSphereCoordinate E F i j y ∈ (extChartAt (𝓡 3) p).source) :
    ContinuousWithinAt (fun w =>
      (((extChartAt (𝓡 3) p) ∘ pieceSphereCoordinate E F i j) w,
       fun a : Fin 2 => fderivWithin ℝ
         ((extChartAt (𝓡 3) p) ∘ pieceSphereCoordinate E F i j)
           ((F.domain i).chart j).map.target w (EuclideanSpace.single a 1)))
      ((F.domain i).chart j).map.target y := by
  let f := sectorCoordinateMap (F.map ∘ F.parametrization i) j
  let D := ((F.domain i).chart j).map.target
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  have hE : ContMDiffWithinAt 𝓘(ℝ, Euc 2) (𝓡 3) 1 (E.toSphere ∘ f) D y :=
    (hinc.contMDiff.of_le (by simp)).contMDiffAt.comp_contMDiffWithinAt y (F.piece_c1 i j y hy)
  have he : ContMDiffAt (𝓡 3) 𝓘(ℝ, Euc 3) 1 (extChartAt (𝓡 3) p) (E.toSphere (f y)) :=
    contMDiffAt_extChartAt' (I := 𝓡 3) (n := 1)
      (by convert! hsrc using 1; rw [extChartAt_source])
  have hc : ContDiffWithinAt ℝ 1
      ((extChartAt (𝓡 3) p) ∘ pieceSphereCoordinate E F i j) D y :=
    (he.comp_contMDiffWithinAt y hE).contDiffWithinAt
  have hud : UniqueDiffOn ℝ D := by
    dsimp only [D]
    rw [((F.domain i).chart j).target_eq]
    exact SectorModel.uniqueDiffOn_domain ((F.domain i).chart j).model
  have hd := hc.continuousWithinAt_fderivWithin hud one_ne_zero hy
  exact hc.continuousWithinAt.prodMk (continuousWithinAt_pi.mpr
    (fun a => hd.clm_apply continuousWithinAt_const))

private theorem native_coordinate_flow_initial_differential_at
    (X : InteriorSmoothVectorField E) (p : ThreeSphere) (z : Euc 3)
    (hz : z ∈ (extChartAt (𝓡 3) p).target) :
    fderiv ℝ (fun w => native_coordinate_flow E X p (0,w)) z =
      ContinuousLinearMap.id ℝ (Euc 3) := by
  have he : (fun w => native_coordinate_flow E X p (0,w)) =ᶠ[𝓝 z] id := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓡 3) p).mem_nhds hz] with w hw
    change (extChartAt (𝓡 3) p)
      (curveAt X.field (field_complete E X) ((extChartAt (𝓡 3) p).symm w) 0) = w
    rw [curveAt_zero, (extChartAt (𝓡 3) p).right_inv hw]
  rw [he.fderiv_eq (𝕜 := ℝ), fderiv_id]

private def native_piece_coordinate_jet {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier) (i : Fin F.pieceCount)
    (j : Fin (F.domain i).count) (p : ThreeSphere) (y : Euc 2) :
    Euc 3 × (Fin 2 → Euc 3) :=
  (((extChartAt (𝓡 3) p) ∘ pieceSphereCoordinate E F i j) y,
   fun a : Fin 2 => fderivWithin ℝ
     ((extChartAt (𝓡 3) p) ∘ pieceSphereCoordinate E F i j)
       ((F.domain i).chart j).map.target y (EuclideanSpace.single a 1))

set_option backward.isDefEq.respectTransparency false in
private theorem native_piece_jet_gram_at_zero (G : A7.SourceGeometry E)
    (X : InteriorSmoothVectorField E) {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier) (i : Fin F.pieceCount)
    (j : Fin (F.domain i).count) (p : ThreeSphere) (y : Euc 2)
    (hy : y ∈ ((F.domain i).chart j).map.target)
    (hsrc : pieceSphereCoordinate E F i j y ∈ (extChartAt (𝓡 3) p).source) :
    native_flow_jet_gram E G X p
      ((0, (native_piece_coordinate_jet E F i j p y).1),
        (native_piece_coordinate_jet E F i j p y).2) =
      sectorCoordinateGram G.metric (F.map ∘ F.parametrization i) j y := by
  let e := extChartAt (𝓡 3) p
  let J := native_piece_coordinate_jet E F i j p y
  have hz : J.1 ∈ e.target := e.map_source hsrc
  have hs : curveAt X.field (field_complete E X) (e.symm J.1) 0 ∈ e.source := by
    rw [curveAt_zero]
    exact e.map_target hz
  have hdiff := (native_coordinate_flow_smooth_at E X p 0 J.1 hz hs).differentiableAt
    (by simp)
  have hi := native_coordinate_flow_initial_differential_at E X p J.1 hz
  have hzero : native_coordinate_flow E X p (0,J.1) = J.1 := by
    change e (curveAt X.field (field_complete E X) (e.symm J.1) 0) = J.1
    rw [curveAt_zero, e.right_inv hz]
  have hv (a : Fin 2) : fderiv ℝ (native_coordinate_flow E X p) (0,J.1)
      (0,J.2 a) = J.2 a := by
    have h := congrArg (fun L : Euc 3 →L[ℝ] Euc 3 => L (J.2 a))
      (spatial_slice_derivative (native_coordinate_flow E X p) 0 J.1 hdiff)
    rw [hi] at h
    exact h.symm
  ext a b
  change coordinateInner (MetricInChart (𝓡 3) G.extension p)
    (native_coordinate_flow E X p (0,J.1))
    (fderiv ℝ (native_coordinate_flow E X p) (0,J.1) (0,J.2 a))
    (fderiv ℝ (native_coordinate_flow E X p) (0,J.1) (0,J.2 b)) = _
  rw [hv, hv, hzero]
  exact native_piece_gram_in_fixed_chart E G F i j y hy p hsrc a b

set_option backward.isDefEq.respectTransparency false in
private theorem native_piece_jet_time_derivative_continuous
    (G : A7.SourceGeometry E) (X : InteriorSmoothVectorField E)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count) (p : ThreeSphere)
    (y : Euc 2) (hy : y ∈ ((F.domain i).chart j).map.target)
    (hsrc : pieceSphereCoordinate E F i j y ∈ (extChartAt (𝓡 3) p).source) :
    ContinuousWithinAt (fun q : ℝ × Euc 2 => fderiv ℝ
      (fun r => Real.sqrt (native_flow_jet_gram E G X p r).det)
      ((q.1, (native_piece_coordinate_jet E F i j p q.2).1),
        (native_piece_coordinate_jet E F i j p q.2).2)
      (((1 : ℝ), (0 : Euc 3)), (0 : Fin 2 → Euc 3)))
      (Set.univ ×ˢ ((F.domain i).chart j).map.target) (0,y) := by
  let J := native_piece_coordinate_jet E F i j p
  let e := extChartAt (𝓡 3) p
  let D := ((F.domain i).chart j).map.target
  have hz : (J y).1 ∈ e.target := e.map_source hsrc
  have hs : curveAt X.field (field_complete E X) (e.symm (J y).1) 0 ∈ e.source := by
    rw [curveAt_zero]
    exact e.map_target hz
  have hpos : (native_flow_jet_gram E G X p ((0,(J y).1),(J y).2)).PosDef := by
    rw [native_piece_jet_gram_at_zero E G X F i j p y hy hsrc]
    exact native_sector_gram_positive G.metric F i j y hy
  have hJ : ContinuousWithinAt J D y :=
    native_piece_jet_continuous_in_chart E F i j p y hy hsrc
  have hJ' : ContinuousWithinAt (fun q : ℝ × Euc 2 => J q.2)
      (univ ×ˢ D) (0,y) := by
    simpa only [Function.comp_def] using hJ.comp
      (continuousWithinAt_snd (s := univ ×ˢ D) (p := (0,y))) mapsTo_snd_prod
  have hmap : ContinuousWithinAt (fun q : ℝ × Euc 2 => ((q.1,(J q.2).1),(J q.2).2))
      (univ ×ˢ D) (0,y) :=
    (continuousWithinAt_fst.prodMk hJ'.fst).prodMk hJ'.snd
  have hcont : ContinuousAt (fun r : (ℝ × Euc 3) × (Fin 2 → Euc 3) =>
      fderiv ℝ (fun r => Real.sqrt (native_flow_jet_gram E G X p r).det) r
        (((1 : ℝ), (0 : Euc 3)), (0 : Fin 2 → Euc 3)))
      ((0,(J y).1),(J y).2) :=
    (native_flow_jet_density_time_derivative_smooth E G X p
      ((0,(J y).1),(J y).2) hz hs hpos).continuousAt
  simpa only [Function.comp_def] using hcont.comp_continuousWithinAt
    (f := fun q : ℝ × Euc 2 => ((q.1,(J q.2).1),(J q.2).2)) hmap


set_option backward.isDefEq.respectTransparency false in
private theorem native_sector_density_continuous
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] (g : SmoothMetric M)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S M)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count) :
    ContinuousOn (sectorCoordinateDensity g (F.map ∘ F.parametrization i) j)
      ((F.domain i).chart j).map.target := by
  open Bundle in
  let D := ((F.domain i).chart j).map.target
  let H := sectorCoordinateMap (F.map ∘ F.parametrization i) j
  have hud : UniqueMDiffOn 𝓘(ℝ, Euc 2) D := by
    intro y hy
    dsimp only [D]
    rw [((F.domain i).chart j).target_eq]
    exact (SectorModel.uniqueDiffOn_domain ((F.domain i).chart j).model y
      (by simpa only [D, ((F.domain i).chart j).target_eq] using hy)).uniqueMDiffWithinAt
  have ht := (F.piece_c1 i j).continuousOn_tangentMapWithin (by simp) hud
  have hv (a : Fin 2) : ContinuousOn (fun y =>
      (⟨H y, mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 3) H D y
        ((tangentSpaceCastModel 𝓘(ℝ, Euc 2) y).symm (EuclideanSpace.single a 1))⟩ :
          TangentBundle (𝓡∂ 3) M)) D :=
    ht.comp ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, Euc 2)).symm.continuous.comp
      (continuous_id.prodMk continuous_const)).continuousOn (fun y hy => hy)
  letI : RiemannianBundle (fun x : M => TangentSpace (𝓡∂ 3) x) := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle (Euc 3) (fun x : M => TangentSpace (𝓡∂ 3) x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  have hgram (a b : Fin 2) : ContinuousOn (fun y =>
      sectorCoordinateGram g (F.map ∘ F.parametrization i) j y a b) D := by
    convert! (hv a).inner_bundle (hv b) using 1
  exact ContinuousOn.sqrt (continuous_id.matrix_det.comp_continuousOn
    (continuousOn_pi.mpr (fun a => continuousOn_pi.mpr (fun b => hgram a b))))

set_option backward.isDefEq.respectTransparency false in
private theorem native_piece_chart_smooth_in_chart
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count) (p : ThreeSphere)
    (y : Euc 2) (hy : y ∈ ((F.domain i).chart j).map.target)
    (hsrc : pieceSphereCoordinate E F i j y ∈ (extChartAt (𝓡 3) p).source) :
    ContDiffWithinAt ℝ 1 ((extChartAt (𝓡 3) p) ∘ pieceSphereCoordinate E F i j)
      ((F.domain i).chart j).map.target y := by
  let f := sectorCoordinateMap (F.map ∘ F.parametrization i) j
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  have hE : ContMDiffWithinAt 𝓘(ℝ, Euc 2) (𝓡 3) 1 (E.toSphere ∘ f)
      ((F.domain i).chart j).map.target y :=
    (hinc.contMDiff.of_le (by simp)).contMDiffAt.comp_contMDiffWithinAt y (F.piece_c1 i j y hy)
  have he : ContMDiffAt (𝓡 3) 𝓘(ℝ, Euc 3) 1 (extChartAt (𝓡 3) p) (E.toSphere (f y)) :=
    contMDiffAt_extChartAt' (I := 𝓡 3) (n := 1)
      (by convert! hsrc using 1; rw [extChartAt_source])
  exact (he.comp_contMDiffWithinAt y hE).contDiffWithinAt

set_option backward.isDefEq.respectTransparency false in
private theorem native_piece_jet_gram_at_time (G : A7.SourceGeometry E)
    (X : InteriorSmoothVectorField E) {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier) (i : Fin F.pieceCount)
    (j : Fin (F.domain i).count) (p : ThreeSphere) (y : Euc 2) (t : ℝ)
    (hy : y ∈ ((F.domain i).chart j).map.target)
    (hsrc : pieceSphereCoordinate E F i j y ∈ (extChartAt (𝓡 3) p).source)
    (hflow : curveAt X.field (field_complete E X) (pieceSphereCoordinate E F i j y) t ∈
      (extChartAt (𝓡 3) p).source) :
    native_flow_jet_gram E G X p
      ((t, (native_piece_coordinate_jet E F i j p y).1),
        (native_piece_coordinate_jet E F i j p y).2) =
      sectorCoordinateGram G.metric
        ((transformed_surface E F (field_flow_exterior_diffeomorph E X t)).map ∘
          (transformed_surface E F (field_flow_exterior_diffeomorph E X t)).parametrization i) j y := by
  let D := ((F.domain i).chart j).map.target
  let f := pieceSphereCoordinate E F i j
  let e := extChartAt (𝓡 3) p
  let J := native_piece_coordinate_jet E F i j p y
  let Ft := transformed_surface E F (field_flow_exterior_diffeomorph E X t)
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  have hf : MDifferentiableWithinAt 𝓘(ℝ, Euc 2) (𝓡 3) f D y :=
    (hinc.contMDiff.mdifferentiableAt (by simp)).comp_mdifferentiableWithinAt y
      ((F.piece_c1 i j y hy).mdifferentiableWithinAt one_ne_zero)
  have hs : ∀ᶠ w in 𝓝[D] y, f w ∈ e.source :=
    hf.continuousWithinAt ((isOpen_extChartAt_source p).mem_nhds hsrc)
  have hz : J.1 ∈ e.target := e.map_source hsrc
  have heinv : e.symm J.1 = f y := e.left_inv hsrc
  have hflow' : curveAt X.field (field_complete E X) (e.symm J.1) t ∈ e.source := by
    rw [heinv]; exact hflow
  have hdiff := (native_coordinate_flow_smooth_at E X p t J.1 hz hflow').differentiableAt
    (by simp)
  have hd : DifferentiableAt ℝ (fun w => native_coordinate_flow E X p (t,w)) J.1 :=
    hdiff.comp J.1 ((differentiableAt_const t).prodMk differentiableAt_id)
  have heq : (e ∘ pieceSphereCoordinate E Ft i j) =ᶠ[𝓝[D] y]
      (fun w => native_coordinate_flow E X p (t,e (f w))) := by
    filter_upwards [hs] with w hw
    change e (curveAt X.field (field_complete E X) (f w) t) =
      e (curveAt X.field (field_complete E X) (e.symm (e (f w))) t)
    rw [e.left_inv hw]
  have hud : UniqueDiffWithinAt ℝ D y := by
    dsimp only [D]
    rw [((F.domain i).chart j).target_eq]
    exact SectorModel.uniqueDiffOn_domain ((F.domain i).chart j).model y
      (by simpa only [D, ((F.domain i).chart j).target_eq] using hy)
  have hder : fderivWithin ℝ (e ∘ pieceSphereCoordinate E Ft i j) D y =
      (fderiv ℝ (fun w => native_coordinate_flow E X p (t,w)) J.1).comp
        (fderivWithin ℝ (e ∘ f) D y) := by
    rw [heq.fderivWithin_eq_of_mem (𝕜 := ℝ) hy]
    exact fderiv_comp_fderivWithin y
      (f := e ∘ f) (g := fun w => native_coordinate_flow E X p (t,w)) hd
      ((native_piece_chart_smooth_in_chart E F i j p y hy hsrc).differentiableWithinAt
        one_ne_zero) hud
  have hzero : native_coordinate_flow E X p (t,J.1) =
      e (pieceSphereCoordinate E Ft i j y) := by
    change e (curveAt X.field (field_complete E X) (e.symm J.1) t) =
      e (curveAt X.field (field_complete E X) (f y) t)
    rw [heinv]
  have hv (a : Fin 2) : fderivWithin ℝ (e ∘ pieceSphereCoordinate E Ft i j) D y
      (EuclideanSpace.single a 1) =
      fderiv ℝ (native_coordinate_flow E X p) (t,J.1) (0,J.2 a) := by
    have h := congrArg (fun L : Euc 2 →L[ℝ] Euc 3 => L (EuclideanSpace.single a 1)) hder
    rw [spatial_slice_derivative (native_coordinate_flow E X p) t J.1 hdiff] at h
    exact h
  ext a b
  have hc := native_piece_gram_in_fixed_chart E G Ft i j y hy p hflow a b
  change coordinateInner (MetricInChart (𝓡 3) G.extension p)
    (e (pieceSphereCoordinate E Ft i j y))
    (fderivWithin ℝ (e ∘ pieceSphereCoordinate E Ft i j) D y (EuclideanSpace.single a 1))
    (fderivWithin ℝ (e ∘ pieceSphereCoordinate E Ft i j) D y (EuclideanSpace.single b 1)) = _ at hc
  change coordinateInner (MetricInChart (𝓡 3) G.extension p)
    (native_coordinate_flow E X p (t,J.1))
    (fderiv ℝ (native_coordinate_flow E X p) (t,J.1) (0,J.2 a))
    (fderiv ℝ (native_coordinate_flow E X p) (t,J.1) (0,J.2 b)) = _
  rw [hzero]
  exact (hv a ▸ hv b ▸ hc)


set_option backward.isDefEq.respectTransparency false in
private theorem native_sector_density_hasDerivAt_in_chart (G : A7.SourceGeometry E)
    (X : InteriorSmoothVectorField E) {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier) (i : Fin F.pieceCount)
    (j : Fin (F.domain i).count) (p : ThreeSphere) (y : Euc 2) (t : ℝ)
    (hy : y ∈ ((F.domain i).chart j).map.target)
    (hsrc : pieceSphereCoordinate E F i j y ∈ (extChartAt (𝓡 3) p).source)
    (hflow : curveAt X.field (field_complete E X) (pieceSphereCoordinate E F i j y) t ∈
      (extChartAt (𝓡 3) p).source) :
    HasDerivAt (fun τ => sectorCoordinateDensity G.metric
      ((transformed_surface E F (field_flow_exterior_diffeomorph E X τ)).map ∘
        (transformed_surface E F (field_flow_exterior_diffeomorph E X τ)).parametrization i) j y)
      (fderiv ℝ (fun r => Real.sqrt (native_flow_jet_gram E G X p r).det)
        ((t, (native_piece_coordinate_jet E F i j p y).1),
          (native_piece_coordinate_jet E F i j p y).2)
        (((1 : ℝ), (0 : Euc 3)), (0 : Fin 2 → Euc 3))) t := by
  let f := pieceSphereCoordinate E F i j
  let e := extChartAt (𝓡 3) p
  let J := native_piece_coordinate_jet E F i j p y
  let Ft := fun τ => transformed_surface E F (field_flow_exterior_diffeomorph E X τ)
  have hz : J.1 ∈ e.target := e.map_source hsrc
  have heinv : e.symm J.1 = f y := e.left_inv hsrc
  have hflow' : curveAt X.field (field_complete E X) (e.symm J.1) t ∈ e.source := by
    rw [heinv]; exact hflow
  have hpos : (native_flow_jet_gram E G X p ((t,J.1),J.2)).PosDef := by
    rw [native_piece_jet_gram_at_time E G X F i j p y t hy hsrc hflow]
    exact native_sector_gram_positive G.metric (Ft t) i j y hy
  have hd := (native_flow_jet_density_smooth E G X p ((t,J.1),J.2)
    hz hflow' hpos).differentiableAt (by simp)
  set_option backward.isDefEq.respectTransparency true in
  have hm : HasDerivAt (fun τ : ℝ => ((τ,J.1),J.2))
      ((((1 : ℝ), (0 : Euc 3)), (0 : Fin 2 → Euc 3))) t :=
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t J.1)).prodMk (hasDerivAt_const t J.2)
  have hr := hd.hasFDerivAt.comp_hasDerivAt t
    (f := fun τ : ℝ => ((τ,J.1),J.2)) hm
  have hs : ∀ᶠ τ in 𝓝 t, curveAt X.field (field_complete E X) (f y) τ ∈ e.source :=
    (curveAt_integralCurve X.field (field_complete E X) (f y)).continuous.continuousAt
      ((isOpen_extChartAt_source p).mem_nhds hflow)
  have heq : (fun τ => sectorCoordinateDensity G.metric
      ((Ft τ).map ∘ (Ft τ).parametrization i) j y) =ᶠ[𝓝 t]
      (fun τ => Real.sqrt (native_flow_jet_gram E G X p ((τ,J.1),J.2)).det) := by
    filter_upwards [hs] with τ hτ
    exact congrArg (fun H : Matrix (Fin 2) (Fin 2) ℝ => Real.sqrt H.det)
      (native_piece_jet_gram_at_time E G X F i j p y τ hy hsrc hτ).symm
  exact hr.congr_of_eventuallyEq heq

set_option backward.isDefEq.respectTransparency false in
private theorem native_sector_density_time_derivative_continuous
    (G : A7.SourceGeometry E) (X : InteriorSmoothVectorField E)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count)
    (y : Euc 2) (hy : y ∈ ((F.domain i).chart j).map.target) :
    ContinuousWithinAt (fun q : ℝ × Euc 2 => deriv (fun t => sectorCoordinateDensity G.metric
      ((transformed_surface E F (field_flow_exterior_diffeomorph E X t)).map ∘
        (transformed_surface E F (field_flow_exterior_diffeomorph E X t)).parametrization i) j q.2) q.1)
      (univ ×ˢ ((F.domain i).chart j).map.target) (0,y) := by
  let f := pieceSphereCoordinate E F i j
  let p := f y
  let e := extChartAt (𝓡 3) p
  let D := ((F.domain i).chart j).map.target
  let Ft := fun t => transformed_surface E F (field_flow_exterior_diffeomorph E X t)
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  have hf : ContinuousWithinAt f D y :=
    ((hinc.contMDiff.of_le (by simp)).contMDiffAt.comp_contMDiffWithinAt y
      (F.piece_c1 i j y hy)).continuousWithinAt
  have hf' : ContinuousWithinAt (fun q : ℝ × Euc 2 => f q.2) (univ ×ˢ D) (0,y) := by
    simpa only [Function.comp_def] using hf.comp
      (continuousWithinAt_snd (s := univ ×ˢ D) (p := (0,y))) mapsTo_snd_prod
  have hflow : ContinuousWithinAt (fun q : ℝ × Euc 2 =>
      curveAt X.field (field_complete E X) (f q.2) q.1) (univ ×ˢ D) (0,y) := by
    simpa only [Function.comp_def] using
      (field_flow_joint E X).continuous.continuousAt.comp_continuousWithinAt
        (f := fun q : ℝ × Euc 2 => (q.1,f q.2)) (continuousWithinAt_fst.prodMk hf')
  have hs : ∀ᶠ q : ℝ × Euc 2 in 𝓝[univ ×ˢ D] (0,y), f q.2 ∈ e.source :=
    hf' ((isOpen_extChartAt_source p).mem_nhds (mem_extChartAt_source p))
  have hfs : ∀ᶠ q : ℝ × Euc 2 in 𝓝[univ ×ˢ D] (0,y),
      curveAt X.field (field_complete E X) (f q.2) q.1 ∈ e.source :=
    hflow (by simpa only [curveAt_zero] using
      ((isOpen_extChartAt_source p).mem_nhds (mem_extChartAt_source p)))
  have heq : (fun q : ℝ × Euc 2 => deriv (fun t => sectorCoordinateDensity G.metric
      ((Ft t).map ∘ (Ft t).parametrization i) j q.2) q.1) =ᶠ[𝓝[univ ×ˢ D] (0,y)]
      (fun q : ℝ × Euc 2 => fderiv ℝ
        (fun r => Real.sqrt (native_flow_jet_gram E G X p r).det)
        ((q.1, (native_piece_coordinate_jet E F i j p q.2).1),
          (native_piece_coordinate_jet E F i j p q.2).2)
        (((1 : ℝ), (0 : Euc 3)), (0 : Fin 2 → Euc 3))) := by
    filter_upwards [hs, hfs, self_mem_nhdsWithin] with q hq hqf hqD
    exact (native_sector_density_hasDerivAt_in_chart E G X F i j p q.2 q.1 hqD.2 hq hqf).deriv
  have hc := native_piece_jet_time_derivative_continuous E G X F i j p y hy
    (mem_extChartAt_source p)
  exact hc.congr_of_eventuallyEq_of_mem heq ⟨mem_univ _, hy⟩


private theorem compact_time_uniform_bound {Y : Type*} [TopologicalSpace Y]
    (K : Set Y) (hK : IsCompact K) (R : ℝ × Y → ℝ)
    (hR : ∀ y ∈ K, ContinuousWithinAt R (univ ×ˢ K) (0,y)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t in 𝓝 (0 : ℝ), ∀ y ∈ K, ‖R (t,y)‖ ≤ C := by
  have hc : ContinuousOn (fun y => R (0,y)) K := by
    intro y hy
    exact (hR y hy).comp
      (continuousWithinAt_const.prodMk continuousWithinAt_id)
      (by intro z hz; exact ⟨mem_univ _, hz⟩)
  obtain ⟨b, hb⟩ := hK.bddAbove_image hc.norm
  let C := max b 0 + 1
  have hC : 0 < C := by dsimp [C]; linarith [le_max_right b 0]
  have hlt (y : Y) (hy : y ∈ K) : ‖R (0,y)‖ < C := by
    have h := hb (mem_image_of_mem (fun y => ‖R (0,y)‖) hy)
    dsimp [C]
    simp only [Real.norm_eq_abs] at h ⊢
    linarith [le_max_left b 0]
  have hm : {q : ℝ × Y | ‖R q‖ < C} ∈ 𝓝ˢ[univ ×ˢ K] ({0} ×ˢ K) := by
    apply (isCompact_singleton.prod hK).mem_nhdsSet_inf_of_forall
    rintro ⟨t,y⟩ ⟨ht,hy⟩
    have ht' : t = 0 := mem_singleton_iff.mp ht
    subst t
    exact (hR y hy).norm.eventually_lt_const (hlt y hy)
  obtain ⟨U, hU, hsub⟩ := generalized_tube_lemma_left isCompact_singleton hK hm
  refine ⟨C, hC, ?_⟩
  have hU' : U ∈ 𝓝 (0 : ℝ) := by
    simpa only [nhdsSetWithin_singleton, nhdsWithin_univ] using hU
  filter_upwards [hU'] with t ht
  intro y hy
  exact le_of_lt (hsub ⟨ht,hy⟩)



set_option backward.isDefEq.respectTransparency false in
private theorem native_sector_density_relative_time_derivative_bound
    (G : A7.SourceGeometry E) (X : InteriorSmoothVectorField E)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count)
    (K₀ : Set (Euc 2)) (hK : IsCompact K₀)
    (hKD : K₀ ⊆ ((F.domain i).chart j).map.target) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t in 𝓝 (0 : ℝ), ∀ y ∈ K₀,
      ‖deriv (fun τ => sectorCoordinateDensity G.metric
        ((transformed_surface E F (field_flow_exterior_diffeomorph E X τ)).map ∘
          (transformed_surface E F (field_flow_exterior_diffeomorph E X τ)).parametrization i) j y) t‖ ≤
        C * sectorCoordinateDensity G.metric (F.map ∘ F.parametrization i) j y := by
  let D := ((F.domain i).chart j).map.target
  let ρ := sectorCoordinateDensity G.metric (F.map ∘ F.parametrization i) j
  let Ft := fun t => transformed_surface E F (field_flow_exterior_diffeomorph E X t)
  let R : ℝ × Euc 2 → ℝ := fun q =>
    deriv (fun t => sectorCoordinateDensity G.metric ((Ft t).map ∘ (Ft t).parametrization i)
      j q.2) q.1 / ρ q.2
  have hρpos (y : Euc 2) (hy : y ∈ D) : 0 < ρ y :=
    Real.sqrt_pos.mpr (native_sector_gram_positive G.metric F i j y hy).det_pos
  have hR : ∀ y ∈ K₀, ContinuousWithinAt R (univ ×ˢ K₀) (0,y) := by
    intro y hy
    have hc := native_sector_density_time_derivative_continuous E G X F i j y (hKD hy)
    have hρ : ContinuousWithinAt (fun q : ℝ × Euc 2 => ρ q.2) (univ ×ˢ D) (0,y) := by
      simpa only [ρ, Function.comp_def] using
        (native_sector_density_continuous G.metric F i j y (hKD hy)).comp
          (continuousWithinAt_snd (s := univ ×ˢ D) (p := (0,y))) mapsTo_snd_prod
    exact (hc.div hρ (ne_of_gt (hρpos y (hKD hy)))).mono
      (prod_mono (Subset.refl _) hKD)
  obtain ⟨C, hC, hb⟩ := compact_time_uniform_bound K₀ hK R hR
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb] with t ht
  intro y hy
  have hr : |deriv (fun τ => sectorCoordinateDensity G.metric
      ((Ft τ).map ∘ (Ft τ).parametrization i) j y) t| / ρ y ≤ C := by
    simpa only [R, norm_div, Real.norm_eq_abs, abs_of_pos (hρpos y (hKD hy))] using ht y hy
  simpa only [Real.norm_eq_abs] using (div_le_iff₀ (hρpos y (hKD hy))).mp hr


set_option backward.isDefEq.respectTransparency false in
private theorem native_sector_density_chart_covariance
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] (g : SmoothMetric M)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S M)
    (i : Fin F.pieceCount) (j l : Fin (F.domain i).count) (y : Euc 2)
    (hy : y ∈ interior ((F.domain i).chart j).map.target)
    (hsrc : ((F.domain i).chart j).map.symm y ∈ ((F.domain i).chart l).map.source) :
    sectorCoordinateDensity g (F.map ∘ F.parametrization i) j y =
      |(fderiv ℝ (((F.domain i).chart l).map ∘ ((F.domain i).chart j).map.symm) y).det| *
        sectorCoordinateDensity g (F.map ∘ F.parametrization i) l
          (((F.domain i).chart l).map (((F.domain i).chart j).map.symm y)) := by
  open Bundle in
  let a := ((F.domain i).chart j).map
  let B := ((F.domain i).chart l).map
  let t := B ∘ a.symm
  let D := interior a.target ∩ a.symm ⁻¹' B.source
  have hyD : y ∈ D := ⟨hy, hsrc⟩
  have hopen : IsOpen D :=
    (a.symm.continuousOn.mono interior_subset).isOpen_inter_preimage
      isOpen_interior ((F.domain i).chart l).source_open
  have hsmoothT : ContDiffOn ℝ ∞ t D := (F.domain i).transition_smooth_interior j l
  have hmaps : MapsTo t D (interior B.target) := by
    intro z hz
    rw [← AreaCertificates.sector_chart_piece_interior (F.domain i) l]
    refine ⟨a.symm z, ⟨?_, hz.2⟩, rfl⟩
    exact (AreaCertificates.sector_chart_inverse_interior (F.domain i) j hz.1).1
  let fA := sectorCoordinateMap (F.map ∘ F.parametrization i) j
  let fB := sectorCoordinateMap (F.map ∘ F.parametrization i) l
  have hmatch : ∀ z ∈ D, fB (t z) = fA z := by
    intro z hz
    change F.map (F.parametrization i (B.symm (B (a.symm z)))) = _
    rw [B.left_inv hz.2]
    rfl
  have heq : fA =ᶠ[𝓝 y] fB ∘ t := by
    filter_upwards [hopen.mem_nhds hyD] with z hz
    exact (hmatch z hz).symm
  have hiy : y ∈ interior a.target := hyD.1
  have hty : t y ∈ interior B.target := hmaps hyD
  have hdB : MDifferentiableAt 𝓘(ℝ, Euc 2) (𝓡∂ 3) fB (t y) :=
    ((F.piece_smooth_interior i l).mdifferentiableOn (by simp) _ hty).mdifferentiableAt
      (isOpen_interior.mem_nhds hty)
  have hdtAt : MDifferentiableAt 𝓘(ℝ, Euc 2) 𝓘(ℝ, Euc 2) t y :=
    (hsmoothT.contDiffAt (hopen.mem_nhds hyD)).differentiableAt (by simp)
      |>.mdifferentiableAt
  have hder : ∀ w : Euc 2, @Eq (Euc 3)
      (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 3) fA a.target y w)
      (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 3) fB B.target (t y) (fderiv ℝ t y w)) := by
    intro w
    rw [mfderivWithin_of_mem_nhds
      (Filter.mem_of_superset (isOpen_interior.mem_nhds hiy) interior_subset),
      mfderivWithin_of_mem_nhds
      (Filter.mem_of_superset (isOpen_interior.mem_nhds hty) interior_subset)]
    have hd := congrArg (fun L : Euc 2 →L[ℝ] Euc 3 => L w)
      (heq.mfderiv_eq (I := 𝓘(ℝ, Euc 2)) (I' := 𝓡∂ 3))
    rw [mfderiv_comp y hdB hdtAt, mfderiv_eq_fderiv] at hd
    exact hd
  letI : RiemannianBundle (fun x : M => TangentSpace (𝓡∂ 3) x) := ⟨g.toRiemannianMetric⟩
  let dA := (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 3) fA a.target y).toLinearMap.comp
    (tangentSpaceCastModel 𝓘(ℝ, Euc 2) y).symm.toLinearMap
  let dB := (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 3) fB B.target (t y)).toLinearMap.comp
    (tangentSpaceCastModel 𝓘(ℝ, Euc 2) (t y)).symm.toLinearMap
  have density {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
      (d : Euc 2 →ₗ[ℝ] V) :
      Real.sqrt (Matrix.gram ℝ (fun z : Fin 2 => d (EuclideanSpace.single z 1))).det =
        (d.normDet : ℝ) := by
    have hd := d.normDet_sq_eq_det_gram (EuclideanSpace.basisFun (Fin 2) ℝ)
    simp only [EuclideanSpace.basisFun_apply] at hd
    rw [← hd]
    exact Real.sqrt_sq d.normDet_nonneg
  change Real.sqrt (Matrix.gram ℝ (fun z : Fin 2 => dA (EuclideanSpace.single z 1))).det =
    |(fderiv ℝ t y).det| *
    Real.sqrt (Matrix.gram ℝ (fun z : Fin 2 => dB (EuclideanSpace.single z 1))).det
  rw [density dA, density dB]
  have factor : ∀ (x z : M) (hp : x = z)
      (dA : Euc 2 →ₗ[ℝ] TangentSpace (𝓡∂ 3) z)
      (dB : Euc 2 →ₗ[ℝ] TangentSpace (𝓡∂ 3) x)
      (L : Euc 2 →ₗ[ℝ] Euc 2),
      (∀ w, @Eq (Euc 3) (dA w) (dB (L w))) →
      (dA.normDet : ℝ) = |L.det| * (dB.normDet : ℝ) := by
    intro x z hp
    cases hp
    intro dA dB L hd
    have he : dA = dB.comp L := by
      ext w
      exact hd w
    rw [he, LinearMap.normDet_comp_of_finrank_eq L dB rfl,
      LinearMap.normDet_eq_abs_det]
    exact mul_comm _ _
  exact factor _ _ (hmatch y hyD) dA dB (fderiv ℝ t y).toLinearMap hder


set_option backward.isDefEq.respectTransparency false in
private theorem native_flow_piece_maps_add (X : InteriorSmoothVectorField E)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (s t : ℝ) :
    let Fs := transformed_surface E F (field_flow_exterior_diffeomorph E X s)
    let Fst := transformed_surface E Fs (field_flow_exterior_diffeomorph E X t)
    let Fsum := transformed_surface E F (field_flow_exterior_diffeomorph E X (s+t))
    Fst.map ∘ Fst.parametrization i = Fsum.map ∘ Fsum.parametrization i := by
  funext x
  apply Subtype.ext
  change curveAt X.field (field_complete E X)
      (curveAt X.field (field_complete E X) (E.toSphere (F.map (F.parametrization i x))) s) t =
    curveAt X.field (field_complete E X) (E.toSphere (F.map (F.parametrization i x))) (s+t)
  exact (curveAt_add X.field (X.smooth.of_le (by simp)) (field_complete E X) _ s t).symm

set_option backward.isDefEq.respectTransparency false in
private theorem native_sector_density_differentiable_alltime
    (G : A7.SourceGeometry E) (X : InteriorSmoothVectorField E)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count)
    (y : Euc 2) (hy : y ∈ ((F.domain i).chart j).map.target) (t : ℝ) :
    DifferentiableAt ℝ (fun τ => sectorCoordinateDensity G.metric
      ((transformed_surface E F (field_flow_exterior_diffeomorph E X τ)).map ∘
        (transformed_surface E F (field_flow_exterior_diffeomorph E X τ)).parametrization i) j y) t := by
  let Ft := transformed_surface E F (field_flow_exterior_diffeomorph E X t)
  let H : ℝ → ℝ := fun r => sectorCoordinateDensity G.metric
    ((transformed_surface E Ft (field_flow_exterior_diffeomorph E X r)).map ∘
      (transformed_surface E Ft (field_flow_exterior_diffeomorph E X r)).parametrization i) j y
  have hd : DifferentiableAt ℝ H (t-t) := by
    simpa only [sub_self] using
      (native_sector_density_first_variation E G X Ft i j y hy).differentiableAt
  have heq : (fun τ => sectorCoordinateDensity G.metric
      ((transformed_surface E F (field_flow_exterior_diffeomorph E X τ)).map ∘
        (transformed_surface E F (field_flow_exterior_diffeomorph E X τ)).parametrization i) j y) =
      (fun τ => H (τ-t)) := by
    funext τ
    have hm := native_flow_piece_maps_add E X F i t (τ-t)
    have ht : t + (τ-t) = τ := by ring
    rw [ht] at hm
    exact congrArg (fun h => sectorCoordinateDensity G.metric h j y) hm.symm
  rw [heq]
  simpa only [Function.comp_def] using hd.comp t
    (f := fun τ : ℝ => τ-t) (differentiableAt_id.sub_const t)


set_option backward.isDefEq.respectTransparency false in
private theorem native_whole_piece_density_relative_derivative_bound
    (G : A7.SourceGeometry E) (X : InteriorSmoothVectorField E)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t in 𝓝 (0 : ℝ), ∀ j : Fin (F.domain i).count,
      ∀ y ∈ interior ((F.domain i).chart j).map.target,
        ‖deriv (fun τ => sectorCoordinateDensity G.metric
          ((transformed_surface E F (field_flow_exterior_diffeomorph E X τ)).map ∘
            (transformed_surface E F (field_flow_exterior_diffeomorph E X τ)).parametrization i) j y) t‖ ≤
          C * sectorCoordinateDensity G.metric (F.map ∘ F.parametrization i) j y := by
  classical
  obtain ⟨n,Q,b,p,hemb,hsource,hcover,hsmooth,hrank,hinterior⟩ :=
    SeifertSurfaces.OriginalEndpoints.sector_corner_chart_cover_exists (F.domain i)
  let K₀ := fun k : Fin n => Set.range (((F.domain i).chart (b k)).map ∘ p k)
  have hK (k : Fin n) : IsCompact (K₀ k) := isCompact_range (hsmooth k).continuous
  have hKD (k : Fin n) : K₀ k ⊆ ((F.domain i).chart (b k)).map.target := by
    rintro _ ⟨x,rfl⟩
    exact ((F.domain i).chart (b k)).map.map_source (hsource k (mem_univ x))
  have hb (k : Fin n) := native_sector_density_relative_time_derivative_bound E G X F
    i (b k) (K₀ k) (hK k) (hKD k)
  choose C hC hB using hb
  let B := 1 + ∑ k : Fin n, C k
  have hBpos : 0 < B := by
    have hsum : 0 ≤ ∑ k : Fin n, C k := Finset.sum_nonneg (fun k _ => (hC k).le)
    dsimp [B]
    linarith
  have hCB (k : Fin n) : C k ≤ B := by
    have h := Finset.single_le_sum (fun l _ => (hC l).le) (Finset.mem_univ k)
    dsimp [B]
    linarith
  have htime : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ k : Fin n, ∀ y ∈ K₀ k,
      ‖deriv (fun τ => sectorCoordinateDensity G.metric
        ((transformed_surface E F (field_flow_exterior_diffeomorph E X τ)).map ∘
          (transformed_surface E F (field_flow_exterior_diffeomorph E X τ)).parametrization i)
          (b k) y) t‖ ≤ C k * sectorCoordinateDensity G.metric
            (F.map ∘ F.parametrization i) (b k) y := Filter.eventually_all.mpr hB
  refine ⟨B,hBpos,?_⟩
  filter_upwards [htime] with t ht
  intro j y hy
  let a := ((F.domain i).chart j).map
  have hx : a.symm y ∈ ⋃ k, Set.range (p k) := by rw [hcover]; trivial
  obtain ⟨k,hk⟩ := mem_iUnion.mp hx
  obtain ⟨x,hx⟩ := hk
  let c := ((F.domain i).chart (b k)).map
  let z := c (a.symm y)
  let L := |(fderiv ℝ (c ∘ a.symm) y).det|
  have hsrc : a.symm y ∈ c.source := hx ▸ hsource k (mem_univ x)
  have hz : z ∈ K₀ k := ⟨x, congrArg c hx⟩
  let Ft := fun τ => transformed_surface E F (field_flow_exterior_diffeomorph E X τ)
  have heq : (fun τ => sectorCoordinateDensity G.metric
      ((Ft τ).map ∘ (Ft τ).parametrization i) j y) =
      (fun τ => L * sectorCoordinateDensity G.metric
        ((Ft τ).map ∘ (Ft τ).parametrization i) (b k) z) := by
    funext τ
    exact native_sector_density_chart_covariance G.metric (Ft τ) i j (b k) y hy hsrc
  have hd : deriv (fun τ => sectorCoordinateDensity G.metric
      ((Ft τ).map ∘ (Ft τ).parametrization i) j y) t =
      L * deriv (fun τ => sectorCoordinateDensity G.metric
        ((Ft τ).map ∘ (Ft τ).parametrization i) (b k) z) t := by
    rw [heq,deriv_const_mul_field]
  have hzero := native_sector_density_chart_covariance G.metric F i j (b k) y hy hsrc
  have hL : 0 ≤ L := abs_nonneg _
  calc
    ‖deriv (fun τ => sectorCoordinateDensity G.metric
        ((Ft τ).map ∘ (Ft τ).parametrization i) j y) t‖ =
        L * ‖deriv (fun τ => sectorCoordinateDensity G.metric
          ((Ft τ).map ∘ (Ft τ).parametrization i) (b k) z) t‖ := by
      rw [hd,norm_mul,Real.norm_eq_abs,abs_of_nonneg hL]
    _ ≤ L * (C k * sectorCoordinateDensity G.metric
        (F.map ∘ F.parametrization i) (b k) z) := mul_le_mul_of_nonneg_left (ht k z hz) hL
    _ = C k * sectorCoordinateDensity G.metric (F.map ∘ F.parametrization i) j y := by
      rw [hzero]
      ring
    _ ≤ B * sectorCoordinateDensity G.metric (F.map ∘ F.parametrization i) j y :=
      mul_le_mul_of_nonneg_right (hCB k) (Real.sqrt_nonneg _)


open B1Bridges in
private theorem native_sector_cell_ae_interior
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (α : SectorCellIndex F) :
    ∀ᵐ y ∂volume.restrict
      (((F.domain α.1).chart (sectorCellChart F α)).map '' sectorCellSet F α),
        y ∈ interior ((F.domain α.1).chart (sectorCellChart F α)).map.target := by
  let c := ((F.domain α.1).chart (sectorCellChart F α)).map
  let A := c '' sectorCellSet F α
  have hnull : volume (A \ interior c.target) = 0 := by
    apply measure_mono_null (t := c '' ((F.domain α.1).boundary ∩ c.source))
    · rintro z ⟨⟨q,hq,rfl⟩,hnot⟩
      have hsrc : q ∈ c.source := (canonicalSectorPartition (F.domain α.1)).subordinate α.2 hq
      have hboundary : q ∈ (F.domain α.1).boundary := by
        by_contra hn
        have hi : q ∈ (F.domain α.1).interior := hn
        apply hnot
        rw [← AreaCertificates.sector_chart_piece_interior (F.domain α.1) (sectorCellChart F α)]
        exact ⟨q,⟨hi,hsrc⟩,rfl⟩
      exact ⟨q,⟨hboundary,hsrc⟩,rfl⟩
    · exact (own_sector_exclusions_separately_null F α.1 (sectorCellChart F α)).1
  have ha := measure_eq_zero_iff_ae_notMem.mp hnull
  rw [ae_restrict_iff' (native_sector_cell_coordinates_measurable E F α)]
  filter_upwards [ha] with y hy hA
  by_contra hn
  exact hy ⟨hA,hn⟩

open B1Bridges in
set_option backward.isDefEq.respectTransparency false in
private theorem native_sector_cell_integral_first_variation
    (G : A7.SourceGeometry E) (X : InteriorSmoothVectorField E)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (α : SectorCellIndex F) :
    HasDerivAt (fun t => ∫ y in
      ((F.domain α.1).chart (sectorCellChart F α)).map '' sectorCellSet F α,
        sectorCoordinateDensity G.metric
          ((transformed_surface E F (field_flow_exterior_diffeomorph E X t)).map ∘
            (transformed_surface E F (field_flow_exterior_diffeomorph E X t)).parametrization α.1)
            (sectorCellChart F α) y)
      (∫ y in ((F.domain α.1).chart (sectorCellChart F α)).map '' sectorCellSet F α,
        pieceTangentialDivergence E G F X α.1 (sectorCellChart F α) y *
          sectorCoordinateDensity G.metric (F.map ∘ F.parametrization α.1)
            (sectorCellChart F α) y) 0 := by
  let j := sectorCellChart F α
  let c := ((F.domain α.1).chart j).map
  let A := c '' sectorCellSet F α
  let D := c.target
  let Ft := fun t => transformed_surface E F (field_flow_exterior_diffeomorph E X t)
  let ρ : ℝ → Euc 2 → ℝ := fun t =>
    sectorCoordinateDensity G.metric ((Ft t).map ∘ (Ft t).parametrization α.1) j
  let ρ₀ := sectorCoordinateDensity G.metric (F.map ∘ F.parametrization α.1) j
  have hA : MeasurableSet A := native_sector_cell_coordinates_measurable E F α
  have hAD : A ⊆ D := by
    rintro _ ⟨q,hq,rfl⟩
    exact c.map_source ((canonicalSectorPartition (F.domain α.1)).subordinate α.2 hq)
  have hae : ∀ᵐ y ∂volume.restrict A, y ∈ interior D := native_sector_cell_ae_interior E F α
  obtain ⟨C,hC,hB⟩ := native_whole_piece_density_relative_derivative_bound E G X F α.1
  let U := {t : ℝ | ∀ k : Fin (F.domain α.1).count,
    ∀ y ∈ interior ((F.domain α.1).chart k).map.target,
      ‖deriv (fun τ => sectorCoordinateDensity G.metric
        ((Ft τ).map ∘ (Ft τ).parametrization α.1) k y) t‖ ≤
        C * sectorCoordinateDensity G.metric (F.map ∘ F.parametrization α.1) k y}
  have hU : U ∈ 𝓝 (0 : ℝ) := hB
  have hmeas : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (ρ t) (volume.restrict A) :=
    Filter.Eventually.of_forall (fun t =>
      (native_flow_sector_cell_density_integrable E G X F α t).aestronglyMeasurable)
  have hint : Integrable (ρ 0) (volume.restrict A) :=
    native_flow_sector_cell_density_integrable E G X F α 0
  have hdercont : ContinuousOn (fun y => deriv (fun t => ρ t y) 0) D := by
    intro y hy
    simpa only [ρ,Ft,Function.comp_def] using
      (native_sector_density_time_derivative_continuous E G X F α.1 j y hy).comp
        (f := fun y : Euc 2 => ((0 : ℝ),y))
        (continuousWithinAt_const.prodMk continuousWithinAt_id)
        (by intro z hz; exact ⟨mem_univ _,hz⟩)
  have hdermeas : AEStronglyMeasurable (fun y => deriv (fun t => ρ t y) 0)
      (volume.restrict A) := (hdercont.mono hAD).aestronglyMeasurable hA
  have hbound : ∀ᵐ y ∂volume.restrict A, ∀ t ∈ U,
      ‖deriv (fun τ => ρ τ y) t‖ ≤ C * ρ₀ y :=
    hae.mono (fun y hy t ht => ht j y hy)
  have hboundint : Integrable (fun y => C * ρ₀ y) (volume.restrict A) :=
    (native_sector_cell_density_integrable E G F α).const_mul C
  have hdiff : ∀ᵐ y ∂volume.restrict A, ∀ t ∈ U,
      HasDerivAt (fun τ => ρ τ y) (deriv (fun τ => ρ τ y) t) t :=
    hae.mono (fun y hy t _ =>
      (native_sector_density_differentiable_alltime E G X F α.1 j y (interior_subset hy) t).hasDerivAt)
  have hv := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := ρ)
    (F' := fun t y => deriv (fun τ => ρ τ y) t) hU hmeas hint hdermeas hbound hboundint hdiff
  apply hv.2.congr_deriv
  apply integral_congr_ae
  filter_upwards [hae] with y hy
  exact (native_sector_density_first_variation E G X F α.1 j y (interior_subset hy)).deriv


open B1Bridges in
set_option backward.isDefEq.respectTransparency false in
private theorem native_area_first_variation
    (G : A7.SourceGeometry E) (X : InteriorSmoothVectorField E)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier) :
    HasDerivAt (fun t => geometricArea G.metric
      (transformed_surface E F (field_flow_exterior_diffeomorph E X t)))
      (pieceDivergenceSum E G F X) 0 := by
  let A := fun (i : Fin F.pieceCount)
      (a : Fin (canonicalSectorPartition (F.domain i)).count) (t : ℝ) =>
    ∫ y in ((F.domain i).chart ((canonicalSectorPartition (F.domain i)).chartIndex a)).map ''
      (canonicalSectorPartition (F.domain i)).piece a,
      sectorCoordinateDensity G.metric
        ((transformed_surface E F (field_flow_exterior_diffeomorph E X t)).map ∘
          (transformed_surface E F (field_flow_exterior_diffeomorph E X t)).parametrization i)
          ((canonicalSectorPartition (F.domain i)).chartIndex a) y
  let D := fun (i : Fin F.pieceCount)
      (a : Fin (canonicalSectorPartition (F.domain i)).count) =>
    ∫ y in ((F.domain i).chart ((canonicalSectorPartition (F.domain i)).chartIndex a)).map ''
      (canonicalSectorPartition (F.domain i)).piece a,
      pieceTangentialDivergence E G F X i ((canonicalSectorPartition (F.domain i)).chartIndex a) y *
        sectorCoordinateDensity G.metric (F.map ∘ F.parametrization i)
          ((canonicalSectorPartition (F.domain i)).chartIndex a) y
  have h (i : Fin F.pieceCount) : HasDerivAt (∑ a, A i a) (∑ a, D i a) 0 :=
    HasDerivAt.sum (fun a _ => native_sector_cell_integral_first_variation E G X F ⟨i,a⟩)
  have hh := HasDerivAt.sum (u := Finset.univ) (fun i _ => h i)
  convert! hh using 1
  ext t
  simp only [Finset.sum_apply, geometricArea, sectorArea, sectorPartitionArea, A]
  rfl

private theorem native_stationarity_of_minimum
    (G : A7.SourceGeometry E) {S R : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier)
    (Fprime : GeometricPiecewiseSurface R E.Carrier)
    (hminimum : FixedBoundaryMinimizer E G.metric F Fprime) :
    ∀ X : InteriorSmoothVectorField E, pieceDivergenceSum E G Fprime X = 0 := by
  intro X
  exact (flow_area_local_minimum E G.metric F Fprime hminimum X).hasDerivAt_eq_zero
    (native_area_first_variation E G X Fprime)

/-- Actual first clause of original A.2, derived from the original competitor
minimum by native ambient flow and differentiation of the actual Gram densities. -/
theorem A2_original_stationarity (G : A7.SourceGeometry E)
    {S R : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier)
    (Fprime : GeometricPiecewiseSurface R E.Carrier)
    (hminimum : FixedBoundaryMinimizer E G.metric F Fprime) :
    ∀ X : InteriorSmoothVectorField E, pieceDivergenceSum E G Fprime X = 0 :=
  native_stationarity_of_minimum E G F Fprime hminimum


set_option backward.isDefEq.respectTransparency false in
/-- Differentiating metric orthogonality along an actual immersion gives the
negative traced acceleration formula, before any integration by parts. -/
private theorem coordinate_normal_trace_identity (g : MetricTensor)
    (Φ W : E2 → E3) (x : E2)
    (hΦ : ContDiffAt ℝ ∞ Φ x) (hW : DifferentiableAt ℝ W x)
    (hg : ∀ a b, DifferentiableAt ℝ (fun z => g z a b) (Φ x))
    (hdet : IsUnit (g (Φ x)).det)
    (hsym : ∀ z a b, g z a b = g z b a)
    (horth : ∀ᶠ y in 𝓝 x, ∀ j : Fin 2,
      coordinateInner g (Φ y) (W y) (graphTangent Φ y j) = 0) :
    (∑ i : Fin 2, ∑ j : Fin 2, (inducedMetric g Φ x)⁻¹ i j *
      coordinateInner g (Φ x)
        (fderiv ℝ W x (coordinateVector 2 i) +
          coordinateConnection g (Φ x) (graphTangent Φ x i) (W x))
        (graphTangent Φ x j)) =
      -coordinateInner g (Φ x) (W x) (tracedAcceleration g Φ x) := by
  have htan (j : Fin 2) : DifferentiableAt ℝ (fun y => graphTangent Φ y j) x := by
    have hfd : ContDiffAt ℝ 1 (fderiv ℝ Φ) x := hΦ.fderiv_right (by simp)
    exact hfd.differentiableAt one_ne_zero |>.clm_apply
      (differentiableAt_const (coordinateVector 2 j))
  have hpair (i j : Fin 2) :
      coordinateInner g (Φ x)
        (fderiv ℝ W x (coordinateVector 2 i) +
          coordinateConnection g (Φ x) (graphTangent Φ x i) (W x))
        (graphTangent Φ x j) =
      -coordinateInner g (Φ x) (W x) (covariantAcceleration g Φ x i j) := by
    let c : ℝ → E2 := fun t => x + t • coordinateVector 2 i
    have hc : HasDerivAt c (coordinateVector 2 i) 0 := by
      convert!
        (hasDerivAt_const (0 : ℝ) x).add ((hasDerivAt_id (0 : ℝ)).smul_const
          (coordinateVector 2 i)) using 1 <;> simp only [c, one_smul, zero_add]
    have hc0 : c 0 = x := by simp [c]
    have hz : HasDerivAt (fun t => Φ (c t)) (graphTangent Φ x i) 0 := by
      convert!
        (show HasFDerivAt Φ (fderiv ℝ Φ x) (c 0) from
          hc0.symm ▸ (hΦ.differentiableAt (by simp)).hasFDerivAt).comp_hasDerivAt 0 hc using 1
    have hw : HasDerivAt (fun t => W (c t)) (fderiv ℝ W x (coordinateVector 2 i)) 0 := by
      convert! (show HasFDerivAt W (fderiv ℝ W x) (c 0) from hc0.symm ▸ hW.hasFDerivAt).comp_hasDerivAt 0 hc using 1
    have hv : HasDerivAt (fun t => graphTangent Φ (c t) j)
        (fderiv ℝ (fun y => graphTangent Φ y j) x (coordinateVector 2 i)) 0 := by
      convert! (show HasFDerivAt (fun y => graphTangent Φ y j)
          (fderiv ℝ (fun y => graphTangent Φ y j) x) (c 0) from
          hc0.symm ▸ (htan j).hasFDerivAt).comp_hasDerivAt 0 hc using 1
    have hh := coordinate_inner_curve_derivative g (fun t => Φ (c t))
      (fun t => W (c t)) (fun t => graphTangent Φ (c t) j)
      (graphTangent Φ x i) (fderiv ℝ W x (coordinateVector 2 i))
      (fderiv ℝ (fun y => graphTangent Φ y j) x (coordinateVector 2 i))
      (by convert! hg) hz hw hv
    have he : (fun t => coordinateInner g (Φ (c t)) (W (c t))
        (graphTangent Φ (c t) j)) =ᶠ[𝓝 (0 : ℝ)] (fun _ => (0 : ℝ)) := by
      have hc' : Tendsto c (𝓝 (0 : ℝ)) (𝓝 x) := by
        rw [← hc0]
        exact hc.continuousAt
      filter_upwards [hc' horth] with t ht
      exact ht j
    have hzero := hh.unique ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq he)
    simp only [hc0] at hzero
    have hcompat := native_metric_connection_compatibility g (Φ x) hdet hsym
      (graphTangent Φ x i) (W x) (graphTangent Φ x j)
    have hacc : covariantAcceleration g Φ x i j =
        fderiv ℝ (fun y => graphTangent Φ y j) x (coordinateVector 2 i) +
        coordinateConnection g (Φ x) (graphTangent Φ x i) (graphTangent Φ x j) := by
      unfold covariantAcceleration coordinateConnection
      simp only [metric_christoffel_matches g hsym]
    rw [hacc, coordinateInner_add_left, coordinate_metric_add_right]
    linarith
  simp_rw [hpair]
  simp only [tracedAcceleration, Fin.sum_univ_two]
  simp only [coordinate_metric_add_right]
  have hsmul (r : ℝ) (v : E3) : coordinateInner g (Φ x) (W x) (r • v) =
      r * coordinateInner g (Φ x) (W x) v := by
    rw [coordinate_metric_symmetric g hsym, coordinateInner_smul_left,
      coordinate_metric_symmetric g hsym]
  simp only [hsmul]
  ring


set_option backward.isDefEq.respectTransparency false in
private theorem actual_chart_inner (h : AmbientMetric ThreeSphere)
    (c : SmoothAmbientChart ThreeSphere) (z v w : E3) :
    coordinateInner (actualChartTensor h c) z v w =
      h.inner (c.chart.symm z) (inverseChartDifferential c z v)
        (inverseChartDifferential c z w) := by
  have hsum (v : E3) : (∑ i : Fin 3, v i • coordinateVector 3 i) = v := by
    ext j
    simp [coordinateVector, EuclideanSpace.single, Pi.single_apply]
  have hdiff (v : E3) : inverseChartDifferential c z v =
      ∑ i : Fin 3, v i • inverseChartDifferential c z (coordinateVector 3 i) := by
    simpa only [map_sum, map_smul] using
      congrArg (inverseChartDifferential c z) (hsum v).symm
  unfold coordinateInner actualChartTensor
  rw [hdiff v, hdiff w, map_sum]
  simp only [map_smul, _root_.sum_apply, _root_.smul_apply, map_sum, smul_eq_mul,
    Fin.sum_univ_three, map_add, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply]
  ring

private theorem actual_chart_metric_symmetric (h : AmbientMetric ThreeSphere)
    (c : SmoothAmbientChart ThreeSphere) :
    ∀ z a b, actualChartTensor h c z a b = actualChartTensor h c z b a := by
  intro z a b
  exact h.symm _ _ _

private theorem actual_chart_metric_positive (h : AmbientMetric ThreeSphere)
    (c : SmoothAmbientChart ThreeSphere) {z : E3} (hz : z ∈ c.chart.target) :
    (actualChartTensor h c z).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · apply Matrix.IsHermitian.ext
    intro a b
    simpa only [Matrix.conjTranspose_apply, star_trivial, actualChartTensor] using h.symm _ _ _
  · intro ξ hξ
    let w : E3 := WithLp.toLp 2 ξ
    have hw : w ≠ 0 := fun he => hξ (WithLp.toLp_injective 2 he)
    have hp := (A4GeometryBridges.actual_chart_tensor_metric_properties h c).2.2 z hz w hw
    convert! hp using 1
    simp only [coordinateInner, dotProduct, Matrix.mulVec, Fin.sum_univ_three,
      Pi.star_apply, star_trivial]
    dsimp only [w]
    ring

set_option backward.isDefEq.respectTransparency false in
private theorem actual_chart_inverse_comp (c : SmoothAmbientChart ThreeSphere)
    (p : ThreeSphere) (hp : p ∈ c.chart.source) (v : TangentSpace (𝓡 3) p) :
    inverseChartDifferential c (c.chart p) (chartDifferential c p v) = v := by
  have hmd : c.chart.MDifferentiable (𝓡 3) 𝓘(ℝ, E3) :=
    ⟨c.smooth.mdifferentiableOn (by simp), c.inverse_smooth.mdifferentiableOn (by simp)⟩
  exact congrArg (fun L => L v) (hmd.symm_comp_deriv hp)

set_option backward.isDefEq.respectTransparency false in
private theorem actual_patch_metric_covariance (h : AmbientMetric ThreeSphere)
    (c : SmoothAmbientChart ThreeSphere) (f : Euc 2 → ThreeSphere)
    (D : Set (Euc 2)) (y u v : Euc 2)
    (hu : UniqueMDiffWithinAt 𝓘(ℝ, Euc 2) D y)
    (hf : MDifferentiableWithinAt 𝓘(ℝ, Euc 2) (𝓡 3) f D y)
    (hsrc : f y ∈ c.chart.source) :
    coordinateInner (actualChartTensor h c) (c.chart (f y))
      (fderivWithin ℝ (c.chart ∘ f) D y u)
      (fderivWithin ℝ (c.chart ∘ f) D y v) =
      h.inner (f y) (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡 3) f D y u)
        (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡 3) f D y v) := by
  have hemd : MDifferentiableAt (𝓡 3) 𝓘(ℝ, E3) c.chart (f y) :=
    (c.smooth.contMDiffAt (c.chart.open_source.mem_nhds hsrc)).mdifferentiableAt (by simp)
  have hcomp := mfderivWithin_comp y hemd.mdifferentiableWithinAt hf
    (s := D) (u := univ) (by simp) hu
  rw [mfderivWithin_univ, mfderivWithin_eq_fderivWithin] at hcomp
  have hd (w : Euc 2) :
      inverseChartDifferential c (c.chart (f y))
        (fderivWithin ℝ (c.chart ∘ f) D y w) =
      mfderivWithin 𝓘(ℝ, Euc 2) (𝓡 3) f D y w := by
    have he : fderivWithin ℝ (c.chart ∘ f) D y w =
        chartDifferential c (f y) (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡 3) f D y w) :=
      congrArg (fun L => L w) hcomp
    rw [he]
    exact actual_chart_inverse_comp c (f y) hsrc _
  rw [actual_chart_inner h c, hd u, hd v]
  rw [c.chart.left_inv hsrc]

set_option backward.isDefEq.respectTransparency false in
private theorem actual_piece_gram_in_fixed_chart (G : A7.SourceGeometry E)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count) (y : Euc 2)
    (hy : y ∈ ((F.domain i).chart j).map.target)
    (c : SmoothAmbientChart ThreeSphere)
    (hsrc : pieceSphereCoordinate E F i j y ∈ c.chart.source) (a b : Fin 2) :
    coordinateInner (actualChartTensor G.extension c)
      (c.chart (pieceSphereCoordinate E F i j y))
      (fderivWithin ℝ (c.chart ∘ pieceSphereCoordinate E F i j)
        ((F.domain i).chart j).map.target y (EuclideanSpace.single a 1))
      (fderivWithin ℝ (c.chart ∘ pieceSphereCoordinate E F i j)
        ((F.domain i).chart j).map.target y (EuclideanSpace.single b 1)) =
    sectorCoordinateGram G.metric (F.map ∘ F.parametrization i) j y a b := by
  let D := ((F.domain i).chart j).map.target
  let f := sectorCoordinateMap (F.map ∘ F.parametrization i) j
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  have hud : UniqueMDiffWithinAt 𝓘(ℝ, Euc 2) D y := by
    dsimp only [D]
    rw [((F.domain i).chart j).target_eq]
    exact (SectorModel.uniqueDiffOn_domain ((F.domain i).chart j).model y
      (by simpa only [((F.domain i).chart j).target_eq] using hy)).uniqueMDiffWithinAt
  have hf : MDifferentiableWithinAt 𝓘(ℝ, Euc 2) (𝓡∂ 3) f D y :=
    (F.piece_c1 i j y hy).mdifferentiableWithinAt one_ne_zero
  have hfc : MDifferentiableWithinAt 𝓘(ℝ, Euc 2) (𝓡 3) (E.toSphere ∘ f) D y :=
    hinc.contMDiff.mdifferentiableAt (by simp) |>.comp_mdifferentiableWithinAt y hf
  have hc := actual_patch_metric_covariance G.extension c (E.toSphere ∘ f) D y
    (EuclideanSpace.single a 1) (EuclideanSpace.single b 1) hud hfc hsrc
  refine hc.trans ?_
  have hd := mfderivWithin_comp y
    (hinc.contMDiff.mdifferentiableAt (by simp)).mdifferentiableWithinAt hf
    (u := univ) (by simp) hud
  rw [mfderivWithin_univ] at hd
  rw [hd]
  exact (G.metric_restriction (f y)
    (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 3) f D y (EuclideanSpace.single a 1))
    (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 3) f D y (EuclideanSpace.single b 1))).symm

def actualFieldCoordinate (X : InteriorSmoothVectorField E)
    (c : SmoothAmbientChart ThreeSphere) (z : E3) : E3 :=
  chartDifferential c (c.chart.symm z) (X.field (c.chart.symm z))

private def actual_coordinate_flow (X : InteriorSmoothVectorField E)
    (c : SmoothAmbientChart ThreeSphere) (q : ℝ × E3) : E3 :=
  c.chart (curveAt X.field (field_complete E X) (c.chart.symm q.2) q.1)

set_option backward.isDefEq.respectTransparency false in
private theorem actual_coordinate_flow_smooth (X : InteriorSmoothVectorField E)
    (c : SmoothAmbientChart ThreeSphere) (p : ThreeSphere) (hp : p ∈ c.chart.source) :
    ContDiffAt ℝ ∞ (actual_coordinate_flow E X c) (0, c.chart p) := by
  have hinv : ContMDiffAt 𝓘(ℝ, E3) (𝓡 3) ∞ c.chart.symm (c.chart p) :=
    c.inverse_smooth.contMDiffAt (c.chart.open_target.mem_nhds (c.chart.map_source hp))
  have hpair : ContMDiffAt (𝓘(ℝ).prod 𝓘(ℝ, E3)) (𝓘(ℝ).prod (𝓡 3)) ∞
      (fun q : ℝ × E3 => (q.1, c.chart.symm q.2)) (0, c.chart p) :=
    contMDiffAt_fst.prodMk (hinv.comp (0, c.chart p) (f := Prod.snd) contMDiffAt_snd)
  have hflow := (field_flow_joint E X).contMDiffAt.comp (0, c.chart p) hpair
  have he : ContMDiffAt (𝓡 3) 𝓘(ℝ, E3) ∞ c.chart p :=
    c.smooth.contMDiffAt (c.chart.open_source.mem_nhds hp)
  have he' : ContMDiffAt (𝓡 3) 𝓘(ℝ, E3) ∞ c.chart
      (curveAt X.field (field_complete E X) (c.chart.symm (c.chart p)) 0) := by
    simpa only [curveAt_zero, c.chart.left_inv hp] using he
  have hc := he'.comp (0, c.chart p) hflow
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hc
  exact hc.contDiffAt

set_option backward.isDefEq.respectTransparency false in
private theorem actual_integral_curve_coordinate_derivative (X : InteriorSmoothVectorField E)
    (c : SmoothAmbientChart ThreeSphere) (γ : ℝ → ThreeSphere)
    (hγ : IsMIntegralCurve γ X.field) (t : ℝ) (hsrc : γ t ∈ c.chart.source) :
    HasDerivAt (c.chart ∘ γ) (actualFieldCoordinate E X c (c.chart (γ t))) t := by
  have hmd : MDifferentiableAt (𝓡 3) 𝓘(ℝ, E3) c.chart (γ t) :=
    (c.smooth.contMDiffAt (c.chart.open_source.mem_nhds hsrc)).mdifferentiableAt (by simp)
  have hd := hasMFDerivAt_iff_hasFDerivAt.mp (hmd.hasMFDerivAt.comp t (hγ t))
  apply hasDerivAt_iff_hasFDerivAt.mpr
  apply hd.congr_fderiv
  apply ContinuousLinearMap.ext
  intro r
  change ℝ at r
  change (NormedSpace.fromTangentSpace (c.chart (γ t)))
      (mfderiv (𝓡 3) 𝓘(ℝ, E3) c.chart (γ t) (r • X.field (γ t))) =
    r • actualFieldCoordinate E X c (c.chart (γ t))
  rw [map_smul, map_smul]
  congr 1
  unfold actualFieldCoordinate chartDifferential
  simp only [ContinuousLinearMap.comp_apply]
  rw [c.chart.left_inv hsrc]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem actual_coordinate_flow_velocity (X : InteriorSmoothVectorField E)
    (c : SmoothAmbientChart ThreeSphere) {z : E3} (hz : z ∈ c.chart.target) :
    HasDerivAt (fun t => actual_coordinate_flow E X c (t,z))
      (actualFieldCoordinate E X c z) 0 := by
  have hγ := curveAt_integralCurve X.field (field_complete E X) (c.chart.symm z)
  have hc := actual_integral_curve_coordinate_derivative E X c
    (curveAt X.field (field_complete E X) (c.chart.symm z)) hγ 0
    (by simpa only [curveAt_zero] using c.chart.map_target hz)
  simp only [curveAt_zero] at hc
  change HasDerivAt (fun t => actual_coordinate_flow E X c (t,z))
    (actualFieldCoordinate E X c (c.chart (c.chart.symm z))) 0 at hc
  rw [c.chart.right_inv hz] at hc
  exact hc

private theorem actual_coordinate_flow_tangent_velocity (X : InteriorSmoothVectorField E)
    (c : SmoothAmbientChart ThreeSphere) (p : ThreeSphere) (hp : p ∈ c.chart.source)
    (v : E3) :
    HasDerivAt (fun t => fderiv ℝ (fun z => actual_coordinate_flow E X c (t,z))
      (c.chart p) v)
      (fderiv ℝ (actualFieldCoordinate E X c) (c.chart p) v) 0 := by
  have hm := mixed_flow_jet (actual_coordinate_flow E X c) (c.chart p) v
    ((actual_coordinate_flow_smooth E X c p hp).of_le (by simp))
  have he : (fun z => deriv (fun t => actual_coordinate_flow E X c (t,z)) 0) =ᶠ[
      𝓝 (c.chart p)] (actualFieldCoordinate E X c) := by
    filter_upwards [c.chart.open_target.mem_nhds (c.chart.map_source hp)] with z hz
    exact (actual_coordinate_flow_velocity E X c hz).deriv
  simpa only [he.fderiv_eq (𝕜 := ℝ)] using hm

private theorem actual_coordinate_flow_initial_differential (X : InteriorSmoothVectorField E)
    (c : SmoothAmbientChart ThreeSphere) (p : ThreeSphere) (hp : p ∈ c.chart.source) :
    fderiv ℝ (fun z => actual_coordinate_flow E X c (0,z)) (c.chart p) =
      ContinuousLinearMap.id ℝ E3 := by
  have he : (fun z => actual_coordinate_flow E X c (0,z)) =ᶠ[𝓝 (c.chart p)] id := by
    filter_upwards [c.chart.open_target.mem_nhds (c.chart.map_source hp)] with z hz
    change c.chart (curveAt X.field (field_complete E X) (c.chart.symm z) 0) = z
    rw [curveAt_zero, c.chart.right_inv hz]
  rw [he.fderiv_eq (𝕜 := ℝ), fderiv_id]

private theorem actual_flow_gram_density_variation (G : A7.SourceGeometry E)
    (X : InteriorSmoothVectorField E) (c : SmoothAmbientChart ThreeSphere)
    (p : ThreeSphere) (hp : p ∈ c.chart.source) (v : Fin 2 → E3)
    (hgram : Matrix.PosDef (fun i j => coordinateInner (actualChartTensor G.extension c)
      (c.chart p) (v i) (v j))) :
    let z := c.chart p
    let g := actualChartTensor G.extension c
    let Φ := actual_coordinate_flow E X c
    let V := fun t i => fderiv ℝ (fun w => Φ (t,w)) z (v i)
    let A : ℝ → Matrix (Fin 2) (Fin 2) ℝ :=
      fun t i j => coordinateInner g (Φ (t,z)) (V t i) (V t j)
    HasDerivAt (fun t => Real.sqrt (A t).det)
      (Real.sqrt (A 0).det * (∑ i : Fin 2, ∑ j : Fin 2, (A 0)⁻¹ i j *
        coordinateInner g z
          (fderiv ℝ (actualFieldCoordinate E X c) z (v i) +
            coordinateConnection g z (v i) (actualFieldCoordinate E X c z)) (v j))) 0 := by
  let z := c.chart p
  let g := actualChartTensor G.extension c
  let Φ := actual_coordinate_flow E X c
  let V := fun t i => fderiv ℝ (fun w => Φ (t,w)) z (v i)
  let A : ℝ → Matrix (Fin 2) (Fin 2) ℝ :=
    fun t i j => coordinateInner g (Φ (t,z)) (V t i) (V t j)
  have hZ : Φ (0,z) = z := by
    change c.chart (curveAt X.field (field_complete E X) (c.chart.symm z) 0) = z
    rw [curveAt_zero, c.chart.right_inv (c.chart.map_source hp)]
  have hV (i : Fin 2) : V 0 i = v i := by
    dsimp only [V, Φ, z]
    rw [actual_coordinate_flow_initial_differential E X c p hp]
    rfl
  have hA : (A 0).PosDef := by simpa only [A, hZ, hV] using hgram
  have hgm : (g z).PosDef := actual_chart_metric_positive G.extension c (c.chart.map_source hp)
  have hunit : IsUnit (g z).det := isUnit_iff_ne_zero.mpr (ne_of_gt hgm.det_pos)
  have hg (a b : Fin 3) : DifferentiableAt ℝ (fun y => g y a b) (Φ (0,z)) := by
    rw [hZ]
    exact ((A4GeometryBridges.actual_chart_tensor_metric_properties G.extension c).1 a b |>.contDiffAt
      (c.chart.open_target.mem_nhds (c.chart.map_source hp))).differentiableAt
      (by simp)
  have hD (i j : Fin 2) : HasDerivAt (fun t => A t i j)
      ((∑ a : Fin 3, ∑ b : Fin 3, fderiv ℝ (fun y => g y a b) z
          (actualFieldCoordinate E X c z) * v i a * v j b) +
        coordinateInner g z (fderiv ℝ (actualFieldCoordinate E X c) z (v i)) (v j) +
        coordinateInner g z (v i) (fderiv ℝ (actualFieldCoordinate E X c) z (v j))) 0 := by
    have hr := coordinate_inner_curve_derivative g (fun t => Φ (t,z))
      (fun t => V t i) (fun t => V t j) (actualFieldCoordinate E X c z)
      (fderiv ℝ (actualFieldCoordinate E X c) z (v i))
      (fderiv ℝ (actualFieldCoordinate E X c) z (v j)) hg
      (actual_coordinate_flow_velocity E X c (c.chart.map_source hp))
      (actual_coordinate_flow_tangent_velocity E X c p hp (v i))
      (actual_coordinate_flow_tangent_velocity E X c p hp (v j))
    simpa only [hZ, hV] using hr
  exact covariant_gram_density_variation g z (actualFieldCoordinate E X c z) hunit
    (actual_chart_metric_symmetric G.extension c) A hA v
    (fun i => fderiv ℝ (actualFieldCoordinate E X c) z (v i)) hD

set_option backward.isDefEq.respectTransparency false in
private theorem actual_piece_chart_smooth (c : SmoothAmbientChart ThreeSphere)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count) (y : Euc 2)
    (hy : y ∈ interior ((F.domain i).chart j).map.target)
    (hsrc : pieceSphereCoordinate E F i j y ∈ c.chart.source) :
    ContDiffAt ℝ ∞ (c.chart ∘ pieceSphereCoordinate E F i j) y := by
  exact ((c.smooth.contMDiffAt (c.chart.open_source.mem_nhds hsrc)).comp y
    ((native_piece_smooth_and_rank E F i j).1.contMDiffAt
      (isOpen_interior.mem_nhds hy))).contDiffAt

set_option backward.isDefEq.respectTransparency false in
private theorem actual_flow_piece_chart_derivative (X : InteriorSmoothVectorField E)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count) (y : Euc 2)
    (hy : y ∈ interior ((F.domain i).chart j).map.target)
    (c : SmoothAmbientChart ThreeSphere)
    (hsrc : pieceSphereCoordinate E F i j y ∈ c.chart.source) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      fderiv ℝ (c.chart ∘ pieceSphereCoordinate E
        (transformed_surface E F (field_flow_exterior_diffeomorph E X t)) i j) y =
      (fderiv ℝ (fun w => actual_coordinate_flow E X c (t,w))
        (c.chart (pieceSphereCoordinate E F i j y))).comp
        (fderiv ℝ (c.chart ∘ pieceSphereCoordinate E F i j) y) := by
  let f := pieceSphereCoordinate E F i j
  let p := f y
  let z := c.chart p
  have hf : ContinuousAt f y :=
    ((native_piece_smooth_and_rank E F i j).1.contMDiffAt (isOpen_interior.mem_nhds hy)).continuousAt
  have hs : ∀ᶠ q in 𝓝 y, f q ∈ c.chart.source :=
    hf (c.chart.open_source.mem_nhds hsrc)
  have hdiff : ∀ᶠ q in 𝓝 ((0 : ℝ),z), DifferentiableAt ℝ (actual_coordinate_flow E X c) q :=
    (((actual_coordinate_flow_smooth E X c p hsrc).of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually
      (by simp)).mono (fun _ h => h.differentiableAt one_ne_zero)
  have ht := ((continuous_id.prodMk continuous_const).continuousAt :
      ContinuousAt (fun t : ℝ => (t,z)) 0) hdiff
  filter_upwards [ht] with t ht
  have hd : DifferentiableAt ℝ (fun w => actual_coordinate_flow E X c (t,w)) z :=
    ht.comp z ((differentiableAt_const t).prodMk differentiableAt_id)
  have he : (c.chart ∘ pieceSphereCoordinate E
      (transformed_surface E F (field_flow_exterior_diffeomorph E X t)) i j) =ᶠ[𝓝 y]
      (fun q => actual_coordinate_flow E X c (t, c.chart (f q))) := by
    filter_upwards [hs] with q hq
    change c.chart (curveAt X.field (field_complete E X) (f q) t) =
      c.chart (curveAt X.field (field_complete E X) (c.chart.symm (c.chart (f q))) t)
    rw [c.chart.left_inv hq]
  rw [he.fderiv_eq (𝕜 := ℝ)]
  exact fderiv_comp y hd ((actual_piece_chart_smooth E c F i j y hy hsrc).differentiableAt (by simp))

set_option backward.isDefEq.respectTransparency false in
private theorem actual_sector_density_first_variation (G : A7.SourceGeometry E)
    (X : InteriorSmoothVectorField E) {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier) (i : Fin F.pieceCount)
    (j : Fin (F.domain i).count) (y : Euc 2)
    (hy : y ∈ interior ((F.domain i).chart j).map.target)
    (c : SmoothAmbientChart ThreeSphere)
    (hsrc : pieceSphereCoordinate E F i j y ∈ c.chart.source) :
    let f := c.chart ∘ pieceSphereCoordinate E F i j
    let z := f y
    let g := actualChartTensor G.extension c
    let v := fun a : Fin 2 => fderiv ℝ f y (coordinateVector 2 a)
    let A : Matrix (Fin 2) (Fin 2) ℝ := fun a b => coordinateInner g z (v a) (v b)
    HasDerivAt (fun t => sectorCoordinateDensity G.metric
      ((transformed_surface E F (field_flow_exterior_diffeomorph E X t)).map ∘
        (transformed_surface E F (field_flow_exterior_diffeomorph E X t)).parametrization i) j y)
      (sectorCoordinateDensity G.metric (F.map ∘ F.parametrization i) j y *
        (∑ a : Fin 2, ∑ b : Fin 2, A⁻¹ a b * coordinateInner g z
          (fderiv ℝ (actualFieldCoordinate E X c) z (v a) +
            coordinateConnection g z (v a) (actualFieldCoordinate E X c z)) (v b))) 0 := by
  let f := pieceSphereCoordinate E F i j
  let p := f y
  let z := c.chart p
  let g := actualChartTensor G.extension c
  let D := ((F.domain i).chart j).map.target
  let v := fun a : Fin 2 => fderiv ℝ (c.chart ∘ f) y (coordinateVector 2 a)
  let H : Matrix (Fin 2) (Fin 2) ℝ := fun a b => coordinateInner g z (v a) (v b)
  let Φ := actual_coordinate_flow E X c
  let V := fun t a => fderiv ℝ (fun w => Φ (t,w)) z (v a)
  let A : ℝ → Matrix (Fin 2) (Fin 2) ℝ :=
    fun t a b => coordinateInner g (Φ (t,z)) (V t a) (V t b)
  have hn : D ∈ 𝓝 y := mem_interior_iff_mem_nhds.mp hy
  have hH : H = sectorCoordinateGram G.metric (F.map ∘ F.parametrization i) j y := by
    ext a b
    have hh := actual_piece_gram_in_fixed_chart E G F i j y (interior_subset hy) c hsrc a b
    rw [fderivWithin_of_mem_nhds hn] at hh
    exact hh
  have hpos : H.PosDef := by rw [hH]; exact native_sector_gram_positive G.metric F i j y (interior_subset hy)
  have hr := actual_flow_gram_density_variation E G X c p hsrc v hpos
  have hZ : Φ (0,z) = z := by
    change c.chart (curveAt X.field (field_complete E X) (c.chart.symm z) 0) = z
    rw [curveAt_zero, c.chart.right_inv (c.chart.map_source hsrc)]
  have hV (a : Fin 2) : V 0 a = v a := by
    dsimp only [V, Φ, z, p]
    rw [actual_coordinate_flow_initial_differential E X c (f y) hsrc]
    rfl
  have hA : A 0 = H := by
    ext a b
    change coordinateInner g (Φ (0,z)) (V 0 a) (V 0 b) = _
    rw [hZ, hV, hV]
  have hvar : HasDerivAt (fun t => Real.sqrt (A t).det)
      (sectorCoordinateDensity G.metric (F.map ∘ F.parametrization i) j y *
        (∑ a : Fin 2, ∑ b : Fin 2, H⁻¹ a b * coordinateInner g z
          (fderiv ℝ (actualFieldCoordinate E X c) z (v a) +
            coordinateConnection g z (v a) (actualFieldCoordinate E X c z)) (v b))) 0 := by
    apply hr.congr_deriv
    change Real.sqrt (A 0).det *
      (∑ a : Fin 2, ∑ b : Fin 2, (A 0)⁻¹ a b * coordinateInner g z
        (fderiv ℝ (actualFieldCoordinate E X c) z (v a) +
          coordinateConnection g z (v a) (actualFieldCoordinate E X c z)) (v b)) = _
    rw [hA]
    unfold sectorCoordinateDensity
    rw [← hH]
  have hflow : ∀ᶠ t in 𝓝 (0 : ℝ), curveAt X.field (field_complete E X) p t ∈ c.chart.source := by
    have hc : ContinuousAt (fun t => curveAt X.field (field_complete E X) p t) 0 :=
      ((curveAt_integralCurve X.field (field_complete E X) p) 0).mdifferentiableAt.continuousAt
    have hp0 : curveAt X.field (field_complete E X) p 0 = p := curveAt_zero _ _ _
    apply hc
    change c.chart.source ∈ 𝓝 (curveAt X.field (field_complete E X) p 0)
    rw [hp0]
    exact c.chart.open_source.mem_nhds hsrc
  have he : (fun t => Real.sqrt (A t).det) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => sectorCoordinateDensity G.metric
        ((transformed_surface E F (field_flow_exterior_diffeomorph E X t)).map ∘
          (transformed_surface E F (field_flow_exterior_diffeomorph E X t)).parametrization i) j y) := by
    filter_upwards [hflow, actual_flow_piece_chart_derivative E X F i j y hy c hsrc] with t ht hd
    let Ft := transformed_surface E F (field_flow_exterior_diffeomorph E X t)
    have hsrc' : pieceSphereCoordinate E Ft i j y ∈ c.chart.source := ht
    have heq : A t = sectorCoordinateGram G.metric (Ft.map ∘ Ft.parametrization i) j y := by
      ext a b
      have hcov := actual_piece_gram_in_fixed_chart E G Ft i j y (interior_subset hy) c hsrc' a b
      have hn' : ((Ft.domain i).chart j).map.target ∈ 𝓝 y := hn
      rw [fderivWithin_of_mem_nhds hn', hd] at hcov
      have hf0 : Φ (t,z) = c.chart (pieceSphereCoordinate E Ft i j y) := by
        change c.chart (curveAt X.field (field_complete E X) (c.chart.symm (c.chart p)) t) =
          c.chart (curveAt X.field (field_complete E X) p t)
        rw [c.chart.left_inv hsrc]
      simpa only [A, hf0, V, v, ContinuousLinearMap.comp_apply, coordinateVector] using hcov
    rw [heq]
    rfl
  exact hvar.congr_of_eventuallyEq he.symm

set_option backward.isDefEq.respectTransparency false in
/-- The native centred-chart divergence is the ordinary covariant trace in
EVERY actual smooth ambient chart containing the same piece image point. -/
theorem native_piece_divergence_in_actual_chart (G : A7.SourceGeometry E)
    (X : InteriorSmoothVectorField E) {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier) (i : Fin F.pieceCount)
    (j : Fin (F.domain i).count) (y : Euc 2)
    (hy : y ∈ interior ((F.domain i).chart j).map.target)
    (c : SmoothAmbientChart ThreeSphere)
    (hsrc : pieceSphereCoordinate E F i j y ∈ c.chart.source) :
    let f := c.chart ∘ pieceSphereCoordinate E F i j
    let z := f y
    let g := actualChartTensor G.extension c
    let v := fun a : Fin 2 => fderiv ℝ f y (coordinateVector 2 a)
    let A : Matrix (Fin 2) (Fin 2) ℝ := fun a b => coordinateInner g z (v a) (v b)
    pieceTangentialDivergence E G F X i j y =
      ∑ a : Fin 2, ∑ b : Fin 2, A⁻¹ a b * coordinateInner g z
        (fderiv ℝ (actualFieldCoordinate E X c) z (v a) +
          ∑ k : Fin 3, (∑ r : Fin 3, ∑ q : Fin 3,
            christoffel g z r q k * v a r * actualFieldCoordinate E X c z q) •
              coordinateVector 3 k) (v b) := by
  let ρ := sectorCoordinateDensity G.metric (F.map ∘ F.parametrization i) j y
  have hρ : ρ ≠ 0 := ne_of_gt
    (Real.sqrt_pos.mpr (native_sector_gram_positive G.metric F i j y (interior_subset hy)).det_pos)
  have h := (native_sector_density_first_variation E G X F i j y (interior_subset hy)).unique
    (actual_sector_density_first_variation E G X F i j y hy c hsrc)
  simp only [coordinateConnection, metric_christoffel_matches _ (actual_chart_metric_symmetric G.extension c)] at h
  apply (mul_left_cancel₀ hρ)
  convert! h using 1
  ring


open B1Bridges

set_option backward.isDefEq.respectTransparency false in
private theorem native_sector_divergence_continuous (G : A7.SourceGeometry E)
    (X : InteriorSmoothVectorField E) {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier) (i : Fin F.pieceCount)
    (j : Fin (F.domain i).count) :
    ContinuousOn (pieceTangentialDivergence E G F X i j)
      ((F.domain i).chart j).map.target := by
  let D := ((F.domain i).chart j).map.target
  let ρ := sectorCoordinateDensity G.metric (F.map ∘ F.parametrization i) j
  let Ft := fun t => transformed_surface E F (field_flow_exterior_diffeomorph E X t)
  let R := fun y => deriv (fun t => sectorCoordinateDensity G.metric
    ((Ft t).map ∘ (Ft t).parametrization i) j y) 0
  intro y hy
  have hρpos : ρ y ≠ 0 := ne_of_gt
    (Real.sqrt_pos.mpr (native_sector_gram_positive G.metric F i j y hy).det_pos)
  have hc : ContinuousWithinAt R D y := by
    exact (native_sector_density_time_derivative_continuous E G X F i j y hy).comp
      (continuousWithinAt_const.prodMk continuousWithinAt_id)
      (by intro z hz; exact ⟨mem_univ _, hz⟩)
  have hd : ContinuousWithinAt (fun z => R z / ρ z) D y :=
    hc.div (native_sector_density_continuous G.metric F i j y hy) hρpos
  have he : pieceTangentialDivergence E G F X i j =ᶠ[𝓝[D] y] (fun z => R z / ρ z) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    change _ = deriv (fun t => sectorCoordinateDensity G.metric
      ((Ft t).map ∘ (Ft t).parametrization i) j z) 0 / ρ z
    rw [(native_sector_density_first_variation E G X F i j z hz).deriv]
    exact (mul_div_cancel_right₀ _ (ne_of_gt
      (Real.sqrt_pos.mpr (native_sector_gram_positive G.metric F i j z hz).det_pos))).symm
  exact hd.congr_of_eventuallyEq_of_mem he hy

set_option backward.isDefEq.respectTransparency false in
private theorem native_sector_divergence_density_integrable (G : A7.SourceGeometry E)
    (X : InteriorSmoothVectorField E) {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier) (α : SectorCellIndex F) :
    IntegrableOn (fun y => pieceTangentialDivergence E G F X α.1 (sectorCellChart F α) y *
      sectorCoordinateDensity G.metric (F.map ∘ F.parametrization α.1) (sectorCellChart F α) y)
      (((F.domain α.1).chart (sectorCellChart F α)).map '' sectorCellSet F α) := by
  let j := sectorCellChart F α
  let A := ((F.domain α.1).chart j).map '' sectorCellSet F α
  let ρ := sectorCoordinateDensity G.metric (F.map ∘ F.parametrization α.1) j
  let Ft := fun t => transformed_surface E F (field_flow_exterior_diffeomorph E X t)
  have hAD : A ⊆ ((F.domain α.1).chart j).map.target := by
    rintro y ⟨q,hq,rfl⟩
    exact ((F.domain α.1).chart j).map.map_source
      ((canonicalSectorPartition (F.domain α.1)).subordinate α.2 hq)
  have hm : AEStronglyMeasurable
      (fun y => pieceTangentialDivergence E G F X α.1 j y * ρ y) (volume.restrict A) :=
    (((native_sector_divergence_continuous E G X F α.1 j).mul
      (native_sector_density_continuous G.metric F α.1 j)).mono hAD).aestronglyMeasurable
      (native_sector_cell_coordinates_measurable E F α)
  obtain ⟨C,hC,hbound⟩ := native_whole_piece_density_relative_derivative_bound E G X F α.1
  have hb := hbound.self_of_nhds
  have hint : Integrable (fun y => C * ρ y) (volume.restrict A) :=
    (native_sector_cell_density_integrable E G F α).const_mul C
  apply hint.mono' hm
  filter_upwards [native_sector_cell_ae_interior E F α] with y hy
  have hh := hb j y hy
  rw [(native_sector_density_first_variation E G X F α.1 j y (interior_subset hy)).deriv] at hh
  simpa only [norm_mul, Real.norm_eq_abs, abs_of_nonneg hC.le,
    abs_of_nonneg (Real.sqrt_nonneg _)] using hh



set_option backward.isDefEq.respectTransparency false in
private theorem native_same_image_divergence_density_covariance
    (G : A7.SourceGeometry E) (X : InteriorSmoothVectorField E)
    {S R : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier) (H : GeometricPiecewiseSurface R E.Carrier)
    (a : R ≃ₜ S) (ha : ∀ x, F.map (a x) = H.map x)
    (hb : a ⁻¹' S.boundary = R.boundary)
    (i : Fin H.pieceCount) (j : Fin (H.domain i).count)
    (r : Fin F.pieceCount) (l : Fin (F.domain r).count)
    (T : SectorImageTransition F H a i j r l) (y : Euc 2)
    (hy : y ∈ T.coordinate.source) :
    pieceTangentialDivergence E G H X i j y *
      sectorCoordinateDensity G.metric (H.map ∘ H.parametrization i) j y =
    |(fderiv ℝ T.coordinate y).det| *
      (pieceTangentialDivergence E G F X r l (T.coordinate y) *
        sectorCoordinateDensity G.metric (F.map ∘ F.parametrization r) l (T.coordinate y)) := by
  let Ft := fun t => transformed_surface E F (field_flow_exterior_diffeomorph E X t)
  let Ht := fun t => transformed_surface E H (field_flow_exterior_diffeomorph E X t)
  have hmatch (t : ℝ) : ∀ x, (Ft t).map (a x) = (Ht t).map x :=
    fun x => congrArg (field_flow_exterior_diffeomorph E X t) (ha x)
  let Tt (t : ℝ) : SectorImageTransition (Ft t) (Ht t) a i j r l := {
    coordinate := T.coordinate
    source_eq := T.source_eq
    target_eq := T.target_eq
    open_source := T.open_source
    open_target := T.open_target
    parametrization_matches := T.parametrization_matches
    smooth := T.smooth
    smooth_inverse := T.smooth_inverse
    derivative_injective := T.derivative_injective
    jacobian_ne_zero := T.jacobian_ne_zero }
  have hcov (t : ℝ) :
      sectorCoordinateDensity G.metric ((Ht t).map ∘ (Ht t).parametrization i) j y =
      |(fderiv ℝ T.coordinate y).det| *
        sectorCoordinateDensity G.metric ((Ft t).map ∘ (Ft t).parametrization r) l
          (T.coordinate y) :=
    (sector_same_image_density_integral_transport G.metric (Ft t) (Ht t) a (hmatch t) hb
      i j r l (Tt t) {y} (measurableSet_singleton y)
        (by intro z hz; simpa only [mem_singleton_iff] using hz ▸ hy)).1 y (mem_singleton y)
  have hyH : y ∈ interior ((H.domain i).chart j).map.target := by
    rw [T.source_eq] at hy
    exact hy.1
  have hyF : T.coordinate y ∈ interior ((F.domain r).chart l).map.target := by
    have hty := T.coordinate.map_source hy
    rw [T.target_eq] at hty
    exact hty.1
  exact (native_sector_density_first_variation E G X H i j y (interior_subset hyH)).unique
    ((native_sector_density_first_variation E G X F r l (T.coordinate y)
      (interior_subset hyF)).const_mul |(fderiv ℝ T.coordinate y).det|
        |>.congr_of_eventuallyEq (Filter.Eventually.of_forall hcov))

set_option backward.isDefEq.respectTransparency false in
private theorem native_same_image_divergence_integral_transport
    (G : A7.SourceGeometry E) (X : InteriorSmoothVectorField E)
    {S R : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier) (H : GeometricPiecewiseSurface R E.Carrier)
    (a : R ≃ₜ S) (ha : ∀ x, F.map (a x) = H.map x)
    (hb : a ⁻¹' S.boundary = R.boundary)
    (i : Fin H.pieceCount) (j : Fin (H.domain i).count)
    (r : Fin F.pieceCount) (l : Fin (F.domain r).count)
    (T : SectorImageTransition F H a i j r l) (s : Set (Euc 2))
    (hs : MeasurableSet s) (hsub : s ⊆ T.coordinate.source) :
    (∫ y in s, pieceTangentialDivergence E G H X i j y *
      sectorCoordinateDensity G.metric (H.map ∘ H.parametrization i) j y) =
    (∫ y in T.coordinate '' s, pieceTangentialDivergence E G F X r l y *
      sectorCoordinateDensity G.metric (F.map ∘ F.parametrization r) l y) := by
  have hderivative : ∀ y ∈ s, HasFDerivWithinAt T.coordinate
      (fderiv ℝ T.coordinate y) s y := by
    intro y hy
    exact ((T.smooth.contDiffAt (T.open_source.mem_nhds (hsub hy))).differentiableAt
      (by simp)).hasFDerivAt.hasFDerivWithinAt
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hs hderivative
    (T.coordinate.injOn.mono hsub)]
  apply setIntegral_congr_fun hs
  intro y hy
  exact native_same_image_divergence_density_covariance E G X F H a ha hb i j r l T y
    (hsub hy)


set_option backward.isDefEq.respectTransparency false in
private theorem native_divergence_chart_density_covariance
    (G : A7.SourceGeometry E) (X : InteriorSmoothVectorField E)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j l : Fin (F.domain i).count) (y : Euc 2)
    (hy : y ∈ interior ((F.domain i).chart j).map.target)
    (hsrc : ((F.domain i).chart j).map.symm y ∈ ((F.domain i).chart l).map.source) :
    pieceTangentialDivergence E G F X i j y *
      sectorCoordinateDensity G.metric (F.map ∘ F.parametrization i) j y =
    |(fderiv ℝ (((F.domain i).chart l).map ∘ ((F.domain i).chart j).map.symm) y).det| *
      (pieceTangentialDivergence E G F X i l
          (((F.domain i).chart l).map (((F.domain i).chart j).map.symm y)) *
        sectorCoordinateDensity G.metric (F.map ∘ F.parametrization i) l
          (((F.domain i).chart l).map (((F.domain i).chart j).map.symm y))) := by
  let a := ((F.domain i).chart j).map
  let b := ((F.domain i).chart l).map
  let t := b ∘ a.symm
  let Ft := fun τ => transformed_surface E F (field_flow_exterior_diffeomorph E X τ)
  have hty : t y ∈ interior b.target := by
    rw [← AreaCertificates.sector_chart_piece_interior (F.domain i) l]
    exact ⟨a.symm y,
      ⟨(AreaCertificates.sector_chart_inverse_interior (F.domain i) j hy).1,hsrc⟩,rfl⟩
  have hcov (τ : ℝ) :
      sectorCoordinateDensity G.metric ((Ft τ).map ∘ (Ft τ).parametrization i) j y =
      |(fderiv ℝ t y).det| *
        sectorCoordinateDensity G.metric ((Ft τ).map ∘ (Ft τ).parametrization i) l (t y) :=
    native_sector_density_chart_covariance G.metric (Ft τ) i j l y hy hsrc
  exact (native_sector_density_first_variation E G X F i j y (interior_subset hy)).unique
    ((native_sector_density_first_variation E G X F i l (t y) (interior_subset hty)).const_mul
      |(fderiv ℝ t y).det| |>.congr_of_eventuallyEq (Filter.Eventually.of_forall hcov))

set_option backward.isDefEq.respectTransparency false in
private theorem native_divergence_chart_integral_transport
    (G : A7.SourceGeometry E) (X : InteriorSmoothVectorField E)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j l : Fin (F.domain i).count) (s : Set (Euc 2))
    (hs : MeasurableSet s)
    (hsub : s ⊆ interior ((F.domain i).chart j).map.target ∩
      ((F.domain i).chart j).map.symm ⁻¹' ((F.domain i).chart l).map.source) :
    (∫ y in s, pieceTangentialDivergence E G F X i j y *
      sectorCoordinateDensity G.metric (F.map ∘ F.parametrization i) j y) =
    (∫ y in (((F.domain i).chart l).map ∘ ((F.domain i).chart j).map.symm) '' s,
      pieceTangentialDivergence E G F X i l y *
        sectorCoordinateDensity G.metric (F.map ∘ F.parametrization i) l y) := by
  let a := ((F.domain i).chart j).map
  let b := ((F.domain i).chart l).map
  let t := b ∘ a.symm
  let U := interior a.target ∩ a.symm ⁻¹' b.source
  have ho : IsOpen U :=
    (a.symm.continuousOn.mono interior_subset).isOpen_inter_preimage isOpen_interior
      ((F.domain i).chart l).source_open
  have hd : ∀ y ∈ s, HasFDerivWithinAt t (fderiv ℝ t y) s y := by
    intro y hy
    exact (((F.domain i).transition_smooth_interior j l).contDiffAt
      (ho.mem_nhds (hsub hy))).differentiableAt (by simp) |>.hasFDerivAt.hasFDerivWithinAt
  have hinj : InjOn t s := by
    intro y hy z hz he
    have hay : a.symm y ∈ b.source := (hsub hy).2
    have haz : a.symm z ∈ b.source := (hsub hz).2
    have haeq := b.injOn hay haz he
    exact a.symm.injOn (interior_subset (hsub hy).1) (interior_subset (hsub hz).1) haeq
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hs hd hinj]
  apply setIntegral_congr_fun hs
  intro y hy
  exact native_divergence_chart_density_covariance E G X F i j l y (hsub hy).1 (hsub hy).2


set_option backward.isDefEq.respectTransparency false in
private theorem native_divergence_zero_off_field_support
    (G : A7.SourceGeometry E) (X : InteriorSmoothVectorField E)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count) (y : Euc 2)
    (hp : pieceSphereCoordinate E F i j y ∉ closure {p | X.field p ≠ 0}) :
    pieceTangentialDivergence E G F X i j y = 0 := by
  let p := pieceSphereCoordinate E F i j y
  let e := extChartAt (𝓡 3) p
  let z := e p
  let V := fieldCoordinate E X p
  have hn : ∀ᶠ q in 𝓝 p, X.field q = 0 := by
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hp] with q hq
    exact Classical.not_not.mp (fun h => hq (subset_closure h))
  have he : V =ᶠ[𝓝 z] (fun _ => (0 : Euc 3)) := by
    have hs := continuousAt_extChartAt_symm (I := 𝓡 3) p
    have hs' : Tendsto e.symm (𝓝 z) (𝓝 p) := by
      change Tendsto e.symm (𝓝 z) (𝓝 (e.symm (e p))) at hs
      rw [e.left_inv (mem_extChartAt_source p)] at hs
      exact hs
    filter_upwards [hs' hn] with w hw
    change X.field ((extChartAt (𝓡 3) p).symm w) = 0 at hw
    simp only [V, fieldCoordinate, hw, map_zero]
  have hv : V z = 0 := he.eq_of_nhds
  have hd : fderiv ℝ V z = 0 := by
    rw [he.fderiv_eq]
    exact fderiv_const_apply (𝕜 := ℝ) (c := (0 : Euc 3)) (x := z)
  unfold pieceTangentialDivergence covariantFieldCoordinate
  change ∑ a : Fin 2, ∑ b : Fin 2, _ * coordinateInner _ _
    (fderiv ℝ V z _ + ∑ k : Fin 3, (∑ r : Fin 3, ∑ q : Fin 3,
      _ * _ * V z q) • EuclideanSpace.single k 1) _ = 0
  simp [hv, hd, coordinateInner_zero_left]


set_option backward.isDefEq.respectTransparency false in
private theorem native_divergence_chart_integrable_transport
    (G : A7.SourceGeometry E) (X : InteriorSmoothVectorField E)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j l : Fin (F.domain i).count) (s : Set (Euc 2))
    (hs : MeasurableSet s)
    (hsub : s ⊆ interior ((F.domain i).chart j).map.target ∩
      ((F.domain i).chart j).map.symm ⁻¹' ((F.domain i).chart l).map.source)
    (hint : IntegrableOn (fun y => pieceTangentialDivergence E G F X i j y *
      sectorCoordinateDensity G.metric (F.map ∘ F.parametrization i) j y) s) :
    IntegrableOn (fun y => pieceTangentialDivergence E G F X i l y *
      sectorCoordinateDensity G.metric (F.map ∘ F.parametrization i) l y)
      ((((F.domain i).chart l).map ∘ ((F.domain i).chart j).map.symm) '' s) := by
  let a := ((F.domain i).chart j).map
  let b := ((F.domain i).chart l).map
  let t := b ∘ a.symm
  let U := interior a.target ∩ a.symm ⁻¹' b.source
  have ho : IsOpen U :=
    (a.symm.continuousOn.mono interior_subset).isOpen_inter_preimage isOpen_interior
      ((F.domain i).chart l).source_open
  have hd : ∀ y ∈ s, HasFDerivWithinAt t (fderiv ℝ t y) s y := by
    intro y hy
    exact (((F.domain i).transition_smooth_interior j l).contDiffAt
      (ho.mem_nhds (hsub hy))).differentiableAt (by simp) |>.hasFDerivAt.hasFDerivWithinAt
  have hinj : InjOn t s := by
    intro y hy z hz he
    exact a.symm.injOn (interior_subset (hsub hy).1) (interior_subset (hsub hz).1)
      (b.injOn (hsub hy).2 (hsub hz).2 he)
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hs hd hinj]
  apply hint.congr_fun _ hs
  intro y hy
  exact native_divergence_chart_density_covariance E G X F i j l y (hsub hy).1 (hsub hy).2

set_option backward.isDefEq.respectTransparency false in
private theorem native_divergence_canonical_row_localization
    (G : A7.SourceGeometry E) (X : InteriorSmoothVectorField E)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count)
    (hzero : ∀ k : Fin (F.domain i).count, ∀ y ∈ interior ((F.domain i).chart k).map.target,
      ((F.domain i).chart k).map.symm y ∉ ((F.domain i).chart j).map.source →
        pieceTangentialDivergence E G F X i k y = 0) :
    (∑ a : Fin (canonicalSectorPartition (F.domain i)).count,
      ∫ y in ((F.domain i).chart ((canonicalSectorPartition (F.domain i)).chartIndex a)).map ''
        (canonicalSectorPartition (F.domain i)).piece a,
        pieceTangentialDivergence E G F X i ((canonicalSectorPartition (F.domain i)).chartIndex a) y *
          sectorCoordinateDensity G.metric (F.map ∘ F.parametrization i)
            ((canonicalSectorPartition (F.domain i)).chartIndex a) y) =
    (∫ y in interior ((F.domain i).chart j).map.target,
      pieceTangentialDivergence E G F X i j y *
        sectorCoordinateDensity G.metric (F.map ∘ F.parametrization i) j y) := by
  classical
  let Q := F.domain i
  letI : BorelSpace Q := ⟨rfl⟩
  letI : MetricSpace Q := TopologicalSpace.metrizableSpaceMetric Q
  let P := canonicalSectorPartition Q
  let c := (Q.chart j).map
  let B := fun a : Fin P.count => P.piece a ∩ Q.interior ∩ c.source
  let k := fun a : Fin P.count => (Q.chart (P.chartIndex a)).map
  let A := fun a : Fin P.count => k a '' B a
  let C := fun a : Fin P.count => c '' B a
  let I := fun l y => pieceTangentialDivergence E G F X i l y *
    sectorCoordinateDensity G.metric (F.map ∘ F.parametrization i) l y
  have hB (a : Fin P.count) : MeasurableSet (B a) :=
    ((P.measurable a).inter (AreaCertificates.sector_piece_boundary_closed Q).measurableSet.compl).inter
      ((Q.chart j).source_open.measurableSet)
  have hsubk (a : Fin P.count) : B a ⊆ (k a).source :=
    fun q hq => P.subordinate a hq.1.1
  have hsubc (a : Fin P.count) : B a ⊆ c.source := fun _ hq => hq.2
  have hA (a : Fin P.count) : MeasurableSet (A a) :=
    (hB a).image_of_continuousOn_injOn ((k a).continuousOn.mono (hsubk a))
      ((k a).injOn.mono (hsubk a))
  have hC (a : Fin P.count) : MeasurableSet (C a) :=
    (hB a).image_of_continuousOn_injOn (c.continuousOn.mono (hsubc a))
      (c.injOn.mono (hsubc a))
  have hAtrans (a : Fin P.count) :
      A a ⊆ interior (k a).target ∩ (k a).symm ⁻¹' c.source := by
    rintro y ⟨q,hq,rfl⟩
    refine ⟨?_,?_⟩
    · rw [← AreaCertificates.sector_chart_piece_interior Q (P.chartIndex a)]
      exact ⟨q,⟨hq.1.2,hsubk a hq⟩,rfl⟩
    · change (k a).symm ((k a) q) ∈ c.source
      rw [(k a).left_inv (hsubk a hq)]
      exact hq.2
  have hAC (a : Fin P.count) : (c ∘ (k a).symm) '' A a = C a := by
    ext y
    constructor
    · rintro ⟨_,⟨q,hq,rfl⟩,rfl⟩
      exact ⟨q,hq,by simp only [Function.comp_apply,(k a).left_inv (hsubk a hq)]⟩
    · rintro ⟨q,hq,rfl⟩
      exact ⟨(k a) q,⟨q,hq,rfl⟩,
        by simp only [Function.comp_apply,(k a).left_inv (hsubk a hq)]⟩
  have hiA (a : Fin P.count) : IntegrableOn (I (P.chartIndex a)) (A a) :=
    (native_sector_divergence_density_integrable E G X F ⟨i,a⟩).mono_set
      (image_mono (fun q hq => hq.1.1))
  have hiC (a : Fin P.count) : IntegrableOn (I j) (C a) := by
    rw [← hAC a]
    exact native_divergence_chart_integrable_transport E G X F i (P.chartIndex a) j
      (A a) (hA a) (hAtrans a) (hiA a)
  have hrow (a : Fin P.count) :
      (∫ y in (k a) '' P.piece a, I (P.chartIndex a) y) = ∫ y in C a, I j y := by
    have hfull : MeasurableSet ((k a) '' P.piece a) :=
      native_sector_cell_coordinates_measurable E F ⟨i,a⟩
    have hs : A a ⊆ (k a) '' P.piece a := image_mono fun q hq => hq.1.1
    have he : (∫ y in (k a) '' P.piece a, I (P.chartIndex a) y) =
        ∫ y in A a, I (P.chartIndex a) y := by
      apply setIntegral_eq_of_subset_of_ae_sdiff_eq_zero hfull.nullMeasurableSet hs
      filter_upwards [ae_imp_of_ae_restrict (native_sector_cell_ae_interior E F ⟨i,a⟩)]
        with y hy hdiff
      have hiy : y ∈ interior (k a).target := hy hdiff.1
      obtain ⟨q,hq,hqy⟩ := hdiff.1
      subst y
      have hqsrc : q ∈ (k a).source := P.subordinate a hq
      have hqint : q ∈ Q.interior := by
        have hh := (AreaCertificates.sector_chart_inverse_interior Q (P.chartIndex a) hiy).1
        change (k a).symm ((k a) q) ∈ Q.interior at hh
        simpa only [(k a).left_inv hqsrc] using hh
      have hnot : (k a).symm ((k a) q) ∉ c.source := by
        rw [(k a).left_inv hqsrc]
        intro hc
        exact hdiff.2 ⟨q,⟨⟨hq,hqint⟩,hc⟩,rfl⟩
      exact mul_eq_zero_of_left (hzero (P.chartIndex a) ((k a) q) hiy hnot) _
    rw [he,← hAC a]
    exact native_divergence_chart_integral_transport E G X F i (P.chartIndex a) j
      (A a) (hA a) (hAtrans a)
  have hcover : (⋃ a, C a) = interior c.target := by
    rw [← image_iUnion]
    have he : (⋃ a, B a) = Q.interior ∩ c.source := by
      ext q
      constructor
      · intro hq
        obtain ⟨a,hqa⟩ := mem_iUnion.mp hq
        exact ⟨hqa.1.2,hqa.2⟩
      · intro hq
        have hqp : q ∈ ⋃ a, P.piece a := by rw [P.covers]; trivial
        obtain ⟨a,hqa⟩ := mem_iUnion.mp hqp
        exact mem_iUnion.mpr ⟨a,⟨⟨hqa,hq.1⟩,hq.2⟩⟩
    rw [he,AreaCertificates.sector_chart_piece_interior Q j]
  have hdisj : Pairwise (fun a b => Disjoint (C a) (C b)) := by
    intro a b hab
    apply Set.disjoint_left.mpr
    rintro y ⟨q,hq,hqy⟩ ⟨z,hz,hzy⟩
    have he := c.injOn hq.2 hz.2 (hqy.trans hzy.symm)
    subst z
    exact Set.disjoint_left.mp (P.disjoint hab) hq.1.1 hz.1.1
  change (∑ a,∫ y in (k a) '' P.piece a, I (P.chartIndex a) y) = ∫ y in interior c.target,I j y
  simp_rw [hrow]
  rw [← integral_iUnion_fintype hC hdisj hiC,hcover]


set_option backward.isDefEq.respectTransparency false in
private theorem native_piece_chart_ambient_isolation
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count) (y : Euc 2)
    (hy : y ∈ interior ((F.domain i).chart j).map.target) :
    ∃ V : Set ThreeSphere, IsOpen V ∧ pieceSphereCoordinate E F i j y ∈ V ∧
      ∀ q : S, E.toSphere (F.map q) ∈ V ↔
        q ∈ (F.parametrization i) '' ((F.domain i).interior ∩ ((F.domain i).chart j).map.source) := by
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  have hemb := hinc.isEmbedding.comp F.embedding
  obtain ⟨V,hV,hpre⟩ := hemb.isInducing.isOpen_iff.mp
    (AreaCertificates.geometric_piece_chart_interior_image_open F i j)
  have hp : F.parametrization i (((F.domain i).chart j).map.symm y) ∈
      (F.parametrization i) '' ((F.domain i).interior ∩ ((F.domain i).chart j).map.source) :=
    ⟨_,AreaCertificates.sector_chart_inverse_interior (F.domain i) j hy,rfl⟩
  refine ⟨V,hV,?_,?_⟩
  · change E.toSphere (F.map (F.parametrization i (((F.domain i).chart j).map.symm y))) ∈ V
    change F.parametrization i (((F.domain i).chart j).map.symm y) ∈
      (E.toSphere ∘ F.map) ⁻¹' V
    rwa [hpre]
  · intro q
    change q ∈ (E.toSphere ∘ F.map) ⁻¹' V ↔ _
    rw [← hpre]

set_option backward.isDefEq.respectTransparency false in
private theorem native_piece_divergence_sum_localization
    (G : A7.SourceGeometry E) (X : InteriorSmoothVectorField E)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count)
    (hsupport : ∀ q : S, E.toSphere (F.map q) ∈ closure {p | X.field p ≠ 0} →
      q ∈ (F.parametrization i) '' ((F.domain i).interior ∩ ((F.domain i).chart j).map.source)) :
    pieceDivergenceSum E G F X =
      (∫ y in interior ((F.domain i).chart j).map.target,
        pieceTangentialDivergence E G F X i j y *
          sectorCoordinateDensity G.metric (F.map ∘ F.parametrization i) j y) := by
  classical
  have hi (k : Fin (F.domain i).count) (y : Euc 2)
      (hy : y ∈ interior ((F.domain i).chart k).map.target)
      (hnot : ((F.domain i).chart k).map.symm y ∉ ((F.domain i).chart j).map.source) :
      pieceTangentialDivergence E G F X i k y = 0 := by
    apply native_divergence_zero_off_field_support E G X F i k y
    intro hp
    obtain ⟨q,hq,he⟩ := hsupport (F.parametrization i (((F.domain i).chart k).map.symm y)) hp
    have hqeq := (F.parametrization_embedding i).injective he
    exact hnot (hqeq ▸ hq.2)
  have hr (r : Fin F.pieceCount) (hri : r ≠ i) (k : Fin (F.domain r).count)
      (y : Euc 2) (hy : y ∈ interior ((F.domain r).chart k).map.target) :
      pieceTangentialDivergence E G F X r k y = 0 := by
    apply native_divergence_zero_off_field_support E G X F r k y
    intro hp
    obtain ⟨q,hq,he⟩ := hsupport (F.parametrization r (((F.domain r).chart k).map.symm y)) hp
    exact Set.disjoint_left.mp (F.pieces_distinct hri)
      ⟨_,(AreaCertificates.sector_chart_inverse_interior (F.domain r) k hy).1,rfl⟩
      ⟨q,hq.1,he⟩
  unfold pieceDivergenceSum
  rw [Finset.sum_eq_single i]
  · exact native_divergence_canonical_row_localization E G X F i j hi
  · intro r _ hri
    apply Finset.sum_eq_zero
    intro a _
    apply integral_eq_zero_of_ae
    filter_upwards [native_sector_cell_ae_interior E F ⟨r,a⟩] with y hy
    exact mul_eq_zero_of_left (hr r hri _ y hy) _
  · simp

private theorem native_piece_stationarity_in_one_chart
    (G : A7.SourceGeometry E) {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier)
    (hstationary : ∀ X : InteriorSmoothVectorField E, pieceDivergenceSum E G F X = 0)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count) (X : InteriorSmoothVectorField E)
    (hsupport : ∀ q : S, E.toSphere (F.map q) ∈ closure {p | X.field p ≠ 0} →
      q ∈ (F.parametrization i) '' ((F.domain i).interior ∩ ((F.domain i).chart j).map.source)) :
    (∫ y in interior ((F.domain i).chart j).map.target,
      pieceTangentialDivergence E G F X i j y *
        sectorCoordinateDensity G.metric (F.map ∘ F.parametrization i) j y) = 0 := by
  rw [← native_piece_divergence_sum_localization E G X F i j hsupport]
  exact hstationary X


open A2NativeNormalProjection A2NativeTests


set_option backward.isDefEq.respectTransparency false in
private theorem native_exterior_interior_ambient_nhds (x : E.Carrier)
    (hx : x ∈ (𝓡∂ 3).interior E.Carrier) :
    E.toSphere '' (𝓡∂ 3).interior E.Carrier ∈ 𝓝 (E.toSphere x) := by
  let e := extChartAt (𝓡∂ 3) x
  let U := interior e.target
  let f : U → ThreeSphere := fun y => E.toSphere (e.symm y)
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  have hc : Continuous f :=
    hinc.isEmbedding.continuous.comp (((continuousOn_extChartAt_symm x).mono
      interior_subset).domRestrict)
  have hi : Function.Injective f := by
    intro y z he
    apply Subtype.ext
    exact e.symm.injOn (interior_subset y.property) (interior_subset z.property)
      (hinc.isEmbedding.injective he)
  have ho : IsOpen (Set.range f) :=
    DifferentialGeometry.Topology.isOpen_range_of_isOpen_of_continuous_injective_real
      (𝓡 3) isOpen_interior f hc hi
  have hxe : e x ∈ U := (𝓡∂ 3).isInteriorPoint_iff.mp hx
  have hp : E.toSphere x ∈ Set.range f :=
    ⟨⟨e x,hxe⟩,congrArg E.toSphere (e.left_inv (mem_extChartAt_source x))⟩
  apply Filter.mem_of_superset (ho.mem_nhds hp)
  rintro p ⟨y,rfl⟩
  refine ⟨e.symm y,?_,rfl⟩
  apply ((𝓡∂ 3).isInteriorPoint_iff_of_mem_atlas (n := ∞) (by simp)
    (chart_mem_atlas (EuclideanHalfSpace 3) x)
      (by simpa only [e,extChartAt_source] using e.map_target (interior_subset y.property))).mpr
  change e (e.symm y) ∈ interior e.target
  rw [e.right_inv (interior_subset y.property)]
  exact y.property

set_option backward.isDefEq.respectTransparency false in
private theorem native_actual_chart_differential_invertible
    (c : SmoothAmbientChart ThreeSphere) (p : ThreeSphere) (hp : p ∈ c.chart.source) :
    (mfderiv (𝓡 3) 𝓘(ℝ,E3) c.chart p).IsInvertible := by
  have hc : c.chart ∈ IsManifold.maximalAtlas (𝓡 3) 1 ThreeSphere :=
    c.chart.mem_maximalAtlas_of_contMDiffOn (c.smooth.of_le (by simp))
      (c.inverse_smooth.of_le (by simp))
  convert! isInvertible_mfderiv_extend hc hp using 1


set_option backward.isDefEq.respectTransparency false in
private theorem native_chart_cutoff_field
    (c : SmoothAmbientChart ThreeSphere) (U : Set ThreeSphere) (hU : IsOpen U)
    (hUc : U ⊆ c.chart.source)
    (hUE : U ⊆ E.toSphere '' (𝓡∂ 3).interior E.Carrier)
    (p : ThreeSphere) (hp : p ∈ U) (W : E3 → E3)
    (hW : ContDiffOn ℝ ∞ W (c.chart '' U)) :
    ∃ (X : InteriorSmoothVectorField E) (χ : ThreeSphere → ℝ),
      ContMDiff (𝓡 3) 𝓘(ℝ) ∞ χ ∧ HasCompactSupport χ ∧
      (∀ q, 0 ≤ χ q) ∧ χ p = 1 ∧
      closure {q | X.field q ≠ 0} ⊆ U ∧
      (∀ q ∈ U, chartDifferential c q (X.field q) = χ q • W (c.chart q)) := by
  classical
  let V := c.chart '' U
  have hV : IsOpen V := c.chart.isOpen_image_of_subset_source hU hUc
  let Z : ∀ z : E3, TangentSpace 𝓘(ℝ,E3) z :=
    fun z => (NormedSpace.fromTangentSpace z).symm (W z)
  let Y := VectorField.mpullback (𝓡 3) 𝓘(ℝ,E3) c.chart Z
  have hZ : ContMDiffOn 𝓘(ℝ,E3) (𝓘(ℝ,E3)).tangent ∞
      (fun z => Bundle.TotalSpace.mk' E3 z (Z z)) V := by
    convert! (contMDiff_tangentBundleModelSpaceHomeomorph_symm (I := 𝓘(ℝ,E3))).comp_contMDiffOn
      ((contDiffOn_id.prodMk hW).contMDiffOn) using 1
  have hY : ContMDiffOn (𝓡 3) (𝓡 3).tangent ∞
      (fun q => Bundle.TotalSpace.mk' E3 q (Y q)) U := by
    intro q hq
    have hqV : c.chart q ∈ V := mem_image_of_mem c.chart hq
    have hZZ := hZ.contMDiffAt (hV.mem_nhds hqV)
    have hcc := c.smooth.contMDiffAt (c.chart.open_source.mem_nhds (hUc hq))
    exact (hZZ.mpullback_vectorField_preimage hcc
      (native_actual_chart_differential_invertible c q (hUc hq))
      (by simp)).contMDiffWithinAt
  obtain ⟨χ,_,hχU⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓡 3) p).mem_iff.mp
    (hU.mem_nhds hp)
  let Yχ := fun q => χ q • Y q
  have hYχ : ContMDiff (𝓡 3) (𝓡 3).tangent ∞
      (fun q => Bundle.TotalSpace.mk' E3 q (Yχ q)) :=
    χ.contMDiff.contMDiffOn.smul_section_of_tsupport hU hχU hY
  have hsu : closure {q | Yχ q ≠ 0} ⊆ tsupport χ := by
    apply closure_mono
    intro q hq
    exact fun h => hq (by simp only [Yχ,h,zero_smul])
  let X : InteriorSmoothVectorField E := {
    field := Yχ
    smooth := hYχ
    compact_support := χ.hasCompactSupport.of_isClosed_subset isClosed_closure hsu
    support_interior := hsu.trans (hχU.trans hUE) }
  refine ⟨X,χ,χ.contMDiff,χ.hasCompactSupport,(fun q => χ.nonneg (x := q)),χ.eq_one,hsu.trans hχU,?_⟩
  intro q hq
  change chartDifferential c q (χ q • Y q) = _
  rw [map_smul]
  congr 1
  unfold chartDifferential Y VectorField.mpullback
  rw [ContinuousLinearMap.comp_apply,
    (native_actual_chart_differential_invertible c q (hUc hq)).self_apply_inverse]
  exact (NormedSpace.fromTangentSpace (c.chart q)).apply_symm_apply _


set_option backward.isDefEq.respectTransparency false in
private theorem native_piece_chart_small_ambient_isolation
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count) (W : Set E2)
    (hW : IsOpen W) (hWD : W ⊆ interior ((F.domain i).chart j).map.target)
    (x : E2) (hx : x ∈ W) :
    ∃ V : Set ThreeSphere, IsOpen V ∧ pieceSphereCoordinate E F i j x ∈ V ∧
      ∀ q : S, E.toSphere (F.map q) ∈ V ↔
        q ∈ (F.parametrization i) ''
          (((F.domain i).chart j).map.source ∩ ((F.domain i).chart j).map ⁻¹' W) := by
  let a := ((F.domain i).chart j).map
  let Q := a.source ∩ a ⁻¹' W
  have hQ : IsOpen Q := a.continuousOn.isOpen_inter_preimage
    ((F.domain i).chart j).source_open hW
  have hQI : Q ⊆ (F.domain i).interior := by
    intro q hq
    have h := AreaCertificates.sector_chart_inverse_interior (F.domain i) j (hWD hq.2)
    have haq : a.symm (a q) = q := a.left_inv hq.1
    rw [haq] at h
    exact h.1
  obtain ⟨O,hO,he⟩ := (F.parametrization_embedding i).isInducing.isOpen_iff.mp hQ
  have him : IsOpen (F.parametrization i '' Q) := by
    have heq : F.parametrization i '' Q =
        (F.parametrization i '' (F.domain i).interior) ∩ O := by
      rw [← he]
      rw [← image_inter_preimage]
      congr 1
      exact (inter_eq_right.mpr (he ▸ hQI)).symm
    rw [heq]
    exact (AreaCertificates.geometric_piece_interior_image_open F i).inter hO
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  obtain ⟨V,hV,hpre⟩ := (hinc.isEmbedding.comp F.embedding).isInducing.isOpen_iff.mp him
  have hp : F.parametrization i (a.symm x) ∈ F.parametrization i '' Q := by
    refine ⟨a.symm x,⟨a.map_target (interior_subset (hWD hx)),?_⟩,rfl⟩
    change a (a.symm x) ∈ W
    rwa [a.right_inv (interior_subset (hWD hx))]
  refine ⟨V,hV,?_,?_⟩
  · change F.parametrization i (a.symm x) ∈ (E.toSphere ∘ F.map) ⁻¹' V
    rwa [hpre]
  · intro q
    change q ∈ (E.toSphere ∘ F.map) ⁻¹' V ↔ _
    rw [← hpre]

set_option backward.isDefEq.respectTransparency false in
private theorem actual_field_coordinate_smooth (X : InteriorSmoothVectorField E)
    (c : SmoothAmbientChart ThreeSphere) (z : E3) (hz : z ∈ c.chart.target) :
    ContDiffAt ℝ ∞ (actualFieldCoordinate E X c) z := by
  let Φ := actual_coordinate_flow E X c
  have hΦ : ContDiffAt ℝ ∞ Φ (0,z) := by
    simpa only [c.chart.right_inv hz] using
      actual_coordinate_flow_smooth E X c (c.chart.symm z) (c.chart.map_target hz)
  have hD : ContDiffAt ℝ ∞ (fun w : E3 => fderiv ℝ Φ (0,w) (1,0)) z :=
    ((hΦ.fderiv_right (by simp)).comp z
      (contDiffAt_const.prodMk contDiffAt_id)).clm_apply contDiffAt_const
  apply hD.congr_of_eventuallyEq
  have hΦ' : ∀ᶠ w in 𝓝 z, DifferentiableAt ℝ Φ (0,w) := by
    have hdiff : ∀ᶠ q in 𝓝 ((0 : ℝ),z), DifferentiableAt ℝ Φ q :=
      ((hΦ.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)).mono
        (fun q hq => hq.differentiableAt one_ne_zero)
    exact (show Tendsto (fun w : E3 => ((0 : ℝ),w)) (𝓝 z) (𝓝 ((0 : ℝ),z)) from
      (continuous_const.prodMk continuous_id).continuousAt) hdiff
  filter_upwards [hΦ',c.chart.open_target.mem_nhds hz] with w hw hwc
  have hc : HasDerivAt (fun t : ℝ => (t,w)) (1,0) 0 :=
    (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 w)
  have hh := hw.hasFDerivAt.comp_hasDerivAt 0 hc
  change HasDerivAt (fun t => Φ (t,w)) _ 0 at hh
  exact (hh.unique (actual_coordinate_flow_velocity E X c hwc)).symm

set_option backward.isDefEq.respectTransparency false in
private theorem native_actual_chart_data (G : A7.SourceGeometry E)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count)
    (c : SmoothAmbientChart ThreeSphere) :
    let P := pieceSphereCoordinate E F i j
    let U := interior ((F.domain i).chart j).map.target ∩ P ⁻¹' c.chart.source
    let f := c.chart ∘ P
    IsOpen U ∧ ContDiffOn ℝ ∞ f U ∧ MapsTo f U c.chart.target ∧
      (∀ x ∈ U, Function.Injective (fderiv ℝ f x)) ∧
      ∀ x ∈ U, (inducedMetric (actualChartTensor G.extension c) f x).PosDef := by
  dsimp only
  let P := pieceSphereCoordinate E F i j
  let D := interior ((F.domain i).chart j).map.target
  let U := D ∩ P ⁻¹' c.chart.source
  let f := c.chart ∘ P
  have hn := native_piece_smooth_and_rank E F i j
  have hU : IsOpen U := hn.1.continuousOn.isOpen_inter_preimage
    isOpen_interior c.chart.open_source
  have hf : ContDiffOn ℝ ∞ f U := by
    intro x hx
    exact (actual_piece_chart_smooth E c F i j x hx.1 hx.2).contDiffWithinAt
  have hm : MapsTo f U c.chart.target := fun x hx => c.chart.map_source hx.2
  refine ⟨hU,hf,hm,?_,?_⟩
  · intro x hx
    have hp : MDifferentiableAt 𝓘(ℝ,E2) (𝓡 3) P x :=
      (hn.1.contMDiffAt (isOpen_interior.mem_nhds hx.1)).mdifferentiableAt (by simp)
    have hc : MDifferentiableAt (𝓡 3) 𝓘(ℝ,E3) c.chart (P x) :=
      (c.smooth.contMDiffAt (c.chart.open_source.mem_nhds hx.2)).mdifferentiableAt (by simp)
    have he : Function.Injective (mfderiv (𝓡 3) 𝓘(ℝ,E3) c.chart (P x)) := by
      intro v w hvw
      have hh := congrArg (inverseChartDifferential c (c.chart (P x)))
        (congrArg (NormedSpace.fromTangentSpace (c.chart (P x))) hvw)
      change inverseChartDifferential c (c.chart (P x)) (chartDifferential c (P x) v) =
        inverseChartDifferential c (c.chart (P x)) (chartDifferential c (P x) w) at hh
      simpa only [actual_chart_inverse_comp c (P x) hx.2] using hh
    have hh := mfderiv_comp x hc hp
    rw [mfderiv_eq_fderiv] at hh
    have hinj := he.comp (hn.2 x hx.1)
    intro v w hvw
    apply (NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm.injective
    apply hinj
    change ((mfderiv (𝓡 3) 𝓘(ℝ,E3) c.chart (P x)).comp
      (mfderiv 𝓘(ℝ,E2) (𝓡 3) P x)) ((NormedSpace.fromTangentSpace x).symm v) =
      ((mfderiv (𝓡 3) 𝓘(ℝ,E3) c.chart (P x)).comp
      (mfderiv 𝓘(ℝ,E2) (𝓡 3) P x)) ((NormedSpace.fromTangentSpace x).symm w)
    rw [← hh]
    exact congrArg (NormedSpace.fromTangentSpace (𝕜 := ℝ) (f x)).symm hvw
  · intro x hx
    have he : inducedMetric (actualChartTensor G.extension c) f x =
        sectorCoordinateGram G.metric (F.map ∘ F.parametrization i) j x := by
      ext a b
      have hh := actual_piece_gram_in_fixed_chart E G F i j x (interior_subset hx.1) c hx.2 a b
      rw [fderivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hx.1)] at hh
      exact hh
    rw [he]
    exact native_sector_gram_positive G.metric F i j x (interior_subset hx.1)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 100000 in
private theorem native_normal_field_divergence (G : A7.SourceGeometry E)
    (X : InteriorSmoothVectorField E) {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier) (i : Fin F.pieceCount)
    (j : Fin (F.domain i).count) (y : E2)
    (hy : y ∈ interior ((F.domain i).chart j).map.target)
    (c : SmoothAmbientChart ThreeSphere)
    (hsrc : pieceSphereCoordinate E F i j y ∈ c.chart.source)
    (horth : ∀ᶠ z in 𝓝 y, ∀ k : Fin 2,
      coordinateInner (actualChartTensor G.extension c)
        ((c.chart ∘ pieceSphereCoordinate E F i j) z)
        (actualFieldCoordinate E X c ((c.chart ∘ pieceSphereCoordinate E F i j) z))
        (graphTangent (c.chart ∘ pieceSphereCoordinate E F i j) z k) = 0) :
    pieceTangentialDivergence E G F X i j y =
      -coordinateInner (actualChartTensor G.extension c)
        ((c.chart ∘ pieceSphereCoordinate E F i j) y)
        (actualFieldCoordinate E X c ((c.chart ∘ pieceSphereCoordinate E F i j) y))
        (tracedAcceleration (actualChartTensor G.extension c)
          (c.chart ∘ pieceSphereCoordinate E F i j) y) := by
  let f := c.chart ∘ pieceSphereCoordinate E F i j
  let g := actualChartTensor G.extension c
  have hf := actual_piece_chart_smooth E c F i j y hy hsrc
  have hW := actual_field_coordinate_smooth E X c (f y) (c.chart.map_source hsrc)
  have hcomp : fderiv ℝ (actualFieldCoordinate E X c ∘ f) y =
      (fderiv ℝ (actualFieldCoordinate E X c) (f y)).comp (fderiv ℝ f y) :=
    fderiv_comp y (hW.differentiableAt (by simp)) (hf.differentiableAt (by simp))
  have hprops := A4GeometryBridges.actual_chart_tensor_metric_properties G.extension c
  have hd := actual_chart_metric_positive G.extension c (c.chart.map_source hsrc)
  have hn := coordinate_normal_trace_identity g f (actualFieldCoordinate E X c ∘ f) y hf
    ((hW.differentiableAt (by simp)).comp y (hf.differentiableAt (by simp)))
    (fun a b => (hprops.1 a b |>.contDiffAt (c.chart.open_target.mem_nhds
      (c.chart.map_source hsrc))).differentiableAt (by simp))
    (isUnit_iff_ne_zero.mpr hd.det_pos.ne') (actual_chart_metric_symmetric G.extension c) horth
  change pieceTangentialDivergence E G F X i j y =
    -coordinateInner g (f y) (actualFieldCoordinate E X c (f y)) (tracedAcceleration g f y)
  have hb := native_piece_divergence_in_actual_chart E G X F i j y hy c hsrc
  change pieceTangentialDivergence E G F X i j y =
    ∑ a : Fin 2, ∑ b : Fin 2, (inducedMetric g f y)⁻¹ a b * coordinateInner g (f y)
      (fderiv ℝ (actualFieldCoordinate E X c) (f y) (graphTangent f y a) +
        ∑ k : Fin 3, (∑ r : Fin 3, ∑ q : Fin 3,
          christoffel g (f y) r q k * graphTangent f y a r * actualFieldCoordinate E X c (f y) q) •
          coordinateVector 3 k) (graphTangent f y b) at hb
  rw [hb]
  rw [hcomp] at hn
  simpa only [ContinuousLinearMap.comp_apply, Function.comp_apply,
    graphTangent, coordinateConnection,
    metric_christoffel_matches g (actual_chart_metric_symmetric G.extension c)] using hn


set_option backward.isDefEq.respectTransparency false in
private theorem native_piece_image_in_exterior_interior
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count) (y : E2)
    (hy : y ∈ interior ((F.domain i).chart j).map.target) :
    pieceSphereCoordinate E F i j y ∈ E.toSphere '' (𝓡∂ 3).interior E.Carrier := by
  let q := F.parametrization i (((F.domain i).chart j).map.symm y)
  have hq : q ∉ S.boundary := AreaCertificates.sector_source_point_avoids_boundary F i j hy
  refine ⟨F.map q,?_,rfl⟩
  rw [← (𝓡∂ 3).compl_boundary]
  intro hb
  apply hq
  rw [← F.boundary_preimage]
  exact hb

set_option backward.isDefEq.respectTransparency false in
private theorem native_exterior_interior_image_open :
    IsOpen (E.toSphere '' (𝓡∂ 3).interior E.Carrier) := by
  rw [isOpen_iff_mem_nhds]
  rintro p ⟨q,hq,rfl⟩
  exact native_exterior_interior_ambient_nhds E q hq

set_option backward.isDefEq.respectTransparency false in
private theorem native_normal_trace_test_field (G : A7.SourceGeometry E)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count) (x : E2)
    (hx : x ∈ interior ((F.domain i).chart j).map.target)
    (c : SmoothAmbientChart ThreeSphere)
    (hsrc : pieceSphereCoordinate E F i j x ∈ c.chart.source) :
    let P := pieceSphereCoordinate E F i j
    let f := c.chart ∘ P
    let g := actualChartTensor G.extension c
    let H := fun y => normalProjection g (f y) (fderiv ℝ f y) (tracedAcceleration g f y)
    ∃ (X : InteriorSmoothVectorField E) (χ : ThreeSphere → ℝ) (V : Set ThreeSphere),
      IsOpen V ∧ P x ∈ V ∧ V ⊆ c.chart.source ∧
      closure {p | X.field p ≠ 0} ⊆ V ∧ (∀ p, 0 ≤ χ p) ∧ χ (P x) = 1 ∧
      (∀ q : S, E.toSphere (F.map q) ∈ V →
        q ∈ F.parametrization i '' ((F.domain i).interior ∩ ((F.domain i).chart j).map.source)) ∧
      ∀ y ∈ interior ((F.domain i).chart j).map.target, P y ∈ V →
        actualFieldCoordinate E X c (f y) = χ (P y) • H y := by
  classical
  let P := pieceSphereCoordinate E F i j
  let f := c.chart ∘ P
  let g := actualChartTensor G.extension c
  let U := interior ((F.domain i).chart j).map.target ∩ P ⁻¹' c.chart.source
  let H := fun y => normalProjection g (f y) (fderiv ℝ f y) (tracedAcceleration g f y)
  obtain ⟨hU,hf,hmap,hinj,hgram⟩ := native_actual_chart_data E G F i j c
  have hxU : x ∈ U := ⟨hx,hsrc⟩
  obtain ⟨A,W,R,hA,hfxA,hW,hxW,hWU,hR,hfWA,hRf⟩ :=
    exists_smooth_local_left_inverse f U hU hf x hxU (hinj x hxU)
  have hprops := A4GeometryBridges.actual_chart_tensor_metric_properties G.extension c
  have hgsdet (z : E3) (hz : z ∈ c.chart.target) : (g z).det ≠ 0 :=
    (actual_chart_metric_positive G.extension c hz).det_pos.ne'
  have hHs : ContDiffOn ℝ ∞ H U := normal_trace_smooth g c.chart.target
    c.chart.open_target hprops.1 hgsdet f U hU hf hmap
      (fun y hy => (hgram y hy).det_pos.ne')
  let A' := A ∩ R ⁻¹' W
  have hA' : IsOpen A' := hR.continuousOn.isOpen_inter_preimage hA hW
  have hfxA' : f x ∈ A' := by
    refine ⟨hfxA,?_⟩
    change R (f x) ∈ W
    rw [hRf x hxW]
    exact hxW
  have hHR : ContDiffOn ℝ ∞ (H ∘ R) A' :=
    hHs.comp (hR.mono inter_subset_left) (fun z hz => hWU hz.2)
  obtain ⟨B,hB,hpxB,hBsheet⟩ := native_piece_chart_small_ambient_isolation E F i j W hW
    (hWU.trans inter_subset_left) x hxW
  let V := ((B ∩ c.chart.source) ∩ c.chart ⁻¹' A') ∩
    (E.toSphere '' (𝓡∂ 3).interior E.Carrier)
  have hV : IsOpen V := by
    simpa only [V,inter_assoc] using
      (hB.inter (c.chart.continuousOn.isOpen_inter_preimage c.chart.open_source hA')).inter
      (native_exterior_interior_image_open E)
  have hpxV : P x ∈ V := ⟨⟨⟨hpxB,hsrc⟩,hfxA'⟩,
    native_piece_image_in_exterior_interior E F i j x hx⟩
  have hVc : V ⊆ c.chart.source := fun p hp => hp.1.1.2
  have hVext : V ⊆ E.toSphere '' (𝓡∂ 3).interior E.Carrier := inter_subset_right
  have hHRV : ContDiffOn ℝ ∞ (H ∘ R) (c.chart '' V) :=
    hHR.mono (by rintro z ⟨p,hp,rfl⟩; exact hp.1.2)
  obtain ⟨X,χ,_,_,hχ,hχone,hsup,hform⟩ := native_chart_cutoff_field E c V hV hVc hVext
    (P x) hpxV (H ∘ R) hHRV
  refine ⟨X,χ,V,hV,hpxV,hVc,hsup,hχ,hχone,?_,?_⟩
  · intro q hq
    obtain ⟨w,hw,he⟩ := (hBsheet q).mp hq.1.1.1
    refine ⟨w,⟨?_,hw.1⟩,he⟩
    have hwi := AreaCertificates.sector_chart_inverse_interior (F.domain i) j (hWU hw.2).1
    rw [((F.domain i).chart j).map.left_inv hw.1] at hwi
    exact hwi.1
  · intro y hy hpy
    have hyW : y ∈ W := by
      obtain ⟨w,hw,he⟩ := (hBsheet
        (F.parametrization i (((F.domain i).chart j).map.symm y))).mp hpy.1.1.1
      have hwq := (F.parametrization_embedding i).injective he
      have hw' := hw.2
      rw [hwq] at hw'
      change ((F.domain i).chart j).map
        (((F.domain i).chart j).map.symm y) ∈ W at hw'
      rw [((F.domain i).chart j).map.right_inv (interior_subset hy)] at hw'
      exact hw'
    change chartDifferential c (c.chart.symm (c.chart (P y)))
      (X.field (c.chart.symm (c.chart (P y)))) = χ (P y) • H y
    rw [c.chart.left_inv (hVc hpy), hform (P y) hpy]
    change χ (P y) • H (R (f y)) = χ (P y) • H y
    rw [hRf y hyW]


set_option backward.isDefEq.respectTransparency false in
private theorem native_whole_chart_divergence_density_integrable (G : A7.SourceGeometry E)
    (X : InteriorSmoothVectorField E) {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier) (i : Fin F.pieceCount)
    (j : Fin (F.domain i).count) :
    IntegrableOn (fun y => pieceTangentialDivergence E G F X i j y *
      sectorCoordinateDensity G.metric (F.map ∘ F.parametrization i) j y)
      (interior ((F.domain i).chart j).map.target) := by
  classical
  let Q := F.domain i
  letI : BorelSpace Q := ⟨rfl⟩
  letI : MetricSpace Q := TopologicalSpace.metrizableSpaceMetric Q
  let P := canonicalSectorPartition Q
  let c := (Q.chart j).map
  let B := fun a : Fin P.count => P.piece a ∩ Q.interior ∩ c.source
  let k := fun a : Fin P.count => (Q.chart (P.chartIndex a)).map
  let A := fun a : Fin P.count => k a '' B a
  let C := fun a : Fin P.count => c '' B a
  let I := fun l y => pieceTangentialDivergence E G F X i l y *
    sectorCoordinateDensity G.metric (F.map ∘ F.parametrization i) l y
  have hB (a : Fin P.count) : MeasurableSet (B a) :=
    ((P.measurable a).inter (AreaCertificates.sector_piece_boundary_closed Q).measurableSet.compl).inter
      ((Q.chart j).source_open.measurableSet)
  have hsubk (a : Fin P.count) : B a ⊆ (k a).source :=
    fun q hq => P.subordinate a hq.1.1
  have hsubc (a : Fin P.count) : B a ⊆ c.source := fun _ hq => hq.2
  have hA (a : Fin P.count) : MeasurableSet (A a) :=
    (hB a).image_of_continuousOn_injOn ((k a).continuousOn.mono (hsubk a))
      ((k a).injOn.mono (hsubk a))
  have hC (a : Fin P.count) : MeasurableSet (C a) :=
    (hB a).image_of_continuousOn_injOn (c.continuousOn.mono (hsubc a))
      (c.injOn.mono (hsubc a))
  have hAtrans (a : Fin P.count) :
      A a ⊆ interior (k a).target ∩ (k a).symm ⁻¹' c.source := by
    rintro y ⟨q,hq,rfl⟩
    refine ⟨?_,?_⟩
    · rw [← AreaCertificates.sector_chart_piece_interior Q (P.chartIndex a)]
      exact ⟨q,⟨hq.1.2,hsubk a hq⟩,rfl⟩
    · change (k a).symm ((k a) q) ∈ c.source
      rw [(k a).left_inv (hsubk a hq)]
      exact hq.2
  have hAC (a : Fin P.count) : (c ∘ (k a).symm) '' A a = C a := by
    ext y
    constructor
    · rintro ⟨_,⟨q,hq,rfl⟩,rfl⟩
      exact ⟨q,hq,by simp only [Function.comp_apply,(k a).left_inv (hsubk a hq)]⟩
    · rintro ⟨q,hq,rfl⟩
      exact ⟨(k a) q,⟨q,hq,rfl⟩,
        by simp only [Function.comp_apply,(k a).left_inv (hsubk a hq)]⟩
  have hiA (a : Fin P.count) : IntegrableOn (I (P.chartIndex a)) (A a) :=
    (native_sector_divergence_density_integrable E G X F ⟨i,a⟩).mono_set
      (image_mono (fun q hq => hq.1.1))
  have hiC (a : Fin P.count) : IntegrableOn (I j) (C a) := by
    rw [← hAC a]
    exact native_divergence_chart_integrable_transport E G X F i (P.chartIndex a) j
      (A a) (hA a) (hAtrans a) (hiA a)
  have hcover : (⋃ a, C a) = interior c.target := by
    rw [← image_iUnion]
    have he : (⋃ a, B a) = Q.interior ∩ c.source := by
      ext q
      constructor
      · intro hq
        obtain ⟨a,hqa⟩ := mem_iUnion.mp hq
        exact ⟨hqa.1.2,hqa.2⟩
      · intro hq
        have hqp : q ∈ ⋃ a, P.piece a := by rw [P.covers]; trivial
        obtain ⟨a,hqa⟩ := mem_iUnion.mp hqp
        exact mem_iUnion.mpr ⟨a,⟨⟨hqa,hq.1⟩,hq.2⟩⟩
    rw [he,AreaCertificates.sector_chart_piece_interior Q j]
  rw [← hcover]
  exact integrableOn_finite_iUnion.mpr hiC


set_option backward.isDefEq.respectTransparency false in
private theorem native_normal_trace_zero_of_actual_stationarity
    (G : A7.SourceGeometry E) {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier)
    (hstationary : ∀ X : InteriorSmoothVectorField E, pieceDivergenceSum E G F X = 0)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count) (x : E2)
    (hx : x ∈ interior ((F.domain i).chart j).map.target)
    (c : SmoothAmbientChart ThreeSphere)
    (hsrc : pieceSphereCoordinate E F i j x ∈ c.chart.source) :
    normalProjection (actualChartTensor G.extension c)
      ((c.chart ∘ pieceSphereCoordinate E F i j) x)
      (fderiv ℝ (c.chart ∘ pieceSphereCoordinate E F i j) x)
      (tracedAcceleration (actualChartTensor G.extension c)
        (c.chart ∘ pieceSphereCoordinate E F i j) x) = 0 := by
  let P := pieceSphereCoordinate E F i j
  let f := c.chart ∘ P
  let g := actualChartTensor G.extension c
  let H := fun y => normalProjection g (f y) (fderiv ℝ f y) (tracedAcceleration g f y)
  let D := interior ((F.domain i).chart j).map.target
  obtain ⟨X,χ,V,hV,hpxV,hVc,hsup,hχ,hχone,hsheet,hform⟩ :=
    native_normal_trace_test_field E G F i j x hx c hsrc
  have hprops := A4GeometryBridges.actual_chart_tensor_metric_properties G.extension c
  have hdata := native_actual_chart_data E G F i j c
  have hformula (y : E2) (hy : y ∈ D) (hpy : P y ∈ V) :
      pieceTangentialDivergence E G F X i j y =
        -(χ (P y) * coordinateInner g (f y) (H y) (H y)) := by
    have hsy : P y ∈ c.chart.source := hVc hpy
    have hpcont : ContinuousAt P y :=
      ((native_piece_smooth_and_rank E F i j).1.contMDiffAt
        (isOpen_interior.mem_nhds hy)).continuousAt
    have hn := hpcont (hV.mem_nhds hpy)
    have horth : ∀ᶠ z in 𝓝 y, ∀ k : Fin 2,
        coordinateInner g (f z) (actualFieldCoordinate E X c (f z)) (graphTangent f z k) = 0 := by
      filter_upwards [hn,isOpen_interior.mem_nhds hy] with z hz hzD
      intro k
      rw [hform z hzD hz,coordinateInner_smul_left]
      have ho := normalProjection_orthogonal g (f z) (fderiv ℝ f z)
        (tracedAcceleration g f z) (actual_chart_metric_symmetric G.extension c (f z))
        (hdata.2.2.2.2 z ⟨hzD,hVc hz⟩) (coordinateVector 2 k)
      change coordinateInner g (f z) (H z) (graphTangent f z k) = 0 at ho
      rw [ho,mul_zero]
    have hd := native_normal_field_divergence E G X F i j y hy c hsy horth
    change pieceTangentialDivergence E G F X i j y =
      -coordinateInner g (f y) (actualFieldCoordinate E X c (f y)) (tracedAcceleration g f y) at hd
    rw [hform y hy hpy,coordinateInner_smul_left] at hd
    have ht := normalProjection_inner_trace g (f y) (fderiv ℝ f y)
      (tracedAcceleration g f y) (actual_chart_metric_symmetric G.extension c (f y))
      (hdata.2.2.2.2 y ⟨hy,hsy⟩)
    change coordinateInner g (f y) (H y) (tracedAcceleration g f y) =
      coordinateInner g (f y) (H y) (H y) at ht
    rwa [ht] at hd
  have hnonpos (y : E2) (hy : y ∈ D) : pieceTangentialDivergence E G F X i j y ≤ 0 := by
    by_cases hpy : P y ∈ V
    · rw [hformula y hy hpy]
      apply neg_nonpos.mpr
      apply mul_nonneg (hχ _)
      by_cases hH : H y = 0
      · simp [hH,coordinateInner]
      · exact (hprops.2.2 (f y) (c.chart.map_source (hVc hpy)) (H y) hH).le
    · rw [native_divergence_zero_off_field_support E G X F i j y
        (fun h => hpy (hsup h))]
  let ρ := sectorCoordinateDensity G.metric (F.map ∘ F.parametrization i) j
  let L := fun y => -(pieceTangentialDivergence E G F X i j y * ρ y)
  have hcont : ContinuousOn L D :=
    (((native_sector_divergence_continuous E G X F i j).mul
      (native_sector_density_continuous G.metric F i j)).neg).mono interior_subset
  have hint : IntegrableOn L D :=
    (native_whole_chart_divergence_density_integrable E G X F i j).neg
  have hnonneg : ∀ᵐ y ∂volume.restrict D, 0 ≤ L y := by
    filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with y hy
    exact neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg (hnonpos y hy) (Real.sqrt_nonneg _))
  have hlocal := native_piece_stationarity_in_one_chart E G F hstationary i j X
    (fun q hq => hsheet q (hsup hq))
  have hLI : (∫ y in D, L y) = 0 := by
    rw [integral_neg]
    change -(∫ y in D, pieceTangentialDivergence E G F X i j y * ρ y) = 0
    rw [hlocal,neg_zero]
  have heq := Measure.eqOn_open_of_ae_eq ((integral_eq_zero_iff_of_nonneg_ae hnonneg hint).mp hLI)
    isOpen_interior hcont continuousOn_const
  have hLx : L x = 0 := heq hx
  have hρx : 0 < ρ x := Real.sqrt_pos.mpr
    (native_sector_gram_positive G.metric F i j x (interior_subset hx)).det_pos
  have hdx : pieceTangentialDivergence E G F X i j x = 0 := by
    have hh : pieceTangentialDivergence E G F X i j x * ρ x = 0 := neg_eq_zero.mp hLx
    exact (mul_eq_zero.mp hh).resolve_right hρx.ne'
  have hnorm : coordinateInner g (f x) (H x) (H x) = 0 := by
    rw [hformula x hx hpxV,hχone,one_mul] at hdx
    exact neg_eq_zero.mp hdx
  change H x = 0
  by_contra hne
  exact (hprops.2.2 (f x) (c.chart.map_source hsrc) (H x) hne).ne' hnorm

/-- Minimality of every actual whole piece in every actual ambient chart,
derived from the native stationarity functional. -/
theorem native_minimality_of_actual_stationarity (G : A7.SourceGeometry E)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (hstationary : ∀ X : InteriorSmoothVectorField E, pieceDivergenceSum E G F X = 0) :
    PiecesMinimal E G F := by
  intro i j
  obtain ⟨hsmooth,hrank⟩ := native_piece_smooth_and_rank E F i j
  refine ⟨hsmooth,hrank,?_⟩
  intro c
  obtain ⟨hU,hf,hmap,hinj,hgram⟩ := native_actual_chart_data E G F i j c
  refine ⟨hf,?_⟩
  intro x hx
  apply (normalProjection_zero_iff_range (actualChartTensor G.extension c)
    ((c.chart ∘ pieceSphereCoordinate E F i j) x)
    (fderiv ℝ (c.chart ∘ pieceSphereCoordinate E F i j) x)
    (tracedAcceleration (actualChartTensor G.extension c) (c.chart ∘ pieceSphereCoordinate E F i j) x)
    (actual_chart_metric_symmetric G.extension c _)
    ((A4GeometryBridges.actual_chart_tensor_metric_properties G.extension c).2.2 _ (hmap hx))
    (hgram x hx)).mp
  exact native_normal_trace_zero_of_actual_stationarity E G F hstationary i j x hx.1 c hx.2


/-- The stationarity and whole-piece minimality components of original A2,
with stationarity produced from the fixed-boundary minimum and minimality
proved by the localized actual normal test field. -/
theorem A2_original_stationarity_and_minimality
    (G : A7.SourceGeometry E) (J : LongitudeFoliation.{u} E)
    {S R : CompactOrientedSurface.{u}} [ConnectedSpace S]
    (F : GeometricPiecewiseSurface S E.Carrier)
    (hF_incompressible : F.Incompressible) (hF_boundary : J.BoundaryIn F.map)
    (Fprime : GeometricPiecewiseSurface R E.Carrier)
    (hminimum : FixedBoundaryMinimizer E G.metric F Fprime) :
    (∀ X : InteriorSmoothVectorField E, pieceDivergenceSum E G Fprime X = 0) ∧
    PiecesMinimal E G Fprime := by
  refine ⟨A2_original_stationarity E G F Fprime hminimum, ?_⟩
  apply native_minimality_of_actual_stationarity E G Fprime
  exact A2_original_stationarity E G F Fprime hminimum


open A2MetricFlux


/-- The actual metric in the actual ambient chart, with its paid smoothness,
symmetry and positive definiteness. -/
def nativeActualCoordinateMetric (G : A7.SourceGeometry E)
    (c : SmoothAmbientChart ThreeSphere) : CoordinateMetric c.chart.target where
  tensor := actualChartTensor G.extension c
  smooth := (A4GeometryBridges.actual_chart_tensor_metric_properties G.extension c).1
  symmetric := (A4GeometryBridges.actual_chart_tensor_metric_properties G.extension c).2.1
  positive := (A4GeometryBridges.actual_chart_tensor_metric_properties G.extension c).2.2

/-- The already paid native fixed-chart divergence has precisely the metric
trace expected by the paid halfbox flux theorem. -/
theorem native_piece_metric_flux_divergence (G : A7.SourceGeometry E)
    (X : InteriorSmoothVectorField E) {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier) (i : Fin F.pieceCount)
    (j : Fin (F.domain i).count) (y : E2)
    (hy : y ∈ interior ((F.domain i).chart j).map.target)
    (c : SmoothAmbientChart ThreeSphere)
    (hsrc : pieceSphereCoordinate E F i j y ∈ c.chart.source) :
    pieceTangentialDivergence E G F X i j y =
      metricTangentialDivergence (actualChartTensor G.extension c)
        (actualFieldCoordinate E X c) ((c.chart ∘ pieceSphereCoordinate E F i j) y)
        (fderiv ℝ (c.chart ∘ pieceSphereCoordinate E F i j) y) := by
  exact native_piece_divergence_in_actual_chart E G X F i j y hy c hsrc

set_option backward.isDefEq.respectTransparency false in
theorem native_piece_metric_flux_density (G : A7.SourceGeometry E)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count) (y : E2)
    (hy : y ∈ interior ((F.domain i).chart j).map.target)
    (c : SmoothAmbientChart ThreeSphere)
    (hsrc : pieceSphereCoordinate E F i j y ∈ c.chart.source) :
    metricDensity (actualChartTensor G.extension c)
      ((c.chart ∘ pieceSphereCoordinate E F i j) y)
      (fderiv ℝ (c.chart ∘ pieceSphereCoordinate E F i j) y) =
      sectorCoordinateDensity G.metric (F.map ∘ F.parametrization i) j y := by
  have hd : fderivWithin ℝ (c.chart ∘ pieceSphereCoordinate E F i j)
      ((F.domain i).chart j).map.target y =
      fderiv ℝ (c.chart ∘ pieceSphereCoordinate E F i j) y :=
    fderivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hy)
  have hq : metricGram (actualChartTensor G.extension c)
      ((c.chart ∘ pieceSphereCoordinate E F i j) y)
      (fderiv ℝ (c.chart ∘ pieceSphereCoordinate E F i j) y) =
      sectorCoordinateGram G.metric (F.map ∘ F.parametrization i) j y := by
    ext a b
    have h := actual_piece_gram_in_fixed_chart E G F i j y (interior_subset hy) c hsrc a b
    rw [hd] at h
    exact h
  change Real.sqrt _ = Real.sqrt _
  rw [hq]

set_option backward.isDefEq.respectTransparency false in
theorem native_piece_metric_flux_normalTrace_zero (G : A7.SourceGeometry E)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (hminimal : PiecesMinimal E G F) (i : Fin F.pieceCount)
    (j : Fin (F.domain i).count) (y : E2)
    (hy : y ∈ interior ((F.domain i).chart j).map.target)
    (c : SmoothAmbientChart ThreeSphere)
    (hsrc : pieceSphereCoordinate E F i j y ∈ c.chart.source) :
    normalTrace (actualChartTensor G.extension c)
      (c.chart ∘ pieceSphereCoordinate E F i j) y = 0 := by
  apply (normalProjection_zero_iff_range _ _ _ _
    (actual_chart_metric_symmetric G.extension c _)
    ((nativeActualCoordinateMetric E G c).positive _ (c.chart.map_source hsrc))
    ((native_actual_chart_data E G F i j c).2.2.2.2 y ⟨hy,hsrc⟩)).mpr
  exact ((hminimal i j).2.2 c).2 y ⟨hy,hsrc⟩

/-- Minimality removes the paid flux theorem's actual normal-curvature term,
and both the divergence and density agree with the original native integrand. -/
theorem native_piece_metric_flux_integrand (G : A7.SourceGeometry E)
    (X : InteriorSmoothVectorField E) {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier) (hminimal : PiecesMinimal E G F)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count) (y : E2)
    (hy : y ∈ interior ((F.domain i).chart j).map.target)
    (c : SmoothAmbientChart ThreeSphere)
    (hsrc : pieceSphereCoordinate E F i j y ∈ c.chart.source) :
    let f := c.chart ∘ pieceSphereCoordinate E F i j
    let g := actualChartTensor G.extension c
    let W := actualFieldCoordinate E X c
    metricDensity g (f y) (fderiv ℝ f y) *
      (metricTangentialDivergence g W (f y) (fderiv ℝ f y) +
        coordinateInner g (f y) (normalTrace g f y) (W (f y))) =
      pieceTangentialDivergence E G F X i j y *
        sectorCoordinateDensity G.metric (F.map ∘ F.parametrization i) j y := by
  dsimp only
  rw [native_piece_metric_flux_density E G F i j y hy c hsrc,
    native_piece_metric_flux_normalTrace_zero E G F hminimal i j y hy c hsrc,
    ← native_piece_metric_flux_divergence E G X F i j y hy c hsrc]
  simp [coordinateInner, mul_comm]


/-- An actual interior point of one whole piece is outside the entire
range of every other whole piece. The cut-set boundary cannot contaminate
the open native divergence integrals. -/
private theorem native_piece_interior_avoids_other_range
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i r : Fin F.pieceCount) (hir : i ≠ r) (q : F.domain i)
    (hq : q ∈ (F.domain i).interior) :
    F.parametrization i q ∉ range (F.parametrization r) := by
  intro hother
  exact native_piece_interior_avoids_cut E F i ⟨q,hq,rfl⟩
    (native_distinct_piece_intersection_subset_cut E F i r hir ⟨⟨q,rfl⟩,hother⟩)

/-- Canonical native rows localize onto exactly the two actual selected
piece charts. Only a support containment is needed here; no boundary
flux or stationarity conclusion is supplied as a premise. -/
theorem native_two_sheet_divergence_sum_localization (G : A7.SourceGeometry E)
    (X : InteriorSmoothVectorField E) {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier)
    (i r : Fin F.pieceCount) (hir : i ≠ r)
    (j : Fin (F.domain i).count) (l : Fin (F.domain r).count)
    (hsupport : ∀ q : S, E.toSphere (F.map q) ∈ closure {p | X.field p ≠ 0} →
      q ∈ F.parametrization i '' ((F.domain i).chart j).map.source ∪
        F.parametrization r '' ((F.domain r).chart l).map.source) :
    pieceDivergenceSum E G F X =
      (∫ y in interior ((F.domain i).chart j).map.target,
        pieceTangentialDivergence E G F X i j y *
          sectorCoordinateDensity G.metric (F.map ∘ F.parametrization i) j y) +
      (∫ y in interior ((F.domain r).chart l).map.target,
        pieceTangentialDivergence E G F X r l y *
          sectorCoordinateDensity G.metric (F.map ∘ F.parametrization r) l y) := by
  classical
  have hi (k : Fin (F.domain i).count) (y : E2)
      (hy : y ∈ interior ((F.domain i).chart k).map.target)
      (hnot : ((F.domain i).chart k).map.symm y ∉ ((F.domain i).chart j).map.source) :
      pieceTangentialDivergence E G F X i k y = 0 := by
    apply native_divergence_zero_off_field_support E G X F i k y
    intro hp
    rcases hsupport (F.parametrization i (((F.domain i).chart k).map.symm y)) hp with h | h
    · obtain ⟨q,hq,he⟩ := h
      exact hnot ((F.parametrization_embedding i).injective he ▸ hq)
    · obtain ⟨q,_,he⟩ := h
      exact native_piece_interior_avoids_other_range E F i r hir _
        (AreaCertificates.sector_chart_inverse_interior (F.domain i) k hy).1 ⟨q,he⟩
  have hr (k : Fin (F.domain r).count) (y : E2)
      (hy : y ∈ interior ((F.domain r).chart k).map.target)
      (hnot : ((F.domain r).chart k).map.symm y ∉ ((F.domain r).chart l).map.source) :
      pieceTangentialDivergence E G F X r k y = 0 := by
    apply native_divergence_zero_off_field_support E G X F r k y
    intro hp
    rcases hsupport (F.parametrization r (((F.domain r).chart k).map.symm y)) hp with h | h
    · obtain ⟨q,_,he⟩ := h
      exact native_piece_interior_avoids_other_range E F r i (Ne.symm hir) _
        (AreaCertificates.sector_chart_inverse_interior (F.domain r) k hy).1 ⟨q,he⟩
    · obtain ⟨q,hq,he⟩ := h
      exact hnot ((F.parametrization_embedding r).injective he ▸ hq)
  have hother (a : Fin F.pieceCount) (hai : a ≠ i) (har : a ≠ r)
      (k : Fin (F.domain a).count) (y : E2)
      (hy : y ∈ interior ((F.domain a).chart k).map.target) :
      pieceTangentialDivergence E G F X a k y = 0 := by
    apply native_divergence_zero_off_field_support E G X F a k y
    intro hp
    rcases hsupport (F.parametrization a (((F.domain a).chart k).map.symm y)) hp with h | h
    · obtain ⟨q,_,he⟩ := h
      exact native_piece_interior_avoids_other_range E F a i hai _
        (AreaCertificates.sector_chart_inverse_interior (F.domain a) k hy).1 ⟨q,he⟩
    · obtain ⟨q,_,he⟩ := h
      exact native_piece_interior_avoids_other_range E F a r har _
        (AreaCertificates.sector_chart_inverse_interior (F.domain a) k hy).1 ⟨q,he⟩
  unfold pieceDivergenceSum
  rw [Finset.sum_eq_add_of_mem i r (Finset.mem_univ _) (Finset.mem_univ _) hir]
  · rw [native_divergence_canonical_row_localization E G X F i j hi,
      native_divergence_canonical_row_localization E G X F r l hr]
  · intro a _ ha
    apply Finset.sum_eq_zero
    intro b _
    apply integral_eq_zero_of_ae
    filter_upwards [native_sector_cell_ae_interior E F ⟨a,b⟩] with y hy
    exact mul_eq_zero_of_left (hother a ha.1 ha.2 _ y hy) _

/-- Native stationarity gives the sum of the two actual full chart
integrals equal to zero before the paid halfbox boundary flux is applied. -/
theorem native_two_sheet_stationarity_in_charts (G : A7.SourceGeometry E)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (hstationary : ∀ X : InteriorSmoothVectorField E, pieceDivergenceSum E G F X = 0)
    (X : InteriorSmoothVectorField E) (i r : Fin F.pieceCount) (hir : i ≠ r)
    (j : Fin (F.domain i).count) (l : Fin (F.domain r).count)
    (hsupport : ∀ q : S, E.toSphere (F.map q) ∈ closure {p | X.field p ≠ 0} →
      q ∈ F.parametrization i '' ((F.domain i).chart j).map.source ∪
        F.parametrization r '' ((F.domain r).chart l).map.source) :
    (∫ y in interior ((F.domain i).chart j).map.target,
      pieceTangentialDivergence E G F X i j y *
        sectorCoordinateDensity G.metric (F.map ∘ F.parametrization i) j y) +
    (∫ y in interior ((F.domain r).chart l).map.target,
      pieceTangentialDivergence E G F X r l y *
        sectorCoordinateDensity G.metric (F.map ∘ F.parametrization r) l y) = 0 := by
  rw [← native_two_sheet_divergence_sum_localization E G X F i r hir j l hsupport]
  exact hstationary X


/-- The actual ambient two-sheet cover gives the exact source-chart support
containment needed by the native canonical-row localization. -/
theorem native_two_sheet_support_from_ambient_cover
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (X : InteriorSmoothVectorField E) (i r : Fin F.pieceCount)
    (j : Fin (F.domain i).count) (l : Fin (F.domain r).count)
    (V : Set ThreeSphere) (hsupport : closure {p | X.field p ≠ 0} ⊆ V)
    (hcover : E.toSphere '' F.image ∩ V =
      ((E.toSphere ∘ F.map ∘ F.parametrization i) '' ((F.domain i).chart j).map.source ∪
        (E.toSphere ∘ F.map ∘ F.parametrization r) '' ((F.domain r).chart l).map.source) ∩ V) :
    ∀ q : S, E.toSphere (F.map q) ∈ closure {p | X.field p ≠ 0} →
      q ∈ F.parametrization i '' ((F.domain i).chart j).map.source ∪
        F.parametrization r '' ((F.domain r).chart l).map.source := by
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  intro q hq
  have hp : E.toSphere (F.map q) ∈ E.toSphere '' F.image ∩ V :=
    ⟨⟨F.map q,⟨q,rfl⟩,rfl⟩,hsupport hq⟩
  rw [hcover] at hp
  rcases hp.1 with h | h
  · obtain ⟨p,hp,he⟩ := h
    apply Or.inl
    exact ⟨p,hp,F.embedding.injective (hinc.isEmbedding.injective he)⟩
  · obtain ⟨p,hp,he⟩ := h
    apply Or.inr
    exact ⟨p,hp,F.embedding.injective (hinc.isEmbedding.injective he)⟩

/-- Original stationarity localizes in an actual ambient seam window to the
sum of the two selected chart integrals, with no auxiliary row data. -/
theorem native_two_sheet_stationarity_in_ambient_window (G : A7.SourceGeometry E)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (hstationary : ∀ X : InteriorSmoothVectorField E, pieceDivergenceSum E G F X = 0)
    (X : InteriorSmoothVectorField E) (i r : Fin F.pieceCount) (hir : i ≠ r)
    (j : Fin (F.domain i).count) (l : Fin (F.domain r).count)
    (V : Set ThreeSphere) (hsupport : closure {p | X.field p ≠ 0} ⊆ V)
    (hcover : E.toSphere '' F.image ∩ V =
      ((E.toSphere ∘ F.map ∘ F.parametrization i) '' ((F.domain i).chart j).map.source ∪
        (E.toSphere ∘ F.map ∘ F.parametrization r) '' ((F.domain r).chart l).map.source) ∩ V) :
    (∫ y in interior ((F.domain i).chart j).map.target,
      pieceTangentialDivergence E G F X i j y *
        sectorCoordinateDensity G.metric (F.map ∘ F.parametrization i) j y) +
    (∫ y in interior ((F.domain r).chart l).map.target,
      pieceTangentialDivergence E G F X r l y *
        sectorCoordinateDensity G.metric (F.map ∘ F.parametrization r) l y) = 0 := by
  exact native_two_sheet_stationarity_in_charts E G F hstationary X i r hir j l
    (native_two_sheet_support_from_ambient_cover E F X i r j l V hsupport hcover)


/-- Native divergence integrals restrict to any actual coordinate window
containing the pullback of the ambient field support. -/
theorem native_piece_divergence_integral_restrict_to_supported_window
    (G : A7.SourceGeometry E) (X : InteriorSmoothVectorField E)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count)
    (A : Set E2) (hA : A ⊆ interior ((F.domain i).chart j).map.target)
    (hsupport : ∀ y ∈ interior ((F.domain i).chart j).map.target,
      pieceSphereCoordinate E F i j y ∈ closure {p | X.field p ≠ 0} → y ∈ A) :
    (∫ y in interior ((F.domain i).chart j).map.target,
      pieceTangentialDivergence E G F X i j y *
        sectorCoordinateDensity G.metric (F.map ∘ F.parametrization i) j y) =
    (∫ y in A, pieceTangentialDivergence E G F X i j y *
      sectorCoordinateDensity G.metric (F.map ∘ F.parametrization i) j y) := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero isOpen_interior.measurableSet hA
  intro y hy
  rw [native_divergence_zero_off_field_support E G X F i j y
    (fun hp => hy.2 (hsupport y hy.1 hp)),zero_mul]

/-- Stationarity in an actual two-sheet ambient cover remains valid on the
actual selected interior halfbox images once they contain the support. -/
theorem native_two_sheet_stationarity_in_supported_windows (G : A7.SourceGeometry E)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (hstationary : ∀ X : InteriorSmoothVectorField E, pieceDivergenceSum E G F X = 0)
    (X : InteriorSmoothVectorField E) (i r : Fin F.pieceCount) (hir : i ≠ r)
    (j : Fin (F.domain i).count) (l : Fin (F.domain r).count)
    (V : Set ThreeSphere) (hsupport : closure {p | X.field p ≠ 0} ⊆ V)
    (hcover : E.toSphere '' F.image ∩ V =
      ((E.toSphere ∘ F.map ∘ F.parametrization i) '' ((F.domain i).chart j).map.source ∪
        (E.toSphere ∘ F.map ∘ F.parametrization r) '' ((F.domain r).chart l).map.source) ∩ V)
    (A B : Set E2)
    (hA : A ⊆ interior ((F.domain i).chart j).map.target)
    (hB : B ⊆ interior ((F.domain r).chart l).map.target)
    (hsA : ∀ y ∈ interior ((F.domain i).chart j).map.target,
      pieceSphereCoordinate E F i j y ∈ closure {p | X.field p ≠ 0} → y ∈ A)
    (hsB : ∀ y ∈ interior ((F.domain r).chart l).map.target,
      pieceSphereCoordinate E F r l y ∈ closure {p | X.field p ≠ 0} → y ∈ B) :
    (∫ y in A, pieceTangentialDivergence E G F X i j y *
      sectorCoordinateDensity G.metric (F.map ∘ F.parametrization i) j y) +
    (∫ y in B, pieceTangentialDivergence E G F X r l y *
      sectorCoordinateDensity G.metric (F.map ∘ F.parametrization r) l y) = 0 := by
  have h := native_two_sheet_stationarity_in_ambient_window E G F hstationary X i r hir
    j l V hsupport hcover
  rwa [native_piece_divergence_integral_restrict_to_supported_window E G X F i j A hA hsA,
    native_piece_divergence_integral_restrict_to_supported_window E G X F r l B hB hsB] at h


set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3000000 in
/-- Pointwise boundary balance from the actual metric weak flux identity.
The tests are the original admissible interior smooth vector fields, and
are constructed here by an ambient cutoff, rather than supplied traces. -/
theorem native_boundary_vector_zero_of_actual_weak_flux
    (G : A7.SourceGeometry E) (c : SmoothAmbientChart ThreeSphere)
    (edge : ℝ → ThreeSphere) (l r : ℝ)
    (he : ContinuousOn edge (Icc l r))
    (hemb : IsEmbedding (fun t : Icc l r => edge t))
    (hc : MapsTo edge (Icc l r) c.chart.source)
    (eta : ℝ → E3) (heta : ContinuousOn eta (Icc l r))
    (speed : ℝ → ℝ) (hspeed : ContinuousOn speed (Icc l r))
    (hpos : ∀ t ∈ Ioo l r, 0 < speed t)
    (V : Set ThreeSphere) (hV : IsOpen V)
    (hVc : V ⊆ c.chart.source)
    (hVE : V ⊆ E.toSphere '' (𝓡∂ 3).interior E.Carrier)
    (hweak : ∀ X : InteriorSmoothVectorField E,
      closure {p | X.field p ≠ 0} ⊆ V →
      (∫ t in Icc l r, coordinateInner (actualChartTensor G.extension c)
        (c.chart (edge t)) (eta t)
        (actualFieldCoordinate E X c (c.chart (edge t))) * speed t) = 0)
    (t0 : ℝ) (ht0 : t0 ∈ Ioo l r) (ht0V : edge t0 ∈ V) : eta t0 = 0 := by
  by_contra hne
  let D := Icc l r
  let v := eta t0
  let g := actualChartTensor G.extension c
  let ce := c.chart ∘ edge
  have hce : ContinuousOn ce D := c.chart.continuousOn.comp he hc
  have htarget : MapsTo ce D c.chart.target := fun t ht => c.chart.map_source (hc ht)
  have hg : ∀ a b, ContinuousOn (fun t => g (ce t) a b) D := fun a b =>
    ((nativeActualCoordinateMetric E G c).smooth a b).continuousOn.comp hce htarget
  let beta := fun t => coordinateInner g (ce t) v (eta t) * speed t
  have hbeta : ContinuousOn beta D := by
    apply ContinuousOn.mul _ hspeed
    apply continuousOn_finsetSum
    intro a ha
    apply continuousOn_finsetSum
    intro b hb
    exact ((hg a b).mul continuousOn_const).mul
      ((EuclideanSpace.proj b).continuous.comp_continuousOn heta)
  have ht0D : t0 ∈ D := ⟨ht0.1.le,ht0.2.le⟩
  have hbeta0 : 0 < beta t0 := mul_pos
    ((nativeActualCoordinateMetric E G c).positive (ce t0) (htarget ht0D) v hne) (hpos t0 ht0)
  let ed : C(D,ThreeSphere) := ⟨fun t => edge t, he.domRestrict⟩
  let bd : C(D,ℝ) := ⟨fun t => beta t, hbeta.domRestrict⟩
  obtain ⟨U0,hU0,hpU0,hpre⟩ := native_compact_parameter_window ed hemb
    ⟨t0,ht0D⟩ (bd ⁻¹' Ioi 0) (isOpen_Ioi.preimage bd.continuous) hbeta0
  let U := V ∩ U0
  have hU : IsOpen U := hV.inter hU0
  have hUE : U ⊆ E.toSphere '' (𝓡∂ 3).interior E.Carrier :=
    inter_subset_left.trans hVE
  obtain ⟨X,chi,hchi,hcompact,hchinonneg,hchi0,hsupport,hform⟩ :=
    native_chart_cutoff_field E c U hU (inter_subset_left.trans hVc) hUE
      (edge t0) ⟨ht0V,hpU0⟩ (fun _ => v) contDiffOn_const
  let F := fun t => coordinateInner g (ce t) (eta t)
    (actualFieldCoordinate E X c (ce t)) * speed t
  have hfield : ContinuousOn (fun t => actualFieldCoordinate E X c (ce t)) D := by
    have hh : ContinuousOn (actualFieldCoordinate E X c) c.chart.target := by
      intro z hz
      exact (actual_field_coordinate_smooth E X c z hz).continuousAt.continuousWithinAt
    exact hh.comp hce htarget
  have hF : ContinuousOn F D := by
    apply ContinuousOn.mul _ hspeed
    apply continuousOn_finsetSum
    intro a ha
    apply continuousOn_finsetSum
    intro b hb
    exact ((hg a b).mul ((EuclideanSpace.proj a).continuous.comp_continuousOn heta)).mul
      ((EuclideanSpace.proj b).continuous.comp_continuousOn hfield)
  have hfield_eq (t : ℝ) (ht : t ∈ D) (heU : edge t ∈ U) :
      actualFieldCoordinate E X c (ce t) = chi (edge t) • v := by
    change chartDifferential c (c.chart.symm (c.chart (edge t)))
      (X.field (c.chart.symm (c.chart (edge t)))) = _
    rw [c.chart.left_inv (hc ht)]
    exact hform (edge t) heU
  have hnonneg (t : ℝ) (ht : t ∈ D) : 0 ≤ F t := by
    by_cases heU : edge t ∈ U
    · have htd : ed ⟨t,ht⟩ ∈ U0 := heU.2
      have hbt_sub := hpre (show ed ⟨t,ht⟩ ∈ U0 from htd)
      have hbt : 0 < beta t := hbt_sub
      change 0 ≤ coordinateInner g (ce t) (eta t)
        (actualFieldCoordinate E X c (ce t)) * speed t
      rw [hfield_eq t ht heU,
        coordinate_metric_symmetric g (actual_chart_metric_symmetric G.extension c)
          (ce t) (eta t) (chi (edge t) • v), coordinateInner_smul_left,mul_assoc]
      exact mul_nonneg (hchinonneg _) hbt.le
    · have hxzero : X.field (edge t) = 0 := by
        by_contra hn
        exact heU (hsupport (subset_closure hn))
      have hwzero : actualFieldCoordinate E X c (ce t) = 0 := by
        change chartDifferential c (c.chart.symm (c.chart (edge t)))
          (X.field (c.chart.symm (c.chart (edge t)))) = 0
        rw [c.chart.left_inv (hc ht),hxzero,map_zero]
      simp [F,hwzero,coordinateInner]
  have hint : IntegrableOn F D := hF.integrableOn_compact isCompact_Icc
  have hnn : ∀ᵐ t ∂volume.restrict D, 0 ≤ F t := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hnonneg t ht
  have hInt : (∫ t in D,F t) = 0 := hweak X (hsupport.trans inter_subset_left)
  have hAE := (integral_eq_zero_iff_of_nonneg_ae hnn hint).mp hInt
  have hEq := Measure.eqOn_open_of_ae_eq
    (ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self hAE)
    isOpen_Ioo (hF.mono Ioo_subset_Icc_self) continuousOn_const
  have hzero : F t0 = 0 := hEq ht0
  have hform0 := hfield_eq t0 ht0D ⟨ht0V,hpU0⟩
  rw [hchi0,one_smul] at hform0
  change coordinateInner g (ce t0) v
    (actualFieldCoordinate E X c (ce t0)) * speed t0 = 0 at hzero
  rw [hform0] at hzero
  exact hbeta0.ne' hzero

section
open scoped Manifold ContDiff
open Set Topology MeasureTheory Matrix Filter
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
set_option backward.isDefEq.respectTransparency false in
/-- The actual transported native conormal has exactly the closed-chart
differential coordinate used in the metric halfbox formula. -/
theorem native_actual_piece_conormal_chart_coordinate
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count)
    (y v : E2) (hy : y ∈ ((F.domain i).chart j).map.target)
    (p : ThreeSphere) (heq : pieceSphereCoordinate E F i j y = p)
    (c : SmoothAmbientChart ThreeSphere) (hp : p ∈ c.chart.source) :
    chartDifferential c p (actualPieceConormal E F i j y v p heq) =
      fderivWithin ℝ (c.chart ∘ pieceSphereCoordinate E F i j)
        ((F.domain i).chart j).map.target y v := by
  subst p
  let D := ((F.domain i).chart j).map.target
  let P := pieceSphereCoordinate E F i j
  have hud : UniqueMDiffWithinAt 𝓘(ℝ,E2) D y := by
    dsimp only [D]
    rw [((F.domain i).chart j).target_eq]
    exact (SectorModel.uniqueDiffOn_domain ((F.domain i).chart j).model y
      (by simpa only [((F.domain i).chart j).target_eq] using hy)).uniqueMDiffWithinAt
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  have hf : MDifferentiableWithinAt 𝓘(ℝ,E2) (𝓡 3) P D y :=
    hinc.contMDiff.mdifferentiableAt (by simp) |>.comp_mdifferentiableWithinAt y
      ((F.piece_c1 i j y hy).mdifferentiableWithinAt one_ne_zero)
  have hc : MDifferentiableAt (𝓡 3) 𝓘(ℝ,E3) c.chart (P y) :=
    (c.smooth.contMDiffAt (c.chart.open_source.mem_nhds hp)).mdifferentiableAt (by simp)
  have hd := mfderivWithin_comp y hc.mdifferentiableWithinAt hf
    (s := D) (u := univ) (by simp) hud
  rw [mfderivWithin_univ,mfderivWithin_eq_fderivWithin] at hd
  exact (congrArg (fun L => L v) hd).symm

set_option backward.isDefEq.respectTransparency false in
/-- The SAME ambient metric pairs the original tangent vectors exactly as
the actual fixed-chart tensor pairs their coordinates. -/
theorem native_tangent_pair_metric_in_chart
    (G : A7.SourceGeometry E) (c : SmoothAmbientChart ThreeSphere)
    (p : ThreeSphere) (hp : p ∈ c.chart.source)
    (v w : TangentSpace (𝓡 3) p) :
    coordinateInner (actualChartTensor G.extension c) (c.chart p)
      (chartDifferential c p v) (chartDifferential c p w) = G.extension.inner p v w := by
  rw [actual_chart_inner G.extension c,
    actual_chart_inverse_comp c p hp v,actual_chart_inverse_comp c p hp w,
    c.chart.left_inv hp]

set_option backward.isDefEq.respectTransparency false in
/-- Vanishing of the actual sum in one fixed chart is equivalent to the
original tangent-bundle balance, with no sign or orientation change. -/
theorem native_actual_conormal_balance_of_chart_balance
    (c : SmoothAmbientChart ThreeSphere) (p : ThreeSphere) (hp : p ∈ c.chart.source)
    (v w : TangentSpace (𝓡 3) p)
    (h : chartDifferential c p v + chartDifferential c p w = 0) : v+w=0 := by
  have hh := congrArg (inverseChartDifferential c (c.chart p)) h
  simpa only [map_add,map_zero,actual_chart_inverse_comp c p hp] using hh


end


section
open scoped Manifold ContDiff
open Set Topology MeasureTheory Matrix Filter
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
set_option backward.isDefEq.respectTransparency false in
/-- A continuous actual tangent section has continuous coordinates in the
same smooth ambient chart. No auxiliary normal-field provider is used. -/
theorem native_tangent_section_chart_continuousOn
    {P : Type*} [TopologicalSpace P] (D : Set P)
    (c : SmoothAmbientChart ThreeSphere) (edge : P → ThreeSphere)
    (nu : ∀ t, TangentSpace (𝓡 3) (edge t))
    (hnu : ContinuousOn (fun t => Bundle.TotalSpace.mk' (Euc 3) (edge t) (nu t)) D)
    (hc : MapsTo edge D c.chart.source) :
    ContinuousOn (fun t => chartDifferential c (edge t) (nu t)) D := by
  have ht := c.smooth.continuousOn_tangentMapWithin (by simp)
    c.chart.open_source.uniqueMDiffOn
  have htc := ht.comp hnu (fun t ht => hc ht)
  have hco := (tangentBundleModelSpaceHomeomorph 𝓘(ℝ,E3)).continuous.comp_continuousOn htc
  have hs := continuous_snd.comp_continuousOn hco
  apply hs.congr
  intro t ht
  symm
  change (NormedSpace.fromTangentSpace (c.chart (edge t)))
    (mfderivWithin (𝓡 3) 𝓘(ℝ,E3) c.chart c.chart.source (edge t) (nu t)) = _
  rw [mfderivWithin_of_mem_nhds (c.chart.open_source.mem_nhds (hc ht))]
  rfl


end


section
open scoped Manifold ContDiff
open Set Topology MeasureTheory Matrix Filter
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
open SeifertSurfaces.OriginalEndpoints.A2MetricFlux
set_option backward.isDefEq.respectTransparency false in
/-- Closed native C1 and positive Gram data on the actual relative ambient
chart domain, retaining the original differential even on its boundary. -/
theorem native_closed_piece_chart_data (G : A7.SourceGeometry E)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count)
    (c : SmoothAmbientChart ThreeSphere) :
    let D := ((F.domain i).chart j).map.target
    let P := pieceSphereCoordinate E F i j
    let U := D ∩ P ⁻¹' c.chart.source
    let f := c.chart ∘ P
    UniqueDiffOn ℝ U ∧ ContDiffOn ℝ 1 f U ∧ MapsTo f U c.chart.target ∧
      (∀ y ∈ U, fderivWithin ℝ f U y = fderivWithin ℝ f D y) ∧
      (∀ y ∈ U, (metricGram (actualChartTensor G.extension c) (f y)
        (fderivWithin ℝ f U y)).PosDef) := by
  dsimp only
  let D := ((F.domain i).chart j).map.target
  let P := pieceSphereCoordinate E F i j
  let U := D ∩ P ⁻¹' c.chart.source
  let f := c.chart ∘ P
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  have hP : ContMDiffOn 𝓘(ℝ,E2) (𝓡 3) 1 P D :=
    (hinc.contMDiff.of_le (by simp)).comp_contMDiffOn (F.piece_c1 i j)
  have hD : UniqueDiffOn ℝ D := by
    dsimp only [D]
    rw [((F.domain i).chart j).target_eq]
    exact SectorModel.uniqueDiffOn_domain ((F.domain i).chart j).model
  have hUD : UniqueDiffOn ℝ U := by
    intro y hy
    exact (hD y hy.1).inter' ((hP y hy.1).continuousWithinAt
      (c.chart.open_source.mem_nhds hy.2))
  have hfD (y : E2) (hy : y ∈ U) : ContDiffWithinAt ℝ 1 f D y := by
    have hc : ContMDiffAt (𝓡 3) 𝓘(ℝ,E3) 1 c.chart (P y) :=
      (c.smooth.of_le (by simp)).contMDiffAt (c.chart.open_source.mem_nhds hy.2)
    exact (hc.comp_contMDiffWithinAt y (hP y hy.1)).contDiffWithinAt
  have hd (y : E2) (hy : y ∈ U) :
      fderivWithin ℝ f U y = fderivWithin ℝ f D y :=
    fderivWithin_subset inter_subset_left (hUD y hy)
      ((hfD y hy).differentiableWithinAt one_ne_zero)
  refine ⟨hUD,(fun y hy => (hfD y hy).mono inter_subset_left),
    (fun y hy => c.chart.map_source hy.2),hd,?_⟩
  intro y hy
  have hgram : metricGram (actualChartTensor G.extension c) (f y)
      (fderivWithin ℝ f U y) = sectorCoordinateGram G.metric
        (F.map ∘ F.parametrization i) j y := by
    rw [hd y hy]
    ext a b
    exact actual_piece_gram_in_fixed_chart E G F i j y hy.1 c hy.2 a b
  rw [hgram]
  exact native_sector_gram_positive G.metric F i j y hy.1


end


section
open scoped Manifold ContDiff
open Set Topology MeasureTheory Matrix Filter
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
set_option backward.isDefEq.respectTransparency false in
/-- Compact whole pieces isolate the actual preimages of a seam point into
any selected relative-open chart windows. The ambient neighbourhood is an
output; all field support and artificial halfbox faces can be placed there. -/
theorem native_two_piece_chart_windows_ambient_isolation
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i r : Fin F.pieceCount) (j : Fin (F.domain i).count) (l : Fin (F.domain r).count)
    (W Z : Set E2) (hW : IsOpen W) (hZ : IsOpen Z)
    (y z : E2) (hy : y ∈ ((F.domain i).chart j).map.target) (hyW : y ∈ W)
    (hz : z ∈ ((F.domain r).chart l).map.target) (hzZ : z ∈ Z)
    (him : pieceSphereCoordinate E F i j y = pieceSphereCoordinate E F r l z) :
    ∃ U : Set ThreeSphere, IsOpen U ∧ pieceSphereCoordinate E F i j y ∈ U ∧
      (∀ q : F.domain i, E.toSphere (F.map (F.parametrization i q)) ∈ U →
        q ∈ ((F.domain i).chart j).map.source ∧ ((F.domain i).chart j).map q ∈ W) ∧
      (∀ q : F.domain r, E.toSphere (F.map (F.parametrization r q)) ∈ U →
        q ∈ ((F.domain r).chart l).map.source ∧ ((F.domain r).chart l).map q ∈ Z) := by
  let a := ((F.domain i).chart j).map
  let b := ((F.domain r).chart l).map
  let Q := a.source ∩ a ⁻¹' W
  let R := b.source ∩ b ⁻¹' Z
  have hQ : IsOpen Q := a.continuousOn.isOpen_inter_preimage ((F.domain i).chart j).source_open hW
  have hR : IsOpen R := b.continuousOn.isOpen_inter_preimage ((F.domain r).chart l).source_open hZ
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  let fi := E.toSphere ∘ F.map ∘ F.parametrization i
  let fr := E.toSphere ∘ F.map ∘ F.parametrization r
  have hfi : Continuous fi := hinc.isEmbedding.continuous.comp
    (F.map.continuous.comp (F.parametrization i).continuous)
  have hfr : Continuous fr := hinc.isEmbedding.continuous.comp
    (F.map.continuous.comp (F.parametrization r).continuous)
  have hi : Function.Injective fi := hinc.isEmbedding.injective.comp
    (F.embedding.injective.comp (F.parametrization_embedding i).injective)
  have hr : Function.Injective fr := hinc.isEmbedding.injective.comp
    (F.embedding.injective.comp (F.parametrization_embedding r).injective)
  let A := fi '' Qᶜ
  let B := fr '' Rᶜ
  have hA : IsClosed A := (hQ.isClosed_compl.isCompact.image hfi).isClosed
  have hB : IsClosed B := (hR.isClosed_compl.isCompact.image hfr).isClosed
  have hya : a.symm y ∈ Q := by
    refine ⟨a.map_target hy,?_⟩
    change a (a.symm y) ∈ W
    rwa [a.right_inv hy]
  have hzb : b.symm z ∈ R := by
    refine ⟨b.map_target hz,?_⟩
    change b (b.symm z) ∈ Z
    rwa [b.right_inv hz]
  refine ⟨(A ∪ B)ᶜ,(hA.union hB).isOpen_compl,?_,?_,?_⟩
  · rintro (hp | hp)
    · obtain ⟨q,hq,he⟩ := hp
      exact hq (hi he ▸ hya)
    · obtain ⟨q,hq,he⟩ := hp
      change fr q = pieceSphereCoordinate E F i j y at he
      rw [him] at he
      exact hq (hr he ▸ hzb)
  · intro q hq
    by_contra hbad
    exact hq (Or.inl ⟨q,hbad,rfl⟩)
  · intro q hq
    by_contra hbad
    exact hq (Or.inr ⟨q,hbad,rfl⟩)

/-- Relative-open window isolation immediately gives the native pullback
support containment on the actual chart targets, including their boundary. -/
theorem native_piece_coordinate_in_window_of_ambient_support
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (X : InteriorSmoothVectorField E) (i : Fin F.pieceCount) (j : Fin (F.domain i).count)
    (W : Set E2) (U : Set ThreeSphere)
    (hs : closure {p | X.field p ≠ 0} ⊆ U)
    (hu : ∀ q : F.domain i, E.toSphere (F.map (F.parametrization i q)) ∈ U →
      q ∈ ((F.domain i).chart j).map.source ∧ ((F.domain i).chart j).map q ∈ W) :
    ∀ y ∈ ((F.domain i).chart j).map.target,
      pieceSphereCoordinate E F i j y ∈ closure {p | X.field p ≠ 0} → y ∈ W := by
  intro y hy hsup
  have hh := (hu (((F.domain i).chart j).map.symm y) (hs hsup)).2
  rwa [((F.domain i).chart j).map.right_inv hy] at hh


end


section
open scoped Manifold ContDiff
open Set Topology MeasureTheory Matrix
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
open SeifertSurfaces.OriginalEndpoints.A2MetricFlux
open SeifertSurfaces.OriginalEndpoints.CurvedDivergence
open SeifertSurfaces.OriginalEndpoints.CurvedDivergence.GaussGreen
private theorem metricFlux_zero_of_field_zero (g : MetricTensor) (W : E3 → E3)
    (y : E3) (L : E2 →L[ℝ] E3) (hW : W y = 0) : metricFlux g W y L = 0 := by
  ext k
  simp [metricFlux,hW,coordinateInner]

set_option backward.isDefEq.respectTransparency false in
/-- The strict ambient support window eliminates the three artificial
faces of the SAME native affine halfbox. Only its genuine seam face remains. -/
theorem native_affine_halfbox_artificial_faces_zero
    (G : A7.SourceGeometry E) {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier) (X : InteriorSmoothVectorField E)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count)
    (c : SmoothAmbientChart ThreeSphere) (p : E2) (A : E2 ≃L[ℝ] E2)
    (a b h : ℝ) (hab : a < b) (hh : 0 < h)
    (hbox : MapsTo (fun x => p + A x) (halfBoxDomain true a b h)
      ((F.domain i).chart j).map.target)
    (hsource : MapsTo (pieceSphereCoordinate E F i j ∘ (fun x => p + A x))
      (halfBoxDomain true a b h) c.chart.source)
    (hwindow : ∀ q ∈ ((F.domain i).chart j).map.target,
      X.field (pieceSphereCoordinate E F i j q) ≠ 0 →
        coordinates (A.symm (q-p)) ∈ Ioo a b ×ˢ Ioo (-h) h) :
    let f := c.chart ∘ pieceSphereCoordinate E F i j ∘ (fun x => p + A x)
    let g := actualChartTensor G.extension c
    let W := actualFieldCoordinate E X c
    (∀ v ∈ Icc 0 h,
      (metricFlux g W (f (coordinates.symm (a,v)))
        (halfBoxDifferential f true a b h (coordinates.symm (a,v)))) 0 = 0 ∧
      (metricFlux g W (f (coordinates.symm (b,v)))
        (halfBoxDifferential f true a b h (coordinates.symm (b,v)))) 0 = 0) ∧
    (∀ u ∈ Icc a b,
      (metricFlux g W (f (coordinates.symm (u,h)))
        (halfBoxDifferential f true a b h (coordinates.symm (u,h)))) 1 = 0) := by
  dsimp only
  let D := ((F.domain i).chart j).map.target
  let P := pieceSphereCoordinate E F i j
  let f := c.chart ∘ P ∘ (fun x => p + A x)
  let W := actualFieldCoordinate E X c
  have hz (z : ℝ × ℝ) (hz : z ∈ Icc a b ×ˢ Icc 0 h)
      (hout : z ∉ Ioo a b ×ˢ Ioo (-h) h) : W (f (coordinates.symm z)) = 0 := by
    have hb : coordinates.symm z ∈ halfBoxDomain true a b h := by
      simpa only [halfBoxDomain,halfBox,↓reduceIte,mem_preimage,
        ContinuousLinearEquiv.apply_symm_apply,Icc_prod_eq] using hz
    have hX : X.field (P (p + A (coordinates.symm z))) = 0 := by
      by_contra hn
      have hw := hwindow _ (hbox hb) hn
      apply hout
      simpa only [add_sub_cancel_left,ContinuousLinearEquiv.symm_apply_apply,
        ContinuousLinearEquiv.apply_symm_apply] using hw
    have hs := hsource hb
    change P (p + A (coordinates.symm z)) ∈ c.chart.source at hs
    change chartDifferential c (c.chart.symm (c.chart (P (p + A (coordinates.symm z)))))
      (X.field (c.chart.symm (c.chart (P (p + A (coordinates.symm z)))))) = 0
    rw [c.chart.left_inv hs,hX,map_zero]
  constructor
  · intro v hv
    have ha : a ∈ Icc a b := ⟨le_rfl,hab.le⟩
    refine ⟨?_,?_⟩
    · rw [metricFlux_zero_of_field_zero _ _ _ _ (hz (a,v) ⟨ha,hv⟩ (by simp)),PiLp.zero_apply]
    · have hb : b ∈ Icc a b := ⟨ha.2,le_rfl⟩
      rw [metricFlux_zero_of_field_zero _ _ _ _ (hz (b,v) ⟨hb,hv⟩ (by simp)),PiLp.zero_apply]
  · intro u hu
    rw [metricFlux_zero_of_field_zero _ _ _ _
      (hz (u,h) ⟨hu,⟨hh.le,le_rfl⟩⟩ (by simp)),PiLp.zero_apply]


end


section
open scoped Manifold ContDiff
open Set Topology MeasureTheory Matrix Filter
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
set_option backward.isDefEq.respectTransparency false in
/-- Exactly two native incident whole pieces give an actual two-chart
ambient cover at ANY point of the common clock, not just its center. -/
theorem native_incident_pair_two_chart_ambient_cover
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i r : Fin F.pieceCount) (j : Fin (F.domain i).count) (l : Fin (F.domain r).count)
    (q0 : S)
    (hi0 : q0 ∈ F.parametrization i '' ((F.domain i).chart j).map.source)
    (hr0 : q0 ∈ F.parametrization r '' ((F.domain r).chart l).map.source)
    (hincident : ∀ k, q0 ∈ range (F.parametrization k) ↔ k=i ∨ k=r) :
    ∃ V : Set ThreeSphere, IsOpen V ∧ E.toSphere (F.map q0) ∈ V ∧
      E.toSphere '' F.image ∩ V =
      ((E.toSphere ∘ F.map ∘ F.parametrization i) '' ((F.domain i).chart j).map.source ∪
        (E.toSphere ∘ F.map ∘ F.parametrization r) '' ((F.domain r).chart l).map.source) ∩ V := by
  classical
  let B := (F.parametrization i) '' ((F.domain i).chart j).map.sourceᶜ
  let C := (F.parametrization r) '' ((F.domain r).chart l).map.sourceᶜ
  let O := ⋃ k : {k : Fin F.pieceCount // k≠i ∧ k≠r}, range (F.parametrization k.val)
  have hB : IsClosed B :=
    (((F.domain i).chart j).source_open.isClosed_compl.isCompact.image
      (F.parametrization i).continuous).isClosed
  have hC : IsClosed C :=
    (((F.domain r).chart l).source_open.isClosed_compl.isCompact.image
      (F.parametrization r).continuous).isClosed
  have hO : IsClosed O :=
    (isCompact_iUnion (fun k : {k : Fin F.pieceCount // k≠i ∧ k≠r} =>
      isCompact_range (F.parametrization k.val).continuous)).isClosed
  let U := (B ∪ C ∪ O)ᶜ
  have hU : IsOpen U := ((hB.union hC).union hO).isOpen_compl
  have hpU : q0 ∈ U := by
    rintro ((h | h) | h)
    · obtain ⟨p,hp,he⟩ := h
      obtain ⟨p0,hp0,he0⟩ := hi0
      exact hp ((F.parametrization_embedding i).injective (he.trans he0.symm) ▸ hp0)
    · obtain ⟨p,hp,he⟩ := h
      obtain ⟨p0,hp0,he0⟩ := hr0
      exact hp ((F.parametrization_embedding r).injective (he.trans he0.symm) ▸ hp0)
    · obtain ⟨k,hk⟩ := mem_iUnion.mp h
      rcases (hincident k.val).mp hk with h | h
      · exact k.property.1 h
      · exact k.property.2 h
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  have hemb := hinc.isEmbedding.comp F.embedding
  obtain ⟨V,hV,hpre⟩ := hemb.isInducing.isOpen_iff.mp hU
  refine ⟨V,hV,?_,?_⟩
  · change q0 ∈ (E.toSphere ∘ F.map) ⁻¹' V
    rw [hpre]
    exact hpU
  · ext p
    constructor
    · rintro ⟨⟨z,⟨q,hq⟩,hz⟩,hp⟩
      have he : E.toSphere (F.map q) = p := by rw [hq]; exact hz
      have hqU : q ∈ U := by
        have hqV : q ∈ (E.toSphere ∘ F.map) ⁻¹' V := by
          change E.toSphere (F.map q) ∈ V
          rwa [he]
        rw [hpre] at hqV
        exact hqV
      obtain ⟨k,hk⟩ := native_piece_incidence_nonempty E F q
      obtain ⟨x,hx⟩ := hk
      have hkr : k=i ∨ k=r := by
        by_contra hn
        exact hqU (Or.inr (mem_iUnion.mpr ⟨⟨k,not_or.mp hn⟩,⟨x,hx⟩⟩))
      refine ⟨?_,hp⟩
      rcases hkr with h | h
      · subst k
        have hxsrc : x ∈ ((F.domain i).chart j).map.source := by
          by_contra hn
          exact hqU (Or.inl (Or.inl ⟨x,hn,hx⟩))
        exact Or.inl ⟨x,hxsrc,by change E.toSphere (F.map (F.parametrization i x))=p; rwa [hx]⟩
      · subst k
        have hxsrc : x ∈ ((F.domain r).chart l).map.source := by
          by_contra hn
          exact hqU (Or.inl (Or.inr ⟨x,hn,hx⟩))
        exact Or.inr ⟨x,hxsrc,by change E.toSphere (F.map (F.parametrization r x))=p; rwa [hx]⟩
    · rintro ⟨h,hp⟩
      refine ⟨?_,hp⟩
      rcases h with ⟨x,hx,he⟩ | ⟨x,hx,he⟩
      · exact ⟨F.map (F.parametrization i x),⟨F.parametrization i x,rfl⟩,he⟩
      · exact ⟨F.map (F.parametrization r x),⟨F.parametrization r x,rfl⟩,he⟩


end


section
open scoped Manifold ContDiff
open Set Topology MeasureTheory Matrix Filter
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
open SeifertSurfaces.OriginalEndpoints.A2MetricFlux
open SeifertSurfaces.OriginalEndpoints.CurvedDivergence
set_option backward.isDefEq.respectTransparency false in
/-- Native closed C1 and interior smoothness descend to the actual affine
bulk halfbox, while the image remains in the same supplied ambient chart. -/
theorem native_affine_halfbox_regular_geometry
    (G : A7.SourceGeometry E) {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier) (i : Fin F.pieceCount)
    (j : Fin (F.domain i).count) (c : SmoothAmbientChart ThreeSphere)
    (p : E2) (A : E2 ≃L[ℝ] E2) (positive : Bool) (a b h : ℝ)
    (hclosed : MapsTo (fun x => p + A x) (halfBoxDomain positive a b h)
      ((F.domain i).chart j).map.target)
    (hpositive : MapsTo (fun x => p + A x) (openHalfBoxDomain positive a b h)
      (interior ((F.domain i).chart j).map.target))
    (hsource : MapsTo (pieceSphereCoordinate E F i j ∘ (fun x => p + A x))
      (halfBoxDomain positive a b h) c.chart.source) :
    let f := c.chart ∘ pieceSphereCoordinate E F i j ∘ (fun x => p + A x)
    ContDiffOn ℝ 1 f (halfBoxDomain positive a b h) ∧
      ContDiffOn ℝ ∞ f (openHalfBoxDomain positive a b h) ∧
      MapsTo f (halfBoxDomain positive a b h) c.chart.target := by
  dsimp only
  let P := pieceSphereCoordinate E F i j
  let M := fun x : E2 => p+A x
  have hM : ContDiff ℝ ∞ M := contDiff_const.add A.contDiff
  have hsub : openHalfBoxDomain positive a b h ⊆ halfBoxDomain positive a b h := by
    intro x hx
    change GaussGreen.coordinates x ∈ GaussGreen.halfBox positive a b h
    have hz : GaussGreen.coordinates x ∈ GaussGreen.openHalfBox positive a b h := hx
    cases positive <;>
      simpa only [GaussGreen.halfBox,GaussGreen.openHalfBox,↓reduceIte,mem_Icc,
        Prod.le_def] using ⟨⟨hz.1.1.le,hz.2.1.le⟩,⟨hz.1.2.le,hz.2.2.le⟩⟩
  have hclosedU : MapsTo M (halfBoxDomain positive a b h)
      (((F.domain i).chart j).map.target ∩ P ⁻¹' c.chart.source) :=
    fun x hx => ⟨hclosed hx,hsource hx⟩
  have hopenU : MapsTo M (openHalfBoxDomain positive a b h)
      (interior ((F.domain i).chart j).map.target ∩ P ⁻¹' c.chart.source) :=
    fun x hx => ⟨hpositive hx,hsource (hsub hx)⟩
  refine ⟨((native_closed_piece_chart_data E G F i j c).2.1.comp
    (hM.of_le (by simp)).contDiffOn hclosedU),
    ((native_actual_chart_data E G F i j c).2.1.comp hM.contDiffOn hopenU),
    fun x hx => c.chart.map_source (hsource hx)⟩


end


section
open scoped Manifold ContDiff BigOperators
open Set Topology MeasureTheory Matrix Filter
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
open SeifertSurfaces.OriginalEndpoints.A2MetricFlux
open SeifertSurfaces.OriginalEndpoints.CurvedDivergence
open SeifertSurfaces.OriginalEndpoints.CurvedDivergence.GaussGreen
open SeifertSurfaces.OriginalEndpoints.A2NativeTests
set_option backward.isDefEq.respectTransparency false in
/-- Actual native unit length, edge orthogonality and original outwardness
identify the original conormal with the paid conormal of the SAME affine
halfbox. The original clock derivative may have either sign. -/
theorem native_actual_conormal_eq_affine_halfbox
    (G : A7.SourceGeometry E) {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier) (i : Fin F.pieceCount)
    (j : Fin (F.domain i).count) (y out : E2)
    (hy : y ∈ ((F.domain i).chart j).map.target)
    (p0 : ThreeSphere) (heq : pieceSphereCoordinate E F i j y = p0)
    (c : SmoothAmbientChart ThreeSphere) (hp : p0 ∈ c.chart.source)
    (tau : TangentSpace (𝓡 3) p0)
    (hunit : G.extension.inner p0 (actualPieceConormal E F i j y out p0 heq)
      (actualPieceConormal E F i j y out p0 heq) = 1)
    (horth : G.extension.inner p0 (actualPieceConormal E F i j y out p0 heq) tau = 0)
    (origin : E2) (A : E2 ≃L[ℝ] E2) (a b h u k : ℝ)
    (hh : 0 < h) (hu : u ∈ Ioo a b) (hk : k ≠ 0)
    (hpoint : origin + A (boundaryPoint u) = y)
    (hbox : MapsTo (fun x => origin + A x) (halfBoxDomain true a b h)
      ((F.domain i).chart j).map.target)
    (hout : ∃ eps : ℝ, 0 < eps ∧ ∀ t ∈ Ioo 0 eps,
      y+t • out ∉ ((F.domain i).chart j).map.target)
    (L : E2 →L[ℝ] E3)
    (hL : L = (fderivWithin ℝ (c.chart ∘ pieceSphereCoordinate E F i j)
      ((F.domain i).chart j).map.target y).comp (A : E2 →L[ℝ] E2))
    (hGram : (metricGram (actualChartTensor G.extension c) (c.chart p0) L).PosDef)
    (htau : chartDifferential c p0 tau = k • L (coordinateVector 2 0)) :
    chartDifferential c p0 (actualPieceConormal E F i j y out p0 heq) =
      metricConormal (actualChartTensor G.extension c) (c.chart p0) L (outwardCovector true) := by
  let v := A.symm out
  let eta := actualPieceConormal E F i j y out p0 heq
  let g := actualChartTensor G.extension c
  have he : L v = chartDifferential c p0 eta := by
    rw [native_actual_piece_conormal_chart_coordinate E F i j y out hy p0 heq c hp,hL]
    change (fderivWithin ℝ (c.chart ∘ pieceSphereCoordinate E F i j)
      ((F.domain i).chart j).map.target y) (A (A.symm out)) = _
    rw [A.apply_symm_apply]
  have hvunit : coordinateInner g (c.chart p0) (L v) (L v) = 1 := by
    rw [he,native_tangent_pair_metric_in_chart E G c p0 hp]
    exact hunit
  have hvorth : coordinateInner g (c.chart p0) (L v) (L (coordinateVector 2 0)) = 0 := by
    have hh := (native_tangent_pair_metric_in_chart E G c p0 hp eta tau).trans horth
    rw [← he,htau] at hh
    have hr : coordinateInner g (c.chart p0) (L v) (k • L (coordinateVector 2 0)) =
        k * coordinateInner g (c.chart p0) (L v) (L (coordinateVector 2 0)) := by
      simp only [coordinateInner,PiLp.smul_apply,smul_eq_mul,Fin.sum_univ_three]
      ring
    rw [hr] at hh
    exact (mul_eq_zero.mp hh).resolve_left hk
  have hout' : ∃ eps : ℝ, 0 < eps ∧ ∀ t ∈ Ioo 0 eps,
      origin+A (boundaryPoint u)+t • A v ∉ ((F.domain i).chart j).map.target := by
    simpa only [hpoint,v,ContinuousLinearEquiv.apply_symm_apply] using hout
  rw [← he]
  exact native_sector_conormal_eq_paid_halfbox g (c.chart p0) L
    (fun a b => (nativeActualCoordinateMetric E G c).symmetric (c.chart p0)
      (c.chart.map_source hp) a b) hGram ((F.domain i).chart j).map.target origin
    (A : E2 →L[ℝ] E2) a b h u hh hu hbox v hvunit hvorth hout'


end


section
open scoped Manifold ContDiff BigOperators
open Set Topology MeasureTheory Matrix Filter
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
open SeifertSurfaces.OriginalEndpoints.A2MetricFlux
set_option backward.isDefEq.respectTransparency false in
/-- The derivative of the actual common edge in one fixed ambient chart
is the coordinate of its original manifold tangent. -/
theorem native_common_edge_chart_derivative
    (c : SmoothAmbientChart ThreeSphere) (edge : ℝ → ThreeSphere) (t : ℝ)
    (hed : MDifferentiableAt 𝓘(ℝ) (𝓡 3) edge t)
    (hc : edge t ∈ c.chart.source) :
    fderiv ℝ (c.chart ∘ edge) t 1 =
      chartDifferential c (edge t) (mfderiv 𝓘(ℝ) (𝓡 3) edge t 1) := by
  have hcd : MDifferentiableAt (𝓡 3) 𝓘(ℝ,E3) c.chart (edge t) :=
    (c.smooth.contMDiffAt (c.chart.open_source.mem_nhds hc)).mdifferentiableAt (by simp)
  have hh := mfderiv_comp t hcd hed
  rw [mfderiv_eq_fderiv] at hh
  exact congrArg (fun L => L 1) hh

set_option backward.isDefEq.respectTransparency false in
/-- The native common edge is regular in the actual ambient coordinates
because the same chart differential is invertible. -/
theorem native_common_edge_chart_derivative_ne_zero
    (c : SmoothAmbientChart ThreeSphere) (edge : ℝ → ThreeSphere) (t : ℝ)
    (hed : MDifferentiableAt 𝓘(ℝ) (𝓡 3) edge t)
    (hc : edge t ∈ c.chart.source)
    (hr : mfderiv 𝓘(ℝ) (𝓡 3) edge t 1 ≠ 0) :
    fderiv ℝ (c.chart ∘ edge) t 1 ≠ 0 := by
  intro hz
  apply hr
  have hh : chartDifferential c (edge t) (mfderiv 𝓘(ℝ) (𝓡 3) edge t 1) +
      chartDifferential c (edge t) 0 = 0 := by
    rw [← native_common_edge_chart_derivative c edge t hed hc,map_zero,add_zero]
    exact hz
  simpa only [add_zero] using native_actual_conormal_balance_of_chart_balance c (edge t) hc
    (mfderiv 𝓘(ℝ) (𝓡 3) edge t 1) 0 hh

set_option backward.isDefEq.respectTransparency false in
/-- Both actual halfbox clocks have the same original metric edge speed.
Only equality of the actual edge germs is used. -/
theorem native_clock_metric_speed_eq_actual_edge_speed
    (G : A7.SourceGeometry E) (c : SmoothAmbientChart ThreeSphere)
    (edge : ℝ → ThreeSphere) (f : E2 → E3) (clock : ℝ → ℝ) (t : ℝ)
    (hed : MDifferentiableAt 𝓘(ℝ) (𝓡 3) edge t)
    (hc : edge t ∈ c.chart.source)
    (heq : clockEdge f clock =ᶠ[𝓝 t] c.chart ∘ edge) :
    clockMetricSpeed (actualChartTensor G.extension c) f clock t =
      Real.sqrt (G.extension.inner (edge t) (mfderiv 𝓘(ℝ) (𝓡 3) edge t 1)
        (mfderiv 𝓘(ℝ) (𝓡 3) edge t 1)) := by
  unfold clockMetricSpeed
  dsimp only
  rw [heq.eq_of_nhds,heq.fderiv_eq,
    native_common_edge_chart_derivative c edge t hed hc]
  dsimp only [Function.comp_def]
  rw [native_tangent_pair_metric_in_chart E G c (edge t) hc]


end


section
open scoped Manifold ContDiff
open Set Topology MeasureTheory Filter Bundle
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
set_option backward.isDefEq.respectTransparency false in
/-- The common native regular edge has continuous, strictly positive speed
in the SAME original ambient metric. -/
theorem native_regular_edge_metric_speed_continuous_positive
    (G : A7.SourceGeometry E) (edge : ℝ → ThreeSphere) (U : Set ℝ) (hU : IsOpen U)
    (he : ContMDiffOn 𝓘(ℝ) (𝓡 3) ∞ edge U)
    (hr : ∀ t ∈ U, mfderiv 𝓘(ℝ) (𝓡 3) edge t 1 ≠ 0) :
    let speed := fun t => Real.sqrt (G.extension.inner (edge t)
      (mfderiv 𝓘(ℝ) (𝓡 3) edge t 1) (mfderiv 𝓘(ℝ) (𝓡 3) edge t 1))
    ContinuousOn speed U ∧ ∀ t ∈ U, 0 < speed t := by
  dsimp only
  have ht := he.continuousOn_tangentMapWithin (by simp) hU.uniqueMDiffOn
  have hinput : Continuous (fun t : ℝ =>
      (⟨t,(1 : TangentSpace 𝓘(ℝ) t)⟩ : TangentBundle 𝓘(ℝ) ℝ)) :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ)).symm.continuous.comp
      (continuous_id.prodMk continuous_const)
  have hv0 := ht.comp hinput.continuousOn (fun t ht => ht)
  have hv : ContinuousOn (fun t : ℝ =>
      (⟨edge t,mfderiv 𝓘(ℝ) (𝓡 3) edge t 1⟩ : TangentBundle (𝓡 3) ThreeSphere)) U := by
    apply hv0.congr
    intro t ht
    change (⟨edge t,mfderiv 𝓘(ℝ) (𝓡 3) edge t 1⟩ : TangentBundle (𝓡 3) ThreeSphere) =
      ⟨edge t,mfderivWithin 𝓘(ℝ) (𝓡 3) edge U t 1⟩
    rw [mfderivWithin_of_mem_nhds (hU.mem_nhds ht)]
  letI : RiemannianBundle (fun p : ThreeSphere => TangentSpace (𝓡 3) p) :=
    ⟨G.extension.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle (Euc 3) (fun p : ThreeSphere => TangentSpace (𝓡 3) p) :=
    ⟨⟨G.extension.inner,G.extension.contMDiff.continuous,fun _ _ _ => rfl⟩⟩
  refine ⟨?_,fun t ht => Real.sqrt_pos.mpr (G.extension.pos _ _ (hr t ht))⟩
  convert! (hv.inner_bundle hv).sqrt using 1


end


section
open scoped Manifold ContDiff
open Set Topology MeasureTheory Matrix Filter
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
set_option backward.isDefEq.respectTransparency false in
/-- The actual weak sum of the two native boundary conormals yields their
original tangent-bundle balance. All pointwise smooth cutoff tests are
constructed by the paid native boundary test theorem. -/
theorem native_tangent_boundary_balance_of_actual_weak_flux
    (G : A7.SourceGeometry E) (c : SmoothAmbientChart ThreeSphere)
    (edge : ℝ → ThreeSphere) (l r : ℝ)
    (he : ContinuousOn edge (Icc l r))
    (hemb : IsEmbedding (fun t : Icc l r => edge t))
    (hc : MapsTo edge (Icc l r) c.chart.source)
    (one two : ∀ t, TangentSpace (𝓡 3) (edge t))
    (hOne : ContinuousOn (fun t => Bundle.TotalSpace.mk' (Euc 3) (edge t) (one t)) (Icc l r))
    (hTwo : ContinuousOn (fun t => Bundle.TotalSpace.mk' (Euc 3) (edge t) (two t)) (Icc l r))
    (speed : ℝ → ℝ) (hspeed : ContinuousOn speed (Icc l r))
    (hpos : ∀ t ∈ Ioo l r, 0 < speed t)
    (V : Set ThreeSphere) (hV : IsOpen V)
    (hVc : V ⊆ c.chart.source)
    (hVE : V ⊆ E.toSphere '' (𝓡∂ 3).interior E.Carrier)
    (hweak : ∀ X : InteriorSmoothVectorField E,
      closure {p | X.field p ≠ 0} ⊆ V →
      (∫ t in Icc l r, G.extension.inner (edge t) (one t + two t) (X.field (edge t)) * speed t) = 0)
    (t0 : ℝ) (ht0 : t0 ∈ Ioo l r) (ht0V : edge t0 ∈ V) : one t0 + two t0 = 0 := by
  let eta := fun t => chartDifferential c (edge t) (one t) + chartDifferential c (edge t) (two t)
  have heta : ContinuousOn eta (Icc l r) :=
    (native_tangent_section_chart_continuousOn (Icc l r) c edge one hOne hc).add
      (native_tangent_section_chart_continuousOn (Icc l r) c edge two hTwo hc)
  have hweakC : ∀ X : InteriorSmoothVectorField E,
      closure {p | X.field p ≠ 0} ⊆ V →
      (∫ t in Icc l r, coordinateInner (actualChartTensor G.extension c)
        (c.chart (edge t)) (eta t)
        (actualFieldCoordinate E X c (c.chart (edge t))) * speed t) = 0 := by
    intro X hs
    rw [← hweak X hs]
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    have hcoord : actualFieldCoordinate E X c (c.chart (edge t)) =
        chartDifferential c (edge t) (X.field (edge t)) := by
      dsimp only [actualFieldCoordinate]
      rw [c.chart.left_inv (hc ht)]
    dsimp only [eta]
    rw [hcoord,← map_add,native_tangent_pair_metric_in_chart E G c (edge t) (hc ht)]
  have hz := native_boundary_vector_zero_of_actual_weak_flux E G c edge l r he hemb hc
    eta heta speed hspeed hpos V hV hVc hVE hweakC t0 ht0 ht0V
  exact native_actual_conormal_balance_of_chart_balance c (edge t0)
    (hc ⟨ht0.1.le,ht0.2.le⟩) (one t0) (two t0) hz


end


section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff BigOperators
open Set Topology MeasureTheory Matrix Filter Bundle
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
open SeifertSurfaces.OriginalEndpoints.A2MetricFlux
open SeifertSurfaces.OriginalEndpoints.A2NativeTests
open SeifertSurfaces.OriginalEndpoints.CurvedDivergence
open SeifertSurfaces.OriginalEndpoints.CurvedDivergence.GaussGreen
run_cmd do
  let pref := Lean.Name.num (`_private.OriginalA2ScaffoldV464) 0
  let n := (["SeifertSurfaces", "OriginalEndpoints", "AppendixAOriginal"].foldl Lean.Name.str pref)
  Lean.Elab.Command.modifyScope fun s => { s with openDecls := .simple n [] :: s.openDecls }
run_cmd do
  let pref := Lean.Name.num (`_private.A2MetricFluxV468) 0
  let n := (["SeifertSurfaces", "OriginalEndpoints", "A2MetricFlux"].foldl Lean.Name.str pref)
  Lean.Elab.Command.modifyScope fun s => { s with openDecls := .simple n [] :: s.openDecls }

/-- Apply the paid halfbox flux and boundary-only clock transport to the
SAME native affine map and its original outward conormal. The resulting
boundary integral uses the actual edge, vector field and ambient metric. -/
theorem native_halfbox_actual_boundary_flux
    (G : A7.SourceGeometry E) {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier) (X : InteriorSmoothVectorField E)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count)
    (c : SmoothAmbientChart ThreeSphere) (origin : E2) (A : E2 ≃L[ℝ] E2)
    (a b h : ℝ) (hab : a < b) (hh : 0 < h)
    (hclosed : MapsTo (fun x => origin + A x) (halfBoxDomain true a b h)
      ((F.domain i).chart j).map.target)
    (hpositive : MapsTo (fun x => origin + A x) (openHalfBoxDomain true a b h)
      (interior ((F.domain i).chart j).map.target))
    (hsource : MapsTo (pieceSphereCoordinate E F i j ∘ (fun x => origin + A x))
      (halfBoxDomain true a b h) c.chart.source)
    (hwindow : ∀ q ∈ ((F.domain i).chart j).map.target,
      X.field (pieceSphereCoordinate E F i j q) ≠ 0 →
        coordinates (A.symm (q-origin)) ∈ Ioo a b ×ˢ Ioo (-h) h)
    (f : E2 → E3)
    (hfdef : f = c.chart ∘ pieceSphereCoordinate E F i j ∘ (fun x => origin + A x))
    (hrank : ∀ x ∈ halfBoxDomain true a b h,
      Function.Injective (halfBoxDifferential f true a b h x))
    (hi : IntegrableOn (fun z : ℝ × ℝ =>
      let x := coordinates.symm z
      let L := halfBoxDifferential f true a b h x
      metricDensity (actualChartTensor G.extension c) (f x) L *
        (metricTangentialDivergence (actualChartTensor G.extension c) (actualFieldCoordinate E X c) (f x) L +
          coordinateInner (actualChartTensor G.extension c) (f x)
            (normalTrace (actualChartTensor G.extension c) f x) (actualFieldCoordinate E X c (f x))))
      (halfBox true a b h))
    (clock : ℝ → ℝ) (l r l0 r0 : ℝ) (hlr : l < r)
    (hclockWindow : Icc l r ⊆ Ioo l0 r0)
    (hclock : ContDiffOn ℝ 1 clock (Ioo l0 r0))
    (hclockRegular : ∀ t ∈ Icc l r, deriv clock t ≠ 0)
    (hclockInjective : InjOn clock (Icc l r))
    (hclockImage : clock '' Icc l r = Icc a b)
    (edge : ℝ → ThreeSphere)
    (hed : ∀ t ∈ Ioo l r, MDifferentiableAt 𝓘(ℝ) (𝓡 3) edge t)
    (hec : MapsTo edge (Icc l r) c.chart.source)
    (hedge : ∀ t ∈ Ioo l r, clockEdge f clock =ᶠ[𝓝 t] c.chart ∘ edge)
    (lift out : ℝ → E2)
    (hlift : MapsTo lift (Icc l r) ((F.domain i).chart j).map.target)
    (himage : ∀ t ∈ Icc l r, pieceSphereCoordinate E F i j (lift t) = edge t)
    (hpoint : ∀ t ∈ Icc l r, origin + A (boundaryPoint (clock t)) = lift t)
    (hL : ∀ t ∈ Ioo l r, halfBoxDifferential f true a b h (boundaryPoint (clock t)) =
      (fderivWithin ℝ (c.chart ∘ pieceSphereCoordinate E F i j)
        ((F.domain i).chart j).map.target (lift t)).comp (A : E2 →L[ℝ] E2))
    (nu : ∀ t, TangentSpace (𝓡 3) (edge t))
    (hnu : ∀ t (ht : t ∈ Icc l r), nu t =
      actualPieceConormal E F i j (lift t) (out t) (edge t) (himage t ht))
    (hunit : ∀ t ∈ Ioo l r, G.extension.inner (edge t) (nu t) (nu t) = 1)
    (horth : ∀ t ∈ Ioo l r, G.extension.inner (edge t) (nu t)
      (mfderiv 𝓘(ℝ) (𝓡 3) edge t 1) = 0)
    (hout : ∀ t ∈ Ioo l r, ∃ eps : ℝ, 0 < eps ∧ ∀ q ∈ Ioo 0 eps,
      lift t + q • out t ∉ ((F.domain i).chart j).map.target) :
    (∫ z in halfBox true a b h,
      let x := coordinates.symm z
      let L := halfBoxDifferential f true a b h x
      metricDensity (actualChartTensor G.extension c) (f x) L *
        (metricTangentialDivergence (actualChartTensor G.extension c) (actualFieldCoordinate E X c) (f x) L +
          coordinateInner (actualChartTensor G.extension c) (f x)
            (normalTrace (actualChartTensor G.extension c) f x) (actualFieldCoordinate E X c (f x)))) =
      ∫ t in Icc l r, G.extension.inner (edge t) (nu t) (X.field (edge t)) *
        Real.sqrt (G.extension.inner (edge t) (mfderiv 𝓘(ℝ) (𝓡 3) edge t 1)
          (mfderiv 𝓘(ℝ) (𝓡 3) edge t 1)) := by
  let g := nativeActualCoordinateMetric E G c
  let W := actualFieldCoordinate E X c
  have hreg := native_affine_halfbox_regular_geometry E G F i j c origin A true a b h
    hclosed hpositive hsource
  rw [← hfdef] at hreg
  have hW : ContDiffOn ℝ 1 W c.chart.target := by
    intro y hy
    exact ((actual_field_coordinate_smooth E X c y hy).of_le (by simp)).contDiffWithinAt
  have hfaces := native_affine_halfbox_artificial_faces_zero E G F X i j c origin A a b h
    hab hh hclosed hsource hwindow
  rw [← hfdef] at hfaces
  have hf := c1_halfbox_metric_flux c.chart.target c.chart.open_target g f W a b h hab hh true
    hreg.1 hreg.2.1 hreg.2.2 hrank hW hfaces.1 hfaces.2 hi
  have hclockFlux := c1_boundary_clock_metric_flux c.chart.target c.chart.open_target g f W a b h
    hab hh true hreg.1 hreg.2.2 hrank hW.continuousOn clock l r l0 r0 hlr hclockWindow
    hclock hclockRegular hclockInjective hclockImage
  have hc (t : ℝ) (ht : t ∈ Icc l r) : HasDerivAt clock (deriv clock t) t :=
    ((hclock t (hclockWindow ht)).contDiffAt (isOpen_Ioo.mem_nhds (hclockWindow ht))).differentiableAt
      one_ne_zero |>.hasDerivAt
  have hclockClosed (t : ℝ) (ht : t ∈ Icc l r) : clock t ∈ Icc a b := by
    rw [← hclockImage]
    exact mem_image_of_mem clock ht
  have hclockOpen (t : ℝ) (ht : t ∈ Ioo l r) : clock t ∈ Ioo a b := by
    have htcl : t ∈ Icc l r := ⟨ht.1.le,ht.2.le⟩
    have hb := hclockClosed t htcl
    constructor
    · apply lt_of_le_of_ne hb.1
      intro he
      have hm : IsLocalMin clock t := by
        filter_upwards [isOpen_Ioo.mem_nhds ht] with q hq
        rw [← he]
        exact (hclockClosed q ⟨hq.1.le,hq.2.le⟩).1
      exact hclockRegular t htcl hm.deriv_eq_zero
    · apply lt_of_le_of_ne hb.2
      intro he
      have hm : IsLocalMax clock t := by
        filter_upwards [isOpen_Ioo.mem_nhds ht] with q hq
        rw [he]
        exact (hclockClosed q ⟨hq.1.le,hq.2.le⟩).2
      exact hclockRegular t htcl hm.deriv_eq_zero
  have heq (t : ℝ) (ht : t ∈ Ioo l r) :
      let x := boundaryPoint (clock t)
      let L := halfBoxDifferential f true a b h x
      coordinateInner g.tensor (f x) (metricConormal g.tensor (f x) L (outwardCovector true))
        (W (f x)) * clockMetricSpeed g.tensor f clock t =
        G.extension.inner (edge t) (nu t) (X.field (edge t)) *
          Real.sqrt (G.extension.inner (edge t) (mfderiv 𝓘(ℝ) (𝓡 3) edge t 1)
            (mfderiv 𝓘(ℝ) (𝓡 3) edge t 1)) := by
    dsimp only
    have htcl : t ∈ Icc l r := ⟨ht.1.le,ht.2.le⟩
    let x := boundaryPoint (clock t)
    let L := halfBoxDifferential f true a b h x
    have hx : x ∈ halfBoxDomain true a b h := boundary_mem_halfBox a b h hh true (hclockClosed t htcl)
    have hfp : f x = c.chart (edge t) := by
      rw [hfdef]
      change c.chart (pieceSphereCoordinate E F i j (origin + A (boundaryPoint (clock t)))) = _
      rw [hpoint t htcl,himage t htcl]
    have hGram : (metricGram g.tensor (c.chart (edge t)) L).PosDef := by
      rw [← hfp]
      exact gram_positive g.tensor _ _ (g.symmetric _ (hreg.2.2 hx))
        (g.positive _ (hreg.2.2 hx)) (hrank _ hx)
    have hbd := hf.2.2.1 (clock t) (hclockOpen t ht)
    have hd := hbd.hasFDerivAt.comp_hasDerivAt t (hc t htcl)
    have htau : chartDifferential c (edge t) (mfderiv 𝓘(ℝ) (𝓡 3) edge t 1) =
        deriv clock t • L (coordinateVector 2 0) := by
      rw [← native_common_edge_chart_derivative c edge t (hed t ht) (hec htcl),← (hedge t ht).fderiv_eq]
      change fderiv ℝ (fun q => f (boundaryPoint (clock q))) t 1 =
        deriv clock t • halfBoxDifferential f true a b h (boundaryPoint (clock t)) (coordinateVector 2 0)
      simpa only [Function.comp_def,ContinuousLinearMap.toSpanSingleton_apply,one_smul] using
        congrArg (fun K : ℝ →L[ℝ] E3 => K 1) hd.hasFDerivAt.fderiv
    have hconormal := native_actual_conormal_eq_affine_halfbox E G F i j (lift t) (out t)
      (hlift htcl) (edge t) (himage t htcl) c (hec htcl)
      (mfderiv 𝓘(ℝ) (𝓡 3) edge t 1)
      (by rw [← hnu t htcl]; exact hunit t ht)
      (by rw [← hnu t htcl]; exact horth t ht)
      origin A a b h (clock t) (deriv clock t) hh (hclockOpen t ht) (hclockRegular t htcl)
      (hpoint t htcl) hclosed (hout t ht) L (hL t ht) hGram htau
    have hconormal' : chartDifferential c (edge t) (nu t) =
        metricConormal g.tensor (c.chart (edge t)) L (outwardCovector true) := by
      rwa [← hnu t htcl] at hconormal
    have hfield : W (c.chart (edge t)) = chartDifferential c (edge t) (X.field (edge t)) := by
      dsimp only [W,actualFieldCoordinate]
      rw [c.chart.left_inv (hec htcl)]
    rw [hfp,← hconormal',hfield]
    dsimp only [g,nativeActualCoordinateMetric]
    rw [native_tangent_pair_metric_in_chart E G c (edge t) (hec htcl)]
    rw [native_clock_metric_speed_eq_actual_edge_speed E G c edge f clock t (hed t ht) (hec htcl) (hedge t ht)]
  calc
    _ = _ := hf.2.2.2.2
    _ = _ := hclockFlux.2
    _ = _ := (setIntegral_congr_set (Ioo_ae_eq_Icc (a := l) (b := r)).symm).trans
      ((setIntegral_congr_fun measurableSet_Ioo heq).trans (setIntegral_congr_set Ioo_ae_eq_Icc))

end

section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff BigOperators
open Set Topology MeasureTheory Matrix Filter Bundle
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
open SeifertSurfaces.OriginalEndpoints.A2MetricFlux
open SeifertSurfaces.OriginalEndpoints.A2NativeTests
open SeifertSurfaces.OriginalEndpoints.CurvedDivergence
open SeifertSurfaces.OriginalEndpoints.CurvedDivergence.GaussGreen
run_cmd do
  let pref := Lean.Name.num (`_private.OriginalA2ScaffoldV464) 0
  let n := (["SeifertSurfaces", "OriginalEndpoints", "AppendixAOriginal"].foldl Lean.Name.str pref)
  Lean.Elab.Command.modifyScope fun s => { s with openDecls := .simple n [] :: s.openDecls }

/-- The exact paid affine first differential is the original closed native
piece differential in the same bulk frame, and has rank two up to the seam. -/
theorem native_affine_halfbox_closed_differential_and_rank
    (G : A7.SourceGeometry E) {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count)
    (c : SmoothAmbientChart ThreeSphere) (origin : E2) (A : E2 ≃L[ℝ] E2)
    (a b h : ℝ) (hab : a < b) (hh : 0 < h)
    (hclosed : MapsTo (fun x => origin + A x) (halfBoxDomain true a b h)
      ((F.domain i).chart j).map.target)
    (hsource : MapsTo (pieceSphereCoordinate E F i j ∘ (fun x => origin + A x))
      (halfBoxDomain true a b h) c.chart.source) :
    let f := c.chart ∘ pieceSphereCoordinate E F i j ∘ (fun x => origin + A x)
    ∀ x ∈ halfBoxDomain true a b h,
      halfBoxDifferential f true a b h x =
        (fderivWithin ℝ (c.chart ∘ pieceSphereCoordinate E F i j)
          ((F.domain i).chart j).map.target (origin + A x)).comp (A : E2 →L[ℝ] E2) ∧
      Function.Injective (halfBoxDifferential f true a b h x) := by
  dsimp only
  let f0 := c.chart ∘ pieceSphereCoordinate E F i j
  let D := ((F.domain i).chart j).map.target ∩ pieceSphereCoordinate E F i j ⁻¹' c.chart.source
  have hd := native_closed_piece_chart_data E G F i j c
  have hm : MapsTo (fun x => origin + A x) (halfBoxDomain true a b h) D :=
    fun x hx => ⟨hclosed hx,hsource hx⟩
  have ha := affine_halfbox_closed_metric_reparametrization (actualChartTensor G.extension c)
    (fun _ => 0) f0 D hd.1 hd.2.1 A origin true a b h hab hh hm (fun x hx => hd.2.2.2.2 _ (hm hx))
  intro x hx
  have he := (ha x hx).1
  have hinj := actual_positive_gram_differential_injective (actualChartTensor G.extension c)
    (f0 (origin + A x)) (fderivWithin ℝ f0 D (origin + A x)) (hd.2.2.2.2 _ (hm hx))
  change halfBoxDifferential (f0 ∘ (fun x => origin + A x)) true a b h x =
    (fderivWithin ℝ f0 ((F.domain i).chart j).map.target (origin + A x)).comp (A : E2 →L[ℝ] E2) ∧ _
  refine ⟨?_,?_⟩
  · rw [he,hd.2.2.2.1 _ (hm hx)]
  · change Function.Injective (halfBoxDifferential (f0 ∘ (fun x => origin + A x)) true a b h x)
    rw [he]
    exact hinj.comp A.injective

/-- On the actual open affine halfbox, minimality eliminates the transformed
normal trace. The remaining integrand is exactly the native divergence row
multiplied by the determinant of that same affine frame. -/
theorem native_affine_halfbox_metric_integrand
    (G : A7.SourceGeometry E) {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier) (hminimal : PiecesMinimal E G F)
    (X : InteriorSmoothVectorField E)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count)
    (c : SmoothAmbientChart ThreeSphere) (origin : E2) (A : E2 ≃L[ℝ] E2)
    (a b h : ℝ) (hab : a < b) (hh : 0 < h)
    (hclosed : MapsTo (fun x => origin + A x) (halfBoxDomain true a b h)
      ((F.domain i).chart j).map.target)
    (hpositive : MapsTo (fun x => origin + A x) (openHalfBoxDomain true a b h)
      (interior ((F.domain i).chart j).map.target))
    (hsource : MapsTo (pieceSphereCoordinate E F i j ∘ (fun x => origin + A x))
      (halfBoxDomain true a b h) c.chart.source) :
    let f := c.chart ∘ pieceSphereCoordinate E F i j ∘ (fun x => origin + A x)
    let g := actualChartTensor G.extension c
    let W := actualFieldCoordinate E X c
    ∀ x ∈ openHalfBoxDomain true a b h,
      metricDensity g (f x) (halfBoxDifferential f true a b h x) *
        (metricTangentialDivergence g W (f x) (halfBoxDifferential f true a b h x) +
          coordinateInner g (f x) (normalTrace g f x) (W (f x))) =
      |(A : E2 →L[ℝ] E2).det| *
        (pieceTangentialDivergence E G F X i j (origin + A x) *
          sectorCoordinateDensity G.metric (F.map ∘ F.parametrization i) j (origin + A x)) := by
  dsimp only
  let f0 := c.chart ∘ pieceSphereCoordinate E F i j
  let g := actualChartTensor G.extension c
  let W := actualFieldCoordinate E X c
  let D := ((F.domain i).chart j).map.target ∩ pieceSphereCoordinate E F i j ⁻¹' c.chart.source
  let U := interior ((F.domain i).chart j).map.target ∩ pieceSphereCoordinate E F i j ⁻¹' c.chart.source
  have hd := native_closed_piece_chart_data E G F i j c
  have hu := native_actual_chart_data E G F i j c
  have hm : MapsTo (fun x => origin + A x) (halfBoxDomain true a b h) D :=
    fun x hx => ⟨hclosed hx,hsource hx⟩
  have ha := affine_halfbox_closed_metric_reparametrization g W f0 D hd.1 hd.2.1 A origin
    true a b h hab hh hm (fun x hx => hd.2.2.2.2 _ (hm hx))
  intro x hx
  have hxcl : x ∈ halfBoxDomain true a b h := by
    exact ⟨⟨hx.1.1.le,hx.2.1.le⟩,⟨hx.1.2.le,hx.2.2.le⟩⟩
  have hy := hpositive hx
  have hs := hsource hxcl
  have hyU : origin + A x ∈ U := ⟨hy,hs⟩
  have hfd : fderivWithin ℝ f0 D (origin + A x) = fderiv ℝ f0 (origin + A x) := by
    rw [hd.2.2.2.1 _ (hm hxcl)]
    exact fderivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hy)
  have hnormal := affine_metric_normal_trace_reparametrization g f0 U hu.1 hu.2.1 A origin x hyU
    (actual_chart_metric_symmetric G.extension c _) (hu.2.2.2.2 _ hyU)
  have hn : normalTrace g (f0 ∘ (fun x => origin + A x)) x = 0 := by
    rw [hnormal]
    exact native_piece_metric_flux_normalTrace_zero E G F hminimal i j _ hy c hs
  have hb := ha x hxcl
  rw [hfd] at hb
  change metricDensity g ((f0 ∘ (fun x => origin + A x)) x)
    (halfBoxDifferential (f0 ∘ (fun x => origin + A x)) true a b h x) *
    (metricTangentialDivergence g W ((f0 ∘ (fun x => origin + A x)) x)
      (halfBoxDifferential (f0 ∘ (fun x => origin + A x)) true a b h x) +
      coordinateInner g ((f0 ∘ (fun x => origin + A x)) x)
        (normalTrace g (f0 ∘ (fun x => origin + A x)) x) (W ((f0 ∘ (fun x => origin + A x)) x))) = _
  rw [hb.2.1,hb.2.2,hn]
  have hn0 := native_piece_metric_flux_normalTrace_zero E G F hminimal i j _ hy c hs
  have hi := native_piece_metric_flux_integrand E G X F hminimal i j _ hy c hs
  dsimp only at hi
  rw [hn0] at hi
  simpa only [g,W,f0,Function.comp_apply,mul_assoc] using
    congrArg (fun z => |(A : E2 →L[ℝ] E2).det| * z) hi

end

section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff BigOperators
open Set Topology MeasureTheory Matrix Filter Bundle
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
open SeifertSurfaces.OriginalEndpoints.A2MetricFlux
open SeifertSurfaces.OriginalEndpoints.A2NativeTests
open SeifertSurfaces.OriginalEndpoints.CurvedDivergence
open SeifertSurfaces.OriginalEndpoints.CurvedDivergence.GaussGreen
run_cmd do
  let pref := Lean.Name.num (`_private.OriginalA2ScaffoldV464) 0
  let n := (["SeifertSurfaces", "OriginalEndpoints", "AppendixAOriginal"].foldl Lean.Name.str pref)
  Lean.Elab.Command.modifyScope fun s => { s with openDecls := .simple n [] :: s.openDecls }
run_cmd do
  let pref := Lean.Name.num (`_private.A2MetricFluxV468) 0
  let n := (["SeifertSurfaces", "OriginalEndpoints", "A2MetricFlux"].foldl Lean.Name.str pref)
  Lean.Elab.Command.modifyScope fun s => { s with openDecls := .simple n [] :: s.openDecls }

/-- Transport the original native divergence row through the same affine bulk
frame and discard only the null boundary faces. This supplies the actual
integrability premise of the paid C1 flux theorem. -/
theorem native_affine_halfbox_bulk_flux_transport
    (G : A7.SourceGeometry E) {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier) (hminimal : PiecesMinimal E G F)
    (X : InteriorSmoothVectorField E)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count)
    (c : SmoothAmbientChart ThreeSphere) (origin : E2) (A : E2 ≃L[ℝ] E2)
    (a b h : ℝ) (hab : a < b) (hh : 0 < h)
    (hclosed : MapsTo (fun x => origin + A x) (halfBoxDomain true a b h)
      ((F.domain i).chart j).map.target)
    (hpositive : MapsTo (fun x => origin + A x) (openHalfBoxDomain true a b h)
      (interior ((F.domain i).chart j).map.target))
    (hsource : MapsTo (pieceSphereCoordinate E F i j ∘ (fun x => origin + A x))
      (halfBoxDomain true a b h) c.chart.source) :
    let f := c.chart ∘ pieceSphereCoordinate E F i j ∘ (fun x => origin + A x)
    let g := actualChartTensor G.extension c
    let W := actualFieldCoordinate E X c
    let I := fun z : ℝ × ℝ =>
      let x := coordinates.symm z
      let L := halfBoxDifferential f true a b h x
      metricDensity g (f x) L *
        (metricTangentialDivergence g W (f x) L +
          coordinateInner g (f x) (normalTrace g f x) (W (f x)))
    let U := (fun z : ℝ × ℝ => origin + A (coordinates.symm z)) '' openHalfBox true a b h
    IntegrableOn I (halfBox true a b h) ∧
      (∫ q in U, pieceTangentialDivergence E G F X i j q *
        sectorCoordinateDensity G.metric (F.map ∘ F.parametrization i) j q) =
        ∫ z in halfBox true a b h, I z := by
  dsimp only
  let d := fun q => pieceTangentialDivergence E G F X i j q *
    sectorCoordinateDensity G.metric (F.map ∘ F.parametrization i) j q
  let T := fun z : ℝ × ℝ => origin + A (coordinates.symm z)
  let I := fun z : ℝ × ℝ =>
    let x := coordinates.symm z
    let f := c.chart ∘ pieceSphereCoordinate E F i j ∘ (fun x => origin + A x)
    let g := actualChartTensor G.extension c
    let W := actualFieldCoordinate E X c
    let L := halfBoxDifferential f true a b h x
    metricDensity g (f x) L *
      (metricTangentialDivergence g W (f x) L +
        coordinateInner g (f x) (normalTrace g f x) (W (f x)))
  have hZ : MeasurableSet (openHalfBox true a b h) := by
    exact measurableSet_Ioo.prod measurableSet_Ioo
  have hsub : T '' openHalfBox true a b h ⊆ interior ((F.domain i).chart j).map.target := by
    rintro q ⟨z,hz,rfl⟩
    exact hpositive (by simpa only [openHalfBoxDomain,mem_preimage,
      ContinuousLinearEquiv.apply_symm_apply] using hz)
  have hd : IntegrableOn d (T '' openHalfBox true a b h) :=
    (native_whole_chart_divergence_density_integrable E G X F i j).mono_set hsub
  have htr := native_affine_bulk_volume_transport origin A (openHalfBox true a b h) hZ d
  have hpull := htr.2.1.mp hd
  have heq (z : ℝ × ℝ) (hz : z ∈ openHalfBox true a b h) :
      |(A : E2 →L[ℝ] E2).det| * d (T z) = I z := by
    symm
    exact native_affine_halfbox_metric_integrand E G F hminimal X i j c origin A a b h hab hh
      hclosed hpositive hsource (coordinates.symm z) (by
        simpa only [openHalfBoxDomain,mem_preimage,ContinuousLinearEquiv.apply_symm_apply] using hz)
  have hIo : IntegrableOn I (openHalfBox true a b h) := hpull.congr_fun heq hZ
  have hAE := halfBox_ae_open true a b h
  refine ⟨hIo.congr_set_ae hAE,?_⟩
  exact htr.2.2.trans ((setIntegral_congr_fun hZ heq).trans (setIntegral_congr_set hAE.symm))

end

section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff BigOperators
open Set Topology MeasureTheory Matrix Filter Bundle
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
open SeifertSurfaces.OriginalEndpoints.A2MetricFlux
open SeifertSurfaces.OriginalEndpoints.A2NativeTests
open SeifertSurfaces.OriginalEndpoints.CurvedDivergence
open SeifertSurfaces.OriginalEndpoints.CurvedDivergence.GaussGreen
run_cmd do
  let pref := Lean.Name.num (`_private.OriginalA2ScaffoldV464) 0
  let n := (["SeifertSurfaces", "OriginalEndpoints", "AppendixAOriginal"].foldl Lean.Name.str pref)
  Lean.Elab.Command.modifyScope fun s => { s with openDecls := .simple n [] :: s.openDecls }
run_cmd do
  let pref := Lean.Name.num (`_private.A2MetricFluxV468) 0
  let n := (["SeifertSurfaces", "OriginalEndpoints", "A2MetricFlux"].foldl Lean.Name.str pref)
  Lean.Elab.Command.modifyScope fun s => { s with openDecls := .simple n [] :: s.openDecls }

/-- Full original native sheet flux law in the same affine bulk frame.
The rank, normal trace and combined integrability are derived from the
actual native piece; no analytic conclusion is an input. -/
theorem native_affine_sheet_actual_flux
    (G : A7.SourceGeometry E) {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier) (hminimal : PiecesMinimal E G F)
    (X : InteriorSmoothVectorField E)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count)
    (c : SmoothAmbientChart ThreeSphere) (origin : E2) (A : E2 ≃L[ℝ] E2)
    (a b h : ℝ) (hab : a < b) (hh : 0 < h)
    (hclosed : MapsTo (fun x => origin + A x) (halfBoxDomain true a b h)
      ((F.domain i).chart j).map.target)
    (hpositive : MapsTo (fun x => origin + A x) (openHalfBoxDomain true a b h)
      (interior ((F.domain i).chart j).map.target))
    (hsource : MapsTo (pieceSphereCoordinate E F i j ∘ (fun x => origin + A x))
      (halfBoxDomain true a b h) c.chart.source)
    (hwindow : ∀ q ∈ ((F.domain i).chart j).map.target,
      X.field (pieceSphereCoordinate E F i j q) ≠ 0 →
        coordinates (A.symm (q-origin)) ∈ Ioo a b ×ˢ Ioo (-h) h)
    (f : E2 → E3)
    (hfdef : f = c.chart ∘ pieceSphereCoordinate E F i j ∘ (fun x => origin + A x))
    (clock : ℝ → ℝ) (l r l0 r0 : ℝ) (hlr : l < r)
    (hclockWindow : Icc l r ⊆ Ioo l0 r0)
    (hclock : ContDiffOn ℝ 1 clock (Ioo l0 r0))
    (hclockRegular : ∀ t ∈ Icc l r, deriv clock t ≠ 0)
    (hclockInjective : InjOn clock (Icc l r))
    (hclockImage : clock '' Icc l r = Icc a b)
    (edge : ℝ → ThreeSphere)
    (hed : ∀ t ∈ Ioo l r, MDifferentiableAt 𝓘(ℝ) (𝓡 3) edge t)
    (hec : MapsTo edge (Icc l r) c.chart.source)
    (hedge : ∀ t ∈ Ioo l r, clockEdge f clock =ᶠ[𝓝 t] c.chart ∘ edge)
    (lift out : ℝ → E2)
    (hlift : MapsTo lift (Icc l r) ((F.domain i).chart j).map.target)
    (himage : ∀ t ∈ Icc l r, pieceSphereCoordinate E F i j (lift t) = edge t)
    (hpoint : ∀ t ∈ Icc l r, origin + A (boundaryPoint (clock t)) = lift t)
    (nu : ∀ t, TangentSpace (𝓡 3) (edge t))
    (hnu : ∀ t (ht : t ∈ Icc l r), nu t =
      actualPieceConormal E F i j (lift t) (out t) (edge t) (himage t ht))
    (hunit : ∀ t ∈ Ioo l r, G.extension.inner (edge t) (nu t) (nu t) = 1)
    (horth : ∀ t ∈ Ioo l r, G.extension.inner (edge t) (nu t)
      (mfderiv 𝓘(ℝ) (𝓡 3) edge t 1) = 0)
    (hout : ∀ t ∈ Ioo l r, ∃ eps : ℝ, 0 < eps ∧ ∀ q ∈ Ioo 0 eps,
      lift t + q • out t ∉ ((F.domain i).chart j).map.target) :
    (∫ q in (fun z : ℝ × ℝ => origin + A (coordinates.symm z)) '' openHalfBox true a b h,
      pieceTangentialDivergence E G F X i j q *
        sectorCoordinateDensity G.metric (F.map ∘ F.parametrization i) j q) =
      ∫ t in Icc l r, G.extension.inner (edge t) (nu t) (X.field (edge t)) *
        Real.sqrt (G.extension.inner (edge t) (mfderiv 𝓘(ℝ) (𝓡 3) edge t 1)
          (mfderiv 𝓘(ℝ) (𝓡 3) edge t 1)) := by
  have hd := native_affine_halfbox_closed_differential_and_rank E G F i j c origin A a b h
    hab hh hclosed hsource
  have hb := native_affine_halfbox_bulk_flux_transport E G F hminimal X i j c origin A a b h
    hab hh hclosed hpositive hsource
  rw [← hfdef] at hd hb
  have hL : ∀ t ∈ Ioo l r, halfBoxDifferential f true a b h (boundaryPoint (clock t)) =
      (fderivWithin ℝ (c.chart ∘ pieceSphereCoordinate E F i j)
        ((F.domain i).chart j).map.target (lift t)).comp (A : E2 →L[ℝ] E2) := by
    intro t ht
    have htcl : t ∈ Icc l r := ⟨ht.1.le,ht.2.le⟩
    have hc : clock t ∈ Icc a b := by
      rw [← hclockImage]
      exact mem_image_of_mem clock htcl
    have hx : boundaryPoint (clock t) ∈ halfBoxDomain true a b h :=
      boundary_mem_halfBox a b h hh true hc
    simpa only [hpoint t htcl] using (hd _ hx).1
  exact hb.2.trans (native_halfbox_actual_boundary_flux E G F X i j c origin A a b h hab hh
    hclosed hpositive hsource hwindow f hfdef (fun x hx => (hd x hx).2) hb.1
    clock l r l0 r0 hlr hclockWindow hclock hclockRegular hclockInjective hclockImage
    edge hed hec hedge lift out hlift himage hpoint hL nu hnu hunit horth hout)

end

section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff BigOperators
open Set Topology MeasureTheory Matrix Filter Bundle
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
open SeifertSurfaces.OriginalEndpoints.A2MetricFlux
open SeifertSurfaces.OriginalEndpoints.A2NativeTests
open SeifertSurfaces.OriginalEndpoints.CurvedDivergence
open SeifertSurfaces.OriginalEndpoints.CurvedDivergence.GaussGreen

set_option backward.isDefEq.respectTransparency false in
/-- Original metric boundary flux of a continuous actual conormal against
an original admissible vector field is integrable on the compact clock. -/
theorem native_boundary_conormal_flux_integrable
    (G : A7.SourceGeometry E) (X : InteriorSmoothVectorField E)
    (edge : ℝ → ThreeSphere) (l r : ℝ) (he : ContinuousOn edge (Icc l r))
    (nu : ∀ t, TangentSpace (𝓡 3) (edge t))
    (hnu : ContinuousOn (fun t => Bundle.TotalSpace.mk' (Euc 3) (edge t) (nu t)) (Icc l r))
    (speed : ℝ → ℝ) (hspeed : ContinuousOn speed (Icc l r)) :
    IntegrableOn (fun t => G.extension.inner (edge t) (nu t) (X.field (edge t)) * speed t) (Icc l r) := by
  letI : RiemannianBundle (fun p : ThreeSphere => TangentSpace (𝓡 3) p) :=
    ⟨G.extension.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle (Euc 3) (fun p : ThreeSphere => TangentSpace (𝓡 3) p) :=
    ⟨⟨G.extension.inner,G.extension.contMDiff.continuous,fun _ _ _ => rfl⟩⟩
  have hfield : ContinuousOn (fun t => Bundle.TotalSpace.mk' (Euc 3) (edge t) (X.field (edge t)))
      (Icc l r) := X.smooth.continuous.comp_continuousOn he
  have hi : ContinuousOn (fun t => G.extension.inner (edge t) (nu t) (X.field (edge t)))
      (Icc l r) := by
    convert! hnu.inner_bundle hfield using 1
  exact (hi.mul hspeed).integrableOn_compact isCompact_Icc

end

section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff BigOperators
open Set Topology MeasureTheory Matrix Filter Bundle
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
open SeifertSurfaces.OriginalEndpoints.A2MetricFlux
open SeifertSurfaces.OriginalEndpoints.A2NativeTests
open SeifertSurfaces.OriginalEndpoints.CurvedDivergence
open SeifertSurfaces.OriginalEndpoints.CurvedDivergence.GaussGreen

set_option backward.isDefEq.respectTransparency false in
/-- Actual native stationarity and the two paid native chart flux identities
force opposite original conormals. Every ambient cutoff test is constructed
by the native tester; the only analytic inputs are the two sheet flux laws. -/
theorem native_two_sheet_conormal_balance_of_native_chart_flux
    (G : A7.SourceGeometry E) {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier)
    (hstationary : ∀ X : InteriorSmoothVectorField E, pieceDivergenceSum E G F X = 0)
    (i r : Fin F.pieceCount) (hir : i ≠ r)
    (j : Fin (F.domain i).count) (k : Fin (F.domain r).count)
    (A B : Set E2)
    (hA : A ⊆ interior ((F.domain i).chart j).map.target)
    (hB : B ⊆ interior ((F.domain r).chart k).map.target)
    (V : Set ThreeSphere) (hV : IsOpen V)
    (hVE : V ⊆ E.toSphere '' (𝓡∂ 3).interior E.Carrier)
    (hcover : E.toSphere '' F.image ∩ V =
      ((E.toSphere ∘ F.map ∘ F.parametrization i) '' ((F.domain i).chart j).map.source ∪
        (E.toSphere ∘ F.map ∘ F.parametrization r) '' ((F.domain r).chart k).map.source) ∩ V)
    (hsA : ∀ y ∈ interior ((F.domain i).chart j).map.target,
      pieceSphereCoordinate E F i j y ∈ V → y ∈ A)
    (hsB : ∀ y ∈ interior ((F.domain r).chart k).map.target,
      pieceSphereCoordinate E F r k y ∈ V → y ∈ B)
    (c : SmoothAmbientChart ThreeSphere) (hVc : V ⊆ c.chart.source)
    (edge : ℝ → ThreeSphere) (l h : ℝ)
    (he : ContinuousOn edge (Icc l h))
    (hemb : IsEmbedding (fun t : Icc l h => edge t))
    (hc : MapsTo edge (Icc l h) c.chart.source)
    (one two : ∀ t, TangentSpace (𝓡 3) (edge t))
    (hOne : ContinuousOn (fun t => Bundle.TotalSpace.mk' (Euc 3) (edge t) (one t)) (Icc l h))
    (hTwo : ContinuousOn (fun t => Bundle.TotalSpace.mk' (Euc 3) (edge t) (two t)) (Icc l h))
    (speed : ℝ → ℝ) (hspeed : ContinuousOn speed (Icc l h))
    (hpos : ∀ t ∈ Ioo l h, 0 < speed t)
    (hflux : ∀ X : InteriorSmoothVectorField E, closure {p | X.field p ≠ 0} ⊆ V →
      ((∫ y in A, pieceTangentialDivergence E G F X i j y *
        sectorCoordinateDensity G.metric (F.map ∘ F.parametrization i) j y) =
          ∫ t in Icc l h, G.extension.inner (edge t) (one t) (X.field (edge t)) * speed t) ∧
      ((∫ y in B, pieceTangentialDivergence E G F X r k y *
        sectorCoordinateDensity G.metric (F.map ∘ F.parametrization r) k y) =
          ∫ t in Icc l h, G.extension.inner (edge t) (two t) (X.field (edge t)) * speed t))
    (t0 : ℝ) (ht0 : t0 ∈ Ioo l h) (ht0V : edge t0 ∈ V) : one t0 + two t0 = 0 := by
  apply native_tangent_boundary_balance_of_actual_weak_flux E G c edge l h he hemb hc
    one two hOne hTwo speed hspeed hpos V hV hVc hVE _ t0 ht0 ht0V
  intro X hs
  have hbal := native_two_sheet_stationarity_in_supported_windows E G F hstationary X i r hir
    j k V hs hcover A B hA hB
    (fun y hy hp => hsA y hy (hs hp)) (fun y hy hp => hsB y hy (hs hp))
  have hIone := native_boundary_conormal_flux_integrable E G X edge l h he one hOne speed hspeed
  have hItwo := native_boundary_conormal_flux_integrable E G X edge l h he two hTwo speed hspeed
  have heq : (fun t => G.extension.inner (edge t) (one t + two t) (X.field (edge t)) * speed t) =
      (fun t => G.extension.inner (edge t) (one t) (X.field (edge t)) * speed t +
        G.extension.inner (edge t) (two t) (X.field (edge t)) * speed t) := by
    funext t
    simp only [map_add,ContinuousLinearMap.add_apply,add_mul]
  rw [heq,integral_add hIone hItwo,← (hflux X hs).1,← (hflux X hs).2]
  exact hbal

end

open Lean Elab Command
set_option maxHeartbeats 0
set_option maxRecDepth 100000
run_cmd do
  let source := System.FilePath.mk (← getFileName)
  let dir := source.parent.getD "." / "A2ProofData"
  let mut constants : Array ConstantInfo := #[]
  for file in #["A2NativeBulkFrameProbe.olean", "A2NativeRectangleSelectionProbe.olean", "A2NativeHalfstripClockIntervalProbe.olean", "A2NativeHalfstripChartRectangleProbe.olean", "A2NativeHalfstripBulkWindowProbe.olean", "A2NativeClockOpenImageProbe.olean", "A2NativeLocalSectionExtensionProbe.olean", "A2NativeTangentSectionExtensionProbe.olean", "A2NativeHalfstripRelativeWindowConsumerProbe.olean", "A2NativeHalfstripEdgeEmbeddingProbe.olean", "A2NativeActualTwoSheetFluxBalanceProbe.olean", "A2NativeActualPairBalanceProbe.olean", "A2NativeOriginalConormalConclusionsProbe.olean"] do
    let (data,_) ← liftIO <| readModuleData (dir / file)
    constants := constants ++ data.constants
  let all := constants.foldl (fun m ci => m.insert ci.name ci) ({} : Std.HashMap Name ConstantInfo)
  let pref := `SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
  let roots := #[pref ++ `native_actual_arc_conormal_conclusion,pref ++ `native_actual_circle_conormal_conclusion]
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
  let mut pending := constants.filter (fun ci => required.contains ci.name && (initial.find? ci.name).isNone)
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
  logInfo m!"PAID_NATIVE_CONCLUSIONS_REPLAY_PASS {required.toArray.size} dependency names"


/-- Original Lemma A.2: the actual sum of tangential-divergence area integrals
vanishes for every smooth interior-supported field; every whole piece is
minimal; and the two actual pieces at EVERY interior seam point have opposite
outward conormals. Actual flow and induced first variation are constructed from the supplied minimum. -/
theorem A2_original (G : A7.SourceGeometry E) (J : LongitudeFoliation.{u} E)
    {S R : CompactOrientedSurface.{u}} [ConnectedSpace S]
    (F : GeometricPiecewiseSurface S E.Carrier)
    (hF_incompressible : F.Incompressible) (hF_boundary : J.BoundaryIn F.map)
    (Fprime : GeometricPiecewiseSurface R E.Carrier)
    (hminimum : FixedBoundaryMinimizer E G.metric F Fprime) :
    (∀ X : InteriorSmoothVectorField E, pieceDivergenceSum E G Fprime X = 0) ∧
    PiecesMinimal E G Fprime ∧
    (∀ a : Fin Fprime.seam.arcCount, ∀ s : Time,
      0 < s → s < 1 → Nonempty (OppositePieceConormals E G Fprime a s)) ∧
    (∀ a : Fin Fprime.seam.circleCount, ∀ s : Circle,
      Nonempty (OppositeCirclePieceConormals E G Fprime a s)) := by
  have hstationary := A2_original_stationarity E G F Fprime hminimum
  have hminimal := native_minimality_of_actual_stationarity E G Fprime hstationary
  refine ⟨hstationary,hminimal,?_,?_⟩
  · intro a s hleft hright
    exact native_actual_arc_conormal_conclusion E G Fprime hstationary hminimal a s hleft hright
  · intro a s
    exact native_actual_circle_conormal_conclusion E G Fprime hstationary hminimal a s

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
