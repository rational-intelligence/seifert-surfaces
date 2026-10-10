import SeamClockShorteningProbe
import NativeArcLiftAssemblyProbe
import NativeCircleLiftAssemblyProbe
import NativeHalfStripAmbientProbe
import NativeVelocityTransportProbe
import NativeIncidenceTwoLowerProbe

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped Manifold ContDiff
open Set Topology Filter
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
universe u
variable {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)

structure NativeSharedSeamData (G : A7.SourceGeometry E)
    {S : CompactOrientedSurface.{u}} (Fprime : GeometricPiecewiseSurface S E.Carrier)
    (β : SeamLocalTime → S) where
  scale : ℝ
  scale_pos : 0 < scale
  scale_lt_one : scale < 1
  edge : ℝ → ThreeSphere
  edge_formula : ∀ t : SeamLocalTime,
    edge t = E.toSphere (Fprime.map (β (seamScale scale scale_pos scale_lt_one t)))
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
  contains_point : E.toSphere (Fprime.map (β ⟨0, neg_one_lt_zero, zero_lt_one⟩)) ∈ neighbourhood
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
    β (seamScale scale scale_pos scale_lt_one t) ∈ range (Fprime.parametrization i) ↔ i = one ∨ i = two
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
