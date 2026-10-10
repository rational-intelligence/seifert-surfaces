import AppendixBAnalysis
import BoundaryFoliation
import SurfaceClasses
import EndpointGeometry
import B1SourceContext

noncomputable section
open Set Topology Function
open scoped Manifold ContDiff

namespace SeifertSurfaces.OriginalEndpoints
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixB

universe v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}

/-- The source's relative area minimum over all geometric piecewise-smooth
proper competitors in the proper isotopy class, with boundary sliding through
the supplied longitude foliation. The smooth A is represented by its exact
map; no incompressibility or smoothness restriction is placed on competitors.
Both areas use the actual supplied metric, and the competitor isotopy is the
geometric piecewise proper isotopy, with free intermediate boundary motion. -/
def IsRelativeAreaMinimizer (g : SmoothMetric E.Carrier) (J : LongitudeFoliation.{v} E)
    (A : IncompressibleSpanningSurface.{v} E) : Prop :=
  J.BoundaryIn A.1.embedding.toFun ∧
  ∃ F : GeometricPiecewiseSurface A.1.surface E.Carrier,
    F.map = ProperSmoothEmbedding.continuousMap (ProperSmoothEmbedding.ofNeat A.1.embedding) ∧
    ∀ S : CompactOrientedSurface.{v}, ∀ C : GeometricPiecewiseSurface S E.Carrier,
      J.BoundaryIn C.map → GeometricImageIsotopic F C →
        area g A.1.embedding.toFun ≤ geometricArea g C

abbrev T2Coordinate := Circle × (ℝ × ℝ)

def halfCylinder (r0 eta : ℝ) : Set T2Coordinate :=
  {x | x.2.1 ∈ Icc (0 : ℝ) r0 ∧ |x.2.2| < eta}

def radialCylinder (r0 : ℝ) : Set (Circle × ℝ) :=
  {x | x.2 ∈ Icc (0 : ℝ) r0}

/-- Strict convexity in the source's inward-normal convention. Smooth
extensions of the actual boundary-chart metric retain the same coefficients
on the half-space; the Hessian is strictly negative on nonzero level vectors. -/
def IsStrictlyConvexBoundary (g : SmoothMetric E.Carrier) : Prop :=
  ∀ p ∈ (𝓡∂ 3).boundary E.Carrier,
    ∃ V : Set SeifertSurfaces.AppendixACoordinates.E3, IsOpen V ∧
    ∃ G : SeifertSurfaces.AppendixACoordinates.CoordinateMetric V,
      extChartAt (𝓡∂ 3) p p ∈ V ∧
      (∀ y ∈ V ∩ (extChartAt (𝓡∂ 3) p).target,
        G.tensor y = SeifertSurfaces.AppendixC.MetricInChart (𝓡∂ 3) g p y) ∧
      ∀ w : SeifertSurfaces.AppendixACoordinates.E3, w ≠ 0 → w 0 = 0 →
        SeifertSurfaces.AppendixACoordinates.hessianQuadratic G.tensor
          (fun y => y 0) (extChartAt (𝓡∂ 3) p p) w < 0

/-- Actual configuration T2 and the very same graph difference of (22).
No finite-critical-set assumption occurs in this record. It must be supplied
by the original Proposition 5.7(2) route for this exact pair/graph.
The smooth extension only represents the stated smoothness up to r=0. -/
structure B1OriginalData (g : SmoothMetric E.Carrier) (J : LongitudeFoliation.{v} E) where
  boundary_strictly_convex : IsStrictlyConvexBoundary g
  A : IncompressibleSpanningSurface.{v} E
  B : IncompressibleSpanningSurface.{v} E
  A_relative_minimum : IsRelativeAreaMinimizer g J A
  B_relative_minimum : IsRelativeAreaMinimizer g J B
  foliation_analytic : J.IntrinsicallyAnalytic
  distance_two : (oneSkeleton E).dist
    (classOf E (surfaceImageOf E A)) (classOf E (surfaceImageOf E B)) = 2
  boundaryLabel : Circle
  A_boundary : A.1.embedding.toFun '' A.1.surface.boundary = J.leaf boundaryLabel
  B_boundary : B.1.embedding.toFun '' B.1.surface.boundary = J.leaf boundaryLabel
  leafParameter : Circle → E.Carrier
  leafParameter_embedding : Manifold.IsSmoothEmbedding (𝓡 1) (𝓡∂ 3) ∞ leafParameter
  leafParameter_image : range leafParameter = J.leaf boundaryLabel
  leafLength : ℝ
  leafLength_pos : 0 < leafLength
  leaf_arclength : ∀ t : ℝ,
    let gamma := fun a : ℝ => leafParameter (Circle.exp (2 * Real.pi * a / leafLength))
    let velocity := mfderiv 𝓘(ℝ) (𝓡∂ 3) gamma t
      ((NormedSpace.fromTangentSpace t).symm 1)
    g.inner (gamma t) velocity velocity = 1
  r0 : ℝ
  r0_pos : 0 < r0
  eta : ℝ
  eta_pos : 0 < eta
  collar : T2Coordinate → E.Carrier
  collar_smooth : ContMDiffOn ((𝓡 1).prod (𝓘(ℝ).prod 𝓘(ℝ))) (𝓡∂ 3) ∞
    collar (halfCylinder r0 eta)
  collar_embedding : IsEmbedding (fun x : halfCylinder r0 eta => collar x)
  collar_immersion : ∀ x ∈ halfCylinder r0 eta,
    Function.Injective (mfderivWithin ((𝓡 1).prod (𝓘(ℝ).prod 𝓘(ℝ))) (𝓡∂ 3)
      collar (halfCylinder r0 eta) x)
  collar_boundary : ∀ x ∈ halfCylinder r0 eta,
    collar x ∈ (𝓡∂ 3).boundary E.Carrier ↔ x.2.1 = 0
  collar_leaf : ∀ s : Circle, collar (s, 0, 0) = leafParameter s
  radialCoordinate : E.Carrier → ℝ
  radial_exact : ∀ x ∈ halfCylinder r0 eta, radialCoordinate (collar x) = x.2.1
  radial_inward_distance : IsInwardDistanceCoordinate g
    (collar '' halfCylinder r0 eta) radialCoordinate
  sourceFlow : B1SourceFoliationFlow J
  collar_flow : ∀ s r y, r ∈ Icc (0 : ℝ) r0 → |y| < eta →
    collar (s, r, y) = sourceFlow.ambient y (collar (s, r, 0))
  f : Circle → ℝ → ℝ
  extendedDomain : Set (Circle × ℝ)
  extendedDomain_open : IsOpen extendedDomain
  extendedDomain_contains : radialCylinder r0 ⊆ extendedDomain
  f_smooth : ContMDiffOn ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ) ∞
    (fun x : Circle × ℝ => f x.1 x.2) extendedDomain
  f_boundary_zero : ∀ s, f s 0 = 0
  graph_inside : ∀ s r, r ∈ Icc (0 : ℝ) r0 → |f s r| < eta
  A_graph_exact : A.1.image ∩ (collar '' halfCylinder r0 eta) =
    (fun x : Circle × ℝ => collar (x.1, x.2, f x.1 x.2)) '' radialCylinder r0
  B_graph_exact : B.1.image ∩ (collar '' halfCylinder r0 eta) =
    (fun x : Circle × ℝ => collar (x.1, x.2, 0)) '' radialCylinder r0

def B1NormalDerivative {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}
    (D : B1OriginalData g J) (s : Circle) : ℝ := deriv (D.f s) 0

/-- The source's actual supremum of the absolute second radial derivative
on the same compact closed half-cylinder. Its finiteness is a derived obligation. -/
def B1Lambda {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}
    (D : B1OriginalData g J) : ℝ :=
  sSup {l : ℝ | ∃ s : Circle, ∃ r ∈ Icc (0 : ℝ) D.r0,
    l = |deriv (deriv (D.f s)) r|}

/-- A genuine nondegenerate closed boundary-leaf arc: its circle parameter
set and actual image are both closed, with an interval homeomorphism. The
same longitude parametrization identifies its points with the values of f. -/
structure ClosedLeafArc (J : LongitudeFoliation.{v} E) (label : Circle)
    (leafParameter : Circle → E.Carrier) where
  parameterSet : Set Circle
  parameterSet_closed : IsClosed parameterSet
  parameterHomeomorph : Set.Icc (0 : ℝ) 1 ≃ₜ parameterSet
  carrier : Set E.Carrier
  carrier_exact : carrier = leafParameter '' parameterSet
  carrier_closed : IsClosed carrier
  leaf_subset : carrier ⊆ J.leaf label
  intervalHomeomorph : Set.Icc (0 : ℝ) 1 ≃ₜ carrier

end SeifertSurfaces.OriginalEndpoints
