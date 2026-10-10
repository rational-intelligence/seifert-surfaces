import ExactPaidSource
import B1InteriorMetricChart_v475
import B1InteriorChartContinuation_v475
import B1ActualAmbientFlowMinimum_v475
import B1ActualFixedBoundaryMinima_v475
import B1InteriorCylinderPDE_v475
import B1InteriorCoefficientMeanValue_v475
import A3MetricVariationBridges
import B1ActualGermLocusClosed_v475
import B1InteriorLocalZeroContinuation_v475
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import B1ActualCommonInteriorGraph_v475
import A7NativeExtensionV464
import A7HalfSpaceStraighteningV464
import A7HalfSpaceSignV464
import B1InteriorCommonCylinder_v475
import B1ActualCollarGraphUniqueness_v475
import B1CollarWindow_v468
import B1ActualGeometry_v468
import Mathlib.Topology.DiscreteSubset
import Mathlib.Analysis.Normed.Module.ContinuousInverse
import Mathlib.Analysis.Normed.Operator.CompleteCodomain
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import A7HalfSpaceExtensionV464
import A7PlaneAlgebraV464
import DifferentialGeometry.Topology.Manifold.ChartPartialDiffeomorph
import DifferentialGeometry.Analysis.Calculus.Inverse.LocalInverse
import B1InteriorNormalizedClassical_v475
import B1InteriorClassicalWeak_v475
import B1WeakTransportReflection
import B1BoundaryMetricProvider_v466
import B1FiniteIntegerOrder_v468
import OriginalB1
import B1TangencyGraph
import KnotLinkConditions
import KnotGenus
import Section5Combinatorics
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Topology.Covering.Basic
import A7NativeImmersionCriterionV464
import ExtensionObligation
import MetricAreaAnalysis.Assembly
import DifferentialGeometry.Topology.Manifold.IntervalExtension
import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import DifferentialGeometry.Topology.Embedding.Extension
import DifferentialGeometry.Topology.Manifold.ImmersionCriterion
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingComposition
import DifferentialGeometry.Topology.InvarianceOfDomainManifold

section

noncomputable section
open Set Topology Function MeasureTheory Bundle
open scoped Manifold ContDiff BigOperators ENNReal

namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates

variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]

variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
/-- The metric is installed only on tangent fibers; the exterior topology is unchanged. -/
def metricEDist (g : SmoothMetric M) (p q : M) : ℝ≥0∞ :=
  letI : RiemannianBundle (fun x : M => TangentSpace (𝓡∂ 3) x) :=
    ⟨g.toRiemannianMetric⟩
  Manifold.riemannianEDist (𝓡∂ 3) p q

def metricDist (g : SmoothMetric M) (p q : M) : ℝ :=
  (metricEDist g p q).toReal

def metricBall (g : SmoothMetric M) (p : M) (r : ℝ) : Set M :=
  {q | metricEDist g p q < ENNReal.ofReal r}

def metricDiameter (g : SmoothMetric M) (C : Set M) : ℝ :=
  sSup {d | ∃ p ∈ C, ∃ q ∈ C, d = metricDist g p q}

/-- The empty-set distance is infinite before the cap; in particular N=0 is legal. -/
def cappedDistance (g : SmoothMetric M) (r : ℝ)
    (C : Set M) (p : M) : ℝ :=
  min (ENNReal.ofReal r) (⨅ q : C, metricEDist g p q.1) |>.toReal

def boundaryEDist (g : SmoothMetric M) (p : M) : ℝ≥0∞ :=
  ⨅ q : (𝓡∂ 3).boundary M, metricEDist g p q.1

def tangentPlaneAt {S : CompactOrientedSurface.{0}}
    (F : NeatEmbedding S M) (x : S) (p : M)
    (h : F.toFun x = p) : Submodule ℝ (TangentSpace (𝓡∂ 3) p) :=
  h ▸ LinearMap.range (mfderiv (𝓡∂ 2) (𝓡∂ 3) F.toFun x).toLinearMap

def interiorTangencies {S R : CompactOrientedSurface.{0}}
    (A : NeatEmbedding S M) (B : NeatEmbedding R M) : Set M :=
  {p | p ∈ (𝓡∂ 3).interior M ∧
    ∃ a : S, ∃ b : R, ∃ ha : A.toFun a = p, ∃ hb : B.toFun b = p,
      tangentPlaneAt A a p ha = tangentPlaneAt B b p hb}

def Transverse {S R : CompactOrientedSurface.{0}}
    (A : NeatEmbedding S M) (B : NeatEmbedding R M) : Prop :=
  ∀ a b (h : A.toFun a = B.toFun b),
    tangentPlaneAt A a (B.toFun b) h ⊔ tangentPlaneAt B b (B.toFun b) rfl = ⊤

def unitNormalAt {S : CompactOrientedSurface.{0}} (g : SmoothMetric M)
    (A : NeatEmbedding S M) (p : M)
    (n : TangentSpace (𝓡∂ 3) p) : Prop :=
  g.inner p n n = 1 ∧ ∀ a (h : A.toFun a = p),
    ∀ w ∈ tangentPlaneAt A a p h, g.inner p n w = 0

/-- Exactly min(α,π-α): the acute angle between the two metric normal lines. -/
def twoSidedAngle {S R : CompactOrientedSurface.{0}} (g : SmoothMetric M)
    (A : NeatEmbedding S M) (B : NeatEmbedding R M)
    (p : M) : ℝ :=
  sInf {a | ∃ n m : TangentSpace (𝓡∂ 3) p,
    unitNormalAt g A p n ∧ unitNormalAt g B p m ∧ a = Real.arccos |g.inner p n m|}

/-- A whole closed connected component of the actual intersection, with a smooth circle parameter. -/
structure ClosedIntersectionComponent (Γ : Set M) where
  parameter : Circle → M
  smoothEmbedding : Manifold.IsSmoothEmbedding (𝓡 1) (𝓡∂ 3) ∞ parameter
  point : M
  point_mem : point ∈ Γ
  component_exact : range parameter = connectedComponentIn Γ point

def curveAt {Γ : Set M} (γ : ClosedIntersectionComponent Γ) (s : ℝ) : M :=
  γ.parameter (Circle.exp (2 * Real.pi * s))

def curveSpeed {Γ : Set M} (g : SmoothMetric M)
    (γ : ClosedIntersectionComponent Γ) (s : ℝ) : ℝ :=
  let v := mfderiv 𝓘(ℝ) (𝓡∂ 3) (curveAt γ) s
    ((NormedSpace.fromTangentSpace s).symm 1)
  Real.sqrt (g.inner (curveAt γ s) v v)

def curveLengthIn {Γ : Set M} (g : SmoothMetric M)
    (γ : ClosedIntersectionComponent Γ) (Z : Set M) : ℝ :=
  by
  classical
  exact ∫ s in (0 : ℝ)..1, if curveAt γ s ∈ Z then curveSpeed g γ s else 0

def curveIntegral {Γ : Set M} (g : SmoothMetric M)
    (γ : ClosedIntersectionComponent Γ) (h : M → ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, h (curveAt γ s) * curveSpeed g γ s

def FiniteClosedIntersection (Γ : Set M) : Prop :=
  Γ.Nonempty ∧ ∃ n : ℕ, ∃ γ : Fin n → ClosedIntersectionComponent Γ,
    Pairwise (fun i j => Disjoint (range (γ i).parameter) (range (γ j).parameter)) ∧
    (⋃ i, range (γ i).parameter) = Γ

/-- A null homotopy is tested in the collar itself, not in the ambient exterior. -/
def EssentialIn {Γ : Set M} (γ : ClosedIntersectionComponent Γ)
    (C : Set M) : Prop :=
  ∃ l : C(Circle, C), (fun z => (l z).1) = γ.parameter ∧
    ¬ ∃ x : C, ContinuousMap.Homotopic l (ContinuousMap.const Circle x)

def exteriorBoundary {S : CompactOrientedSurface.{0}}
    (A : NeatEmbedding S M) : Set M := A.toFun '' S.boundary

def vertexOf (A : IncompressibleSpanningSurface.{0} E) : Vertex.{0} E :=
  classOf E (surfaceImageOf E A)

/-- Definition 4.7: the infimum over the actual smooth neat representatives with leaf boundary. -/
def relativeVertexArea (g : SmoothMetric E.Carrier) (J : LongitudeFoliation.{0} E)
    (v : Vertex.{0} E) : ℝ :=
  sInf {a | ∃ F : IncompressibleSpanningSurface.{0} E,
    vertexOf F = v ∧ J.BoundaryIn F.1.embedding.toFun ∧ a = area g F.1.embedding.toFun}

/-- Only §3's explicitly inherited source input. No Appendix B conclusion is a field. -/
structure RelativeSourceSetting (g : SmoothMetric E.Carrier) (J : LongitudeFoliation.{0} E) : Prop where
  strictly_convex : IsStrictlyConvexBoundary g
  analytic_foliation : J.IntrinsicallyAnalytic
  source_E : ∀ v : Vertex.{0} E, ∃ F : IncompressibleSpanningSurface.{0} E,
    vertexOf F = v ∧ IsRelativeAreaMinimizer g J F
  source_U : ∀ F G : IncompressibleSpanningSurface.{0} E,
    IsRelativeAreaMinimizer g J F → IsRelativeAreaMinimizer g J G →
    Adjacent E (vertexOf F) (vertexOf G) → Disjoint F.1.image G.1.image

/-- Proposition 5.7's original pair; neither finiteness nor nodal order is an input. -/
structure OriginalPair (g : SmoothMetric E.Carrier) (J : LongitudeFoliation.{0} E) where
  A : IncompressibleSpanningSurface.{0} E
  B : IncompressibleSpanningSurface.{0} E
  A_minimum : IsRelativeAreaMinimizer g J A
  B_minimum : IsRelativeAreaMinimizer g J B
  distance_two : (oneSkeleton E).dist (vertexOf A) (vertexOf B) = 2
  convex : IsStrictlyConvexBoundary g
  analytic : J.IntrinsicallyAnalytic

def graphPlaneCoordinates (y : E3) : E2 :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![y 0, y 1]

def graphPoint (x : E2) (y : ℝ) : E3 :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm ![x 0, x 1, y]

/-- Actual normal-coordinate graph data at an interior tangency, as in (21). -/
structure InteriorGraph (A B : IncompressibleSpanningSurface.{0} E) (p : E.Carrier) where
  coordinates : OpenPartialHomeomorph E.Carrier E3
  source_interior : coordinates.source ⊆ (𝓡∂ 3).interior E.Carrier
  smooth : ContMDiffOn (𝓡∂ 3) 𝓘(ℝ, E3) ∞ coordinates coordinates.source
  inverse_smooth : ContMDiffOn 𝓘(ℝ, E3) (𝓡∂ 3) ∞ coordinates.symm coordinates.target
  base_mem : p ∈ coordinates.source
  base_zero : coordinates p = 0
  R : ℝ
  R_pos : 0 < R
  eta : ℝ
  eta_pos : 0 < eta
  cylinder_inside : {y : E3 | ‖graphPlaneCoordinates y‖ < R ∧ |y 2| < eta} ⊆ coordinates.target
  lower : E2 → ℝ
  upper : E2 → ℝ
  lower_smooth : ContDiffOn ℝ ∞ lower (Metric.ball 0 R)
  upper_smooth : ContDiffOn ℝ ∞ upper (Metric.ball 0 R)
  lower_zero : lower 0 = 0
  upper_zero : upper 0 = 0
  lower_tangent : fderiv ℝ lower 0 = 0
  upper_tangent : fderiv ℝ upper 0 = 0
  lower_inside : ∀ x ∈ Metric.ball (0 : E2) R, |lower x| < eta
  upper_inside : ∀ x ∈ Metric.ball (0 : E2) R, |upper x| < eta
  graph_A : A.1.image ∩ coordinates.source =
    (fun x : E2 => coordinates.symm (graphPoint x (upper x))) '' Metric.ball 0 R
  graph_B : B.1.image ∩ coordinates.source =
    (fun x : E2 => coordinates.symm (graphPoint x (lower x))) '' Metric.ball 0 R

def graphDifference {A B : IncompressibleSpanningSurface.{0} E} {p : E.Carrier}
    (c : InteriorGraph A B p) : E2 → ℝ := fun x => c.upper x - c.lower x

def InteriorTangencyConclusion {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}
    (D : OriginalPair g J) : Prop :=
  ∀ p ∈ interiorTangencies D.A.1.embedding D.B.1.embedding,
    (∃ U : Set E.Carrier, IsOpen U ∧ p ∈ U ∧
      U ∩ interiorTangencies D.A.1.embedding D.B.1.embedding = {p}) ∧
    ∃ c : InteriorGraph D.A D.B p, ∃ m : ℕ, 1 ≤ m ∧
      ∃ c1 c2 R : ℝ, 0 < c1 ∧ 0 < c2 ∧ 0 < R ∧ R ≤ c.R ∧
        (∀ x : E2, 0 < ‖x‖ → ‖x‖ < R →
          c1 * ‖x‖ ^ m - c2 * ‖x‖ ^ (m + 1) ≤ ‖fderiv ℝ (graphDifference c) x‖ ∧
          0 < c1 * ‖x‖ ^ m - c2 * ‖x‖ ^ (m + 1)) ∧
        (∀ x ∈ Metric.ball (0 : E2) R,
          fderiv ℝ (graphDifference c) x = 0 ↔ x = 0) ∧
        (∀ V : Set E2, V ∈ 𝓝 (0 : E2) →
          (∃ x ∈ V ∩ Metric.ball 0 R, 0 < graphDifference c x) ∧
          (∃ x ∈ V ∩ Metric.ball 0 R, graphDifference c x < 0))







def collarCriticalPoints {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}
    (D : B1OriginalData g J) : Set Circle :=
  {s | mfderiv ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ) (fun q : Circle × ℝ => D.f q.1 q.2) (s, 0) = 0}

def openCollar {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}
    (D : B1OriginalData g J) (r0 : ℝ) : Set E.Carrier :=
  (fun q : Circle × ℝ => D.collar (q.1, q.2, 0)) '' {q | 0 < q.2 ∧ q.2 < r0}

def extendedRadial {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}
    (D : B1OriginalData g J) (r0 : ℝ) (p : E.Carrier) : ℝ := by
  classical
  exact if p ∈ D.collar '' halfCylinder r0 D.eta
    then D.radialCoordinate p else r0

def collarLevelSet {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}
    (D : B1OriginalData g J) (r0 sign : ℝ) (chi : ℝ → ℝ) (t : ℝ) : Set E.Carrier :=
  (fun q : Circle × ℝ => D.collar (q.1, q.2, 0)) ''
    {q ∈ radialCylinder r0 | D.f q.1 q.2 + sign * t * chi q.2 = 0}

def boundaryArcLength {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}
    (D : B1OriginalData g J) (arc : ClosedLeafArc J D.boundaryLabel D.leafParameter) : ℝ := by
  classical
  exact ∫ s in (0 : ℝ)..D.leafLength,
    if Circle.exp (2 * Real.pi * s / D.leafLength) ∈ arc.parameterSet then 1 else 0

-- Held sibling documentation omitted during mechanical union.
/-- Clause (2) of Lemma 5.4 means time zero lies on the closed side;
positive collar times lie in U. This does not demand F ⊆ U. -/
structure OneSidedCollar {S : CompactOrientedSurface.{0}}
    (F : NeatEmbedding S M) (U : Set M) where
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  map : S × ℝ → M
  initial : ∀ x, map (x, 0) = F.toFun x
  smooth : ContMDiffOn ((𝓡∂ 2).prod 𝓘(ℝ)) (𝓡∂ 3) ∞ map (univ ×ˢ Ico 0 epsilon)
  embedding : IsEmbedding (fun q : univ ×ˢ Ico (0 : ℝ) epsilon => map q.1)
  into_region : ∀ x t, 0 < t → t < epsilon → map (x, t) ∈ U
  closed_side : F.image ⊆ closure U
  boundary_strata : ∀ x t, t ∈ Ico (0 : ℝ) epsilon →
    (map (x, t) ∈ (𝓡∂ 3).boundary M ↔ x ∈ S.boundary)
  immersion : ∀ q ∈ univ ×ˢ Ico (0 : ℝ) epsilon,
    Function.Injective (mfderivWithin ((𝓡∂ 2).prod 𝓘(ℝ)) (𝓡∂ 3)
      map (univ ×ˢ Ico (0 : ℝ) epsilon) q)

-- Held sibling documentation omitted during mechanical union.
/-- Uniform chartwise C^k convergence, including derivatives within the source half-space. -/
def ConvergesC (k : ℕ) {S : CompactOrientedSurface.{0}}
    (stage : ℝ → NeatEmbedding S E.Carrier) (A : NeatEmbedding S E.Carrier) : Prop :=
  ∀ a : S, ∀ b : E.Carrier, ∀ H : Set E2, IsCompact H →
    H ⊆ (extChartAt (𝓡∂ 2) a).target →
    (∀ y ∈ H, A.toFun ((extChartAt (𝓡∂ 2) a).symm y) ∈ (extChartAt (𝓡∂ 3) b).source) →
    ∀ eps : ℝ, 0 < eps → ∃ delta : ℝ, 0 < delta ∧
      ∀ t ∈ Ioc (0 : ℝ) delta, ∀ y ∈ H,
        (stage t).toFun ((extChartAt (𝓡∂ 2) a).symm y) ∈ (extChartAt (𝓡∂ 3) b).source ∧
        ∀ n : ℕ, n ≤ k →
          ‖iteratedFDerivWithin ℝ n
            (extChartAt (𝓡∂ 3) b ∘ (stage t).toFun ∘ (extChartAt (𝓡∂ 2) a).symm)
            (extChartAt (𝓡∂ 2) a).target y -
            iteratedFDerivWithin ℝ n
            (extChartAt (𝓡∂ 3) b ∘ A.toFun ∘ (extChartAt (𝓡∂ 2) a).symm)
            (extChartAt (𝓡∂ 2) a).target y‖ < eps

/-- The cut-open component is literally a topological disc with its whole boundary on Γ. -/
def HasDiscPatch {S : CompactOrientedSurface.{0}} (A : NeatEmbedding S E.Carrier)
    (Γ : Set E.Carrier) : Prop :=
  ∃ x : S, x ∉ A.toFun ⁻¹' Γ ∧ ∃ e : ClosedDisk ≃ₜ closure (connectedComponentIn (A.toFun ⁻¹' Γ)ᶜ x),
    (fun z => (e z).1) '' closedDiskBoundary =
      closure (connectedComponentIn (A.toFun ⁻¹' Γ)ᶜ x) ∩ A.toFun ⁻¹' Γ

/-- The source's chosen disjoint discs and subtract-a-constant cores are output data. -/
structure InteriorPerturbation (A B : IncompressibleSpanningSurface.{0} E)
    (g : SmoothMetric E.Carrier) where
  tangencies : Finset E.Carrier
  tangencies_exact : (tangencies : Set E.Carrier) = interiorTangencies A.1.embedding B.1.embedding
  chart : ∀ p : tangencies, InteriorGraph A B p.1
  coreRadius : ∀ p : tangencies, ℝ
  core_pos : ∀ p, 0 < coreRadius p
  core_inside : ∀ p, coreRadius p < (chart p).R
  bump : ∀ p : tangencies, E2 → ℝ
  bump_smooth : ∀ p, ContDiff ℝ ∞ (bump p)
  bump_bounds : ∀ p x, 0 ≤ bump p x ∧ bump p x ≤ 1
  bump_support : ∀ p, tsupport (bump p) ⊆ Metric.ball (0 : E2) (chart p).R
  bump_core : ∀ p x, ‖x‖ ≤ coreRadius p → bump p x = 1
  domains_disjoint : Pairwise (fun p q => Disjoint (chart p).coordinates.source (chart q).coordinates.source)
  only_critical : ∀ p x, ‖x‖ < (chart p).R →
    (fderiv ℝ (graphDifference (chart p)) x = 0 ↔ x = 0)
  changes_sign : ∀ p, ∀ V : Set E2, V ∈ 𝓝 (0 : E2) →
    (∃ x ∈ V ∩ Metric.ball 0 (chart p).R, 0 < graphDifference (chart p) x) ∧
    (∃ x ∈ V ∩ Metric.ball 0 (chart p).R, graphDifference (chart p) x < 0)

def excludedBalls (g : SmoothMetric E.Carrier) (Tg : Finset E.Carrier) (r : ℝ) : Set E.Carrier :=
  ⋃ p ∈ Tg, metricBall g p r

def goodRegion (g : SmoothMetric E.Carrier) (Tg : Finset E.Carrier) (r : ℝ) : Set E.Carrier :=
  (excludedBalls g Tg r)ᶜ

def T2DistanceRamp {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}
    (D : B1OriginalData g J) (Tg : Finset E.Carrier) (r0 r1 rho2 : ℝ)
    (p : E.Carrier) : ℝ :=
  min (cappedDistance g rho2 (excludedBalls g Tg rho2) p)
    (cappedDistance g rho2 {x | extendedRadial D r0 x ≤ r1 / 2} p)

def T1DistanceRamp (g : SmoothMetric E.Carrier) (Tg : Finset E.Carrier)
    (rho2 : ℝ) (p : E.Carrier) : ℝ :=
  cappedDistance g rho2 (excludedBalls g Tg rho2) p

def rawWidth (eta1 eta2 kappa1 : ℝ) (w : M → ℝ) (p : M) : ℝ :=
  min eta1 (eta2 + kappa1 / 2 * w p)

def wedgeSector (alpha : ℝ) : Set E3 :=
  {y | Real.cot (alpha / 2) * |y 2| < y 1}

def wedgeBoundary (alpha : ℝ) : Set E3 :=
  {y | y 1 = Real.cot (alpha / 2) * |y 2|}

/-- A straightened genuine wedge. The ambient chart remains smooth, its
metric is normalized on the seam, and the selected sector is the given region. -/
structure CornerWedgeWitness (g : SmoothMetric M) (F seams : Set M) (p : M) where
  chart : OpenPartialHomeomorph M E3
  point_mem : p ∈ chart.source
  source_interior : chart.source ⊆ (𝓡∂ 3).interior M
  smooth : ContMDiffOn (𝓡∂ 3) 𝓘(ℝ, E3) ∞ chart chart.source
  inverse_smooth : ContMDiffOn 𝓘(ℝ, E3) (𝓡∂ 3) ∞ chart.symm chart.target
  angle : ℝ → ℝ
  angle_c1 : ContDiff ℝ 1 angle
  angle_range : ∀ y ∈ chart.target, angle (y 0) ∈ Ioo (0 : ℝ) Real.pi
  surface_image : chart '' (F ∩ chart.source) =
    {y ∈ chart.target | y ∈ wedgeBoundary (angle (y 0))}
  seam_image : chart '' (seams ∩ chart.source) =
    {y ∈ chart.target | y 1 = 0 ∧ y 2 = 0}
  sheetPlus : E2 → M
  sheetMinus : E2 → M
  sheets_smooth : ContMDiffOn 𝓘(ℝ, E2) (𝓡∂ 3) ∞ sheetPlus
      {z | (EuclideanSpace.equiv (Fin 3) ℝ).symm
        ![z 0, Real.cot (angle (z 0) / 2) * z 1, z 1] ∈ chart.target} ∧
    ContMDiffOn 𝓘(ℝ, E2) (𝓡∂ 3) ∞ sheetMinus
      {z | (EuclideanSpace.equiv (Fin 3) ℝ).symm
        ![z 0, -Real.cot (angle (z 0) / 2) * z 1, z 1] ∈ chart.target}
  sheets_exact : ∀ z : E2,
    ((EuclideanSpace.equiv (Fin 3) ℝ).symm
      ![z 0, Real.cot (angle (z 0) / 2) * z 1, z 1] ∈ chart.target →
      sheetPlus z = chart.symm ((EuclideanSpace.equiv (Fin 3) ℝ).symm
        ![z 0, Real.cot (angle (z 0) / 2) * z 1, z 1])) ∧
    ((EuclideanSpace.equiv (Fin 3) ℝ).symm
      ![z 0, -Real.cot (angle (z 0) / 2) * z 1, z 1] ∈ chart.target →
      sheetMinus z = chart.symm ((EuclideanSpace.equiv (Fin 3) ℝ).symm
        ![z 0, -Real.cot (angle (z 0) / 2) * z 1, z 1]))
  metric_normalized : ∀ y ∈ chart.target, y 1 = 0 → y 2 = 0 → ∀ i j : Fin 3,
    g.inner (chart.symm y)
      (mfderiv 𝓘(ℝ, E3) (𝓡∂ 3) chart.symm y
        ((NormedSpace.fromTangentSpace y).symm (coordinateVector 3 i)))
      (mfderiv 𝓘(ℝ, E3) (𝓡∂ 3) chart.symm y
        ((NormedSpace.fromTangentSpace y).symm (coordinateVector 3 j))) = if i = j then 1 else 0

structure CorneredSurface (g : SmoothMetric M) where
  source : CompactOrientedSurface.{0}
  surface : GeometricPiecewiseSurface source M
  seams : Set M
  seams_exact : seams = surface.map '' surface.seam.carrier
  seams_finite_closed : FiniteClosedIntersection seams
  seam_boundary_disjoint : Disjoint seams (surface.map '' source.boundary)
  corner : ∀ p, p ∈ seams → CornerWedgeWitness g surface.image seams p

def cornerAngle {g : SmoothMetric M} (F : CorneredSurface g) (p : M) : ℝ :=
  by
  classical
  exact if h : p ∈ F.seams then
    let W := F.corner p h
    let alpha := W.angle ((W.chart p) 0)
    min alpha (Real.pi - alpha)
  else 0

def SelectedCornerRegion {g : SmoothMetric M} (F : CorneredSurface g) (U : Set M) : Prop :=
  IsOpen U ∧ F.surface.image = frontier U ∧ ∀ p (h : p ∈ F.seams),
    let W := F.corner p h
    W.chart '' (U ∩ W.chart.source) =
      {y ∈ W.chart.target | y ∈ wedgeSector (W.angle (y 0))}

def ambientCurveVelocity (c : ℝ → M) (s : ℝ) : TangentSpace (𝓡∂ 3) (c s) :=
  mfderiv 𝓘(ℝ) (𝓡∂ 3) c s ((NormedSpace.fromTangentSpace s).symm 1)

def ambientCurveLength (g : SmoothMetric M) (c : ℝ → M) (a b : ℝ) : ℝ :=
  ∫ s in a..b, Real.sqrt (g.inner (c s) (ambientCurveVelocity c s) (ambientCurveVelocity c s))

/-- The affine geodesic equation for the actual coordinate metric. -/
def IsMetricGeodesic (g : SmoothMetric M) (c : ℝ → M) : Prop :=
  ContMDiffOn 𝓘(ℝ) (𝓡∂ 3) ∞ c (Icc (0 : ℝ) 1) ∧
  c '' Icc (0 : ℝ) 1 ⊆ (𝓡∂ 3).interior M ∧
  ∀ s ∈ Ioo (0 : ℝ) 1, ∀ b : M, c s ∈ (extChartAt (𝓡∂ 3) b).source →
    ∀ k : Fin 3,
      deriv (fun u => deriv (fun z => (extChartAt (𝓡∂ 3) b (c z)) k) u) s +
        ∑ i : Fin 3, ∑ j : Fin 3,
          christoffel (SeifertSurfaces.AppendixC.MetricInChart (𝓡∂ 3) g b)
            (extChartAt (𝓡∂ 3) b (c s)) i j k *
            deriv (fun z => (extChartAt (𝓡∂ 3) b (c z)) i) s *
            deriv (fun z => (extChartAt (𝓡∂ 3) b (c z)) j) s = 0

def seamEDist (g : SmoothMetric M) (Γ : Set M) (p q : M) : ℝ≥0∞ :=
  ⨅ c : {c : ℝ → M // ContMDiffOn 𝓘(ℝ) (𝓡∂ 3) 1 c (Icc (0 : ℝ) 1) ∧
    c '' Icc (0 : ℝ) 1 ⊆ Γ ∧ c 0 = p ∧ c 1 = q},
    ENNReal.ofReal (ambientCurveLength g c.1 0 1)

def normalToSeam (g : SmoothMetric M) (Γ : Set M)
    (p : M) (v : TangentSpace (𝓡∂ 3) p) : Prop :=
  ∀ γ : ClosedIntersectionComponent Γ, ∀ s : ℝ, ∀ h : curveAt γ s = p,
    g.inner p v (h ▸ ambientCurveVelocity (curveAt γ) s) = 0

structure NormalExponentialGeometry (g : SmoothMetric M) (Γ : Set M) where
  domain : Set (Σ x : Γ, TangentSpace (𝓡∂ 3) x.1)
  exp : (Σ x : Γ, TangentSpace (𝓡∂ 3) x.1) → M
  zero_domain : ∀ x : Γ, (⟨x, 0⟩ : Σ x : Γ, TangentSpace (𝓡∂ 3) x.1) ∈ domain
  exp_zero : ∀ x : Γ, exp ⟨x, 0⟩ = x.1
  domain_exact : ∀ v, v ∈ domain ↔
    ∃ c : ℝ → M, ∃ h : c 0 = v.1.1,
      IsMetricGeodesic g c ∧ (h ▸ ambientCurveVelocity c 0) = v.2
  geodesic : ∀ v ∈ domain, ∃ c : ℝ → M, ∃ h : c 0 = v.1.1,
    IsMetricGeodesic g c ∧ (h ▸ ambientCurveVelocity c 0) = v.2 ∧ c 1 = exp v

def normalReachDomain {g : SmoothMetric M} {Γ : Set M}
    (N : NormalExponentialGeometry g Γ) (p : M) (rho : ℝ) :
    Set (Σ x : Γ, TangentSpace (𝓡∂ 3) x.1) :=
  {v | normalToSeam g Γ v.1.1 v.2 ∧
    Real.sqrt (g.inner v.1.1 v.2 v.2) < rho ∧ seamEDist g Γ v.1.1 p < ENNReal.ofReal rho}

def localReach {g : SmoothMetric M} {Γ : Set M}
    (N : NormalExponentialGeometry g Γ) (p : M) : ℝ :=
  sSup {rho : ℝ | 0 < rho ∧ normalReachDomain N p rho ⊆ N.domain ∧
    Set.InjOn N.exp (normalReachDomain N p rho) ∧ IsPreconnected (metricBall g p rho ∩ Γ)}

def actualSurfaceGram (g : SmoothMetric M) (f : E2 → M) (z : E2) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  let d := mfderiv 𝓘(ℝ, E2) (𝓡∂ 3) f z
  fun i j => g.inner (f z)
    (d ((NormedSpace.fromTangentSpace z).symm (coordinateVector 2 i)))
    (d ((NormedSpace.fromTangentSpace z).symm (coordinateVector 2 j)))

def actualSliceDensity (g : SmoothMetric M) (f : E2 → M)
    (s eta : ℝ) : ℝ :=
  ∫ r in (-eta)..eta,
    Real.sqrt (Matrix.det (actualSurfaceGram g f
      ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![s, r])))

def sourceWidthLower (gain : ℝ → ℝ) (C1 Cmet M theta rho rhoBoundary : ℝ) : ℝ :=
  min (rho / (2 * Real.sqrt (1 + Real.cot (theta / 2) ^ 2)))
    (min (Real.sqrt (gain theta / (8 * M ^ 2)))
      (min (gain theta / (4 * C1))
        (min (gain theta / (24 * Cmet * (1 + Real.cot (theta / 2) ^ 2)))
          (rhoBoundary / 2))))

def sourceDerivativeLower (gain : ℝ → ℝ) (theta : ℝ) : ℝ :=
  Real.sqrt (gain theta) / (6 * Real.cot (theta / 2))

def Separates (F : Set M) : Prop :=
  ∃ x ∈ Fᶜ, ∃ y ∈ Fᶜ, y ∉ connectedComponentIn Fᶜ x

/-- Source-faithful C1 smoothing of the literal ramp: the error is uniformly
controlled at the stated scale, with the two source plateaus and the absolute
arclength derivative bound preserved. -/
structure RampSmoothing {Γ : Set E.Carrier} (g : SmoothMetric E.Carrier)
    (rho2 eta1 eta2 kappa1 : ℝ) (w eta : E.Carrier → ℝ) where
  scale : ℝ
  scale_pos : 0 < scale
  scale_small : scale < rho2 / 100
  error : E.Carrier → ℝ
  literal_binding : ∀ p ∈ Γ, eta p = rawWidth eta1 eta2 kappa1 w p + error p
  error_bound : ∀ p ∈ Γ, |error p| ≤ kappa1 * scale
  error_local : ∀ p ∈ Γ, error p ≠ 0 →
    ∃ q ∈ Γ, seamEDist g Γ p q < ENNReal.ofReal scale ∧
      ∃ γ : ClosedIntersectionComponent Γ, ∃ s : ℝ,
        curveAt γ s = q ∧ ¬ ContDiffAt ℝ 1
          (rawWidth eta1 eta2 kappa1 w ∘ curveAt γ) s
  smooth : ∀ γ : ClosedIntersectionComponent Γ, ContDiff ℝ 1 (eta ∘ curveAt γ)
  low_plateau : ∀ p ∈ Γ, w p = 0 → eta p = eta2
  high_plateau : ∀ p ∈ Γ, w p = rho2 → eta p = eta1
  global_derivative : ∀ γ : ClosedIntersectionComponent Γ, ∀ s : ℝ,
    |deriv (eta ∘ curveAt γ) s| ≤ kappa1 * curveSpeed g γ s

structure SheetFrontier {S R : CompactOrientedSurface.{0}}
    (g : SmoothMetric M) (A : NeatEmbedding S M) (B : NeatEmbedding R M) where
  cornered : CorneredSurface g
  region : Set M
  selected_region : SelectedCornerRegion cornered region
  image_sheets : cornered.surface.image ⊆ A.image ∪ B.image
  seams_in_intersection : cornered.seams ⊆ A.image ∩ B.image

/-- Admissibility uses the absolute arclength derivative, not a relative logarithmic bound. -/
def AdmissibleWidth {Γ : Set M} (g : SmoothMetric M)
    (etaMax kappa eta : M → ℝ) : Prop :=
  (∀ p ∈ Γ, 0 < eta p ∧ eta p ≤ etaMax p) ∧
  ∀ γ : ClosedIntersectionComponent Γ,
    ContDiff ℝ 1 (eta ∘ curveAt γ) ∧
    ∀ s : ℝ, |deriv (eta ∘ curveAt γ) s| ≤ kappa (curveAt γ s) * curveSpeed g γ s

def widthTube (g : SmoothMetric M) (Γ : Set M)
    (eta : M → ℝ) : Set M :=
  {p | ∃ x ∈ Γ, metricEDist g p x < ENNReal.ofReal (eta x)}

structure CornerControl (g : SmoothMetric M) (F : CorneredSurface g)
    (cutoff : SeifertSurfaces.AppendixB.RoundingCutoff) where
  etaMax : M → ℝ
  kappa : M → ℝ
  caps_positive : ∀ p ∈ F.seams, 0 < etaMax p ∧ 0 < kappa p
  caps_continuous : ContinuousOn etaMax F.seams ∧ ContinuousOn kappa F.seams
  chart : ∀ p, p ∈ F.seams → CornerWedgeWitness g F.surface.image F.seams p
  chart_angle : ∀ p hp,
    let W := chart p hp
    min (W.angle ((W.chart p) 0)) (Real.pi - W.angle ((W.chart p) 0)) = cornerAngle F p
  selected_chart_side : ∀ U : Set M, SelectedCornerRegion F U → ∀ p hp,
    let W := chart p hp
    W.chart '' (U ∩ W.chart.source) = {y ∈ W.chart.target | y ∈ wedgeSector (W.angle (y 0))}
  normalGeometry : NormalExponentialGeometry g F.seams
  reach : M → ℝ
  reach_exact : reach = localReach normalGeometry
  reach_positive : ∀ p ∈ F.seams, 0 < reach p
  boundary_cap : ∀ p ∈ F.seams, ENNReal.ofReal (2 * etaMax p) ≤ boundaryEDist g p
  C2Bound : ℝ
  slopeBound : ℝ
  metricBound : ℝ
  bounds_positive : 0 < C2Bound ∧ 0 < slopeBound ∧ 0 < metricBound
  cap_lower_bound : ∀ p ∈ F.seams, ∀ rhoBoundary : ℝ,
    0 < rhoBoundary → ENNReal.ofReal rhoBoundary ≤ boundaryEDist g p →
    sourceWidthLower (SeifertSurfaces.AppendixB.angleGain cutoff) C2Bound metricBound
      slopeBound (cornerAngle F p) (reach p) rhoBoundary ≤ etaMax p ∧
    sourceDerivativeLower (SeifertSurfaces.AppendixB.angleGain cutoff) (cornerAngle F p) ≤ kappa p
  chart_estimates : ∀ p (hp : p ∈ F.seams),
    let W := chart p hp
    (∀ y ∈ W.chart.target, ∀ i j : Fin 3,
      |g.inner (W.chart.symm y)
        (mfderiv 𝓘(ℝ, E3) (𝓡∂ 3) W.chart.symm y
          ((NormedSpace.fromTangentSpace y).symm (coordinateVector 3 i)))
        (mfderiv 𝓘(ℝ, E3) (𝓡∂ 3) W.chart.symm y
          ((NormedSpace.fromTangentSpace y).symm (coordinateVector 3 j))) -
        (if i = j then 1 else 0)| ≤ metricBound * Real.sqrt ((y 1) ^ 2 + (y 2) ^ 2)) ∧
    (∀ u, (EuclideanSpace.equiv (Fin 3) ℝ).symm ![u, 0, 0] ∈ W.chart.target →
      |deriv (fun z => Real.cot (W.angle z / 2)) u| ≤ slopeBound) ∧
    (∀ n ≤ 2, ∀ z : E2,
      let D := {z : E2 | (EuclideanSpace.equiv (Fin 3) ℝ).symm
        ![z 0, Real.cot (W.angle (z 0) / 2) * z 1, z 1] ∈ W.chart.target}
      z ∈ D → ‖iteratedFDerivWithin ℝ n (W.chart ∘ W.sheetPlus) D z‖ ≤ C2Bound) ∧
    (∀ n ≤ 2, ∀ z : E2,
      let D := {z : E2 | (EuclideanSpace.equiv (Fin 3) ℝ).symm
        ![z 0, -Real.cot (W.angle (z 0) / 2) * z 1, z 1] ∈ W.chart.target}
      z ∈ D → ‖iteratedFDerivWithin ℝ n (W.chart ∘ W.sheetMinus) D z‖ ≤ C2Bound) ∧
    let u := (W.chart p) 0
    let m := Real.cot (W.angle u / 2)
    let m' := deriv (fun z => Real.cot (W.angle z / 2)) u
    let theta := cornerAngle F p
    8 * (etaMax p) ^ 2 * m' ^ 2 ≤ SeifertSurfaces.AppendixB.angleGain cutoff theta ∧
    36 * m ^ 2 * (kappa p) ^ 2 ≤ SeifertSurfaces.AppendixB.angleGain cutoff theta ∧
    4 * C2Bound * etaMax p ≤ SeifertSurfaces.AppendixB.angleGain cutoff theta ∧
    24 * metricBound * etaMax p * (1 + m ^ 2) ≤ SeifertSurfaces.AppendixB.angleGain cutoff theta ∧
    2 * etaMax p * Real.sqrt (1 + m ^ 2) ≤ reach p

/-- An actual smooth replacement graph for the original C1 width. Its height is
constructed independently of the unsmoothed Appendix B.1 formula. The same
newMap is used by normal geometry, final fibers and original-eta metric gain. -/
structure SmoothSliceReplacement {g : SmoothMetric M} (F : CorneredSurface g)
    {cutoff : SeifertSurfaces.AppendixB.RoundingCutoff} (C : CornerControl g F cutoff)
    (eta : M → ℝ) (p : M) (hp : p ∈ F.seams)
    (interval : Set ℝ) (base : ℝ → F.seams) (radius : ℝ) (newMap : E2 → M) where
  height : E2 → ℝ
  height_smooth : ContDiffOn ℝ ∞ height
    {z | z 0 ∈ interval ∧ |z 1| < eta (base (z 0)).1}
  map_exact : ∀ u ∈ interval, ∀ r, |r| ≤ eta (base u).1 →
    newMap ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![u, r]) =
      (C.chart p hp).chart.symm ((EuclideanSpace.equiv (Fin 3) ℝ).symm
        ![u, height ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![u, r]), r])
  coordinates_target : ∀ u ∈ interval, ∀ r, |r| ≤ eta (base u).1 →
    (EuclideanSpace.equiv (Fin 3) ℝ).symm
      ![u, height ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![u, r]), r]
        ∈ (C.chart p hp).chart.target
  radial_cap : ∀ u ∈ interval, ∀ r, |r| ≤ eta (base u).1 →
    Real.sqrt ((height ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![u, r])) ^ 2 + r ^ 2)
      ≤ radius / 2
  closed_side : ∀ u ∈ interval, ∀ r, |r| ≤ eta (base u).1 →
    Real.cot ((C.chart p hp).angle u / 2) * |r| ≤
      height ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![u, r])
  endpoint_match : ∀ u ∈ interval, ∀ r, |r| = eta (base u).1 →
    height ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![u, r]) =
      Real.cot ((C.chart p hp).angle u / 2) * |r|

structure SmallSliceGeometry {g : SmoothMetric M} (F : CorneredSurface g)
    {cutoff : SeifertSurfaces.AppendixB.RoundingCutoff} (C : CornerControl g F cutoff)
    (eta : M → ℝ) (f : NeatEmbedding F.source M) (p : M) (hp : p ∈ F.seams) where
  interval : Set ℝ
  interval_open : IsOpen interval
  center_mem : ((C.chart p hp).chart p) 0 ∈ interval
  radius : ℝ
  radius_pos : 0 < radius
  radius_reach : radius ≤ C.reach p
  branch_domain : normalReachDomain C.normalGeometry p radius ⊆ C.normalGeometry.domain
  branch_injective : Set.InjOn C.normalGeometry.exp (normalReachDomain C.normalGeometry p radius)
  branch_connected : IsPreconnected (metricBall g p radius ∩ F.seams)
  base : ℝ → F.seams
  base_exact : ∀ u ∈ interval, (base u).1 = (C.chart p hp).chart.symm
    ((EuclideanSpace.equiv (Fin 3) ℝ).symm ![u, 0, 0])
  axis_domain : ∀ u ∈ interval,
    (EuclideanSpace.equiv (Fin 3) ℝ).symm ![u, 0, 0] ∈ (C.chart p hp).chart.target
  base_unit_speed : ∀ u ∈ interval,
    g.inner (base u).1 (ambientCurveVelocity (fun v => (base v).1) u)
      (ambientCurveVelocity (fun v => (base v).1) u) = 1
  normalCoordinates : E3 → (Σ x : F.seams, TangentSpace (𝓡∂ 3) x.1)
  normal_coordinates_base : ∀ y ∈ (C.chart p hp).chart.target, y 0 ∈ interval →
    (normalCoordinates y).1 = base (y 0)
  normal_coordinates_branch : ∀ y ∈ (C.chart p hp).chart.target, y 0 ∈ interval →
    Real.sqrt ((y 1) ^ 2 + (y 2) ^ 2) ≤ radius / 2 →
    normalCoordinates y ∈ normalReachDomain C.normalGeometry p radius ∧
    C.normalGeometry.exp (normalCoordinates y) = (C.chart p hp).chart.symm y ∧
    Real.sqrt (g.inner (normalCoordinates y).1.1 (normalCoordinates y).2
      (normalCoordinates y).2) ≤ (3 / 2 : ℝ) * Real.sqrt ((y 1) ^ 2 + (y 2) ^ 2)
  oldMap : E2 → M
  newMap : E2 → M
  old_profile : ∀ u ∈ interval, ∀ r, |r| ≤ eta (base u).1 →
    oldMap ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![u, r]) =
      (C.chart p hp).chart.symm ((EuclideanSpace.equiv (Fin 3) ℝ).symm
        ![u, Real.cot ((C.chart p hp).angle u / 2) * |r|, r])
  replacement : SmoothSliceReplacement F C eta p hp interval base radius newMap
  capped_coordinates : ∀ u ∈ interval,
    0 < eta (base u).1 ∧
    2 * eta (base u).1 * Real.sqrt (1 + Real.cot ((C.chart p hp).angle u / 2) ^ 2) ≤ radius ∧
    ∀ r, |r| ≤ eta (base u).1 →
      (EuclideanSpace.equiv (Fin 3) ℝ).symm
        ![u, Real.cot ((C.chart p hp).angle u / 2) * |r|, r] ∈ (C.chart p hp).chart.target
  normals_small : ∀ u ∈ interval, ∀ r, |r| ≤ eta (base u).1 →
    let yOld := (EuclideanSpace.equiv (Fin 3) ℝ).symm
      ![u, Real.cot ((C.chart p hp).angle u / 2) * |r|, r]
    let yNew := (EuclideanSpace.equiv (Fin 3) ℝ).symm
      ![u, replacement.height ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![u, r]), r]
    normalCoordinates yOld ∈ normalReachDomain C.normalGeometry p radius ∧
    normalCoordinates yNew ∈ normalReachDomain C.normalGeometry p radius ∧
    C.normalGeometry.exp (normalCoordinates yOld) = oldMap ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![u, r]) ∧
    C.normalGeometry.exp (normalCoordinates yNew) = newMap ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![u, r])
  old_fiber_exact : ∀ u ∈ interval,
    oldMap '' {z : E2 | z 0 = u ∧ |z 1| ≤ eta (base u).1} =
      F.surface.image ∩ (C.chart p hp).chart.source ∩
        {q | ((C.chart p hp).chart q) 0 = u ∧ |((C.chart p hp).chart q) 2| ≤ eta (base u).1}
  new_fiber_exact : ∀ u ∈ interval,
    newMap '' {z : E2 | z 0 = u ∧ |z 1| ≤ eta (base u).1} =
      f.image ∩ (C.chart p hp).chart.source ∩
        {q | ((C.chart p hp).chart q) 0 = u ∧ |((C.chart p hp).chart q) 2| ≤ eta (base u).1}
  old_regular : ContMDiffOn 𝓘(ℝ, E2) (𝓡∂ 3) ∞ oldMap
    {z | z 0 ∈ interval ∧ 0 < |z 1| ∧ |z 1| < eta (base (z 0)).1}
  new_regular : ContMDiffOn 𝓘(ℝ, E2) (𝓡∂ 3) ∞ newMap
    {z | z 0 ∈ interval ∧ |z 1| < eta (base (z 0)).1}
  local_embedding : Set.InjOn oldMap {z | z 0 ∈ interval ∧ |z 1| ≤ eta (base (z 0)).1} ∧
    Set.InjOn newMap {z | z 0 ∈ interval ∧ |z 1| ≤ eta (base (z 0)).1}

structure SliceAreaComparison {g : SmoothMetric M} (F : CorneredSurface g)
    {cutoff : SeifertSurfaces.AppendixB.RoundingCutoff} (C : CornerControl g F cutoff)
    (eta : M → ℝ) (f : NeatEmbedding F.source M) where
  slice : ∀ p (hp : p ∈ F.seams), SmallSliceGeometry F C eta f p hp
  slice_nonnegative : ∀ p hp, ∀ u ∈ (slice p hp).interval,
    0 ≤ actualSliceDensity g (slice p hp).oldMap u (eta ((slice p hp).base u).1) -
      actualSliceDensity g (slice p hp).newMap u (eta ((slice p hp).base u).1)
  slice_gain : ∀ p hp, ∀ u ∈ (slice p hp).interval,
    SeifertSurfaces.AppendixB.angleGain cutoff (cornerAngle F ((slice p hp).base u).1) *
      eta ((slice p hp).base u).1 ≤
      actualSliceDensity g (slice p hp).oldMap u (eta ((slice p hp).base u).1) -
      actualSliceDensity g (slice p hp).newMap u (eta ((slice p hp).base u).1)

structure RoundedSurface {g : SmoothMetric M} (F : CorneredSurface g)
    {cutoff : SeifertSurfaces.AppendixB.RoundingCutoff} (C : CornerControl g F cutoff) (eta : M → ℝ) where
  embedding : NeatEmbedding F.source M
  agrees : embedding.image \ widthTube g F.seams eta = F.surface.image \ widthTube g F.seams eta
  boundary_exact : exteriorBoundary embedding = F.surface.map '' F.source.boundary
  local_closed_side : ∀ p hp,
    let W := C.chart p hp
    W.chart '' (embedding.image ∩ widthTube g F.seams eta ∩ W.chart.source) ⊆
      {y ∈ W.chart.target | Real.cot (W.angle (y 0) / 2) * |y 2| ≤ y 1}
  region_collar : ∀ U : Set M, SelectedCornerRegion F U →
    embedding.image ⊆ closure U ∧ Nonempty (OneSidedCollar embedding U)
  closed_separating : F.surface.map '' F.source.boundary = ∅ → Separates F.surface.image →
    exteriorBoundary embedding = ∅ ∧ Separates embedding.image
  isotopy : TopologicalAmbientIsotopy M
  isotopy_image : (isotopy.stage 1) '' F.surface.image = embedding.image
  support : ∀ t p, p ∉ widthTube g F.seams eta → isotopy.stage t p = p
  complementary_regions : ∀ x, x ∉ F.surface.image →
    let R := connectedComponentIn F.surface.imageᶜ x
    let Rnew := connectedComponentIn embedding.imageᶜ (isotopy.stage 1 x)
    (isotopy.stage 1) '' R = Rnew ∧ Rnew \ widthTube g F.seams eta = R \ widthTube g F.seams eta
  geometric_bridge : ∃ G : GeometricPiecewiseSurface F.source M,
    G.map = embedding.continuousMap ∧ G.seam.carrier = ∅ ∧
    GeometricImageIsotopic F.surface G ∧ geometricArea g G = area g embedding.toFun
  slices : SliceAreaComparison F C eta embedding
  integral_nonnegative : ∀ γ : ClosedIntersectionComponent F.seams,
    0 ≤ curveIntegral g γ (fun p => SeifertSurfaces.AppendixB.angleGain cutoff (cornerAngle F p) * eta p)
  total_area : ∀ n (γ : Fin n → ClosedIntersectionComponent F.seams),
    Pairwise (fun i j => Disjoint (range (γ i).parameter) (range (γ j).parameter)) →
    (⋃ i, range (γ i).parameter) = F.seams →
    area g embedding.toFun ≤ geometricArea g F.surface -
      ∑ i, curveIntegral g (γ i) (fun p => SeifertSurfaces.AppendixB.angleGain cutoff (cornerAngle F p) * eta p)

structure CornerRoundingProvider (cutoff : SeifertSurfaces.AppendixB.RoundingCutoff) where
  produce : ∀ (M : Type) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M], ∀ g : SmoothMetric M, ∀ F : CorneredSurface g,
      ∃ C : CornerControl g F cutoff, ∀ eta : M → ℝ,
        AdmissibleWidth (Γ := F.seams) g C.etaMax C.kappa eta → Nonempty (RoundedSurface F C eta)

structure CompactRiemannianAmbient where
  carrier : Type
  [topology : TopologicalSpace carrier]
  [hausdorff : T2Space carrier]
  [secondCountable : SecondCountableTopology carrier]
  [compact : CompactSpace carrier]
  [charted : ChartedSpace (EuclideanHalfSpace 3) carrier]
  [manifold : IsManifold (𝓡∂ 3) ∞ carrier]
  metric : SmoothMetric carrier

attribute [instance] CompactRiemannianAmbient.topology CompactRiemannianAmbient.hausdorff
  CompactRiemannianAmbient.secondCountable CompactRiemannianAmbient.compact
  CompactRiemannianAmbient.charted CompactRiemannianAmbient.manifold

structure CompactCornerLocalization [T2Space M] [SecondCountableTopology M]
    {g : SmoothMetric M} (F : CorneredSurface g)
    {cutoff : SeifertSurfaces.AppendixB.RoundingCutoff} (C : CornerControl g F cutoff) where
  ambient : CompactRiemannianAmbient
  neighborhood : OpenPartialHomeomorph M ambient.carrier
  source_relatively_compact : IsCompact (closure neighborhood.source)
  surface_inside : F.surface.image ⊆ neighborhood.source
  smooth : ContMDiffOn (𝓡∂ 3) (𝓡∂ 3) ∞ neighborhood neighborhood.source
  inverse_smooth : ContMDiffOn (𝓡∂ 3) (𝓡∂ 3) ∞ neighborhood.symm neighborhood.target
  boundary_strata : ∀ p ∈ neighborhood.source,
    (neighborhood p ∈ (𝓡∂ 3).boundary ambient.carrier ↔ p ∈ (𝓡∂ 3).boundary M)
  differential_bijective : ∀ p ∈ neighborhood.source,
    Function.Bijective (mfderiv (𝓡∂ 3) (𝓡∂ 3) neighborhood p)
  metric_isometry : ∀ p ∈ neighborhood.source, ∀ v w,
    ambient.metric.inner (neighborhood p)
      (mfderiv (𝓡∂ 3) (𝓡∂ 3) neighborhood p v)
      (mfderiv (𝓡∂ 3) (𝓡∂ 3) neighborhood p w) = g.inner p v w
  model : CorneredSurface ambient.metric
  parametrization : F.source ≃ₜ model.source
  parametrization_boundary : parametrization '' F.source.boundary = model.source.boundary
  model_map : ∀ x : F.source,
    model.surface.map (parametrization x) = neighborhood (F.surface.map x)
  model_seams : model.seams = neighborhood '' F.seams
  seam_forward : ∀ p ∈ F.seams, neighborhood p ∈ model.seams
  model_angle : ∀ p ∈ F.seams, cornerAngle model (neighborhood p) = cornerAngle F p
  model_area : geometricArea ambient.metric model.surface = geometricArea g F.surface
  modelControl : CornerControl ambient.metric model cutoff
  caps_transport : ∀ p ∈ F.seams,
    modelControl.etaMax (neighborhood p) = C.etaMax p ∧
    modelControl.kappa (neighborhood p) = C.kappa p
  charts_transport : ∀ p (hp : p ∈ F.seams)
      (hm : neighborhood p ∈ model.seams),
    let W := C.chart p hp
    let V := modelControl.chart (neighborhood p) hm
    W.chart.source ⊆ neighborhood.source ∧
    neighborhood '' W.chart.source = V.chart.source ∧
    W.chart.target = V.chart.target ∧
    (∀ q ∈ W.chart.source, V.chart (neighborhood q) = W.chart q) ∧
    (∀ u, V.angle u = W.angle u)
  tubes_local : widthTube g F.seams C.etaMax ⊆ neighborhood.source ∧
    widthTube ambient.metric model.seams modelControl.etaMax ⊆ neighborhood.target
  distance_transport : ∀ p ∈ F.seams, ∀ q ∈ neighborhood.source,
    min (metricEDist g q p) (ENNReal.ofReal (C.etaMax p)) =
      min (metricEDist ambient.metric (neighborhood q) (neighborhood p))
        (ENNReal.ofReal (modelControl.etaMax (neighborhood p)))
  widths_transport : ∀ eta : M → ℝ,
    AdmissibleWidth (Γ := F.seams) g C.etaMax C.kappa eta →
    AdmissibleWidth (Γ := model.seams) ambient.metric modelControl.etaMax modelControl.kappa
      (eta ∘ neighborhood.symm)

structure LocalizedRoundingTransport [T2Space M] [SecondCountableTopology M]
    {g : SmoothMetric M} {F : CorneredSurface g}
    {cutoff : SeifertSurfaces.AppendixB.RoundingCutoff} {C : CornerControl g F cutoff}
    (L : CompactCornerLocalization F C) (eta : M → ℝ) (R : RoundedSurface F C eta) where
  compactRounded : RoundedSurface L.model L.modelControl (eta ∘ L.neighborhood.symm)
  images_local : R.embedding.image ⊆ L.neighborhood.source ∧
    compactRounded.embedding.image ⊆ L.neighborhood.target
  embedding_transport : ∀ x : F.source,
    compactRounded.embedding.toFun (L.parametrization x) = L.neighborhood (R.embedding.toFun x)
  tube_transport : L.neighborhood '' widthTube g F.seams eta =
    widthTube L.ambient.metric L.model.seams (eta ∘ L.neighborhood.symm)
  isotopy_target : ∀ t q, q ∈ L.neighborhood.target →
    compactRounded.isotopy.stage t q ∈ L.neighborhood.target
  isotopy_conjugacy : ∀ t p, p ∈ L.neighborhood.source →
    L.neighborhood (R.isotopy.stage t p) =
      compactRounded.isotopy.stage t (L.neighborhood p)
  isotopy_source : ∀ t p, p ∈ L.neighborhood.source → R.isotopy.stage t p ∈ L.neighborhood.source
  area_transport : area g R.embedding.toFun =
    area L.ambient.metric compactRounded.embedding.toFun
  slice_transport : ∀ p (hp : p ∈ F.seams) (hm : L.neighborhood p ∈ L.model.seams),
    let S := R.slices.slice p hp
    let T := compactRounded.slices.slice (L.neighborhood p) hm
    S.interval = T.interval ∧
    (∀ u ∈ S.interval, ∀ r, |r| ≤ eta (S.base u).1 →
      T.replacement.height ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![u, r]) =
        S.replacement.height ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![u, r])) ∧
    (∀ u ∈ S.interval, (T.base u).1 = L.neighborhood (S.base u).1) ∧
    (∀ u ∈ S.interval, ∀ r, |r| ≤ eta (S.base u).1 →
      T.oldMap ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![u, r]) =
        L.neighborhood (S.oldMap ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![u, r])) ∧
      T.newMap ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![u, r]) =
        L.neighborhood (S.newMap ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![u, r]))) ∧
    (∀ u ∈ S.interval,
      actualSliceDensity g S.oldMap u (eta (S.base u).1) =
        actualSliceDensity L.ambient.metric T.oldMap u (eta (L.neighborhood.symm (T.base u).1)) ∧
      actualSliceDensity g S.newMap u (eta (S.base u).1) =
        actualSliceDensity L.ambient.metric T.newMap u (eta (L.neighborhood.symm (T.base u).1)))

structure LocalCornerRoundingProvider (cutoff : SeifertSurfaces.AppendixB.RoundingCutoff) where
  produce_localized : ∀ (M : Type) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M], ∀ g : SmoothMetric M, ∀ F : CorneredSurface g,
      ∃ C : CornerControl g F cutoff, ∃ L : CompactCornerLocalization F C,
        ∀ eta : M → ℝ, AdmissibleWidth (Γ := F.seams) g C.etaMax C.kappa eta →
          ∃ R : RoundedSurface F C eta, Nonempty (LocalizedRoundingTransport L eta R)

structure CutOpenCyclicCover (g : SmoothMetric E.Carrier) (S : IncompressibleSpanningSurface.{0} E) where
  carrier : Type
  [topology : TopologicalSpace carrier]
  [hausdorff : T2Space carrier]
  [secondCountable : SecondCountableTopology carrier]
  [charted : ChartedSpace (EuclideanHalfSpace 3) carrier]
  [manifold : IsManifold (𝓡∂ 3) ∞ carrier]
  projection : carrier → E.Carrier
  covering : IsCoveringMap projection
  surjective : Function.Surjective projection
  projection_smooth : ContMDiff (𝓡∂ 3) (𝓡∂ 3) ∞ projection
  projection_rank : ∀ p, Function.Bijective (mfderiv (𝓡∂ 3) (𝓡∂ 3) projection p)
  boundary_preimage : projection ⁻¹' (𝓡∂ 3).boundary E.Carrier = (𝓡∂ 3).boundary carrier
  metric : SmoothMetric carrier
  metric_pullback : ∀ p v w, metric.inner p v w = g.inner (projection p)
    (mfderiv (𝓡∂ 3) (𝓡∂ 3) projection p v) (mfderiv (𝓡∂ 3) (𝓡∂ 3) projection p w)
  deck : ℤ → Diffeomorph (𝓡∂ 3) (𝓡∂ 3) carrier carrier ∞
  deck_zero : ∀ p, deck 0 p = p
  deck_add : ∀ n m p, deck (n + m) p = deck n (deck m p)
  projection_deck : ∀ n p, projection (deck n p) = projection p
  fibers : ∀ p q, projection p = projection q ↔ ∃ n : ℤ, deck n p = q
  free : ∀ n p, deck n p = p → n = 0
  wall : NeatEmbedding S.1.surface carrier
  wall_lift : ∀ x, projection (wall.toFun x) = S.1.embedding.toFun x
  walls_disjoint : Pairwise (fun n m : ℤ => Disjoint ((deck n) '' wall.image) ((deck m) '' wall.image))
  cell : Set carrier
  cell_open : IsOpen cell
  cell_projection : cell ≃ₜ (S.1.imageᶜ : Set E.Carrier)
  cell_projection_exact : ∀ x : cell, (cell_projection x).1 = projection x.1
  cell_frontier : frontier cell = wall.image ∪ (deck 1) '' wall.image
  cells_cover : (⋃ n : ℤ, (deck n) '' (cell ∪ wall.image)) = univ

attribute [instance] CutOpenCyclicCover.topology CutOpenCyclicCover.hausdorff
  CutOpenCyclicCover.secondCountable CutOpenCyclicCover.charted CutOpenCyclicCover.manifold

structure CoverFrontierApplication {SA SB : CompactOrientedSurface.{0}}
    (g : SmoothMetric E.Carrier) (A : NeatEmbedding SA E.Carrier) (B : NeatEmbedding SB E.Carrier)
    (S : IncompressibleSpanningSurface.{0} E) (cutoff : SeifertSurfaces.AppendixB.RoundingCutoff)
    (etaMax kappa eta : E.Carrier → ℝ) where
  cover : CutOpenCyclicCover g S
  liftA : NeatEmbedding SA cover.carrier
  liftB : NeatEmbedding SB cover.carrier
  liftA_exact : ∀ x, cover.projection (liftA.toFun x) = A.toFun x
  liftB_exact : ∀ x, cover.projection (liftB.toFun x) = B.toFun x
  lifts_in_cell : liftA.image ⊆ cover.cell ∧ liftB.image ⊆ cover.cell
  upperA : Set cover.carrier
  lowerA : Set cover.carrier
  upperB : Set cover.carrier
  lowerB : Set cover.carrier
  regions_open : IsOpen upperA ∧ IsOpen lowerA ∧ IsOpen upperB ∧ IsOpen lowerB
  sidesA : upperA ∪ lowerA = liftA.imageᶜ ∧ Disjoint upperA lowerA ∧
    frontier upperA = liftA.image ∧ frontier lowerA = liftA.image
  sidesB : upperB ∪ lowerB = liftB.imageᶜ ∧ Disjoint upperB lowerB ∧
    frontier upperB = liftB.image ∧ frontier lowerB = liftB.image
  upper_wall : (cover.deck 1) '' cover.wall.image ⊆ upperA ∩ upperB
  lower_wall : cover.wall.image ⊆ lowerA ∩ lowerB
  up : CorneredSurface cover.metric
  down : CorneredSurface cover.metric
  frontier_up : up.surface.image = frontier (upperA ∩ upperB)
  frontier_down : down.surface.image = frontier (lowerA ∩ lowerB)
  selected_up : SelectedCornerRegion up (upperA ∩ upperB)
  selected_down : SelectedCornerRegion down (lowerA ∩ lowerB)
  seams_exact : up.seams = liftA.image ∩ liftB.image ∧ down.seams = liftA.image ∩ liftB.image
  sheet_images : up.surface.image ⊆ liftA.image ∪ liftB.image ∧ down.surface.image ⊆ liftA.image ∪ liftB.image
  angles : (∀ p ∈ up.seams, cornerAngle up p = twoSidedAngle g A B (cover.projection p)) ∧
    (∀ p ∈ down.seams, cornerAngle down p = twoSidedAngle g A B (cover.projection p))
  upControl : CornerControl cover.metric up cutoff
  downControl : CornerControl cover.metric down cutoff
  up_localization : CompactCornerLocalization up upControl
  down_localization : CompactCornerLocalization down downControl
  shared_caps : (∀ p ∈ up.seams,
    upControl.etaMax p = etaMax (cover.projection p) ∧ upControl.kappa p = kappa (cover.projection p)) ∧
    (∀ p ∈ down.seams,
    downControl.etaMax p = etaMax (cover.projection p) ∧ downControl.kappa p = kappa (cover.projection p))
  admissible_up : AdmissibleWidth (Γ := up.seams) cover.metric upControl.etaMax upControl.kappa (eta ∘ cover.projection)
  admissible_down : AdmissibleWidth (Γ := down.seams) cover.metric downControl.etaMax downControl.kappa (eta ∘ cover.projection)
  rounded_up : RoundedSurface up upControl (eta ∘ cover.projection)
  rounded_down : RoundedSurface down downControl (eta ∘ cover.projection)
  rounded_up_transport : LocalizedRoundingTransport up_localization (eta ∘ cover.projection) rounded_up
  rounded_down_transport : LocalizedRoundingTransport down_localization (eta ∘ cover.projection) rounded_down
  rounded_in_cell : rounded_up.embedding.image ⊆ cover.cell ∧ rounded_down.embedding.image ⊆ cover.cell
  projected_up : NeatEmbedding up.source E.Carrier
  projected_down : NeatEmbedding down.source E.Carrier
  projected_exact : projected_up.toFun = cover.projection ∘ rounded_up.embedding.toFun ∧
    projected_down.toFun = cover.projection ∘ rounded_down.embedding.toFun
  area_transport : area g projected_up.toFun = area cover.metric rounded_up.embedding.toFun ∧
    area g projected_down.toFun = area cover.metric rounded_down.embedding.toFun

structure SmoothDiscIn {S : CompactOrientedSurface.{0}} {Γ : Set E.Carrier}
    (g : SmoothMetric E.Carrier) (A : NeatEmbedding S E.Carrier) (γ : ClosedIntersectionComponent Γ) where
  map : E2 → E.Carrier
  smooth : ContMDiffOn 𝓘(ℝ, E2) (𝓡∂ 3) ∞ map (Metric.closedBall 0 1)
  embedding : IsEmbedding (fun z : Metric.closedBall (0 : E2) 1 => map z.1)
  immersion : ∀ z ∈ Metric.closedBall (0 : E2) 1,
    Function.Injective (mfderivWithin 𝓘(ℝ, E2) (𝓡∂ 3) map (Metric.closedBall 0 1) z)
  in_surface : map '' Metric.closedBall (0 : E2) 1 ⊆ A.image
  boundary_exact : map '' Metric.sphere (0 : E2) 1 = range γ.parameter
  interior_off_seam : Disjoint (map '' Metric.ball (0 : E2) 1) (range γ.parameter)

structure DiscExchangeFamily {SA SB : CompactOrientedSurface.{0}}
    (g : SmoothMetric E.Carrier) (A : NeatEmbedding SA E.Carrier) (B : NeatEmbedding SB E.Carrier)
    (γ : ClosedIntersectionComponent (A.image ∩ B.image))
    (DA : SmoothDiscIn g A γ) (DB : SmoothDiscIn g B γ)
    (cutoff : SeifertSurfaces.AppendixB.RoundingCutoff) (etaMax kappa eta : E.Carrier → ℝ) where
  delta : ℝ
  delta_pos : 0 < delta
  stage : ℝ → CorneredSurface g
  limit_image : (stage 0).surface.image =
    (B.image \ DB.map '' Metric.ball (0 : E2) 1) ∪ DA.map '' Metric.closedBall (0 : E2) 1
  initial_seam : (stage 0).seams = range γ.parameter
  transport : ℝ → SmoothAmbientIsotopy E.Carrier
  transport_initial : ∀ p, (transport 0).stage 1 p = p
  seam_transport : ∀ r ∈ Ioc (0 : ℝ) delta,
    (stage r).seams = ((transport r).stage 1) '' range γ.parameter
  stage_exact : ∀ r ∈ Ioc (0 : ℝ) delta,
    (stage r).surface.image = ((transport r).stage 1) ''
      (B.image \ DB.map '' Metric.ball (0 : E2) 1) ∪
      ((transport r).stage 1) '' (DA.map '' Metric.closedBall (0 : E2) 1)
  patch_normal : ∀ z : E2, TangentSpace (𝓡∂ 3) (DA.map z)
  patch_normal_unit : ∀ z ∈ Metric.closedBall (0 : E2) 1,
    g.inner (DA.map z) (patch_normal z) (patch_normal z) = 1
  patch_normal_orthogonal : ∀ z ∈ Metric.closedBall (0 : E2) 1, ∀ v : TangentSpace 𝓘(ℝ, E2) z,
    g.inner (DA.map z) (patch_normal z)
      (mfderivWithin 𝓘(ℝ, E2) (𝓡∂ 3) DA.map (Metric.closedBall (0 : E2) 1) z v) = 0
  parallel_patch : ∀ r ∈ Ioc (0 : ℝ) delta, ∀ z ∈ Metric.closedBall (0 : E2) 1,
    ∃ c : ℝ → E.Carrier, ∃ h : c 0 = DA.map z,
      IsMetricGeodesic g c ∧ (h ▸ ambientCurveVelocity c 0) = r • patch_normal z ∧
      c 1 = (transport r).stage 1 (DA.map z)
  patch_off_original : ∀ r ∈ Ioc (0 : ℝ) delta,
    Disjoint (((transport r).stage 1) '' (DA.map '' Metric.ball (0 : E2) 1)) A.image
  initial_angle : ∀ p ∈ range γ.parameter, cornerAngle (stage 0) p = twoSidedAngle g A B p
  initialControl : CornerControl g (stage 0) cutoff
  own_controls : ∀ r, r ∈ Ioc (0 : ℝ) delta → CornerControl g (stage r) cutoff
  corner_c2_convergence : ∀ p (hp : p ∈ (stage 0).seams),
    ∀ K : Set E3, IsCompact K → K ⊆ (initialControl.chart p hp).chart.target →
    ∀ eps : ℝ, 0 < eps → ∃ d : ℝ, 0 < d ∧ d ≤ delta ∧
      ∀ r (hr : r ∈ Ioc (0 : ℝ) d), ∀ hrDelta : r ∈ Ioc (0 : ℝ) delta,
      ∀ hp' : (transport r).stage 1 p ∈ (stage r).seams,
        let W0 := initialControl.chart p hp
        let Wr := (own_controls r hrDelta).chart ((transport r).stage 1 p) hp'
        K ⊆ Wr.chart.target ∧
        (∀ y ∈ K, Wr.chart.symm y ∈ W0.chart.source) ∧
        ∀ n ≤ 2, ∀ y ∈ K,
          ‖iteratedFDerivWithin ℝ n (W0.chart ∘ Wr.chart.symm) K y -
            iteratedFDerivWithin ℝ n (W0.chart ∘ W0.chart.symm) K y‖ < eps
  angle_c1_convergence : ∀ p (hp : p ∈ (stage 0).seams),
    ∀ I : Set ℝ, IsCompact I →
    I ⊆ {u | (EuclideanSpace.equiv (Fin 3) ℝ).symm ![u, 0, 0] ∈ (initialControl.chart p hp).chart.target} →
    ∀ eps : ℝ, 0 < eps → ∃ d : ℝ, 0 < d ∧ d ≤ delta ∧
      ∀ r (hr : r ∈ Ioc (0 : ℝ) d), ∀ hrDelta : r ∈ Ioc (0 : ℝ) delta,
      ∀ hp' : (transport r).stage 1 p ∈ (stage r).seams,
        ∀ n ≤ 1, ∀ u ∈ I,
          ‖iteratedDeriv n ((own_controls r hrDelta).chart ((transport r).stage 1 p) hp').angle u -
            iteratedDeriv n (initialControl.chart p hp).angle u‖ < eps
  shared_admissibility : ∀ r (hr : r ∈ Ioc (0 : ℝ) delta),
      AdmissibleWidth (Γ := (stage r).seams) g (own_controls r hr).etaMax (own_controls r hr).kappa
        (eta ∘ ((transport r).stage 1).symm)
  rounded : ∀ r (hr : r ∈ Ioc (0 : ℝ) delta),
      RoundedSurface (stage r) (own_controls r hr) (eta ∘ ((transport r).stage 1).symm)
  baseline : GeometricPiecewiseSurface SB E.Carrier
  baseline_exact : baseline.map = B.continuousMap
  exchange_isotopy : ∀ r ∈ Ioc (0 : ℝ) delta, GeometricImageIsotopic baseline (stage r).surface
  boundary_fixed : ∀ r ∈ Ioc (0 : ℝ) delta,
    (stage r).surface.map '' (stage r).source.boundary = exteriorBoundary B
  area_limit : Filter.Tendsto (fun r => geometricArea g (stage r).surface) (𝓝[>] (0 : ℝ))
    (𝓝 (area g B.toFun -
      (∫ z in Metric.closedBall (0 : E2) 1, Real.sqrt (Matrix.det (actualSurfaceGram g DB.map z))) +
      (∫ z in Metric.closedBall (0 : E2) 1, Real.sqrt (Matrix.det (actualSurfaceGram g DA.map z)))))
  component : ∀ r, r ∈ Ioc (0 : ℝ) delta → ClosedIntersectionComponent (stage r).seams
  component_exact : ∀ r hr, (component r hr).parameter = (transport r).stage 1 ∘ γ.parameter
  gain_limit : Filter.Tendsto (fun r => if hr : r ∈ Ioc (0 : ℝ) delta then
        curveIntegral g (component r hr) (fun p => SeifertSurfaces.AppendixB.angleGain cutoff
          (cornerAngle (stage r) p) * eta (((transport r).stage 1).symm p)) else 0)
        (𝓝[>] (0 : ℝ)) (𝓝 (curveIntegral g γ
          (fun p => SeifertSurfaces.AppendixB.angleGain cutoff (twoSidedAngle g A B p) * eta p)))

/-- Baseline caps plus the general source provider and actual disc exchanges. -/
structure RoundingControl {S R : CompactOrientedSurface.{0}} (g : SmoothMetric E.Carrier)
    (A : NeatEmbedding S E.Carrier) (B : NeatEmbedding R E.Carrier) where
  etaMax : E.Carrier → ℝ
  kappa : E.Carrier → ℝ
  gainFunction : ℝ → ℝ
  cutoff : SeifertSurfaces.AppendixB.RoundingCutoff
  gain_exact : gainFunction = SeifertSurfaces.AppendixB.angleGain cutoff
  caps_positive : ∀ p ∈ A.image ∩ B.image, 0 < etaMax p ∧ 0 < kappa p
  caps_continuous : ContinuousOn etaMax (A.image ∩ B.image) ∧
    ContinuousOn kappa (A.image ∩ B.image)
  gain_positive : ∀ theta ∈ Ioc (0 : ℝ) (Real.pi / 2), 0 < gainFunction theta
  gain_continuous : ContinuousOn gainFunction (Ioc (0 : ℝ) (Real.pi / 2))
  gain_monotone : MonotoneOn gainFunction (Ioc (0 : ℝ) (Real.pi / 2))
  normalGeometry : NormalExponentialGeometry g (A.image ∩ B.image)
  reach : E.Carrier → ℝ
  reach_exact : reach = localReach normalGeometry
  reach_positive : ∀ p ∈ A.image ∩ B.image, 0 < reach p
  boundary_distance_cap : ∀ p ∈ A.image ∩ B.image,
    ENNReal.ofReal (2 * etaMax p) ≤ boundaryEDist g p
  reach_cap : ∀ p ∈ A.image ∩ B.image, 2 * etaMax p ≤ reach p
  sheet_C2_bound : ℝ
  sheet_C2_bound_pos : 0 < sheet_C2_bound
  sheet_C2_actual : ∀ p ∈ A.image ∩ B.image,
    ∃ c : OpenPartialHomeomorph E.Carrier E3,
      p ∈ c.source ∧ ContMDiffOn (𝓡∂ 3) 𝓘(ℝ, E3) ∞ c c.source ∧
      ContMDiffOn 𝓘(ℝ, E3) (𝓡∂ 3) ∞ c.symm c.target ∧
      ∃ a : S, ∃ b : R, A.toFun a = p ∧ B.toFun b = p ∧
      ∃ VA VB : Set E2, IsOpen VA ∧ IsOpen VB ∧
      extChartAt (𝓡∂ 2) a a ∈ VA ∧ extChartAt (𝓡∂ 2) b b ∈ VB ∧
      VA ⊆ (extChartAt (𝓡∂ 2) a).target ∧ VB ⊆ (extChartAt (𝓡∂ 2) b).target ∧
      (∀ y ∈ VA, A.toFun ((extChartAt (𝓡∂ 2) a).symm y) ∈ c.source) ∧
      (∀ y ∈ VB, B.toFun ((extChartAt (𝓡∂ 2) b).symm y) ∈ c.source) ∧
      (∀ n : ℕ, n ≤ 2 → ∀ y ∈ VA,
        ‖iteratedFDerivWithin ℝ n (c ∘ A.toFun ∘ (extChartAt (𝓡∂ 2) a).symm) VA y‖ ≤ sheet_C2_bound) ∧
      (∀ n : ℕ, n ≤ 2 → ∀ y ∈ VB,
        ‖iteratedFDerivWithin ℝ n (c ∘ B.toFun ∘ (extChartAt (𝓡∂ 2) b).symm) VB y‖ ≤ sheet_C2_bound)
  slopeDerivativeBound : ℝ
  slopeDerivativeBound_pos : 0 < slopeDerivativeBound
  metricErrorBound : ℝ
  metricErrorBound_pos : 0 < metricErrorBound
  etaLower : ℝ → ℝ → ℝ → ℝ
  kappaLower : ℝ → ℝ → ℝ → ℝ
  etaLower_exact : ∀ theta ∈ Ioc (0 : ℝ) (Real.pi / 2), ∀ rho rhoBoundary,
    etaLower theta rho rhoBoundary = sourceWidthLower gainFunction
      sheet_C2_bound metricErrorBound slopeDerivativeBound theta rho rhoBoundary
  kappaLower_exact : ∀ theta ∈ Ioc (0 : ℝ) (Real.pi / 2), ∀ rho rhoBoundary,
    kappaLower theta rho rhoBoundary = sourceDerivativeLower gainFunction theta
  etaLower_positive : ∀ theta rho rhoBoundary, theta ∈ Ioc (0 : ℝ) (Real.pi / 2) →
    0 < rho → 0 < rhoBoundary → 0 < etaLower theta rho rhoBoundary
  kappaLower_positive : ∀ theta rho rhoBoundary, theta ∈ Ioc (0 : ℝ) (Real.pi / 2) →
    0 < rho → 0 < rhoBoundary → 0 < kappaLower theta rho rhoBoundary
  etaLower_monotone : ∀ theta ∈ Ioc (0 : ℝ) (Real.pi / 2),
    ∀ theta' ∈ Ioc (0 : ℝ) (Real.pi / 2), ∀ rho rho' rhoBoundary rhoBoundary',
    0 < rho → 0 < rho' → 0 < rhoBoundary → 0 < rhoBoundary' →
    theta ≤ theta' → rho ≤ rho' → rhoBoundary ≤ rhoBoundary' →
    etaLower theta rho rhoBoundary ≤ etaLower theta' rho' rhoBoundary'
  kappaLower_monotone : ∀ theta ∈ Ioc (0 : ℝ) (Real.pi / 2),
    ∀ theta' ∈ Ioc (0 : ℝ) (Real.pi / 2), ∀ rho rho' rhoBoundary rhoBoundary',
    0 < rho → 0 < rho' → 0 < rhoBoundary → 0 < rhoBoundary' →
    theta ≤ theta' → rho ≤ rho' → rhoBoundary ≤ rhoBoundary' →
    kappaLower theta rho rhoBoundary ≤ kappaLower theta' rho' rhoBoundary'
  cap_lower_bound : ∀ p ∈ A.image ∩ B.image,
    etaLower (twoSidedAngle g A B p) (reach p) (boundaryEDist g p).toReal ≤ etaMax p ∧
    kappaLower (twoSidedAngle g A B p) (reach p) (boundaryEDist g p).toReal ≤ kappa p
  provider : CornerRoundingProvider cutoff
  localProvider : LocalCornerRoundingProvider cutoff
  disc_exchange : ∀ γ : ClosedIntersectionComponent (A.image ∩ B.image),
    ∀ DA : SmoothDiscIn g A γ, ∀ DB : SmoothDiscIn g B γ,
      Disjoint (DA.map '' Metric.ball (0 : E2) 1) B.image →
      ∀ eta : E.Carrier → ℝ,
        AdmissibleWidth (Γ := range γ.parameter) g etaMax kappa eta →
        Nonempty (DiscExchangeFamily g A B γ DA DB cutoff etaMax kappa eta)
  reverse_disc_exchange : ∀ γ : ClosedIntersectionComponent (A.image ∩ B.image),
    ∀ DA : SmoothDiscIn g A γ, ∀ DB : SmoothDiscIn g B γ,
      Disjoint (DB.map '' Metric.ball (0 : E2) 1) A.image →
      ∃ γ' : ClosedIntersectionComponent (B.image ∩ A.image),
        γ'.parameter = γ.parameter ∧
        ∃ DA' : SmoothDiscIn g B γ', ∃ DB' : SmoothDiscIn g A γ',
          DA'.map = DB.map ∧ DB'.map = DA.map ∧
          ∀ eta : E.Carrier → ℝ,
            AdmissibleWidth (Γ := range γ.parameter) g etaMax kappa eta →
            Nonempty (DiscExchangeFamily g B A γ' DA' DB' cutoff etaMax kappa eta)

structure TransverseFamily (g : SmoothMetric E.Carrier) (J : LongitudeFoliation.{0} E)
    (A B S : IncompressibleSpanningSurface.{0} E) where
  stage : ℝ → NeatEmbedding A.1.surface E.Carrier
  delta1 : ℝ
  delta1_pos : 0 < delta1
  initial : (stage 0).toFun = A.1.embedding.toFun
  smooth_family : ContMDiffOn (𝓘(ℝ).prod (𝓡∂ 2)) (𝓡∂ 3) ∞
    (fun p : ℝ × A.1.surface => (stage p.1).toFun p.2) (Icc 0 delta1 ×ˢ univ)
  normal_isotopy : ∀ t ∈ Ioc (0 : ℝ) delta1,
    Nonempty (ReparametrizedNormalIsotopy A.1.surface E.Carrier A.1.embedding (stage t))
  incompressible : ∀ t ∈ Ioc (0 : ℝ) delta1, (stage t).Incompressible
  transverse : ∀ t ∈ Ioc (0 : ℝ) delta1, Transverse (stage t) B.1.embedding
  leaf_boundary : ∀ t ∈ Ioc (0 : ℝ) delta1, J.BoundaryIn (stage t).toFun
  disjoint_boundary : ∀ t ∈ Ioc (0 : ℝ) delta1,
    Disjoint (exteriorBoundary (stage t)) (exteriorBoundary B.1.embedding)
  disjoint_S : ∀ t ∈ Ioc (0 : ℝ) delta1, Disjoint (stage t).image S.1.image
  convergence : ConvergesC 1 stage A.1.embedding
  area_convergence : Filter.Tendsto (fun t => area g (stage t).toFun - area g A.1.embedding.toFun)
    (𝓝[>] (0 : ℝ)) (𝓝 0)
  finite_intersection : ∀ t ∈ Ioc (0 : ℝ) delta1,
    FiniteClosedIntersection ((stage t).image ∩ B.1.image)
  track_isotopy : ∀ t ∈ Ioc (0 : ℝ) delta1, ∀ t' ∈ Ioc (0 : ℝ) delta1,
    ∃ H : SmoothAmbientIsotopy E.Carrier,
      (H.stage 1) '' (stage t).image = (stage t').image ∧
      (∀ a : Time, (H.stage a) '' B.1.image = B.1.image) ∧
      (∀ a : Time, ∀ p ∈ S.1.image, H.stage a p = p)

def familyIntersection {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}
    {A B S : IncompressibleSpanningSurface.{0} E} (F : TransverseFamily g J A B S)
    (t : ℝ) : Set E.Carrier := (F.stage t).image ∩ B.1.image

structure T2Endpoint {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}
    (D : B1OriginalData g J) (S : IncompressibleSpanningSurface.{0} E) where
  r0 : ℝ
  r0_pos : 0 < r0
  r0_inside : r0 ≤ D.r0
  collar_regular : ∀ s : Circle, ∀ r ∈ Ioo (0 : ℝ) r0,
    mfderiv ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ) (fun q : Circle × ℝ => D.f q.1 q.2) (s, r) ≠ 0
  interior : InteriorPerturbation D.A D.B g
  tangencies_away : ∀ p ∈ interior.tangencies, p ∉ openCollar D r0
  sign : ℝ
  sign_unit : sign = 1 ∨ sign = -1
  arc : ClosedLeafArc J D.boundaryLabel D.leafParameter
  a0 : ℝ
  a0_pos : 0 < a0
  r1 : ℝ
  r1_pos : 0 < r1
  r1_small : r1 ≤ r0 / 4
  sign_bound : ∀ s ∈ arc.parameterSet, ∀ r ∈ Ioc (0 : ℝ) r1,
    (1 / 2 : ℝ) * a0 * r ≤ sign * D.f s r
  chi : ℝ → ℝ
  chi_smooth : ContDiff ℝ ∞ chi
  chi_bounds : ∀ r, 0 ≤ chi r ∧ chi r ≤ 1
  chi_one : ∀ r ∈ Icc (0 : ℝ) r1, chi r = 1
  chi_support : tsupport chi ∩ Ici (0 : ℝ) ⊆ Ico 0 r0
  family : TransverseFamily g J D.A D.B S
  collar_formula : ∀ t ∈ Ioc (0 : ℝ) family.delta1,
    (family.stage t).image ∩ (D.collar '' halfCylinder r0 D.eta) =
      (fun q : Circle × ℝ => D.collar (q.1, q.2, D.f q.1 q.2 + sign * t * chi q.2)) '' radialCylinder r0
  interior_formula : ∀ t ∈ Ioc (0 : ℝ) family.delta1, ∀ p : interior.tangencies,
    (family.stage t).image ∩ (interior.chart p).coordinates.source =
      (fun x : E2 => (interior.chart p).coordinates.symm
        (graphPoint x ((interior.chart p).upper x - sign * t * interior.bump p x))) ''
        Metric.ball 0 (interior.chart p).R
  unchanged : ∀ t ∈ Ioc (0 : ℝ) family.delta1,
    (family.stage t).image \ ((D.collar '' halfCylinder r0 D.eta) ∪
      ⋃ p : interior.tangencies, (interior.chart p).coordinates.source) =
    D.A.1.image \ ((D.collar '' halfCylinder r0 D.eta) ∪
      ⋃ p : interior.tangencies, (interior.chart p).coordinates.source)
  boundary_leaf : ∀ t ∈ Ioc (0 : ℝ) family.delta1,
    exteriorBoundary (family.stage t) = J.leaf (D.sourceFlow.labels (sign * t) D.boundaryLabel)
  rho0 : ℝ
  rho0_pos : 0 < rho0
  deltaB2 : ℝ
  deltaB2_pos : 0 < deltaB2
  deltaB2_inside : deltaB2 ≤ family.delta1
  B2_diameter : ∀ t ∈ Ioc (0 : ℝ) deltaB2, ∀ γ : ClosedIntersectionComponent (familyIntersection family t),
    rho0 ≤ metricDiameter g (range γ.parameter)
  Cmet : ℝ
  Cmet_one : 1 ≤ Cmet
  collar_distance : ∀ x y : Circle × ℝ, x ∈ radialCylinder r0 → y ∈ radialCylinder r0 →
    |x.2 - y.2| ≤ Cmet * metricDist g (D.collar (x.1, x.2, 0)) (D.collar (y.1, y.2, 0))
  rho2 : ℝ
  rho2_pos : 0 < rho2
  balls_disjoint : Pairwise (fun p q : interior.tangencies =>
    Disjoint (metricBall g p.1 (2 * rho2)) (metricBall g q.1 (2 * rho2)))
  rho2_budget : 4 * (interior.tangencies.card : ℝ) * rho2 < rho0 / 8
  rho2_collar : rho2 ≤ r0 / 8
  rho2_arc : rho2 ≤ r1 / (2 * Cmet)
  radial_continuous : ContinuousOn (extendedRadial D r0) D.B.1.image
  radial_exact : ∀ s r, r ∈ Icc (0 : ℝ) r0 → extendedRadial D r0 (D.collar (s, r, 0)) = r
  B3_i : ∀ t ∈ Ioc (0 : ℝ) family.delta1,
    Disjoint (familyIntersection family t)
      ((fun q : Circle × ℝ => D.collar (q.1, q.2, 0)) '' (arc.parameterSet ×ˢ Ioc (0 : ℝ) r1))
  B3_i_all_levels : ∀ t : ℝ, 0 < t →
    Disjoint (collarLevelSet D r0 sign chi t)
      ((fun q : Circle × ℝ => D.collar (q.1, q.2, 0)) '' (arc.parameterSet ×ˢ Ioc (0 : ℝ) r1))
  B3_ii : ∀ t ∈ Ioc (0 : ℝ) family.delta1, ∀ γ : ClosedIntersectionComponent (familyIntersection family t),
    range γ.parameter ⊆ openCollar D r0 → EssentialIn γ (openCollar D r0)
  cstar : ℝ
  cstar_pos : 0 < cstar
  cstar_exact : cstar = min (min (3 * rho0 / 8) (r0 / 2)) (boundaryArcLength D arc) / Cmet
  B3_iii : ∀ t ∈ Ioc (0 : ℝ) deltaB2, ∀ γ : ClosedIntersectionComponent (familyIntersection family t),
    cstar ≤ curveLengthIn g γ (goodRegion g interior.tangencies (2 * rho2) ∩ {p | r1 ≤ extendedRadial D r0 p})
  theta1 : ℝ
  theta1_range : theta1 ∈ Ioc (0 : ℝ) (Real.pi / 2)
  etaGeo : ℝ
  etaGeo_pos : 0 < etaGeo
  kappa1 : ℝ
  kappa1_pos : 0 < kappa1
  deltaB4 : ℝ
  deltaB4_pos : 0 < deltaB4
  deltaB4_inside : deltaB4 ≤ deltaB2
  reference_compact : IsCompact (D.A.1.image ∩ D.B.1.image ∩
    goodRegion g interior.tangencies (rho2 / 2) ∩ {p | r1 / 4 ≤ extendedRadial D r0 p})
  reference_angle : ∀ p ∈ D.A.1.image ∩ D.B.1.image ∩
    goodRegion g interior.tangencies (rho2 / 2) ∩ {p | r1 / 4 ≤ extendedRadial D r0 p},
    2 * theta1 ≤ twoSidedAngle g D.A.1.embedding D.B.1.embedding p
  etaMax : ℝ → E.Carrier → ℝ
  kappa : ℝ → E.Carrier → ℝ
  reach : ℝ → E.Carrier → ℝ
  gain : ℝ → ℝ
  cutoff : SeifertSurfaces.AppendixB.RoundingCutoff
  gain_exact : gain = SeifertSurfaces.AppendixB.angleGain cutoff
  controls_sound : ∀ t ∈ Ioc (0 : ℝ) family.delta1,
    ∃ C : RoundingControl g (family.stage t) D.B.1.embedding,
      C.etaMax = etaMax t ∧ C.kappa = kappa t ∧ C.reach = reach t ∧ C.gainFunction = gain
  B4_1 : ∀ t ∈ Ioc (0 : ℝ) deltaB4, ∀ γ : ClosedIntersectionComponent (familyIntersection family t),
    3 * rho0 / 8 ≤ curveLengthIn g γ (goodRegion g interior.tangencies (2 * rho2))
  B4_2 : ∀ t ∈ Ioc (0 : ℝ) deltaB4, ∀ p ∈ familyIntersection family t ∩
      goodRegion g interior.tangencies rho2 ∩ {p | r1 / 2 ≤ extendedRadial D r0 p},
    theta1 ≤ twoSidedAngle g (family.stage t) D.B.1.embedding p
  B4_3 : ∀ t ∈ Ioc (0 : ℝ) deltaB4, ∀ p ∈ familyIntersection family t ∩
      goodRegion g interior.tangencies rho2 ∩ {p | r1 / 2 ≤ extendedRadial D r0 p},
    etaGeo ≤ etaMax t p ∧ kappa1 ≤ kappa t p
  eta1 : ℝ
  eta1_exact : eta1 = min etaGeo (kappa1 * rho2 / 4)
  epsilonStar : ℝ
  epsilon_exact : epsilonStar = gain theta1 * eta1 * cstar
  epsilon_pos : 0 < epsilonStar
  delta : ℝ
  delta_pos : 0 < delta
  delta_small : delta ≤ deltaB4
  no_disc : ∀ t ∈ Ioc (0 : ℝ) delta,
    ¬ HasDiscPatch (family.stage t) (familyIntersection family t) ∧
    ¬ HasDiscPatch D.B.1.embedding (familyIntersection family t)
  error_small : ∀ t ∈ Ioc (0 : ℝ) delta,
    area g (family.stage t).toFun < area g D.A.1.embedding.toFun + epsilonStar / 2
  width : ∀ t ∈ Ioc (0 : ℝ) delta, ∃ eta2 : ℝ, 0 < eta2 ∧ eta2 ≤ eta1 ∧
    eta2 = min eta1 (min (sInf ((etaMax t) '' familyIntersection family t))
      ((1 / 2 : ℝ) * sInf ((reach t) '' familyIntersection family t))) ∧
    (∀ p ∈ familyIntersection family t, 2 * eta2 ≤ reach t p) ∧
    (∀ p ∈ familyIntersection family t, eta2 ≤ etaMax t p) ∧
    (∀ p ∈ familyIntersection family t ∩ goodRegion g interior.tangencies (2 * rho2) ∩
      {p | r1 ≤ extendedRadial D r0 p},
      T2DistanceRamp D interior.tangencies r0 r1 rho2 p = rho2 ∧
      rawWidth eta1 eta2 kappa1 (T2DistanceRamp D interior.tangencies r0 r1 rho2) p = eta1) ∧
    ∃ eta : E.Carrier → ℝ,
      Nonempty (RampSmoothing (Γ := familyIntersection family t) g rho2 eta1 eta2 kappa1
        (T2DistanceRamp D interior.tangencies r0 r1 rho2) eta) ∧
      AdmissibleWidth (Γ := familyIntersection family t) g (etaMax t) (kappa t) eta ∧
      Nonempty (CoverFrontierApplication g (family.stage t) D.B.1.embedding S cutoff
        (etaMax t) (kappa t) eta) ∧
      (∀ p ∈ familyIntersection family t ∩ goodRegion g interior.tangencies (2 * rho2) ∩
        {p | r1 ≤ extendedRadial D r0 p}, eta p = eta1) ∧
      (∀ p ∈ familyIntersection family t, eta2 ≤ eta p ∧ eta p ≤ eta1) ∧
      (∀ γ : ClosedIntersectionComponent (familyIntersection family t),
        epsilonStar ≤ curveIntegral g γ
          (fun p => gain (twoSidedAngle g (family.stage t) D.B.1.embedding p) * eta p))

/-- One original T2 producer: B.2, every B.3/B.4 clause, (39)--(44), and Theorem 5.1(a)--(d).
The B1 sign and arc are results in T2Endpoint, not an additional input theorem. -/
structure T1Endpoint {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}
    (D : OriginalPair g J) (S : IncompressibleSpanningSurface.{0} E) where
  d0 : ℝ
  d0_pos : 0 < d0
  d0_exact : ENNReal.ofReal d0 =
    ⨅ p : ↥(D.A.1.image ∩ D.B.1.image), boundaryEDist g p.1
  interior : InteriorPerturbation D.A D.B g
  discs_away : ∀ p : interior.tangencies, ∀ x ∈ (interior.chart p).coordinates.source,
    ENNReal.ofReal (d0 / 2) < boundaryEDist g x
  family : TransverseFamily g J D.A D.B S
  smooth_convergence : ∀ k : ℕ, ConvergesC k family.stage D.A.1.embedding
  interior_formula : ∀ t ∈ Ioc (0 : ℝ) family.delta1, ∀ p : interior.tangencies,
    (family.stage t).image ∩ (interior.chart p).coordinates.source =
      (fun x : E2 => (interior.chart p).coordinates.symm
        (graphPoint x ((interior.chart p).upper x - t * interior.bump p x))) ''
        Metric.ball 0 (interior.chart p).R
  unchanged : ∀ t ∈ Ioc (0 : ℝ) family.delta1,
    (family.stage t).image \ (⋃ p : interior.tangencies, (interior.chart p).coordinates.source) =
    D.A.1.image \ (⋃ p : interior.tangencies, (interior.chart p).coordinates.source)
  boundary_fixed : ∀ t ∈ Ioc (0 : ℝ) family.delta1,
    exteriorBoundary (family.stage t) = exteriorBoundary D.A.1.embedding
  intersection_away : ∀ t ∈ Ioc (0 : ℝ) family.delta1, ∀ p ∈ familyIntersection family t,
    ENNReal.ofReal (d0 / 2) ≤ boundaryEDist g p
  rho0 : ℝ
  rho0_pos : 0 < rho0
  rho2 : ℝ
  rho2_pos : 0 < rho2
  balls_disjoint : Pairwise (fun p q : interior.tangencies =>
    Disjoint (metricBall g p.1 (2 * rho2)) (metricBall g q.1 (2 * rho2)))
  rho2_budget : 4 * (interior.tangencies.card : ℝ) * rho2 < rho0 / 8
  rho2_boundary : 2 * rho2 < d0 / 2
  theta1 : ℝ
  theta1_range : theta1 ∈ Ioc (0 : ℝ) (Real.pi / 2)
  etaGeo : ℝ
  etaGeo_pos : 0 < etaGeo
  kappa1 : ℝ
  kappa1_pos : 0 < kappa1
  deltaB5 : ℝ
  deltaB5_pos : 0 < deltaB5
  deltaB5_inside : deltaB5 ≤ family.delta1
  reference_compact : IsCompact (D.A.1.image ∩ D.B.1.image ∩
    goodRegion g interior.tangencies (rho2 / 2))
  reference_angle : ∀ p ∈ D.A.1.image ∩ D.B.1.image ∩
    goodRegion g interior.tangencies (rho2 / 2),
    2 * theta1 ≤ twoSidedAngle g D.A.1.embedding D.B.1.embedding p
  etaMax : ℝ → E.Carrier → ℝ
  kappa : ℝ → E.Carrier → ℝ
  reach : ℝ → E.Carrier → ℝ
  gain : ℝ → ℝ
  cutoff : SeifertSurfaces.AppendixB.RoundingCutoff
  gain_exact : gain = SeifertSurfaces.AppendixB.angleGain cutoff
  controls_sound : ∀ t ∈ Ioc (0 : ℝ) family.delta1,
    ∃ C : RoundingControl g (family.stage t) D.B.1.embedding,
      C.etaMax = etaMax t ∧ C.kappa = kappa t ∧ C.reach = reach t ∧ C.gainFunction = gain
  B5_1 : ∀ t ∈ Ioc (0 : ℝ) deltaB5, ∀ γ : ClosedIntersectionComponent (familyIntersection family t),
    rho0 ≤ metricDiameter g (range γ.parameter) ∧
    3 * rho0 / 8 ≤ curveLengthIn g γ (goodRegion g interior.tangencies (2 * rho2))
  B5_2 : ∀ t ∈ Ioc (0 : ℝ) deltaB5, ∀ p ∈ familyIntersection family t ∩ goodRegion g interior.tangencies rho2,
    theta1 ≤ twoSidedAngle g (family.stage t) D.B.1.embedding p
  B5_3 : ∀ t ∈ Ioc (0 : ℝ) deltaB5, ∀ p ∈ familyIntersection family t ∩ goodRegion g interior.tangencies rho2,
    etaGeo ≤ etaMax t p ∧ kappa1 ≤ kappa t p
  eta1 : ℝ
  eta1_exact : eta1 = min etaGeo (kappa1 * rho2 / 4)
  epsilonStar : ℝ
  epsilon_exact : epsilonStar = gain theta1 * eta1 * (3 * rho0 / 8)
  epsilon_pos : 0 < epsilonStar
  delta : ℝ
  delta_pos : 0 < delta
  delta_small : delta ≤ deltaB5
  no_disc : ∀ t ∈ Ioc (0 : ℝ) delta,
    ¬ HasDiscPatch (family.stage t) (familyIntersection family t) ∧
    ¬ HasDiscPatch D.B.1.embedding (familyIntersection family t)
  error_small : ∀ t ∈ Ioc (0 : ℝ) delta,
    area g (family.stage t).toFun < area g D.A.1.embedding.toFun + epsilonStar / 2
  width : ∀ t ∈ Ioc (0 : ℝ) delta, ∃ eta2 : ℝ, 0 < eta2 ∧ eta2 ≤ eta1 ∧
    eta2 = min eta1 (min (sInf ((etaMax t) '' familyIntersection family t))
      ((1 / 2 : ℝ) * sInf ((reach t) '' familyIntersection family t))) ∧
    (∀ p ∈ familyIntersection family t, 2 * eta2 ≤ reach t p) ∧
    (∀ p ∈ familyIntersection family t, eta2 ≤ etaMax t p) ∧
    (∀ p ∈ familyIntersection family t ∩ goodRegion g interior.tangencies (2 * rho2),
      T1DistanceRamp g interior.tangencies rho2 p = rho2 ∧
      rawWidth eta1 eta2 kappa1 (T1DistanceRamp g interior.tangencies rho2) p = eta1) ∧
    ∃ eta : E.Carrier → ℝ,
      Nonempty (RampSmoothing (Γ := familyIntersection family t) g rho2 eta1 eta2 kappa1
        (T1DistanceRamp g interior.tangencies rho2) eta) ∧
      AdmissibleWidth (Γ := familyIntersection family t) g (etaMax t) (kappa t) eta ∧
      Nonempty (CoverFrontierApplication g (family.stage t) D.B.1.embedding S cutoff
        (etaMax t) (kappa t) eta) ∧
      (∀ p ∈ familyIntersection family t ∩ goodRegion g interior.tangencies (2 * rho2), eta p = eta1) ∧
      (∀ p ∈ familyIntersection family t, eta2 ≤ eta p ∧ eta p ≤ eta1) ∧
      (∀ γ : ClosedIntersectionComponent (familyIntersection family t),
        epsilonStar ≤ curveIntegral g γ
          (fun p => gain (twoSidedAngle g (family.stage t) D.B.1.embedding p) * eta p))

-- Held sibling documentation omitted during mechanical union.

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480



end

section

end

-- Exact source from CollarSliceFactsV480.lean
noncomputable section
open Set Topology Function
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]
variable {S : CompactOrientedSurface.{0}} {F : NeatEmbedding S M} {U : Set M}

theorem collar_slice_isEmbedding (collar : OneSidedCollar F U)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) collar.epsilon) :
    IsEmbedding (fun x : S => collar.map (x,t)) := by
  let lift : S → univ ×ˢ Ico (0 : ℝ) collar.epsilon :=
    fun x => ⟨(x,t), ⟨mem_univ x,ht⟩⟩
  have hlift : IsEmbedding lift := by
    apply (IsEmbedding.of_comp_iff IsEmbedding.subtypeVal).mp
    exact isEmbedding_prodMkLeft t
  exact collar.embedding.comp hlift

theorem collar_slice_smooth (collar : OneSidedCollar F U)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) collar.epsilon) :
    ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ (fun x : S => collar.map (x,t)) := by
  apply collar.smooth.comp_contMDiff (contMDiff_id.prodMk contMDiff_const)
  intro x
  exact ⟨mem_univ x,ht⟩

theorem collar_slice_image_subset (collar : OneSidedCollar F U)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) collar.epsilon) :
    range (fun x : S => collar.map (x,t)) ⊆ U := by
  rintro _ ⟨x,rfl⟩
  exact collar.into_region x t ht.1 ht.2

theorem collar_slice_boundary_preimage (collar : OneSidedCollar F U)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) collar.epsilon) :
    (fun x : S => collar.map (x,t)) ⁻¹' (𝓡∂ 3).boundary M = S.boundary := by
  ext x
  exact collar.boundary_strata x t ht

theorem collar_slice_zero (collar : OneSidedCollar F U) :
    (fun x : S => collar.map (x,0)) = F.toFun := by
  funext x
  exact collar.initial x

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
end

-- Exact source from CollarSliceDifferentialV480.lean
set_option maxHeartbeats 1000000

noncomputable section
open Set Topology Function
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]
variable {S : CompactOrientedSurface.{0}} {F : NeatEmbedding S M} {U : Set M}

theorem collar_slice_mfderiv_eq (collar : OneSidedCollar F U)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) collar.epsilon) (x : S) :
    mfderiv (𝓡∂ 2) (𝓡∂ 3) (fun y : S => collar.map (y,t)) x =
      (mfderivWithin ((𝓡∂ 2).prod 𝓘(ℝ)) (𝓡∂ 3) collar.map
        (univ ×ˢ Ico (0 : ℝ) collar.epsilon) (x,t)).comp
        (ContinuousLinearMap.inl ℝ (TangentSpace (𝓡∂ 2) x) (TangentSpace 𝓘(ℝ) t)) := by
  let lift : S → S × ℝ := fun y => (y,t)
  have hmap : (univ : Set S) ⊆ lift ⁻¹' (univ ×ˢ Ico (0 : ℝ) collar.epsilon) :=
    fun y _ => ⟨mem_univ y,ht⟩
  have hlift : MDifferentiableWithinAt (𝓡∂ 2) ((𝓡∂ 2).prod 𝓘(ℝ)) lift univ x :=
    (show ContMDiff (𝓡∂ 2) ((𝓡∂ 2).prod 𝓘(ℝ)) ∞ lift from
      contMDiff_id.prodMk contMDiff_const).mdifferentiableWithinAt (by simp)
  have hcollar : MDifferentiableWithinAt ((𝓡∂ 2).prod 𝓘(ℝ)) (𝓡∂ 3)
      collar.map (univ ×ˢ Ico (0 : ℝ) collar.epsilon) (lift x) :=
    (collar.smooth (lift x) ⟨mem_univ x,ht⟩).mdifferentiableWithinAt (by simp)
  have hchain := mfderivWithin_comp x hcollar hlift hmap
    (uniqueMDiffWithinAt_univ (𝓡∂ 2))
  simpa only [mfderivWithin_univ,mfderiv_prod_left,lift,Function.comp_def] using hchain

theorem collar_slice_mfderiv_injective (collar : OneSidedCollar F U)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) collar.epsilon) (x : S) :
    Injective (mfderiv (𝓡∂ 2) (𝓡∂ 3) (fun y : S => collar.map (y,t)) x) := by
  rw [collar_slice_mfderiv_eq collar ht x]
  exact (collar.immersion (x,t) ⟨mem_univ x,ht⟩).comp
    (fun v w h => congrArg Prod.fst h)

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
end

-- Exact source from CollarBoundaryTransversalityV480.lean

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.OriginalEndpoints.A7Support
variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]
variable {S : CompactOrientedSurface.{0}} {F : NeatEmbedding S M} {U : Set M}

theorem collar_time_normal_zero (collar : OneSidedCollar F U)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) collar.epsilon)
    {x : S} (hx : x ∈ S.boundary) :
    (show Euc 3 from
      mfderivWithin ((𝓡∂ 2).prod 𝓘(ℝ)) (𝓡∂ 3) collar.map
        (univ ×ˢ Ico (0 : ℝ) collar.epsilon) (x,t) (0,1)) 0 = 0 := by
  let A := Ico (0 : ℝ) collar.epsilon
  let lift : ℝ → S × ℝ := fun u => (x,u)
  let γ : ℝ → M := fun u => collar.map (x,u)
  let e := extChartAt (𝓡∂ 3) (γ t)
  let p : Euc 3 →L[ℝ] ℝ := EuclideanSpace.proj 0
  let q : ℝ → ℝ := p ∘ e ∘ γ
  have hmap : A ⊆ lift ⁻¹' (univ ×ˢ A) := fun u hu => ⟨mem_univ x,hu⟩
  have hlift : MDifferentiableWithinAt 𝓘(ℝ) ((𝓡∂ 2).prod 𝓘(ℝ)) lift A t :=
    (show ContMDiff 𝓘(ℝ) ((𝓡∂ 2).prod 𝓘(ℝ)) ∞ lift from
      contMDiff_const.prodMk contMDiff_id).mdifferentiableWithinAt (by simp)
  have hc : MDifferentiableWithinAt ((𝓡∂ 2).prod 𝓘(ℝ)) (𝓡∂ 3)
      collar.map (univ ×ˢ A) (lift t) :=
    (collar.smooth (lift t) ⟨mem_univ x,ht⟩).mdifferentiableWithinAt (by simp)
  have hγ : MDifferentiableWithinAt 𝓘(ℝ) (𝓡∂ 3) γ A t :=
    hc.comp t hlift hmap
  have he : MDifferentiableAt (𝓡∂ 3) 𝓘(ℝ,Euc 3) e (γ t) :=
    (contMDiffAt_extChartAt (I := 𝓡∂ 3) (n := ∞)).mdifferentiableAt (by simp)
  have hp : MDifferentiableAt 𝓘(ℝ,Euc 3) 𝓘(ℝ) p (e (γ t)) :=
    p.mdifferentiableAt
  have hqe : q =ᶠ[𝓝[A] t] fun _ => 0 := by
    have hsource := hγ.continuousWithinAt.preimage_mem_nhdsWithin
      (extChartAt_source_mem_nhds (I := 𝓡∂ 3) (γ t))
    filter_upwards [hsource,self_mem_nhdsWithin] with u hu huA
    exact (chart_boundary_coordinate_iff (γ t) (γ u)
      (by simpa only [mem_preimage,extChartAt_source] using hu)).1
      ((collar.boundary_strata x u huA).2 hx)
  have hq0 : mfderivWithin 𝓘(ℝ) 𝓘(ℝ) q A t = 0 := by
    rw [hqe.mfderivWithin_eq_of_mem ht,mfderivWithin_const]
    simp
  have huniq : UniqueMDiffWithinAt 𝓘(ℝ) A t :=
    (uniqueDiffOn_Ico (0 : ℝ) collar.epsilon t ht).uniqueMDiffWithinAt
  have hchain : mfderivWithin 𝓘(ℝ) (𝓡∂ 3) γ A t =
      (mfderivWithin ((𝓡∂ 2).prod 𝓘(ℝ)) (𝓡∂ 3) collar.map
        (univ ×ˢ A) (x,t)).comp
        (ContinuousLinearMap.inr ℝ (TangentSpace (𝓡∂ 2) x) (TangentSpace 𝓘(ℝ) t)) := by
    have h := mfderivWithin_comp t hc hlift hmap huniq
    have hr : mfderivWithin 𝓘(ℝ) ((𝓡∂ 2).prod 𝓘(ℝ)) lift A t =
        ContinuousLinearMap.inr ℝ (TangentSpace (𝓡∂ 2) x) (TangentSpace 𝓘(ℝ) t) := by
      rw [mfderivWithin_eq_mfderiv huniq
        (show MDifferentiableAt 𝓘(ℝ) ((𝓡∂ 2).prod 𝓘(ℝ)) lift t from
          mdifferentiableAt_const.prodMk mdifferentiableAt_id)]
      exact mfderiv_prod_right
    simpa only [hr,γ,lift,Function.comp_def] using h
  have hcoordinate : mfderivWithin 𝓘(ℝ) 𝓘(ℝ) q A t =
      p.comp ((mfderivWithin ((𝓡∂ 2).prod 𝓘(ℝ)) (𝓡∂ 3) collar.map
        (univ ×ˢ A) (x,t)).comp
        (ContinuousLinearMap.inr ℝ (TangentSpace (𝓡∂ 2) x) (TangentSpace 𝓘(ℝ) t))) := by
    rw [mfderiv_comp_mfderivWithin t hp (he.comp_mdifferentiableWithinAt t hγ) huniq]
    rw [mfderiv_comp_mfderivWithin t he hγ huniq]
    rw [mfderiv_eq_fderiv,p.hasFDerivAt.fderiv,mfderiv_extChartAt_self,hchain]
    rfl
  have hv := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) (hcoordinate.symm.trans hq0)
  change p ((mfderivWithin ((𝓡∂ 2).prod 𝓘(ℝ)) (𝓡∂ 3) collar.map
    (univ ×ˢ A) (x,t)) (0,1)) = 0 at hv
  exact hv

theorem collar_slice_boundary_transverse (collar : OneSidedCollar F U)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) collar.epsilon)
    {x : S} (hx : x ∈ S.boundary) :
    ∃ w : TangentSpace (𝓡∂ 2) x,
      inwardCoordinate (collar.map (x,t))
        (mfderiv (𝓡∂ 2) (𝓡∂ 3) (fun y : S => collar.map (y,t)) x w) ≠ 0 := by
  let L := mfderivWithin ((𝓡∂ 2).prod 𝓘(ℝ)) (𝓡∂ 3) collar.map
    (univ ×ˢ Ico (0 : ℝ) collar.epsilon) (x,t)
  have hdim : Module.finrank ℝ (TangentSpace ((𝓡∂ 2).prod 𝓘(ℝ)) (x,t)) =
      Module.finrank ℝ (TangentSpace (𝓡∂ 3) (collar.map (x,t))) := by
    change Module.finrank ℝ (Euc 2 × ℝ) = Module.finrank ℝ (Euc 3)
    simp
  have hsurj : Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
      (collar.immersion (x,t) ⟨mem_univ x,ht⟩)
  obtain ⟨v,hv⟩ := hsurj (show TangentSpace (𝓡∂ 3) (collar.map (x,t)) from
    EuclideanSpace.single 0 1)
  refine ⟨v.1,?_⟩
  rw [inwardCoordinate_eq_coordinate,collar_slice_mfderiv_eq collar ht x]
  change (show Euc 3 from L (v.1,0)) 0 ≠ 0
  have hz : (show Euc 3 from L (0,v.2)) 0 = 0 := by
    have h := collar_time_normal_zero collar ht hx
    have he : (0,v.2) = v.2 • (show TangentSpace ((𝓡∂ 2).prod 𝓘(ℝ)) (x,t) from (0,1)) := by
      change (0,v.2) = v.2 • (show Euc 2 × ℝ from (0,1))
      simp
    rw [he,map_smul]
    change v.2 * (show Euc 3 from L (0,1)) 0 = 0
    rw [show (show Euc 3 from L (0,1)) 0 = 0 from h,mul_zero]
  have hsum : (show Euc 3 from L (v.1,0)) 0 = 1 := by
    have he : v = (v.1,0) + (0,v.2) := by
      change (show Euc 2 × ℝ from v) = (v.1,0) + (0,v.2)
      ext <;> simp
    have h := congrArg (fun z : Euc 3 => z 0) hv
    rw [he,map_add,PiLp.add_apply,hz,add_zero] at h
    simpa using h
  exact hsum.trans_ne one_ne_zero

def collar_slice_neat (collar : OneSidedCollar F U)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) collar.epsilon) : NeatEmbedding S M where
  toFun := fun x => collar.map (x,t)
  smoothEmbedding := ⟨native_transverse_isImmersion
    (collar_slice_smooth collar ht) (collar_slice_mfderiv_injective collar ht)
    (fun x => collar.boundary_strata x t ht)
    (fun _ hx => collar_slice_boundary_transverse collar ht hx),
    collar_slice_isEmbedding collar ht⟩
  boundary_preimage := collar_slice_boundary_preimage collar ht
  boundary_transverse := fun _ hx => collar_slice_boundary_transverse collar ht hx

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
end

-- Exact source from CollarNativeMotionV480.lean

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]
variable {S : CompactOrientedSurface.{0}} {F : NeatEmbedding S M} {U : Set M}

def collar_slice_normal_isotopy (collar : OneSidedCollar F U)
    {s t : ℝ} (hs : s ∈ Ico (0 : ℝ) collar.epsilon)
    (ht : t ∈ Ico (0 : ℝ) collar.epsilon) :
    SmoothNormalIsotopy S M (collar_slice_neat collar hs) (collar_slice_neat collar ht) := by
  let l : Time → ℝ := fun u => (1-(u : ℝ))*s + (u : ℝ)*t
  have hlC (u : Time) : l u ∈ Ico (0 : ℝ) collar.epsilon := by
    dsimp only [l]
    exact (convex_Ico (𝕜 := ℝ) (0 : ℝ) collar.epsilon) hs ht
      (sub_nonneg.mpr u.property.2) u.property.1 (sub_add_cancel 1 (u : ℝ))
  have hl : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ l :=
    ((contMDiff_const.sub contMDiff_subtypeVal_Icc).mul contMDiff_const).add
      (contMDiff_subtypeVal_Icc.mul contMDiff_const)
  refine {
    stage := fun u => collar_slice_neat collar (hlC u)
    smooth_family := ?_
    initial := ?_
    final := ?_ }
  · exact collar.smooth.comp_contMDiff
      (contMDiff_snd.prodMk (hl.comp contMDiff_fst))
      (fun q => ⟨mem_univ q.2,hlC q.1⟩)
  · funext x
    change collar.map (x,l 0) = collar.map (x,s)
    congr 1
    dsimp only [l]
    norm_num
  · funext x
    change collar.map (x,l 1) = collar.map (x,t)
    congr 1
    dsimp only [l]
    norm_num

theorem collar_slices_ambient_related [T2Space M] [SecondCountableTopology M]
    (collar : OneSidedCollar F U) {s t : ℝ}
    (hs : s ∈ Ico (0 : ℝ) collar.epsilon) (ht : t ∈ Ico (0 : ℝ) collar.epsilon) :
    SmoothAmbientIsotopy.Rel (collar_slice_neat collar hs).image
      (collar_slice_neat collar ht).image := by
  obtain ⟨H,hH⟩ := smooth_isotopy_extension (collar_slice_normal_isotopy collar hs ht)
  refine ⟨H,?_⟩
  change H.stage 1 '' range (fun x : S => collar.map (x,s)) =
    range (fun x : S => collar.map (x,t))
  rw [← range_comp]
  congr 1
  funext x
  exact hH x

theorem collar_initial_ambient_related [T2Space M] [SecondCountableTopology M]
    (collar : OneSidedCollar F U) {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) collar.epsilon) :
    SmoothAmbientIsotopy.Rel F.image (collar_slice_neat collar ht).image := by
  have h0 : (0 : ℝ) ∈ Ico (0 : ℝ) collar.epsilon := ⟨le_rfl,collar.epsilon_pos⟩
  have h := collar_slices_ambient_related collar h0 ht
  have himage : (collar_slice_neat collar h0).image = F.image := by
    change range (fun x : S => collar.map (x,0)) = range F.toFun
    rw [collar_slice_zero collar]
  rwa [himage] at h

theorem collar_native_push_off_family [T2Space M] [SecondCountableTopology M]
    (collar : OneSidedCollar F U) :
    ∃ sigma0 : ℝ, 0 < sigma0 ∧
      ∃ pushed : ℝ → NeatEmbedding S M,
        (∀ sigma ∈ Ioc (0 : ℝ) sigma0,
          (pushed sigma).image ⊆ U ∧ SmoothAmbientIsotopy.Rel F.image (pushed sigma).image) ∧
        (∀ sigma ∈ Ioc (0 : ℝ) sigma0, ∀ sigma' ∈ Ioc (0 : ℝ) sigma0,
          SmoothAmbientIsotopy.Rel (pushed sigma).image (pushed sigma').image) := by
  classical
  let sigma0 := collar.epsilon / 2
  have hsig : 0 < sigma0 := half_pos collar.epsilon_pos
  have hlegal (sigma : ℝ) (hs : sigma ∈ Ioc (0 : ℝ) sigma0) :
      sigma ∈ Ico (0 : ℝ) collar.epsilon :=
    ⟨hs.1.le,hs.2.trans_lt (half_lt_self collar.epsilon_pos)⟩
  let pushed : ℝ → NeatEmbedding S M := fun sigma =>
    if hs : sigma ∈ Ioc (0 : ℝ) sigma0 then collar_slice_neat collar (hlegal sigma hs) else F
  refine ⟨sigma0,hsig,pushed,?_,?_⟩
  · intro sigma hs
    dsimp only [pushed]
    rw [dite_eq_left hs]
    exact ⟨collar_slice_image_subset collar ⟨hs.1,(hlegal sigma hs).2⟩,
      collar_initial_ambient_related collar (hlegal sigma hs)⟩
  · intro sigma hs sigma' hs'
    dsimp only [pushed]
    rw [dite_eq_left hs,dite_eq_left hs']
    exact collar_slices_ambient_related collar (hlegal sigma hs) (hlegal sigma' hs')

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
end

-- Exact source from B2JointCoordinateDensityV480.lean

noncomputable section
open Set Topology Function Filter MeasureTheory Bundle
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.MetricFoundations.AreaAnalysis
variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

/-- The actual chart Gram-density of a jointly smooth surface family is
jointly continuous up to the parameter and surface boundary. -/
theorem jointly_smooth_coordinate_density_continuous_v480
    (g : SmoothMetric M) {S : CompactOrientedSurface.{0}}
    (H : ℝ × S → M) {a b : ℝ} (hab : a < b)
    (hH : ContMDiffOn (𝓘(ℝ).prod (𝓡∂ 2)) (𝓡∂ 3) ∞ H (Icc a b ×ˢ univ))
    (p : S) :
    ContinuousOn (fun q : ℝ × Euc 2 => coordinateAreaDensity g (fun x => H (q.1,x)) p q.2)
      (Icc a b ×ˢ (surfaceChart p).target) := by
  exact_paid_term "{\"all\":[[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"SeifertSurfaces\"],\"OriginalEndpoints\"],\"AppendixBOriginalV480\"],\"jointly_smooth_coordinate_density_continuous_v480\"]],\"dependencies\":[\"TopologicalSpace\",\"ChartedSpace\",\"EuclideanHalfSpace\",\"OfNat.ofNat\",\"Nat\",\"instOfNatNat\",\"Nat.instNeZeroSucc\",\"instTopologicalSpaceEuclideanHalfSpace\",\"IsManifold\",\"Real\",\"DenselyNormedField.toNontriviallyNormedField\",\"Real.denselyNormedField\",\"EuclideanSpace\",\"Fin\",\"PiLp.normedAddCommGroup\",\"ENNReal\",\"instOfNatAtLeastTwo\",\"AddMonoidWithOne.toNatCast\",\"AddCommMonoidWithOne.toAddMonoidWithOne\",\"ENNReal.instAddCommMonoidWithOne\",\"PiLp.innerProductSpace._proof_1\",\"fact_one_le_two_ennreal\",\"Fin.fintype\",\"Real.normedAddCommGroup\",\"PiLp.normedSpace\",\"NontriviallyNormedField.toNormedField\",\"NonUnitalSeminormedRing.toSeminormedAddCommGroup\",\"NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing\",\"SeminormedCommRing.toNonUnitalSeminormedCommRing\",\"NormedCommRing.toSeminormedCommRing\",\"Real.normedCommRing\",\"InnerProductSpace.toNormedSpace\",\"Real.instRCLike\",\"RCLike.toInnerProductSpaceReal\",\"modelWithCornersEuclideanHalfSpace\",\"WithTop.some\",\"ENat\",\"Top.top\",\"instTopENat\",\"SeifertSurfaces.MetricFoundations.SmoothMetric\",\"SeifertSurfaces.Foundations.CompactOrientedSurface\",\"Prod\",\"SeifertSurfaces.Foundations.CompactOrientedSurface.carrier\",\"LT.lt\",\"Real.instLT\",\"ContMDiffOn\",\"Prod.normedAddCommGroup\",\"Prod.normedSpace\",\"NormedAddCommGroup.toSeminormedAddCommGroup\",\"ModelProd\",\"instTopologicalSpaceModelProd\",\"UniformSpace.toTopologicalSpace\",\"PseudoMetricSpace.toUniformSpace\",\"SeminormedAddCommGroup.toPseudoMetricSpace\",\"ModelWithCorners.prod\",\"modelWithCornersSelf\",\"instTopologicalSpaceProd\",\"Real.pseudoMetricSpace\",\"SeifertSurfaces.Foundations.CompactOrientedSurface.topology\",\"prodChartedSpace\",\"chartedSpaceSelf\",\"SeifertSurfaces.Foundations.CompactOrientedSurface.charted\",\"SProd.sprod\",\"Set\",\"Set.instSProd\",\"Set.Icc\",\"Real.instPreorder\",\"Set.univ\",\"ContinuousOn\",\"SeifertSurfaces.Foundations.Euc\",\"PiLp.topologicalSpace\",\"SeifertSurfaces.MetricFoundations.coordinateAreaDensity\",\"Prod.mk\",\"Prod.fst\",\"Prod.snd\",\"PartialEquiv.target\",\"SeifertSurfaces.MetricFoundations.AreaAnalysis.surfaceChart\",\"TopologicalSpace\",\"ChartedSpace\",\"EuclideanHalfSpace\",\"OfNat.ofNat\",\"Nat\",\"instOfNatNat\",\"Nat.instNeZeroSucc\",\"instTopologicalSpaceEuclideanHalfSpace\",\"IsManifold\",\"Real\",\"DenselyNormedField.toNontriviallyNormedField\",\"Real.denselyNormedField\",\"EuclideanSpace\",\"Fin\",\"PiLp.normedAddCommGroup\",\"ENNReal\",\"instOfNatAtLeastTwo\",\"AddMonoidWithOne.toNatCast\",\"AddCommMonoidWithOne.toAddMonoidWithOne\",\"ENNReal.instAddCommMonoidWithOne\",\"PiLp.innerProductSpace._proof_1\",\"fact_one_le_two_ennreal\",\"Fin.fintype\",\"Real.normedAddCommGroup\",\"PiLp.normedSpace\",\"NontriviallyNormedField.toNormedField\",\"NonUnitalSeminormedRing.toSeminormedAddCommGroup\",\"NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing\",\"SeminormedCommRing.toNonUnitalSeminormedCommRing\",\"NormedCommRing.toSeminormedCommRing\",\"Real.normedCommRing\",\"InnerProductSpace.toNormedSpace\",\"Real.instRCLike\",\"RCLike.toInnerProductSpaceReal\",\"modelWithCornersEuclideanHalfSpace\",\"WithTop.some\",\"ENat\",\"Top.top\",\"instTopENat\",\"SeifertSurfaces.MetricFoundations.SmoothMetric\",\"SeifertSurfaces.Foundations.CompactOrientedSurface\",\"Prod\",\"SeifertSurfaces.Foundations.CompactOrientedSurface.carrier\",\"LT.lt\",\"Real.instLT\",\"ContMDiffOn\",\"Prod.normedAddCommGroup\",\"Prod.normedSpace\",\"NormedAddCommGroup.toSeminormedAddCommGroup\",\"ModelProd\",\"instTopologicalSpaceModelProd\",\"UniformSpace.toTopologicalSpace\",\"PseudoMetricSpace.toUniformSpace\",\"SeminormedAddCommGroup.toPseudoMetricSpace\",\"ModelWithCorners.prod\",\"modelWithCornersSelf\",\"instTopologicalSpaceProd\",\"Real.pseudoMetricSpace\",\"SeifertSurfaces.Foundations.CompactOrientedSurface.topology\",\"prodChartedSpace\",\"chartedSpaceSelf\",\"SeifertSurfaces.Foundations.CompactOrientedSurface.charted\",\"SProd.sprod\",\"Set\",\"Set.instSProd\",\"Set.Icc\",\"Real.instPreorder\",\"Set.univ\",\"ModelWithCorners\",\"SeifertSurfaces.Foundations.Euc\",\"PartialEquiv.target\",\"SeifertSurfaces.MetricFoundations.AreaAnalysis.surfaceChart\",\"Prod.mk\",\"Prod.fst\",\"PartialEquiv.toFun\",\"PartialEquiv.symm\",\"Prod.snd\",\"Function.comp\",\"PiLp.topologicalSpace\",\"ContMDiffOn.prodMk\",\"ContMDiff.contMDiffOn\",\"ContDiff.contMDiff\",\"contDiff_fst\",\"ContMDiffOn.comp\",\"extChartAt\",\"contMDiffOn_extChartAt_symm\",\"SeifertSurfaces.Foundations.CompactOrientedSurface.smooth\",\"contDiff_snd\",\"Membership.mem\",\"Set.instMembership\",\"And.right\",\"And.intro\",\"And.left\",\"Set.mem_univ\",\"UniqueMDiffOn\",\"UniqueDiffOn.uniqueMDiffOn\",\"UniqueDiffOn.prod\",\"Real.semiring\",\"Real.instAddCommGroup\",\"Semiring.toModule\",\"IsSemitopologicalSemiring.toContinuousAdd\",\"NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring\",\"NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing\",\"NonUnitalCommRing.toNonUnitalNonAssocCommRing\",\"CommRing.toNonUnitalCommRing\",\"Real.commRing\",\"IsSemitopologicalRing.toIsSemitopologicalSemiring\",\"IsTopologicalRing.toIsSemitopologicalRing\",\"instIsTopologicalRingReal\",\"SeparatelyContinuousMul.to_continuousSMul\",\"MulOne.toMul\",\"MulOneClass.toMulOne\",\"Monoid.toMulOneClass\",\"Semiring.toMonoid\",\"IsSemitopologicalSemiring.toSeparatelyContinuousMul\",\"NormedAddCommGroup.toAddCommGroup\",\"NormedSpace.toModule\",\"IsTopologicalAddGroup.toContinuousAdd\",\"AddCommGroup.toAddGroup\",\"WithLp.instAddCommGroup\",\"Pi.addCommGroup\",\"SeminormedAddCommGroup.toIsTopologicalAddGroup\",\"PiLp.seminormedAddCommGroup\",\"UniformContinuousConstSMul.instContinuousConstSMul\",\"PiLp.uniformSpace\",\"SMulZeroClass.toSMul\",\"AddZero.toZero\",\"AddZeroClass.toAddZero\",\"AddMonoid.toAddZeroClass\",\"SubNegMonoid.toAddMonoid\",\"AddGroup.toSubNegMonoid\",\"DistribSMul.toSMulZeroClass\",\"DistribMulAction.toDistribSMul\",\"Module.toDistribMulAction\",\"AddCommGroup.toAddCommMonoid\",\"IsBoundedSMul.toUniformContinuousConstSMul\",\"PiLp.instPseudoMetricSpace\",\"Real.instZero\",\"NegZeroClass.toZero\",\"SubNegZeroMonoid.toNegZeroClass\",\"SubtractionMonoid.toSubNegZeroMonoid\",\"SubtractionCommMonoid.toSubtractionMonoid\",\"AddCommGroup.toDivisionAddCommMonoid\",\"PiLp.instIsBoundedSMul\",\"SeminormedCommRing.toSeminormedRing\",\"Real.isBoundedSMul\",\"SeifertSurfaces.MetricFoundations.AreaAnalysis.surfaceChart._proof_1\",\"uniqueDiffOn_Icc\",\"uniqueDiffOn_extChartAt_target\",\"ContinuousOn\",\"TangentBundle\",\"instTopologicalSpaceTangentBundle\",\"instIsManifoldOfNatWithTopENatOfMinSmoothness_1\",\"instIsManifoldMinSmoothnessOfNatWithTopENat_1\",\"instIsManifoldMinSmoothnessOfNatWithTopENat\",\"ContMDiffAdd.toIsManifold\",\"minSmoothness\",\"WithTop\",\"WithTop.natCast\",\"ENat.instNatCast\",\"Nat.instAtLeastTwoHAddOfNat\",\"AddCommMagma.toAdd\",\"AddCommSemigroup.toAddCommMagma\",\"AddCommMonoid.toAddCommSemigroup\",\"instContMDiffAddSelf\",\"IsManifold.instOfNatWithTopENat_1\",\"IsManifold.instOfNatWithTopENat_2\",\"IsManifold.instOfSomeENatTopOfLEInfty\",\"IsManifold.instLEInftyOfNatWithTopENat\",\"tangentMapWithin\",\"Set.preimage\",\"Bundle.TotalSpace.proj\",\"TangentSpace\",\"ContMDiffOn.continuousOn_tangentMapWithin\",\"of_eq_true\",\"LE.le\",\"Preorder.toLE\",\"WithTop.instPreorder\",\"instPreorderENat\",\"One.toOfNat1\",\"WithTop.one\",\"instOneENat\",\"OrderTop.toTop\",\"instOrderTopENat\",\"Eq.trans\",\"Ne\",\"WithTop.top\",\"True\",\"WithTop.le_coe_top._simp_1\",\"Not\",\"Eq\",\"False\",\"congrArg\",\"WithTop.one_ne_top._simp_2\",\"not_false_eq_true\",\"ContinuousLinearMap\",\"CommSemiring.toSemiring\",\"Semifield.toCommSemiring\",\"Field.toSemifield\",\"NormedField.toField\",\"RingHom.id\",\"Semiring.toNonAssocSemiring\",\"TopCat.of.chartedSpace\",\"WithLp\",\"instTopologicalSpaceTangentSpace\",\"instAddCommGroupTangentSpace\",\"instModuleTangentSpace\",\"mfderivWithin\",\"ContinuousLinearMap.comp\",\"RingHomCompTriple.ids\",\"ContinuousLinearMap.inr\",\"HasFDerivAt\",\"WithLp.instModule\",\"Pi.Function.module\",\"Semiring.toAddCommMonoid\",\"Ring.toSemiring\",\"Real.instRing\",\"Prod.instAddCommGroup\",\"Prod.instModule\",\"Real.instAddCommMonoid\",\"HasFDerivAt.prodMk\",\"Zero.toOfNat0\",\"ContinuousLinearMap.zero\",\"ContinuousLinearMap.id\",\"hasFDerivAt_const\",\"hasFDerivAt_id\",\"MDifferentiableAt\",\"DifferentiableAt.mdifferentiableAt\",\"HasFDerivAt.differentiableAt\",\"Set.ofPred\",\"And\",\"mfderivWithin_comp\",\"ContMDiffOn.mdifferentiableOn\",\"WithTop.zero\",\"instZeroENat\",\"WithTop.coe_eq_zero._simp_1\",\"ENat.top_ne_zero._simp_1\",\"MDifferentiableAt.mdifferentiableWithinAt\",\"Set.MapsTo\",\"UniqueDiffWithinAt.uniqueMDiffWithinAt\",\"Eq.mp\",\"mfderiv\",\"HasMFDerivAt.mfderiv\",\"HasFDerivAt.hasMFDerivAt\",\"mfderivWithin_eq_mfderiv\",\"Bundle.TotalSpace\",\"Bundle.TotalSpace.mk\",\"DFunLike.coe\",\"ContinuousLinearMap.funLike\",\"ContinuousLinearEquiv\",\"RingHomInvPair.ids\",\"EquivLike.toFunLike\",\"ContinuousLinearEquiv.equivLike\",\"ContinuousLinearEquiv.symm\",\"tangentSpaceCastModel\",\"EuclideanSpace.single\",\"instDecidableEqFin\",\"Real.instOne\",\"Homeomorph\",\"IsManifold.instOfTopWithTopENat\",\"instIsManifoldModelSpace\",\"Homeomorph.instEquivLike\",\"Homeomorph.symm\",\"tangentBundleModelSpaceHomeomorph\",\"Continuous\",\"Continuous.comp\",\"Homeomorph.continuous\",\"Continuous.prodMk\",\"id\",\"continuous_id\",\"continuous_const\",\"ContinuousOn.comp\",\"Continuous.continuousOn\",\"SeifertSurfaces.MetricFoundations.coordinateGram\",\"ContinuousOn.congr\",\"Inner.inner\",\"InnerProductSpace.toInner\",\"Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal\",\"Real.normedField\",\"Bundle.RiemannianBundle.mk\",\"Bundle.ContMDiffRiemannianMetric.toRiemannianMetric\",\"SeifertSurfaces.MetricFoundations.SmoothMetric._proof_1\",\"SeifertSurfaces.MetricFoundations.SmoothMetric._proof_2\",\"TangentSpace.fiberBundle\",\"SeifertSurfaces.MetricFoundations.SmoothMetric._proof_3\",\"instIsTopologicalAddGroupTangentSpace\",\"instContinuousConstSMulTangentSpace\",\"Bundle.instInnerProductSpaceReal\",\"ContinuousOn.inner_bundle\",\"TangentSpace.vectorBundle\",\"IsContinuousRiemannianBundle.mk\",\"Exists.intro\",\"ContinuousLinearMap.topologicalSpace\",\"instIsTopologicalAddGroupReal\",\"ContinuousLinearMap.addCommMonoid\",\"ContinuousLinearMap.module\",\"Algebra.to_smulCommClass\",\"Real.instCommSemiring\",\"Algebra.id\",\"Real.instMul\",\"Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace\",\"ContinuousLinearMap.toNormedAddCommGroup\",\"RingHomIsometric.ids\",\"ContinuousLinearMap.toNormedSpace\",\"ContinuousLinearMap.addCommGroup\",\"Bundle.Trivial.topologicalSpace\",\"Bundle.Trivial.fiberBundle\",\"Bundle.Trivial.vectorBundle\",\"PolynormableSpace.continuousSMul\",\"instPolynormableSpace\",\"Bundle.ContinuousLinearMap.fiberBundle\",\"Bundle.ContinuousLinearMap.vectorBundle\",\"ContinuousLinearMap.isTopologicalAddGroup\",\"ContinuousLinearMap.continuousSMul\",\"RingHomSurjective.ids\",\"Bundle.TotalSpace.mk'\",\"Bundle.ContMDiffRiemannianMetric.inner\",\"ContMDiff.continuous\",\"ContinuousLinearMap.toSeminormedAddCommGroup\",\"ContinuousLinearMap.smulCommClass\",\"AddCommMonoid.toAddMonoid\",\"SeminormedAddCommGroup.toAddCommGroup\",\"ContinuousLinearMap.toNormedSpace._proof_1\",\"IsModuleTopology.toContinuousSMul\",\"SeminormedRing.toPseudoMetricSpace\",\"NormedField.toNormedCommRing\",\"Real.instAdd\",\"IsTopologicalSemiring.toIsModuleTopology\",\"IsTopologicalRing.toIsTopologicalSemiring\",\"FiberBundle.chartedSpace\",\"Bundle.ContMDiffRiemannianMetric.contMDiff\",\"rfl\",\"SeifertSurfaces.MetricFoundations.ProperSmoothEmbedding.ofNeat._proof_1\",\"SeifertSurfaces.MetricFoundations.coordinateGram._proof_1\",\"SeifertSurfaces.MetricFoundations.coordinateGram._proof_2\",\"SeifertSurfaces.MetricFoundations.coordinateGram._proof_3\",\"SeifertSurfaces.MetricFoundations.coordinateGram._proof_4\",\"Eq.mpr\",\"Eq.refl\",\"ContinuousOn.sqrt\",\"Matrix.det\",\"Continuous.comp_continuousOn\",\"Matrix\",\"instTopologicalSpaceMatrix\",\"PartialEquiv\",\"Continuous.matrix_det\",\"Iff.mpr\",\"Pi.topologicalSpace\",\"continuousOn_pi\"],\"kind\":\"thm\",\"levels\":[],\"name\":[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"SeifertSurfaces\"],\"OriginalEndpoints\"],\"AppendixBOriginalV480\"],\"jointly_smooth_coordinate_density_continuous_v480\"],\"print_name\":\"SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480.jointly_smooth_coordinate_density_continuous_v480\",\"type\":{\"nodes\":[[\"sort\",[\"succ\",[\"zero\"]]],[\"const\",[\"str\",[\"anonymous\"],\"TopologicalSpace\"],[[\"zero\"]]],[\"bvar\",0],[\"app\",1,2],[\"const\",[\"str\",[\"anonymous\"],\"ChartedSpace\"],[[\"zero\"],[\"zero\"]]],[\"const\",[\"str\",[\"anonymous\"],\"EuclideanHalfSpace\"],[]],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"OfNat\"],\"ofNat\"],[[\"zero\"]]],[\"const\",[\"str\",[\"anonymous\"],\"Nat\"],[]],[\"app\",6,7],[\"nat\",3],[\"app\",8,9],[\"const\",[\"str\",[\"anonymous\"],\"instOfNatNat\"],[]],[\"app\",11,9],[\"app\",10,12],[\"app\",5,13],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Nat\"],\"instNeZeroSucc\"],[]],[\"nat\",2],[\"app\",8,16],[\"app\",11,16],[\"app\",17,18],[\"app\",15,19],[\"app\",14,20],[\"app\",4,21],[\"const\",[\"str\",[\"anonymous\"],\"instTopologicalSpaceEuclideanHalfSpace\"],[]],[\"app\",23,13],[\"app\",24,20],[\"app\",22,25],[\"bvar\",1],[\"app\",26,27],[\"app\",28,2],[\"const\",[\"str\",[\"anonymous\"],\"IsManifold\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"const\",[\"str\",[\"anonymous\"],\"Real\"],[]],[\"app\",30,31],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"DenselyNormedField\"],\"toNontriviallyNormedField\"],[[\"zero\"]]],[\"app\",33,31],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Real\"],\"denselyNormedField\"],[]],[\"app\",34,35],[\"app\",32,36],[\"const\",[\"str\",[\"anonymous\"],\"EuclideanSpace\"],[[\"zero\"],[\"zero\"]]],[\"app\",38,31],[\"const\",[\"str\",[\"anonymous\"],\"Fin\"],[]],[\"app\",40,13],[\"app\",39,41],[\"app\",37,42],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"PiLp\"],\"normedAddCommGroup\"],[[\"zero\"],[\"zero\"]]],[\"const\",[\"str\",[\"anonymous\"],\"ENNReal\"],[]],[\"app\",6,45],[\"app\",46,16],[\"const\",[\"str\",[\"anonymous\"],\"instOfNatAtLeastTwo\"],[[\"zero\"]]],[\"app\",48,45],[\"app\",49,16],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"AddMonoidWithOne\"],\"toNatCast\"],[[\"zero\"]]],[\"app\",51,45],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"AddCommMonoidWithOne\"],\"toAddMonoidWithOne\"],[[\"zero\"]]],[\"app\",53,45],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"ENNReal\"],\"instAddCommMonoidWithOne\"],[]],[\"app\",54,55],[\"app\",52,56],[\"app\",50,57],[\"const\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"PiLp\"],\"innerProductSpace\"],\"_proof_1\"],[]],[\"app\",58,59],[\"app\",47,60],[\"app\",44,61],[\"app\",62,41],[\"lam\",[\"num\",[\"str\",[\"str\",[\"num\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"x\"],\"_@\"],\"Mathlib\"],\"Analysis\"],\"InnerProductSpace\"],\"PiL2\"],209079104],\"_hygCtx\"],\"_hyg\"],45],41,31,\"default\"],[\"app\",63,64],[\"const\",[\"str\",[\"anonymous\"],\"fact_one_le_two_ennreal\"],[]],[\"app\",65,66],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Fin\"],\"fintype\"],[]],[\"app\",68,13],[\"app\",67,69],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Real\"],\"normedAddCommGroup\"],[]],[\"lam\",[\"str\",[\"anonymous\"],\"i\"],41,71,\"default\"],[\"app\",70,72],[\"app\",43,73],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"PiLp\"],\"normedSpace\"],[[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",75,61],[\"app\",76,31],[\"app\",77,41],[\"app\",78,64],[\"app\",79,66],[\"app\",80,69],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"NontriviallyNormedField\"],\"toNormedField\"],[[\"zero\"]]],[\"app\",82,31],[\"app\",83,36],[\"app\",81,84],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"NonUnitalSeminormedRing\"],\"toSeminormedAddCommGroup\"],[[\"zero\"]]],[\"app\",86,31],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"NonUnitalSeminormedCommRing\"],\"toNonUnitalSeminormedRing\"],[[\"zero\"]]],[\"app\",88,31],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"SeminormedCommRing\"],\"toNonUnitalSeminormedCommRing\"],[[\"zero\"]]],[\"app\",90,31],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"NormedCommRing\"],\"toSeminormedCommRing\"],[[\"zero\"]]],[\"app\",92,31],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Real\"],\"normedCommRing\"],[]],[\"app\",93,94],[\"app\",91,95],[\"app\",89,96],[\"app\",87,97],[\"lam\",[\"str\",[\"anonymous\"],\"i\"],41,98,\"default\"],[\"app\",85,99],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"InnerProductSpace\"],\"toNormedSpace\"],[[\"zero\"],[\"zero\"]]],[\"app\",101,31],[\"app\",102,31],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Real\"],\"instRCLike\"],[]],[\"app\",103,104],[\"app\",105,98],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"RCLike\"],\"toInnerProductSpaceReal\"],[[\"zero\"]]],[\"app\",107,31],[\"app\",108,104],[\"app\",106,109],[\"lam\",[\"str\",[\"anonymous\"],\"i\"],41,110,\"default\"],[\"app\",100,111],[\"app\",74,112],[\"app\",113,21],[\"app\",114,25],[\"const\",[\"str\",[\"anonymous\"],\"modelWithCornersEuclideanHalfSpace\"],[]],[\"app\",116,13],[\"app\",117,20],[\"app\",115,118],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"WithTop\"],\"some\"],[[\"zero\"]]],[\"const\",[\"str\",[\"anonymous\"],\"ENat\"],[]],[\"app\",120,121],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Top\"],\"top\"],[[\"zero\"]]],[\"app\",123,121],[\"const\",[\"str\",[\"anonymous\"],\"instTopENat\"],[]],[\"app\",124,125],[\"app\",122,126],[\"app\",119,127],[\"bvar\",2],[\"app\",128,129],[\"app\",130,27],[\"app\",131,2],[\"const\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"SeifertSurfaces\"],\"MetricFoundations\"],\"SmoothMetric\"],[[\"zero\"]]],[\"bvar\",3],[\"app\",133,134],[\"app\",135,129],[\"app\",136,27],[\"app\",137,2],[\"const\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"SeifertSurfaces\"],\"Foundations\"],\"CompactOrientedSurface\"],[[\"zero\"]]],[\"const\",[\"str\",[\"anonymous\"],\"Prod\"],[[\"zero\"],[\"zero\"]]],[\"app\",140,31],[\"const\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"SeifertSurfaces\"],\"Foundations\"],\"CompactOrientedSurface\"],\"carrier\"],[[\"zero\"]]],[\"app\",142,2],[\"app\",141,143],[\"bvar\",6],[\"forall\",[\"num\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"a\"],\"_@\"],\"_internal\"],\"_hyg\"],0],144,145,\"default\"],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"LT\"],\"lt\"],[[\"zero\"]]],[\"app\",147,31],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Real\"],\"instLT\"],[]],[\"app\",148,149],[\"app\",150,27],[\"app\",151,2],[\"const\",[\"str\",[\"anonymous\"],\"ContMDiffOn\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",153,31],[\"app\",154,36],[\"app\",40,19],[\"app\",39,156],[\"app\",141,157],[\"app\",155,158],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Prod\"],\"normedAddCommGroup\"],[[\"zero\"],[\"zero\"]]],[\"app\",160,31],[\"app\",161,157],[\"app\",162,71],[\"app\",62,156],[\"lam\",[\"num\",[\"str\",[\"str\",[\"num\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"x\"],\"_@\"],\"Mathlib\"],\"Analysis\"],\"InnerProductSpace\"],\"PiL2\"],209079104],\"_hygCtx\"],\"_hyg\"],45],156,31,\"default\"],[\"app\",164,165],[\"app\",166,66],[\"app\",68,19],[\"app\",167,168],[\"lam\",[\"str\",[\"anonymous\"],\"i\"],156,71,\"default\"],[\"app\",169,170],[\"app\",163,171],[\"app\",159,172],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Prod\"],\"normedSpace\"],[[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",174,31],[\"app\",175,31],[\"app\",176,157],[\"app\",177,84],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"NormedAddCommGroup\"],\"toSeminormedAddCommGroup\"],[[\"zero\"]]],[\"app\",179,31],[\"app\",180,71],[\"app\",178,181],[\"app\",179,157],[\"app\",183,171],[\"app\",182,184],[\"app\",105,181],[\"app\",186,109],[\"app\",185,187],[\"app\",77,156],[\"app\",189,165],[\"app\",190,66],[\"app\",191,168],[\"app\",192,84],[\"lam\",[\"str\",[\"anonymous\"],\"i\"],156,98,\"default\"],[\"app\",193,194],[\"lam\",[\"str\",[\"anonymous\"],\"i\"],156,110,\"default\"],[\"app\",195,196],[\"app\",188,197],[\"app\",173,198],[\"const\",[\"str\",[\"anonymous\"],\"ModelProd\"],[[\"zero\"],[\"zero\"]]],[\"app\",200,31],[\"app\",5,19],[\"nat\",1],[\"app\",8,203],[\"app\",11,203],[\"app\",204,205],[\"app\",15,206],[\"app\",202,207],[\"app\",201,208],[\"app\",199,209],[\"const\",[\"str\",[\"anonymous\"],\"instTopologicalSpaceModelProd\"],[[\"zero\"],[\"zero\"]]],[\"app\",211,31],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"UniformSpace\"],\"toTopologicalSpace\"],[[\"zero\"]]],[\"app\",213,31],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"PseudoMetricSpace\"],\"toUniformSpace\"],[[\"zero\"]]],[\"app\",215,31],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"SeminormedAddCommGroup\"],\"toPseudoMetricSpace\"],[[\"zero\"]]],[\"app\",217,31],[\"app\",218,181],[\"app\",216,219],[\"app\",214,220],[\"app\",212,221],[\"app\",222,208],[\"app\",23,19],[\"app\",224,207],[\"app\",223,225],[\"app\",210,226],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"ModelWithCorners\"],\"prod\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",228,31],[\"app\",229,36],[\"app\",230,31],[\"app\",231,71],[\"app\",232,187],[\"app\",233,31],[\"app\",234,221],[\"const\",[\"str\",[\"anonymous\"],\"modelWithCornersSelf\"],[[\"zero\"],[\"zero\"]]],[\"app\",236,31],[\"app\",237,36],[\"app\",238,31],[\"app\",239,71],[\"app\",240,187],[\"app\",235,241],[\"app\",242,157],[\"app\",243,171],[\"app\",244,197],[\"app\",245,208],[\"app\",246,225],[\"app\",116,19],[\"app\",248,207],[\"app\",247,249],[\"app\",227,250],[\"bvar\",4],[\"app\",142,252],[\"app\",141,253],[\"app\",251,254],[\"const\",[\"str\",[\"anonymous\"],\"instTopologicalSpaceProd\"],[[\"zero\"],[\"zero\"]]],[\"app\",256,31],[\"app\",257,253],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Real\"],\"pseudoMetricSpace\"],[]],[\"app\",216,259],[\"app\",214,260],[\"app\",258,261],[\"const\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"SeifertSurfaces\"],\"Foundations\"],\"CompactOrientedSurface\"],\"topology\"],[[\"zero\"]]],[\"app\",263,252],[\"app\",262,264],[\"app\",255,265],[\"const\",[\"str\",[\"anonymous\"],\"prodChartedSpace\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",267,31],[\"app\",268,221],[\"app\",269,31],[\"app\",270,261],[\"const\",[\"str\",[\"anonymous\"],\"chartedSpaceSelf\"],[[\"zero\"]]],[\"app\",272,31],[\"app\",273,221],[\"app\",271,274],[\"app\",275,208],[\"app\",276,225],[\"app\",277,253],[\"app\",278,264],[\"const\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"SeifertSurfaces\"],\"Foundations\"],\"CompactOrientedSurface\"],\"charted\"],[[\"zero\"]]],[\"app\",280,252],[\"app\",279,281],[\"app\",266,282],[\"app\",283,42],[\"app\",284,73],[\"app\",285,112],[\"app\",286,21],[\"app\",287,25],[\"app\",288,118],[\"bvar\",9],[\"app\",289,290],[\"bvar\",8],[\"app\",291,292],[\"bvar\",7],[\"app\",293,294],[\"app\",295,127],[\"app\",296,134],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"SProd\"],\"sprod\"],[[\"zero\"],[\"zero\"],[\"zero\"]]],[\"const\",[\"str\",[\"anonymous\"],\"Set\"],[[\"zero\"]]],[\"app\",299,31],[\"app\",298,300],[\"app\",299,253],[\"app\",301,302],[\"app\",299,254],[\"app\",303,304],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Set\"],\"instSProd\"],[[\"zero\"],[\"zero\"]]],[\"app\",306,31],[\"app\",307,253],[\"app\",305,308],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Set\"],\"Icc\"],[[\"zero\"]]],[\"app\",310,31],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Real\"],\"instPreorder\"],[]],[\"app\",311,312],[\"app\",313,129],[\"app\",314,27],[\"app\",309,315],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Set\"],\"univ\"],[[\"zero\"]]],[\"app\",317,253],[\"app\",316,318],[\"app\",297,319],[\"bvar\",5],[\"app\",142,321],[\"const\",[\"str\",[\"anonymous\"],\"ContinuousOn\"],[[\"zero\"],[\"zero\"]]],[\"const\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"SeifertSurfaces\"],\"Foundations\"],\"Euc\"],[]],[\"app\",324,19],[\"app\",141,325],[\"app\",323,326],[\"app\",327,31],[\"app\",257,325],[\"app\",329,261],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"PiLp\"],\"topologicalSpace\"],[[\"zero\"],[\"zero\"]]],[\"app\",331,61],[\"app\",332,156],[\"app\",333,165],[\"lam\",[\"str\",[\"anonymous\"],\"i\"],156,261,\"default\"],[\"app\",334,335],[\"app\",330,336],[\"app\",328,337],[\"app\",338,261],[\"const\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"SeifertSurfaces\"],\"MetricFoundations\"],\"coordinateAreaDensity\"],[[\"zero\"],[\"zero\"]]],[\"bvar\",12],[\"app\",340,341],[\"bvar\",11],[\"app\",342,343],[\"bvar\",10],[\"app\",344,345],[\"app\",346,290],[\"app\",347,292],[\"app\",348,294],[\"app\",142,294],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Prod\"],\"mk\"],[[\"zero\"],[\"zero\"]]],[\"app\",351,31],[\"app\",142,292],[\"app\",352,353],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Prod\"],\"fst\"],[[\"zero\"],[\"zero\"]]],[\"app\",355,31],[\"app\",356,325],[\"app\",357,27],[\"app\",354,358],[\"app\",359,2],[\"app\",294,360],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],350,361,\"default\"],[\"app\",349,362],[\"app\",363,27],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Prod\"],\"snd\"],[[\"zero\"],[\"zero\"]]],[\"app\",365,31],[\"app\",366,325],[\"app\",367,2],[\"app\",364,368],[\"lam\",[\"str\",[\"anonymous\"],\"q\"],326,369,\"default\"],[\"app\",339,370],[\"app\",299,157],[\"app\",301,372],[\"app\",299,158],[\"app\",373,374],[\"app\",307,157],[\"app\",375,376],[\"app\",313,252],[\"app\",378,134],[\"app\",377,379],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"PartialEquiv\"],\"target\"],[[\"zero\"],[\"zero\"]]],[\"app\",142,145],[\"app\",381,382],[\"app\",383,157],[\"const\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"SeifertSurfaces\"],\"MetricFoundations\"],\"AreaAnalysis\"],\"surfaceChart\"],[[\"zero\"]]],[\"app\",385,145],[\"app\",386,2],[\"app\",384,387],[\"app\",380,388],[\"app\",371,389],[\"forall\",[\"str\",[\"anonymous\"],\"p\"],322,390,\"default\"],[\"forall\",[\"str\",[\"anonymous\"],\"hH\"],320,391,\"default\"],[\"forall\",[\"str\",[\"anonymous\"],\"hab\"],152,392,\"default\"],[\"forall\",[\"str\",[\"anonymous\"],\"b\"],31,393,\"implicit\"],[\"forall\",[\"str\",[\"anonymous\"],\"a\"],31,394,\"implicit\"],[\"forall\",[\"str\",[\"anonymous\"],\"H\"],146,395,\"default\"],[\"forall\",[\"str\",[\"anonymous\"],\"S\"],139,396,\"implicit\"],[\"forall\",[\"str\",[\"anonymous\"],\"g\"],138,397,\"default\"],[\"forall\",[\"num\",[\"str\",[\"str\",[\"num\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"inst\"],\"_@\"],\"OriginalB2B5V480\"],3706074420],\"_hygCtx\"],\"_hyg\"],13],132,398,\"instImplicit\"],[\"forall\",[\"num\",[\"str\",[\"str\",[\"num\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"inst\"],\"_@\"],\"OriginalB2B5V480\"],3706074420],\"_hygCtx\"],\"_hyg\"],6],29,399,\"instImplicit\"],[\"forall\",[\"num\",[\"str\",[\"str\",[\"num\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"inst\"],\"_@\"],\"OriginalB2B5V480\"],3706074420],\"_hygCtx\"],\"_hyg\"],3],3,400,\"instImplicit\"],[\"forall\",[\"str\",[\"anonymous\"],\"M\"],0,401,\"implicit\"]],\"root\":402},\"value\":{\"nodes\":[[\"sort\",[\"succ\",[\"zero\"]]],[\"const\",[\"str\",[\"anonymous\"],\"TopologicalSpace\"],[[\"zero\"]]],[\"bvar\",0],[\"app\",1,2],[\"const\",[\"str\",[\"anonymous\"],\"ChartedSpace\"],[[\"zero\"],[\"zero\"]]],[\"const\",[\"str\",[\"anonymous\"],\"EuclideanHalfSpace\"],[]],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"OfNat\"],\"ofNat\"],[[\"zero\"]]],[\"const\",[\"str\",[\"anonymous\"],\"Nat\"],[]],[\"app\",6,7],[\"nat\",3],[\"app\",8,9],[\"const\",[\"str\",[\"anonymous\"],\"instOfNatNat\"],[]],[\"app\",11,9],[\"app\",10,12],[\"app\",5,13],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Nat\"],\"instNeZeroSucc\"],[]],[\"nat\",2],[\"app\",8,16],[\"app\",11,16],[\"app\",17,18],[\"app\",15,19],[\"app\",14,20],[\"app\",4,21],[\"const\",[\"str\",[\"anonymous\"],\"instTopologicalSpaceEuclideanHalfSpace\"],[]],[\"app\",23,13],[\"app\",24,20],[\"app\",22,25],[\"bvar\",1],[\"app\",26,27],[\"app\",28,2],[\"const\",[\"str\",[\"anonymous\"],\"IsManifold\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"const\",[\"str\",[\"anonymous\"],\"Real\"],[]],[\"app\",30,31],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"DenselyNormedField\"],\"toNontriviallyNormedField\"],[[\"zero\"]]],[\"app\",33,31],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Real\"],\"denselyNormedField\"],[]],[\"app\",34,35],[\"app\",32,36],[\"const\",[\"str\",[\"anonymous\"],\"EuclideanSpace\"],[[\"zero\"],[\"zero\"]]],[\"app\",38,31],[\"const\",[\"str\",[\"anonymous\"],\"Fin\"],[]],[\"app\",40,13],[\"app\",39,41],[\"app\",37,42],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"PiLp\"],\"normedAddCommGroup\"],[[\"zero\"],[\"zero\"]]],[\"const\",[\"str\",[\"anonymous\"],\"ENNReal\"],[]],[\"app\",6,45],[\"app\",46,16],[\"const\",[\"str\",[\"anonymous\"],\"instOfNatAtLeastTwo\"],[[\"zero\"]]],[\"app\",48,45],[\"app\",49,16],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"AddMonoidWithOne\"],\"toNatCast\"],[[\"zero\"]]],[\"app\",51,45],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"AddCommMonoidWithOne\"],\"toAddMonoidWithOne\"],[[\"zero\"]]],[\"app\",53,45],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"ENNReal\"],\"instAddCommMonoidWithOne\"],[]],[\"app\",54,55],[\"app\",52,56],[\"app\",50,57],[\"const\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"PiLp\"],\"innerProductSpace\"],\"_proof_1\"],[]],[\"app\",58,59],[\"app\",47,60],[\"app\",44,61],[\"app\",62,41],[\"lam\",[\"num\",[\"str\",[\"str\",[\"num\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"x\"],\"_@\"],\"Mathlib\"],\"Analysis\"],\"InnerProductSpace\"],\"PiL2\"],209079104],\"_hygCtx\"],\"_hyg\"],45],41,31,\"default\"],[\"app\",63,64],[\"const\",[\"str\",[\"anonymous\"],\"fact_one_le_two_ennreal\"],[]],[\"app\",65,66],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Fin\"],\"fintype\"],[]],[\"app\",68,13],[\"app\",67,69],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Real\"],\"normedAddCommGroup\"],[]],[\"lam\",[\"str\",[\"anonymous\"],\"i\"],41,71,\"default\"],[\"app\",70,72],[\"app\",43,73],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"PiLp\"],\"normedSpace\"],[[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",75,61],[\"app\",76,31],[\"app\",77,41],[\"app\",78,64],[\"app\",79,66],[\"app\",80,69],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"NontriviallyNormedField\"],\"toNormedField\"],[[\"zero\"]]],[\"app\",82,31],[\"app\",83,36],[\"app\",81,84],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"NonUnitalSeminormedRing\"],\"toSeminormedAddCommGroup\"],[[\"zero\"]]],[\"app\",86,31],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"NonUnitalSeminormedCommRing\"],\"toNonUnitalSeminormedRing\"],[[\"zero\"]]],[\"app\",88,31],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"SeminormedCommRing\"],\"toNonUnitalSeminormedCommRing\"],[[\"zero\"]]],[\"app\",90,31],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"NormedCommRing\"],\"toSeminormedCommRing\"],[[\"zero\"]]],[\"app\",92,31],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Real\"],\"normedCommRing\"],[]],[\"app\",93,94],[\"app\",91,95],[\"app\",89,96],[\"app\",87,97],[\"lam\",[\"str\",[\"anonymous\"],\"i\"],41,98,\"default\"],[\"app\",85,99],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"InnerProductSpace\"],\"toNormedSpace\"],[[\"zero\"],[\"zero\"]]],[\"app\",101,31],[\"app\",102,31],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Real\"],\"instRCLike\"],[]],[\"app\",103,104],[\"app\",105,98],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"RCLike\"],\"toInnerProductSpaceReal\"],[[\"zero\"]]],[\"app\",107,31],[\"app\",108,104],[\"app\",106,109],[\"lam\",[\"str\",[\"anonymous\"],\"i\"],41,110,\"default\"],[\"app\",100,111],[\"app\",74,112],[\"app\",113,21],[\"app\",114,25],[\"const\",[\"str\",[\"anonymous\"],\"modelWithCornersEuclideanHalfSpace\"],[]],[\"app\",116,13],[\"app\",117,20],[\"app\",115,118],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"WithTop\"],\"some\"],[[\"zero\"]]],[\"const\",[\"str\",[\"anonymous\"],\"ENat\"],[]],[\"app\",120,121],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Top\"],\"top\"],[[\"zero\"]]],[\"app\",123,121],[\"const\",[\"str\",[\"anonymous\"],\"instTopENat\"],[]],[\"app\",124,125],[\"app\",122,126],[\"app\",119,127],[\"bvar\",2],[\"app\",128,129],[\"app\",130,27],[\"app\",131,2],[\"const\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"SeifertSurfaces\"],\"MetricFoundations\"],\"SmoothMetric\"],[[\"zero\"]]],[\"bvar\",3],[\"app\",133,134],[\"app\",135,129],[\"app\",136,27],[\"app\",137,2],[\"const\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"SeifertSurfaces\"],\"Foundations\"],\"CompactOrientedSurface\"],[[\"zero\"]]],[\"const\",[\"str\",[\"anonymous\"],\"Prod\"],[[\"zero\"],[\"zero\"]]],[\"app\",140,31],[\"const\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"SeifertSurfaces\"],\"Foundations\"],\"CompactOrientedSurface\"],\"carrier\"],[[\"zero\"]]],[\"app\",142,2],[\"app\",141,143],[\"bvar\",6],[\"forall\",[\"num\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"a\"],\"_@\"],\"_internal\"],\"_hyg\"],0],144,145,\"default\"],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"LT\"],\"lt\"],[[\"zero\"]]],[\"app\",147,31],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Real\"],\"instLT\"],[]],[\"app\",148,149],[\"app\",150,27],[\"app\",151,2],[\"const\",[\"str\",[\"anonymous\"],\"ContMDiffOn\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",153,31],[\"app\",154,36],[\"app\",40,19],[\"app\",39,156],[\"app\",141,157],[\"app\",155,158],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Prod\"],\"normedAddCommGroup\"],[[\"zero\"],[\"zero\"]]],[\"app\",160,31],[\"app\",161,157],[\"app\",162,71],[\"app\",62,156],[\"lam\",[\"num\",[\"str\",[\"str\",[\"num\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"x\"],\"_@\"],\"Mathlib\"],\"Analysis\"],\"InnerProductSpace\"],\"PiL2\"],209079104],\"_hygCtx\"],\"_hyg\"],45],156,31,\"default\"],[\"app\",164,165],[\"app\",166,66],[\"app\",68,19],[\"app\",167,168],[\"lam\",[\"str\",[\"anonymous\"],\"i\"],156,71,\"default\"],[\"app\",169,170],[\"app\",163,171],[\"app\",159,172],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Prod\"],\"normedSpace\"],[[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",174,31],[\"app\",175,31],[\"app\",176,157],[\"app\",177,84],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"NormedAddCommGroup\"],\"toSeminormedAddCommGroup\"],[[\"zero\"]]],[\"app\",179,31],[\"app\",180,71],[\"app\",178,181],[\"app\",179,157],[\"app\",183,171],[\"app\",182,184],[\"app\",105,181],[\"app\",186,109],[\"app\",185,187],[\"app\",77,156],[\"app\",189,165],[\"app\",190,66],[\"app\",191,168],[\"app\",192,84],[\"lam\",[\"str\",[\"anonymous\"],\"i\"],156,98,\"default\"],[\"app\",193,194],[\"lam\",[\"str\",[\"anonymous\"],\"i\"],156,110,\"default\"],[\"app\",195,196],[\"app\",188,197],[\"app\",173,198],[\"const\",[\"str\",[\"anonymous\"],\"ModelProd\"],[[\"zero\"],[\"zero\"]]],[\"app\",200,31],[\"app\",5,19],[\"nat\",1],[\"app\",8,203],[\"app\",11,203],[\"app\",204,205],[\"app\",15,206],[\"app\",202,207],[\"app\",201,208],[\"app\",199,209],[\"const\",[\"str\",[\"anonymous\"],\"instTopologicalSpaceModelProd\"],[[\"zero\"],[\"zero\"]]],[\"app\",211,31],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"UniformSpace\"],\"toTopologicalSpace\"],[[\"zero\"]]],[\"app\",213,31],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"PseudoMetricSpace\"],\"toUniformSpace\"],[[\"zero\"]]],[\"app\",215,31],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"SeminormedAddCommGroup\"],\"toPseudoMetricSpace\"],[[\"zero\"]]],[\"app\",217,31],[\"app\",218,181],[\"app\",216,219],[\"app\",214,220],[\"app\",212,221],[\"app\",222,208],[\"app\",23,19],[\"app\",224,207],[\"app\",223,225],[\"app\",210,226],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"ModelWithCorners\"],\"prod\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",228,31],[\"app\",229,36],[\"app\",230,31],[\"app\",231,71],[\"app\",232,187],[\"app\",233,31],[\"app\",234,221],[\"const\",[\"str\",[\"anonymous\"],\"modelWithCornersSelf\"],[[\"zero\"],[\"zero\"]]],[\"app\",236,31],[\"app\",237,36],[\"app\",238,31],[\"app\",239,71],[\"app\",240,187],[\"app\",235,241],[\"app\",242,157],[\"app\",243,171],[\"app\",244,197],[\"app\",245,208],[\"app\",246,225],[\"app\",116,19],[\"app\",248,207],[\"app\",247,249],[\"app\",227,250],[\"bvar\",4],[\"app\",142,252],[\"app\",141,253],[\"app\",251,254],[\"const\",[\"str\",[\"anonymous\"],\"instTopologicalSpaceProd\"],[[\"zero\"],[\"zero\"]]],[\"app\",256,31],[\"app\",257,253],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Real\"],\"pseudoMetricSpace\"],[]],[\"app\",216,259],[\"app\",214,260],[\"app\",258,261],[\"const\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"SeifertSurfaces\"],\"Foundations\"],\"CompactOrientedSurface\"],\"topology\"],[[\"zero\"]]],[\"app\",263,252],[\"app\",262,264],[\"app\",255,265],[\"const\",[\"str\",[\"anonymous\"],\"prodChartedSpace\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",267,31],[\"app\",268,221],[\"app\",269,31],[\"app\",270,261],[\"const\",[\"str\",[\"anonymous\"],\"chartedSpaceSelf\"],[[\"zero\"]]],[\"app\",272,31],[\"app\",273,221],[\"app\",271,274],[\"app\",275,208],[\"app\",276,225],[\"app\",277,253],[\"app\",278,264],[\"const\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"SeifertSurfaces\"],\"Foundations\"],\"CompactOrientedSurface\"],\"charted\"],[[\"zero\"]]],[\"app\",280,252],[\"app\",279,281],[\"app\",266,282],[\"app\",283,42],[\"app\",284,73],[\"app\",285,112],[\"app\",286,21],[\"app\",287,25],[\"app\",288,118],[\"bvar\",9],[\"app\",289,290],[\"bvar\",8],[\"app\",291,292],[\"bvar\",7],[\"app\",293,294],[\"app\",295,127],[\"app\",296,134],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"SProd\"],\"sprod\"],[[\"zero\"],[\"zero\"],[\"zero\"]]],[\"const\",[\"str\",[\"anonymous\"],\"Set\"],[[\"zero\"]]],[\"app\",299,31],[\"app\",298,300],[\"app\",299,253],[\"app\",301,302],[\"app\",299,254],[\"app\",303,304],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Set\"],\"instSProd\"],[[\"zero\"],[\"zero\"]]],[\"app\",306,31],[\"app\",307,253],[\"app\",305,308],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Set\"],\"Icc\"],[[\"zero\"]]],[\"app\",310,31],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Real\"],\"instPreorder\"],[]],[\"app\",311,312],[\"app\",313,129],[\"app\",314,27],[\"app\",309,315],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Set\"],\"univ\"],[[\"zero\"]]],[\"app\",317,253],[\"app\",316,318],[\"app\",297,319],[\"bvar\",5],[\"app\",142,321],[\"const\",[\"str\",[\"anonymous\"],\"ModelWithCorners\"],[[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",323,31],[\"app\",324,36],[\"const\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"SeifertSurfaces\"],\"Foundations\"],\"Euc\"],[]],[\"app\",326,19],[\"app\",141,327],[\"app\",325,328],[\"app\",161,327],[\"app\",330,71],[\"app\",331,171],[\"app\",329,332],[\"app\",176,327],[\"app\",334,84],[\"app\",335,181],[\"app\",179,327],[\"app\",337,171],[\"app\",336,338],[\"app\",339,187],[\"app\",340,197],[\"app\",333,341],[\"app\",342,328],[\"app\",213,328],[\"app\",215,328],[\"app\",217,328],[\"app\",179,328],[\"app\",347,332],[\"app\",346,348],[\"app\",345,349],[\"app\",344,350],[\"app\",343,351],[\"app\",238,328],[\"app\",353,332],[\"app\",354,341],[\"app\",299,328],[\"app\",299,157],[\"app\",301,357],[\"app\",299,158],[\"app\",358,359],[\"app\",307,157],[\"app\",360,361],[\"app\",313,321],[\"app\",363,252],[\"app\",362,364],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"PartialEquiv\"],\"target\"],[[\"zero\"],[\"zero\"]]],[\"app\",142,294],[\"app\",366,367],[\"app\",368,157],[\"const\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"SeifertSurfaces\"],\"MetricFoundations\"],\"AreaAnalysis\"],\"surfaceChart\"],[[\"zero\"]]],[\"app\",370,294],[\"app\",371,27],[\"app\",369,372],[\"app\",365,373],[\"app\",142,290],[\"app\",141,375],[\"forall\",[\"num\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"a\"],\"_@\"],\"_internal\"],\"_hyg\"],0],328,376,\"default\"],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Prod\"],\"mk\"],[[\"zero\"],[\"zero\"]]],[\"app\",378,31],[\"app\",379,375],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Prod\"],\"fst\"],[[\"zero\"],[\"zero\"]]],[\"app\",381,31],[\"app\",382,327],[\"app\",383,2],[\"app\",380,384],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"PartialEquiv\"],\"toFun\"],[[\"zero\"],[\"zero\"]]],[\"app\",386,157],[\"app\",387,375],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"PartialEquiv\"],\"symm\"],[[\"zero\"],[\"zero\"]]],[\"app\",389,375],[\"app\",390,157],[\"app\",370,290],[\"app\",392,134],[\"app\",391,393],[\"app\",388,394],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Prod\"],\"snd\"],[[\"zero\"],[\"zero\"]]],[\"app\",396,31],[\"app\",397,327],[\"app\",398,2],[\"app\",395,399],[\"app\",385,400],[\"lam\",[\"str\",[\"anonymous\"],\"q\"],328,401,\"default\"],[\"bvar\",15],[\"forall\",[\"num\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"a\"],\"_@\"],\"_internal\"],\"_hyg\"],0],328,403,\"default\"],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Function\"],\"comp\"],[[\"succ\",[\"zero\"]],[\"succ\",[\"zero\"]],[\"succ\",[\"zero\"]]]],[\"app\",405,328],[\"app\",406,376],[\"bvar\",14],[\"app\",407,408],[\"app\",409,292],[\"app\",410,2],[\"app\",155,328],[\"app\",412,332],[\"app\",413,341],[\"app\",414,328],[\"app\",415,351],[\"app\",416,134],[\"app\",417,328],[\"app\",257,327],[\"app\",419,261],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"PiLp\"],\"topologicalSpace\"],[[\"zero\"],[\"zero\"]]],[\"app\",421,61],[\"app\",422,156],[\"app\",423,165],[\"lam\",[\"str\",[\"anonymous\"],\"i\"],156,261,\"default\"],[\"app\",424,425],[\"app\",420,426],[\"app\",418,427],[\"app\",272,328],[\"app\",429,351],[\"app\",428,430],[\"app\",431,158],[\"app\",432,172],[\"app\",433,198],[\"app\",434,209],[\"app\",435,226],[\"app\",436,250],[\"bvar\",10],[\"app\",142,438],[\"app\",141,439],[\"app\",437,440],[\"app\",257,439],[\"app\",442,261],[\"app\",263,438],[\"app\",443,444],[\"app\",441,445],[\"app\",277,439],[\"app\",447,444],[\"app\",280,438],[\"app\",448,449],[\"app\",446,450],[\"app\",451,127],[\"app\",452,27],[\"app\",453,129],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"ContMDiffOn\"],\"prodMk\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",455,31],[\"app\",456,36],[\"app\",457,328],[\"app\",458,332],[\"app\",459,341],[\"app\",460,328],[\"app\",461,351],[\"app\",462,355],[\"app\",463,328],[\"app\",464,351],[\"app\",465,430],[\"app\",466,31],[\"app\",467,71],[\"app\",468,187],[\"app\",469,31],[\"app\",470,221],[\"app\",471,241],[\"app\",472,31],[\"app\",473,221],[\"app\",474,274],[\"app\",475,157],[\"app\",476,171],[\"app\",477,197],[\"app\",478,208],[\"app\",479,225],[\"app\",480,249],[\"app\",481,439],[\"app\",482,444],[\"app\",483,449],[\"app\",484,129],[\"app\",485,127],[\"app\",486,383],[\"bvar\",11],[\"app\",142,488],[\"app\",387,489],[\"app\",389,489],[\"app\",491,157],[\"app\",370,488],[\"app\",493,321],[\"app\",492,494],[\"app\",490,495],[\"app\",496,399],[\"lam\",[\"str\",[\"anonymous\"],\"q\"],328,497,\"default\"],[\"app\",487,498],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"ContMDiff\"],\"contMDiffOn\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",500,31],[\"app\",501,36],[\"app\",502,328],[\"app\",503,332],[\"app\",504,341],[\"app\",505,328],[\"app\",506,351],[\"app\",507,355],[\"app\",508,328],[\"app\",509,351],[\"app\",510,430],[\"app\",511,31],[\"app\",512,71],[\"app\",513,187],[\"app\",514,31],[\"app\",515,221],[\"app\",516,241],[\"app\",517,31],[\"app\",518,221],[\"app\",519,274],[\"app\",520,383],[\"app\",521,129],[\"app\",522,127],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"ContDiff\"],\"contMDiff\"],[[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",524,31],[\"app\",525,36],[\"app\",526,328],[\"app\",527,332],[\"app\",528,341],[\"app\",529,31],[\"app\",530,71],[\"app\",531,187],[\"app\",532,127],[\"app\",533,383],[\"const\",[\"str\",[\"anonymous\"],\"contDiff_fst\"],[[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",535,31],[\"app\",536,31],[\"app\",537,327],[\"app\",538,36],[\"app\",539,71],[\"app\",540,187],[\"app\",541,171],[\"app\",542,197],[\"app\",543,127],[\"app\",534,544],[\"app\",523,545],[\"app\",499,546],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"ContMDiffOn\"],\"comp\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",548,31],[\"app\",549,36],[\"app\",550,328],[\"app\",551,332],[\"app\",552,341],[\"app\",553,328],[\"app\",554,351],[\"app\",555,355],[\"app\",556,328],[\"app\",557,351],[\"app\",558,157],[\"app\",559,171],[\"app\",560,197],[\"app\",561,157],[\"app\",213,157],[\"app\",215,157],[\"app\",217,157],[\"app\",565,184],[\"app\",564,566],[\"app\",563,567],[\"app\",562,568],[\"app\",238,157],[\"app\",570,171],[\"app\",571,197],[\"app\",569,572],[\"app\",573,157],[\"app\",574,568],[\"app\",575,157],[\"app\",576,171],[\"app\",577,197],[\"app\",578,208],[\"app\",579,225],[\"app\",580,249],[\"app\",581,439],[\"app\",582,444],[\"app\",583,430],[\"app\",272,157],[\"app\",585,568],[\"app\",584,586],[\"app\",587,449],[\"app\",588,398],[\"app\",589,129],[\"app\",590,127],[\"app\",366,439],[\"app\",592,157],[\"const\",[\"str\",[\"anonymous\"],\"extChartAt\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",594,31],[\"app\",595,157],[\"app\",596,439],[\"app\",597,208],[\"app\",598,36],[\"app\",599,171],[\"app\",600,197],[\"app\",601,225],[\"app\",602,444],[\"app\",603,249],[\"app\",604,449],[\"app\",605,252],[\"app\",593,606],[\"app\",591,607],[\"app\",387,439],[\"app\",389,439],[\"app\",610,157],[\"app\",611,606],[\"app\",609,612],[\"app\",608,613],[\"const\",[\"str\",[\"anonymous\"],\"contMDiffOn_extChartAt_symm\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",615,31],[\"app\",616,36],[\"app\",617,157],[\"app\",618,171],[\"app\",619,197],[\"app\",620,208],[\"app\",621,225],[\"app\",622,249],[\"app\",623,439],[\"app\",624,444],[\"app\",625,449],[\"app\",626,127],[\"const\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"SeifertSurfaces\"],\"Foundations\"],\"CompactOrientedSurface\"],\"smooth\"],[[\"zero\"]]],[\"app\",628,438],[\"app\",627,629],[\"app\",630,252],[\"app\",614,631],[\"app\",511,327],[\"app\",633,171],[\"app\",634,197],[\"app\",635,327],[\"app\",213,327],[\"app\",215,327],[\"app\",217,327],[\"app\",639,338],[\"app\",638,640],[\"app\",637,641],[\"app\",636,642],[\"app\",238,327],[\"app\",644,171],[\"app\",645,197],[\"app\",643,646],[\"app\",647,327],[\"app\",648,642],[\"app\",272,327],[\"app\",650,642],[\"app\",649,651],[\"app\",652,398],[\"app\",653,129],[\"app\",654,127],[\"app\",529,327],[\"app\",656,171],[\"app\",657,197],[\"app\",658,127],[\"app\",659,398],[\"const\",[\"str\",[\"anonymous\"],\"contDiff_snd\"],[[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",661,31],[\"app\",662,31],[\"app\",663,327],[\"app\",664,36],[\"app\",665,71],[\"app\",666,187],[\"app\",667,171],[\"app\",668,197],[\"app\",669,127],[\"app\",660,670],[\"app\",655,671],[\"app\",632,672],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Membership\"],\"mem\"],[[\"zero\"],[\"zero\"]]],[\"app\",674,328],[\"app\",675,356],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Set\"],\"instMembership\"],[[\"zero\"]]],[\"app\",677,328],[\"app\",676,678],[\"app\",679,134],[\"app\",680,2],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"And\"],\"right\"],[]],[\"app\",674,31],[\"app\",683,300],[\"app\",677,31],[\"app\",684,685],[\"app\",313,438],[\"app\",687,290],[\"app\",686,688],[\"app\",382,157],[\"app\",690,27],[\"app\",689,691],[\"app\",682,692],[\"app\",674,157],[\"app\",694,357],[\"app\",677,157],[\"app\",695,696],[\"bvar\",12],[\"app\",142,698],[\"app\",366,699],[\"app\",700,157],[\"app\",370,698],[\"app\",702,145],[\"app\",701,703],[\"app\",697,704],[\"app\",397,157],[\"app\",706,27],[\"app\",705,707],[\"app\",693,708],[\"app\",709,2],[\"lam\",[\"str\",[\"anonymous\"],\"hq\"],681,710,\"default\"],[\"lam\",[\"str\",[\"anonymous\"],\"q\"],328,711,\"default\"],[\"app\",673,712],[\"app\",547,713],[\"app\",416,252],[\"app\",715,328],[\"app\",716,427],[\"app\",717,430],[\"app\",718,42],[\"app\",719,73],[\"app\",720,112],[\"app\",721,21],[\"app\",722,25],[\"app\",723,118],[\"bvar\",16],[\"app\",724,725],[\"app\",726,403],[\"app\",727,408],[\"app\",728,127],[\"app\",729,27],[\"app\",730,134],[\"app\",555,252],[\"app\",732,328],[\"app\",733,427],[\"app\",734,158],[\"app\",735,172],[\"app\",736,198],[\"app\",737,209],[\"app\",738,226],[\"app\",739,250],[\"app\",141,489],[\"app\",740,741],[\"app\",257,489],[\"app\",743,261],[\"app\",263,488],[\"app\",744,745],[\"app\",742,746],[\"app\",747,42],[\"app\",748,73],[\"app\",749,112],[\"app\",750,21],[\"app\",751,25],[\"app\",752,118],[\"app\",753,725],[\"app\",754,403],[\"app\",755,430],[\"app\",277,489],[\"app\",757,745],[\"app\",280,488],[\"app\",758,759],[\"app\",756,760],[\"app\",761,408],[\"app\",762,129],[\"app\",763,134],[\"app\",764,127],[\"app\",299,489],[\"app\",301,766],[\"app\",299,741],[\"app\",767,768],[\"app\",307,489],[\"app\",769,770],[\"app\",313,290],[\"app\",772,292],[\"app\",771,773],[\"app\",317,489],[\"app\",774,775],[\"app\",765,776],[\"app\",777,438],[\"app\",778,145],[\"app\",779,2],[\"app\",679,252],[\"app\",781,2],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"And\"],\"intro\"],[]],[\"app\",313,488],[\"app\",784,438],[\"app\",686,785],[\"bvar\",13],[\"app\",142,787],[\"app\",382,788],[\"app\",252,27],[\"app\",789,790],[\"app\",786,791],[\"app\",783,792],[\"app\",674,788],[\"app\",299,788],[\"app\",794,795],[\"app\",677,788],[\"app\",796,797],[\"app\",317,788],[\"app\",798,799],[\"app\",397,788],[\"app\",801,790],[\"app\",800,802],[\"app\",793,803],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"And\"],\"left\"],[]],[\"app\",786,691],[\"app\",805,806],[\"app\",366,788],[\"app\",808,157],[\"app\",370,787],[\"app\",810,294],[\"app\",809,811],[\"app\",697,812],[\"app\",813,707],[\"app\",807,814],[\"app\",815,2],[\"app\",804,816],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Set\"],\"mem_univ\"],[[\"zero\"]]],[\"app\",818,788],[\"app\",819,802],[\"app\",817,820],[\"lam\",[\"str\",[\"anonymous\"],\"hq\"],782,821,\"default\"],[\"lam\",[\"str\",[\"anonymous\"],\"q\"],328,822,\"default\"],[\"app\",780,823],[\"const\",[\"str\",[\"anonymous\"],\"UniqueMDiffOn\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",825,31],[\"app\",826,36],[\"app\",827,328],[\"app\",828,332],[\"app\",829,341],[\"app\",830,328],[\"app\",831,351],[\"app\",832,321],[\"app\",833,328],[\"app\",834,427],[\"app\",835,430],[\"app\",836,252],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"UniqueDiffOn\"],\"uniqueMDiffOn\"],[[\"zero\"],[\"zero\"]]],[\"app\",838,31],[\"app\",839,36],[\"app\",840,328],[\"app\",841,332],[\"app\",842,341],[\"app\",843,252],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"UniqueDiffOn\"],\"prod\"],[[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",845,31],[\"app\",846,31],[\"app\",847,157],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Real\"],\"semiring\"],[]],[\"app\",848,849],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Real\"],\"instAddCommGroup\"],[]],[\"app\",850,851],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Semiring\"],\"toModule\"],[[\"zero\"]]],[\"app\",853,31],[\"app\",854,849],[\"app\",852,855],[\"app\",856,261],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"IsSemitopologicalSemiring\"],\"toContinuousAdd\"],[[\"zero\"]]],[\"app\",858,31],[\"app\",859,261],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"NonUnitalNonAssocRing\"],\"toNonUnitalNonAssocSemiring\"],[[\"zero\"]]],[\"app\",861,31],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"NonUnitalNonAssocCommRing\"],\"toNonUnitalNonAssocRing\"],[[\"zero\"]]],[\"app\",863,31],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"NonUnitalCommRing\"],\"toNonUnitalNonAssocCommRing\"],[[\"zero\"]]],[\"app\",865,31],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"CommRing\"],\"toNonUnitalCommRing\"],[[\"zero\"]]],[\"app\",867,31],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Real\"],\"commRing\"],[]],[\"app\",868,869],[\"app\",866,870],[\"app\",864,871],[\"app\",862,872],[\"app\",860,873],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"IsSemitopologicalRing\"],\"toIsSemitopologicalSemiring\"],[[\"zero\"]]],[\"app\",875,31],[\"app\",876,261],[\"app\",877,872],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"IsTopologicalRing\"],\"toIsSemitopologicalRing\"],[[\"zero\"]]],[\"app\",879,31],[\"app\",880,261],[\"app\",881,872],[\"const\",[\"str\",[\"anonymous\"],\"instIsTopologicalRingReal\"],[]],[\"app\",882,883],[\"app\",878,884],[\"app\",874,885],[\"app\",857,886],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"SeparatelyContinuousMul\"],\"to_continuousSMul\"],[[\"zero\"]]],[\"app\",888,31],[\"app\",889,261],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"MulOne\"],\"toMul\"],[[\"zero\"]]],[\"app\",891,31],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"MulOneClass\"],\"toMulOne\"],[[\"zero\"]]],[\"app\",893,31],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Monoid\"],\"toMulOneClass\"],[[\"zero\"]]],[\"app\",895,31],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Semiring\"],\"toMonoid\"],[[\"zero\"]]],[\"app\",897,31],[\"app\",898,849],[\"app\",896,899],[\"app\",894,900],[\"app\",892,901],[\"app\",890,902],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"IsSemitopologicalSemiring\"],\"toSeparatelyContinuousMul\"],[[\"zero\"]]],[\"app\",904,31],[\"app\",905,261],[\"app\",906,873],[\"app\",907,885],[\"app\",903,908],[\"app\",887,909],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"NormedAddCommGroup\"],\"toAddCommGroup\"],[[\"zero\"]]],[\"app\",911,157],[\"app\",912,171],[\"app\",910,913],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"NormedSpace\"],\"toModule\"],[[\"zero\"],[\"zero\"]]],[\"app\",915,31],[\"app\",916,157],[\"app\",917,84],[\"app\",918,184],[\"app\",919,197],[\"app\",914,920],[\"app\",921,568],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"IsTopologicalAddGroup\"],\"toContinuousAdd\"],[[\"zero\"]]],[\"app\",923,157],[\"app\",924,568],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"AddCommGroup\"],\"toAddGroup\"],[[\"zero\"]]],[\"app\",926,157],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"WithLp\"],\"instAddCommGroup\"],[[\"zero\"]]],[\"app\",928,61],[\"app\",165,2],[\"forall\",[\"str\",[\"anonymous\"],\"i\"],156,930,\"default\"],[\"app\",929,931],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Pi\"],\"addCommGroup\"],[[\"zero\"],[\"zero\"]]],[\"app\",933,156],[\"app\",934,165],[\"lam\",[\"str\",[\"anonymous\"],\"i\"],156,851,\"default\"],[\"app\",935,936],[\"app\",932,937],[\"app\",927,938],[\"app\",925,939],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"SeminormedAddCommGroup\"],\"toIsTopologicalAddGroup\"],[[\"zero\"]]],[\"app\",941,157],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"PiLp\"],\"seminormedAddCommGroup\"],[[\"zero\"],[\"zero\"]]],[\"app\",943,61],[\"app\",944,156],[\"app\",945,165],[\"app\",946,66],[\"app\",947,168],[\"app\",948,194],[\"app\",942,949],[\"app\",940,950],[\"app\",922,951],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"UniformContinuousConstSMul\"],\"instContinuousConstSMul\"],[[\"zero\"],[\"zero\"]]],[\"app\",953,31],[\"app\",954,157],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"PiLp\"],\"uniformSpace\"],[[\"zero\"],[\"zero\"]]],[\"app\",956,61],[\"app\",957,156],[\"app\",958,165],[\"lam\",[\"str\",[\"anonymous\"],\"i\"],156,260,\"default\"],[\"app\",959,960],[\"app\",955,961],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"SMulZeroClass\"],\"toSMul\"],[[\"zero\"],[\"zero\"]]],[\"app\",963,31],[\"app\",964,157],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"AddZero\"],\"toZero\"],[[\"zero\"]]],[\"app\",966,157],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"AddZeroClass\"],\"toAddZero\"],[[\"zero\"]]],[\"app\",968,157],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"AddMonoid\"],\"toAddZeroClass\"],[[\"zero\"]]],[\"app\",970,157],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"SubNegMonoid\"],\"toAddMonoid\"],[[\"zero\"]]],[\"app\",972,157],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"AddGroup\"],\"toSubNegMonoid\"],[[\"zero\"]]],[\"app\",974,157],[\"app\",927,913],[\"app\",975,976],[\"app\",973,977],[\"app\",971,978],[\"app\",969,979],[\"app\",967,980],[\"app\",965,981],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"DistribSMul\"],\"toSMulZeroClass\"],[[\"zero\"],[\"zero\"]]],[\"app\",983,31],[\"app\",984,157],[\"app\",985,979],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"DistribMulAction\"],\"toDistribSMul\"],[[\"zero\"],[\"zero\"]]],[\"app\",987,31],[\"app\",988,157],[\"app\",989,899],[\"app\",990,978],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Module\"],\"toDistribMulAction\"],[[\"zero\"],[\"zero\"]]],[\"app\",992,31],[\"app\",993,157],[\"app\",994,849],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"AddCommGroup\"],\"toAddCommMonoid\"],[[\"zero\"]]],[\"app\",996,157],[\"app\",997,913],[\"app\",995,998],[\"app\",999,920],[\"app\",991,1000],[\"app\",986,1001],[\"app\",982,1002],[\"app\",962,1003],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"IsBoundedSMul\"],\"toUniformContinuousConstSMul\"],[[\"zero\"],[\"zero\"]]],[\"app\",1005,31],[\"app\",1006,157],[\"app\",1007,259],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"PiLp\"],\"instPseudoMetricSpace\"],[[\"zero\"],[\"zero\"]]],[\"app\",1009,61],[\"app\",1010,156],[\"app\",1011,165],[\"app\",1012,66],[\"app\",1013,168],[\"lam\",[\"str\",[\"anonymous\"],\"i\"],156,259,\"default\"],[\"app\",1014,1015],[\"app\",1008,1016],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Real\"],\"instZero\"],[]],[\"app\",1017,1018],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"NegZeroClass\"],\"toZero\"],[[\"zero\"]]],[\"app\",1020,157],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"SubNegZeroMonoid\"],\"toNegZeroClass\"],[[\"zero\"]]],[\"app\",1022,157],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"SubtractionMonoid\"],\"toSubNegZeroMonoid\"],[[\"zero\"]]],[\"app\",1024,157],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"SubtractionCommMonoid\"],\"toSubtractionMonoid\"],[[\"zero\"]]],[\"app\",1026,157],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"AddCommGroup\"],\"toDivisionAddCommMonoid\"],[[\"zero\"]]],[\"app\",1028,157],[\"app\",1029,938],[\"app\",1027,1030],[\"app\",1025,1031],[\"app\",1023,1032],[\"app\",1021,1033],[\"app\",1019,1034],[\"app\",1035,1003],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"PiLp\"],\"instIsBoundedSMul\"],[[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",1037,61],[\"app\",1038,31],[\"app\",1039,156],[\"app\",1040,165],[\"app\",1041,66],[\"app\",1042,168],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"SeminormedCommRing\"],\"toSeminormedRing\"],[[\"zero\"]]],[\"app\",1044,31],[\"app\",1045,95],[\"app\",1043,1046],[\"app\",1047,194],[\"lam\",[\"str\",[\"anonymous\"],\"i\"],156,855,\"default\"],[\"app\",1048,1049],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Real\"],\"isBoundedSMul\"],[]],[\"lam\",[\"str\",[\"anonymous\"],\"i\"],156,1051,\"default\"],[\"app\",1050,1052],[\"app\",1036,1053],[\"app\",1004,1054],[\"app\",952,1055],[\"app\",1056,688],[\"app\",596,699],[\"const\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"SeifertSurfaces\"],\"MetricFoundations\"],\"AreaAnalysis\"],\"surfaceChart\"],\"_proof_1\"],[]],[\"app\",202,1059],[\"app\",1058,1060],[\"app\",1061,36],[\"app\",1062,171],[\"app\",1063,197],[\"app\",224,1059],[\"app\",1064,1065],[\"app\",263,698],[\"app\",1066,1067],[\"app\",248,1059],[\"app\",1068,1069],[\"app\",280,698],[\"app\",1070,1071],[\"app\",1072,145],[\"app\",701,1073],[\"app\",1057,1074],[\"const\",[\"str\",[\"anonymous\"],\"uniqueDiffOn_Icc\"],[]],[\"app\",1076,438],[\"app\",1077,290],[\"app\",1078,292],[\"app\",1075,1079],[\"const\",[\"str\",[\"anonymous\"],\"uniqueDiffOn_extChartAt_target\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",1081,31],[\"app\",1082,157],[\"app\",1083,699],[\"app\",1084,1060],[\"app\",1085,36],[\"app\",1086,171],[\"app\",1087,197],[\"app\",1088,1065],[\"app\",1089,1067],[\"app\",1090,1069],[\"app\",1091,1071],[\"app\",1092,145],[\"app\",1080,1093],[\"app\",844,1094],[\"const\",[\"str\",[\"anonymous\"],\"ContinuousOn\"],[[\"zero\"],[\"zero\"]]],[\"const\",[\"str\",[\"anonymous\"],\"TangentBundle\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",1097,31],[\"app\",1098,36],[\"app\",1099,328],[\"app\",1100,332],[\"app\",1101,341],[\"app\",1102,328],[\"app\",1103,351],[\"app\",1104,145],[\"app\",1105,328],[\"app\",1106,427],[\"app\",1107,430],[\"app\",1096,1108],[\"app\",1099,42],[\"app\",1110,73],[\"app\",1111,112],[\"app\",1112,21],[\"app\",1113,25],[\"app\",1114,118],[\"bvar\",18],[\"app\",1115,1116],[\"bvar\",17],[\"app\",1117,1118],[\"app\",1119,725],[\"app\",1109,1120],[\"const\",[\"str\",[\"anonymous\"],\"instTopologicalSpaceTangentBundle\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",1122,31],[\"app\",1123,36],[\"app\",1124,328],[\"app\",1125,332],[\"app\",1126,341],[\"app\",1127,328],[\"app\",1128,351],[\"app\",1129,145],[\"app\",1130,328],[\"app\",1131,427],[\"app\",1132,430],[\"const\",[\"str\",[\"anonymous\"],\"instIsManifoldOfNatWithTopENatOfMinSmoothness_1\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",1134,31],[\"app\",1135,36],[\"app\",1136,328],[\"app\",1137,351],[\"app\",1138,328],[\"app\",1139,332],[\"app\",1140,341],[\"app\",1141,145],[\"app\",1142,328],[\"app\",1143,427],[\"app\",1144,430],[\"const\",[\"str\",[\"anonymous\"],\"instIsManifoldMinSmoothnessOfNatWithTopENat_1\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",1146,31],[\"app\",1147,36],[\"app\",1148,328],[\"app\",1149,351],[\"app\",1150,328],[\"app\",1151,332],[\"app\",1152,341],[\"app\",1153,145],[\"app\",1154,328],[\"app\",1155,427],[\"app\",1156,430],[\"const\",[\"str\",[\"anonymous\"],\"instIsManifoldMinSmoothnessOfNatWithTopENat\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",1158,31],[\"app\",1159,36],[\"app\",1160,328],[\"app\",1161,351],[\"app\",1162,328],[\"app\",1163,332],[\"app\",1164,341],[\"app\",1165,145],[\"app\",1166,328],[\"app\",1167,427],[\"app\",1168,430],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"ContMDiffAdd\"],\"toIsManifold\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",1170,31],[\"app\",1171,36],[\"app\",1172,328],[\"app\",1173,351],[\"app\",1174,328],[\"app\",1175,332],[\"app\",1176,341],[\"app\",1177,145],[\"const\",[\"str\",[\"anonymous\"],\"minSmoothness\"],[[\"zero\"]]],[\"app\",1179,31],[\"app\",1180,36],[\"const\",[\"str\",[\"anonymous\"],\"WithTop\"],[[\"zero\"]]],[\"app\",1182,121],[\"app\",6,1183],[\"app\",1184,9],[\"app\",48,1183],[\"app\",1186,9],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"WithTop\"],\"natCast\"],[[\"zero\"]]],[\"app\",1188,121],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"ENat\"],\"instNatCast\"],[]],[\"app\",1189,1190],[\"app\",1187,1191],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Nat\"],\"instAtLeastTwoHAddOfNat\"],[]],[\"app\",1193,19],[\"app\",1194,207],[\"app\",1192,1195],[\"app\",1185,1196],[\"app\",1181,1197],[\"app\",1178,1198],[\"app\",1199,328],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"AddCommMagma\"],\"toAdd\"],[[\"zero\"]]],[\"app\",1201,328],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"AddCommSemigroup\"],\"toAddCommMagma\"],[[\"zero\"]]],[\"app\",1203,328],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"AddCommMonoid\"],\"toAddCommSemigroup\"],[[\"zero\"]]],[\"app\",1205,328],[\"app\",996,328],[\"app\",911,328],[\"app\",1208,332],[\"app\",1207,1209],[\"app\",1206,1210],[\"app\",1204,1211],[\"app\",1202,1212],[\"app\",1200,1213],[\"app\",1214,427],[\"app\",1215,430],[\"const\",[\"str\",[\"anonymous\"],\"instContMDiffAddSelf\"],[[\"zero\"],[\"zero\"]]],[\"app\",1217,31],[\"app\",1218,36],[\"app\",1219,328],[\"app\",1220,332],[\"app\",1221,341],[\"app\",1222,1198],[\"app\",1216,1223],[\"app\",1169,1224],[\"app\",1157,1225],[\"app\",1145,1226],[\"app\",1133,1227],[\"app\",1121,1228],[\"app\",1124,42],[\"app\",1230,73],[\"app\",1231,112],[\"app\",1232,21],[\"app\",1233,25],[\"app\",1234,118],[\"app\",1235,1116],[\"app\",1236,1118],[\"app\",1237,725],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"IsManifold\"],\"instOfNatWithTopENat_1\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",1239,31],[\"app\",1240,36],[\"app\",1241,42],[\"app\",1242,73],[\"app\",1243,112],[\"app\",1244,21],[\"app\",1245,25],[\"app\",1246,118],[\"app\",1247,1116],[\"app\",1248,1118],[\"app\",1249,725],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"IsManifold\"],\"instOfNatWithTopENat_2\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",1251,31],[\"app\",1252,36],[\"app\",1253,42],[\"app\",1254,73],[\"app\",1255,112],[\"app\",1256,21],[\"app\",1257,25],[\"app\",1258,118],[\"app\",1259,1116],[\"app\",1260,1118],[\"app\",1261,725],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"IsManifold\"],\"instOfSomeENatTopOfLEInfty\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",1263,31],[\"app\",1264,36],[\"app\",1265,42],[\"app\",1266,73],[\"app\",1267,112],[\"app\",1268,21],[\"app\",1269,25],[\"app\",1270,118],[\"app\",1271,1116],[\"app\",1272,1118],[\"app\",1273,725],[\"app\",1274,1197],[\"app\",1275,403],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"IsManifold\"],\"instLEInftyOfNatWithTopENat\"],[]],[\"app\",1277,9],[\"app\",1278,1195],[\"app\",1276,1279],[\"app\",1262,1280],[\"app\",1250,1281],[\"app\",1238,1282],[\"app\",1229,1283],[\"const\",[\"str\",[\"anonymous\"],\"tangentMapWithin\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",1285,31],[\"app\",1286,36],[\"app\",1287,328],[\"app\",1288,332],[\"app\",1289,341],[\"app\",1290,328],[\"app\",1291,351],[\"app\",1292,145],[\"app\",1293,328],[\"app\",1294,427],[\"app\",1295,430],[\"app\",1296,42],[\"app\",1297,73],[\"app\",1298,112],[\"app\",1299,21],[\"app\",1300,25],[\"app\",1301,118],[\"app\",1302,1116],[\"app\",1303,1118],[\"app\",1304,725],[\"app\",1305,134],[\"app\",1306,321],[\"app\",1284,1307],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Set\"],\"preimage\"],[[\"zero\"],[\"zero\"]]],[\"app\",1309,1108],[\"app\",1310,328],[\"const\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"Bundle\"],\"TotalSpace\"],\"proj\"],[[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",1312,328],[\"app\",1313,328],[\"const\",[\"str\",[\"anonymous\"],\"TangentSpace\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",1315,31],[\"app\",1316,36],[\"app\",1317,328],[\"app\",1318,332],[\"app\",1319,341],[\"app\",1320,328],[\"app\",1321,351],[\"app\",1322,145],[\"app\",1323,328],[\"app\",1324,427],[\"app\",1325,430],[\"app\",1314,1326],[\"app\",1311,1327],[\"app\",1328,321],[\"app\",1308,1329],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"ContMDiffOn\"],\"continuousOn_tangentMapWithin\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",1331,31],[\"app\",1332,36],[\"app\",1333,127],[\"app\",1334,328],[\"app\",1335,332],[\"app\",1336,341],[\"app\",1337,328],[\"app\",1338,351],[\"app\",1339,145],[\"app\",1340,328],[\"app\",1341,427],[\"app\",1342,430],[\"app\",1343,42],[\"app\",1344,73],[\"app\",1345,112],[\"app\",1346,21],[\"app\",1347,25],[\"app\",1348,118],[\"app\",1349,1116],[\"app\",1350,1118],[\"app\",1351,725],[\"app\",1352,134],[\"app\",1353,321],[\"app\",1354,1227],[\"app\",1355,1282],[\"app\",1356,27],[\"const\",[\"str\",[\"anonymous\"],\"of_eq_true\"],[]],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"LE\"],\"le\"],[[\"zero\"]]],[\"app\",1359,1183],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Preorder\"],\"toLE\"],[[\"zero\"]]],[\"app\",1361,1183],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"WithTop\"],\"instPreorder\"],[[\"zero\"]]],[\"app\",1363,121],[\"const\",[\"str\",[\"anonymous\"],\"instPreorderENat\"],[]],[\"app\",1364,1365],[\"app\",1362,1366],[\"app\",1360,1367],[\"app\",1184,203],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"One\"],\"toOfNat1\"],[[\"zero\"]]],[\"app\",1370,1183],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"WithTop\"],\"one\"],[[\"zero\"]]],[\"app\",1372,121],[\"const\",[\"str\",[\"anonymous\"],\"instOneENat\"],[]],[\"app\",1373,1374],[\"app\",1371,1375],[\"app\",1369,1376],[\"app\",1368,1377],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"OrderTop\"],\"toTop\"],[[\"zero\"]]],[\"app\",1379,121],[\"app\",1361,121],[\"app\",1381,1365],[\"app\",1380,1382],[\"const\",[\"str\",[\"anonymous\"],\"instOrderTopENat\"],[]],[\"app\",1383,1384],[\"app\",124,1385],[\"app\",122,1386],[\"app\",1378,1387],[\"app\",1358,1388],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Eq\"],\"trans\"],[[\"succ\",[\"zero\"]]]],[\"sort\",[\"zero\"]],[\"app\",1390,1391],[\"app\",1392,1388],[\"const\",[\"str\",[\"anonymous\"],\"Ne\"],[[\"succ\",[\"zero\"]]]],[\"app\",1394,1183],[\"app\",1395,1377],[\"app\",123,1183],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"WithTop\"],\"top\"],[[\"zero\"]]],[\"app\",1398,121],[\"app\",1397,1399],[\"app\",1396,1400],[\"app\",1393,1401],[\"const\",[\"str\",[\"anonymous\"],\"True\"],[]],[\"app\",1402,1403],[\"const\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"WithTop\"],\"le_coe_top\"],\"_simp_1\"],[[\"zero\"]]],[\"app\",1405,121],[\"app\",1406,1365],[\"app\",1407,1377],[\"app\",1408,1384],[\"app\",1404,1409],[\"const\",[\"str\",[\"anonymous\"],\"Not\"],[]],[\"const\",[\"str\",[\"anonymous\"],\"Eq\"],[[\"succ\",[\"zero\"]]]],[\"app\",1412,1183],[\"app\",1413,1377],[\"app\",1414,1400],[\"app\",1411,1415],[\"app\",1392,1416],[\"const\",[\"str\",[\"anonymous\"],\"False\"],[]],[\"app\",1411,1418],[\"app\",1417,1419],[\"app\",1420,1403],[\"const\",[\"str\",[\"anonymous\"],\"congrArg\"],[[\"succ\",[\"zero\"]],[\"succ\",[\"zero\"]]]],[\"app\",1422,1391],[\"app\",1423,1391],[\"app\",1424,1415],[\"app\",1425,1418],[\"app\",1426,1411],[\"const\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"WithTop\"],\"one_ne_top\"],\"_simp_2\"],[[\"zero\"]]],[\"app\",1428,121],[\"app\",1429,1374],[\"app\",1427,1430],[\"app\",1421,1431],[\"const\",[\"str\",[\"anonymous\"],\"not_false_eq_true\"],[]],[\"app\",1432,1433],[\"app\",1410,1434],[\"app\",1389,1435],[\"app\",1357,1436],[\"app\",1437,2],[\"app\",679,294],[\"app\",1439,2],[\"const\",[\"str\",[\"anonymous\"],\"ContinuousLinearMap\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",1441,31],[\"app\",1442,31],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"CommSemiring\"],\"toSemiring\"],[[\"zero\"]]],[\"app\",1444,31],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Semifield\"],\"toCommSemiring\"],[[\"zero\"]]],[\"app\",1446,31],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Field\"],\"toSemifield\"],[[\"zero\"]]],[\"app\",1448,31],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"NormedField\"],\"toField\"],[[\"zero\"]]],[\"app\",1450,31],[\"app\",1451,84],[\"app\",1449,1452],[\"app\",1447,1453],[\"app\",1445,1454],[\"app\",1443,1455],[\"app\",1456,1455],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"RingHom\"],\"id\"],[[\"zero\"]]],[\"app\",1458,31],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Semiring\"],\"toNonAssocSemiring\"],[[\"zero\"]]],[\"app\",1460,31],[\"app\",1461,1455],[\"app\",1459,1462],[\"app\",1457,1463],[\"app\",1317,327],[\"app\",1465,171],[\"app\",1466,197],[\"app\",1467,327],[\"app\",1468,642],[\"app\",1469,646],[\"app\",1470,157],[\"app\",1471,426],[\"const\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"TopCat\"],\"of\"],\"chartedSpace\"],[[\"zero\"],[\"zero\"]]],[\"app\",1473,327],[\"app\",1474,642],[\"const\",[\"str\",[\"anonymous\"],\"WithLp\"],[[\"zero\"]]],[\"app\",1476,61],[\"app\",1477,931],[\"app\",1475,1478],[\"app\",1479,426],[\"app\",1480,651],[\"app\",1480,1481],[\"app\",1472,1482],[\"app\",398,27],[\"app\",1483,1484],[\"app\",1464,1485],[\"const\",[\"str\",[\"anonymous\"],\"instTopologicalSpaceTangentSpace\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",1487,31],[\"app\",1488,36],[\"app\",1489,327],[\"app\",1490,171],[\"app\",1491,197],[\"app\",1492,327],[\"app\",1493,642],[\"app\",1494,646],[\"app\",1495,157],[\"app\",1496,426],[\"app\",1497,1482],[\"app\",1498,1484],[\"app\",1486,1499],[\"app\",996,1485],[\"const\",[\"str\",[\"anonymous\"],\"instAddCommGroupTangentSpace\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",1502,31],[\"app\",1503,36],[\"app\",1504,327],[\"app\",1505,171],[\"app\",1506,197],[\"app\",1507,327],[\"app\",1508,642],[\"app\",1509,646],[\"app\",1510,157],[\"app\",1511,426],[\"app\",1512,1482],[\"app\",1513,1484],[\"app\",1501,1514],[\"app\",1500,1515],[\"app\",1317,42],[\"app\",1517,73],[\"app\",1518,112],[\"app\",1519,21],[\"app\",1520,25],[\"app\",1521,118],[\"bvar\",21],[\"app\",1522,1523],[\"bvar\",20],[\"app\",1524,1525],[\"bvar\",19],[\"app\",1526,1527],[\"app\",405,157],[\"app\",142,725],[\"app\",1529,1530],[\"app\",1531,1523],[\"app\",142,1118],[\"app\",379,1533],[\"app\",383,129],[\"app\",1534,1535],[\"app\",1536,2],[\"app\",725,1537],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],1530,1538,\"default\"],[\"app\",1532,1539],[\"app\",387,1530],[\"app\",389,1530],[\"app\",1542,157],[\"app\",370,725],[\"app\",1544,438],[\"app\",1543,1545],[\"app\",1541,1546],[\"app\",1540,1547],[\"app\",1548,1484],[\"app\",1528,1549],[\"app\",1516,1550],[\"app\",1489,42],[\"app\",1552,73],[\"app\",1553,112],[\"app\",1554,21],[\"app\",1555,25],[\"app\",1556,118],[\"app\",1557,1523],[\"app\",1558,1525],[\"app\",1559,1527],[\"app\",1560,1549],[\"app\",1551,1561],[\"app\",996,1550],[\"app\",1504,42],[\"app\",1564,73],[\"app\",1565,112],[\"app\",1566,21],[\"app\",1567,25],[\"app\",1568,118],[\"app\",1569,1523],[\"app\",1570,1525],[\"app\",1571,1527],[\"app\",1572,1549],[\"app\",1563,1573],[\"app\",1562,1574],[\"const\",[\"str\",[\"anonymous\"],\"instModuleTangentSpace\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",1576,31],[\"app\",1577,36],[\"app\",1578,327],[\"app\",1579,171],[\"app\",1580,197],[\"app\",1581,327],[\"app\",1582,642],[\"app\",1583,646],[\"app\",1584,157],[\"app\",1585,426],[\"app\",1586,1482],[\"app\",1587,1484],[\"app\",1575,1588],[\"app\",1578,42],[\"app\",1590,73],[\"app\",1591,112],[\"app\",1592,21],[\"app\",1593,25],[\"app\",1594,118],[\"app\",1595,1523],[\"app\",1596,1525],[\"app\",1597,1527],[\"app\",1598,1549],[\"app\",1589,1599],[\"app\",1412,1600],[\"const\",[\"str\",[\"anonymous\"],\"mfderivWithin\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",1602,31],[\"app\",1603,36],[\"app\",1604,327],[\"app\",1605,171],[\"app\",1606,197],[\"app\",1607,327],[\"app\",1608,642],[\"app\",1609,646],[\"app\",1610,157],[\"app\",1611,426],[\"app\",1612,1482],[\"app\",1613,42],[\"app\",1614,73],[\"app\",1615,112],[\"app\",1616,21],[\"app\",1617,25],[\"app\",1618,118],[\"app\",1619,1523],[\"app\",1620,1525],[\"app\",1621,1527],[\"app\",1622,1548],[\"app\",366,1530],[\"app\",1624,157],[\"app\",1625,1545],[\"app\",1623,1626],[\"app\",1627,1484],[\"app\",1601,1628],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"ContinuousLinearMap\"],\"comp\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",1630,31],[\"app\",1631,31],[\"app\",1632,31],[\"app\",1633,849],[\"app\",1634,1455],[\"app\",1635,1455],[\"app\",1461,849],[\"app\",1459,1637],[\"app\",1636,1638],[\"app\",1639,1463],[\"app\",1640,1463],[\"app\",1470,327],[\"app\",1642,426],[\"app\",1643,1482],[\"app\",1644,1484],[\"app\",1641,1645],[\"app\",1495,327],[\"app\",1647,426],[\"app\",1648,1482],[\"app\",1649,1484],[\"app\",1646,1650],[\"app\",996,1645],[\"app\",1510,327],[\"app\",1653,426],[\"app\",1654,1482],[\"app\",1655,1484],[\"app\",1652,1656],[\"app\",1651,1657],[\"app\",1322,290],[\"app\",1659,328],[\"app\",1660,427],[\"app\",1661,430],[\"app\",1662,27],[\"app\",1658,1663],[\"app\",1489,328],[\"app\",1665,332],[\"app\",1666,341],[\"app\",1667,328],[\"app\",1668,351],[\"app\",1669,290],[\"app\",1670,328],[\"app\",1671,427],[\"app\",1672,430],[\"app\",1673,27],[\"app\",1664,1674],[\"app\",996,1663],[\"app\",1504,328],[\"app\",1677,332],[\"app\",1678,341],[\"app\",1679,328],[\"app\",1680,351],[\"app\",1681,290],[\"app\",1682,328],[\"app\",1683,427],[\"app\",1684,430],[\"app\",1685,27],[\"app\",1676,1686],[\"app\",1675,1687],[\"app\",145,27],[\"app\",1528,1689],[\"app\",1688,1690],[\"app\",1560,1689],[\"app\",1691,1692],[\"app\",996,1690],[\"app\",1572,1689],[\"app\",1694,1695],[\"app\",1693,1696],[\"app\",1584,327],[\"app\",1698,426],[\"app\",1699,1482],[\"app\",1700,1484],[\"app\",1697,1701],[\"app\",1578,328],[\"app\",1703,332],[\"app\",1704,341],[\"app\",1705,328],[\"app\",1706,351],[\"app\",1707,290],[\"app\",1708,328],[\"app\",1709,427],[\"app\",1710,430],[\"app\",1711,27],[\"app\",1702,1712],[\"app\",1598,1689],[\"app\",1713,1714],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"RingHomCompTriple\"],\"ids\"],[[\"zero\"],[\"zero\"]]],[\"app\",1716,31],[\"app\",1717,31],[\"app\",1718,849],[\"app\",1719,1455],[\"app\",1720,1463],[\"app\",1715,1721],[\"app\",1604,328],[\"app\",1723,332],[\"app\",1724,341],[\"app\",1725,328],[\"app\",1726,351],[\"app\",1727,290],[\"app\",1728,328],[\"app\",1729,427],[\"app\",1730,430],[\"app\",1731,42],[\"app\",1732,73],[\"app\",1733,112],[\"app\",1734,21],[\"app\",1735,25],[\"app\",1736,118],[\"app\",1737,1523],[\"app\",1738,1525],[\"app\",1739,1527],[\"app\",1740,145],[\"app\",1741,292],[\"app\",1742,27],[\"app\",1722,1743],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"ContinuousLinearMap\"],\"inr\"],[[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",1745,31],[\"app\",1746,849],[\"app\",1317,31],[\"app\",1748,71],[\"app\",1749,187],[\"app\",1750,31],[\"app\",1751,221],[\"app\",1752,241],[\"app\",1753,31],[\"app\",1754,261],[\"app\",1755,274],[\"app\",383,27],[\"app\",1756,1757],[\"app\",1747,1758],[\"app\",1489,31],[\"app\",1760,71],[\"app\",1761,187],[\"app\",1762,31],[\"app\",1763,221],[\"app\",1764,241],[\"app\",1765,31],[\"app\",1766,261],[\"app\",1767,274],[\"app\",1768,1757],[\"app\",1759,1769],[\"app\",996,1758],[\"app\",1504,31],[\"app\",1772,71],[\"app\",1773,187],[\"app\",1774,31],[\"app\",1775,221],[\"app\",1776,241],[\"app\",1777,31],[\"app\",1778,261],[\"app\",1779,274],[\"app\",1780,1757],[\"app\",1771,1781],[\"app\",1770,1782],[\"app\",1578,31],[\"app\",1784,71],[\"app\",1785,187],[\"app\",1786,31],[\"app\",1787,221],[\"app\",1788,241],[\"app\",1789,31],[\"app\",1790,261],[\"app\",1791,274],[\"app\",1792,1757],[\"app\",1783,1793],[\"app\",1794,1645],[\"app\",1795,1650],[\"app\",1796,1657],[\"app\",1797,1701],[\"app\",1744,1798],[\"app\",1629,1799],[\"forall\",[\"str\",[\"anonymous\"],\"hq\"],1440,1800,\"default\"],[\"forall\",[\"str\",[\"anonymous\"],\"q\"],328,1801,\"default\"],[\"forall\",[\"num\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"a\"],\"_@\"],\"_internal\"],\"_hyg\"],0],327,328,\"default\"],[\"app\",379,327],[\"app\",1804,1535],[\"app\",1805,2],[\"lam\",[\"str\",[\"anonymous\"],\"y\"],327,1806,\"default\"],[\"const\",[\"str\",[\"anonymous\"],\"HasFDerivAt\"],[[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",1808,31],[\"app\",1809,36],[\"app\",1810,327],[\"app\",1811,938],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"WithLp\"],\"instModule\"],[[\"zero\"],[\"zero\"]]],[\"app\",1813,61],[\"app\",1814,31],[\"app\",1815,931],[\"app\",1816,849],[\"app\",1817,937],[\"const\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"Pi\"],\"Function\"],\"module\"],[[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",1819,156],[\"app\",1820,31],[\"app\",1821,31],[\"app\",1822,849],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Semiring\"],\"toAddCommMonoid\"],[[\"zero\"]]],[\"app\",1824,31],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Ring\"],\"toSemiring\"],[[\"zero\"]]],[\"app\",1826,31],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Real\"],\"instRing\"],[]],[\"app\",1827,1828],[\"app\",1825,1829],[\"app\",1823,1830],[\"app\",1831,855],[\"app\",1818,1832],[\"app\",1812,1833],[\"app\",1834,426],[\"app\",1835,328],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Prod\"],\"instAddCommGroup\"],[[\"zero\"],[\"zero\"]]],[\"app\",1837,31],[\"app\",1838,327],[\"app\",1839,851],[\"app\",1840,938],[\"app\",1836,1841],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Prod\"],\"instModule\"],[[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",1843,31],[\"app\",1844,31],[\"app\",1845,327],[\"app\",1846,849],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Real\"],\"instAddCommMonoid\"],[]],[\"app\",1847,1848],[\"app\",996,327],[\"app\",1850,938],[\"app\",1849,1851],[\"app\",1852,855],[\"app\",1853,1833],[\"app\",1842,1854],[\"app\",1855,427],[\"app\",1856,2],[\"app\",1747,31],[\"app\",1858,261],[\"app\",1859,1848],[\"app\",1860,855],[\"app\",1861,327],[\"app\",1862,426],[\"app\",1863,1851],[\"app\",1864,1833],[\"app\",1857,1865],[\"app\",398,129],[\"app\",1866,1867],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"HasFDerivAt\"],\"prodMk\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",1869,31],[\"app\",1870,36],[\"app\",1871,327],[\"app\",1872,171],[\"app\",1873,197],[\"app\",1874,31],[\"app\",1875,71],[\"app\",1876,187],[\"app\",1877,327],[\"app\",1878,171],[\"app\",1879,197],[\"app\",383,134],[\"lam\",[\"num\",[\"str\",[\"str\",[\"num\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"x\"],\"_@\"],\"Mathlib\"],\"Analysis\"],\"Calculus\"],\"FDeriv\"],\"Const\"],3930327781],\"_hygCtx\"],\"_hyg\"],41],327,1881,\"default\"],[\"app\",1880,1882],[\"app\",1464,327],[\"app\",1884,426],[\"app\",1885,1851],[\"app\",1886,31],[\"app\",1887,261],[\"app\",996,31],[\"app\",1889,851],[\"app\",1888,1890],[\"app\",916,327],[\"app\",1892,84],[\"app\",1893,338],[\"app\",1894,197],[\"app\",1891,1895],[\"app\",916,31],[\"app\",1897,84],[\"app\",1898,181],[\"app\",1899,187],[\"app\",1896,1900],[\"app\",6,1901],[\"nat\",0],[\"app\",1902,1903],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Zero\"],\"toOfNat0\"],[[\"zero\"]]],[\"app\",1905,1901],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"ContinuousLinearMap\"],\"zero\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",1907,31],[\"app\",1908,31],[\"app\",1909,1455],[\"app\",1910,1455],[\"app\",1911,1463],[\"app\",1912,327],[\"app\",1913,426],[\"app\",1914,1851],[\"app\",1915,31],[\"app\",1916,261],[\"app\",1917,1890],[\"app\",1918,1895],[\"app\",1919,1900],[\"app\",1906,1920],[\"app\",1904,1921],[\"app\",1883,1922],[\"app\",1923,1867],[\"lam\",[\"str\",[\"anonymous\"],\"y\"],327,2,\"default\"],[\"app\",1924,1925],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"ContinuousLinearMap\"],\"id\"],[[\"zero\"],[\"zero\"]]],[\"app\",1927,31],[\"app\",1928,849],[\"app\",1929,327],[\"app\",1930,426],[\"app\",1931,1851],[\"app\",1932,1833],[\"app\",1926,1933],[\"const\",[\"str\",[\"anonymous\"],\"hasFDerivAt_const\"],[[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",1935,31],[\"app\",1936,36],[\"app\",1937,327],[\"app\",1938,938],[\"app\",1939,1895],[\"app\",1940,426],[\"app\",1941,31],[\"app\",1942,851],[\"app\",1943,1900],[\"app\",1944,261],[\"app\",1945,1535],[\"app\",1946,1867],[\"app\",1934,1947],[\"const\",[\"str\",[\"anonymous\"],\"hasFDerivAt_id\"],[[\"zero\"],[\"zero\"]]],[\"app\",1949,31],[\"app\",1950,36],[\"app\",1951,327],[\"app\",1952,938],[\"app\",1953,1895],[\"app\",1954,426],[\"app\",1955,1867],[\"app\",1948,1956],[\"const\",[\"str\",[\"anonymous\"],\"MDifferentiableAt\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",1958,31],[\"app\",1959,36],[\"app\",1960,327],[\"app\",1961,171],[\"app\",1962,197],[\"app\",1963,327],[\"app\",1964,642],[\"app\",1965,646],[\"app\",1966,327],[\"app\",1967,426],[\"app\",1968,1482],[\"app\",1969,328],[\"app\",1970,332],[\"app\",1971,341],[\"app\",1972,328],[\"app\",1973,351],[\"app\",1974,488],[\"app\",1975,328],[\"app\",1976,427],[\"app\",1977,430],[\"app\",1978,27],[\"app\",398,134],[\"app\",1979,1980],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"DifferentiableAt\"],\"mdifferentiableAt\"],[[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",1982,31],[\"app\",1983,36],[\"app\",1984,327],[\"app\",1985,171],[\"app\",1986,197],[\"app\",1987,328],[\"app\",1988,332],[\"app\",1989,341],[\"app\",1990,27],[\"app\",1991,1980],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"HasFDerivAt\"],\"differentiableAt\"],[[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",1993,31],[\"app\",1994,36],[\"app\",1995,327],[\"app\",1996,938],[\"app\",1997,1833],[\"app\",1998,426],[\"app\",1999,328],[\"app\",2000,1841],[\"app\",2001,1854],[\"app\",2002,427],[\"app\",2003,27],[\"app\",2004,1865],[\"app\",2005,1980],[\"app\",2006,2],[\"app\",1992,2007],[\"app\",398,252],[\"app\",1644,2009],[\"app\",1464,2010],[\"app\",1649,2009],[\"app\",2011,2012],[\"app\",996,2010],[\"app\",1655,2009],[\"app\",2014,2015],[\"app\",2013,2016],[\"bvar\",24],[\"app\",1522,2018],[\"bvar\",23],[\"app\",2019,2020],[\"bvar\",22],[\"app\",2021,2022],[\"app\",405,327],[\"app\",2024,328],[\"app\",2025,2018],[\"app\",2026,290],[\"app\",2027,129],[\"app\",2028,2009],[\"app\",2023,2029],[\"app\",2017,2030],[\"app\",1557,2018],[\"app\",2032,2020],[\"app\",2033,2022],[\"app\",2034,2029],[\"app\",2031,2035],[\"app\",996,2030],[\"app\",1569,2018],[\"app\",2038,2020],[\"app\",2039,2022],[\"app\",2040,2029],[\"app\",2037,2041],[\"app\",2036,2042],[\"app\",1700,2009],[\"app\",2043,2044],[\"app\",1595,2018],[\"app\",2046,2020],[\"app\",2047,2022],[\"app\",2048,2029],[\"app\",2045,2049],[\"app\",1412,2050],[\"app\",1610,327],[\"app\",2052,426],[\"app\",2053,1482],[\"app\",2054,42],[\"app\",2055,73],[\"app\",2056,112],[\"app\",2057,21],[\"app\",2058,25],[\"app\",2059,118],[\"app\",2060,2018],[\"app\",2061,2020],[\"app\",2062,2022],[\"app\",2063,2028],[\"app\",142,1527],[\"app\",366,2065],[\"app\",2066,157],[\"app\",370,1527],[\"app\",2068,787],[\"app\",2067,2069],[\"app\",2064,2070],[\"app\",2071,2009],[\"app\",2051,2072],[\"app\",1633,1455],[\"app\",2074,1455],[\"app\",2075,1455],[\"app\",2076,1463],[\"app\",2077,1463],[\"app\",2078,1463],[\"app\",2079,2010],[\"app\",2080,2012],[\"app\",2081,2016],[\"app\",1322,698],[\"app\",2083,328],[\"app\",2084,427],[\"app\",2085,430],[\"app\",129,2009],[\"app\",2086,2087],[\"app\",2082,2088],[\"app\",1669,698],[\"app\",2090,328],[\"app\",2091,427],[\"app\",2092,430],[\"app\",2093,2087],[\"app\",2089,2094],[\"app\",996,2088],[\"app\",1681,698],[\"app\",2097,328],[\"app\",2098,427],[\"app\",2099,430],[\"app\",2100,2087],[\"app\",2096,2101],[\"app\",2095,2102],[\"app\",290,2087],[\"app\",2023,2104],[\"app\",2103,2105],[\"app\",2034,2104],[\"app\",2106,2107],[\"app\",996,2105],[\"app\",2040,2104],[\"app\",2109,2110],[\"app\",2108,2111],[\"app\",2112,2044],[\"app\",1707,698],[\"app\",2114,328],[\"app\",2115,427],[\"app\",2116,430],[\"app\",2117,2087],[\"app\",2113,2118],[\"app\",2048,2104],[\"app\",2119,2120],[\"app\",1718,1455],[\"app\",2122,1455],[\"app\",2123,1463],[\"app\",2121,2124],[\"app\",1727,698],[\"app\",2126,328],[\"app\",2127,427],[\"app\",2128,430],[\"app\",2129,42],[\"app\",2130,73],[\"app\",2131,112],[\"app\",2132,21],[\"app\",2133,25],[\"app\",2134,118],[\"app\",2135,2018],[\"app\",2136,2020],[\"app\",2137,2022],[\"app\",2138,290],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Set\"],\"ofPred\"],[[\"zero\"]]],[\"app\",2140,158],[\"const\",[\"str\",[\"anonymous\"],\"And\"],[]],[\"app\",313,1116],[\"app\",2143,1118],[\"app\",686,2144],[\"app\",690,2],[\"app\",2145,2146],[\"app\",2142,2147],[\"app\",142,1525],[\"app\",366,2149],[\"app\",2150,157],[\"app\",370,1525],[\"app\",2152,408],[\"app\",2151,2153],[\"app\",697,2154],[\"app\",706,2],[\"app\",2155,2156],[\"app\",2148,2157],[\"lam\",[\"str\",[\"anonymous\"],\"p\"],158,2158,\"default\"],[\"app\",2141,2159],[\"app\",2139,2160],[\"app\",2161,2087],[\"app\",2125,2162],[\"app\",2054,328],[\"app\",2164,332],[\"app\",2165,341],[\"app\",2166,328],[\"app\",2167,351],[\"app\",2168,698],[\"app\",2169,328],[\"app\",2170,427],[\"app\",2171,430],[\"app\",2172,129],[\"app\",2173,2070],[\"app\",2174,2009],[\"app\",2163,2175],[\"app\",2073,2176],[\"const\",[\"str\",[\"anonymous\"],\"mfderivWithin_comp\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",2178,31],[\"app\",2179,36],[\"app\",2180,327],[\"app\",2181,171],[\"app\",2182,197],[\"app\",2183,327],[\"app\",2184,642],[\"app\",2185,646],[\"app\",2186,327],[\"app\",2187,426],[\"app\",2188,1482],[\"app\",2189,328],[\"app\",2190,332],[\"app\",2191,341],[\"app\",2192,328],[\"app\",2193,351],[\"app\",2194,698],[\"app\",2195,328],[\"app\",2196,427],[\"app\",2197,430],[\"app\",2198,42],[\"app\",2199,73],[\"app\",2200,112],[\"app\",2201,21],[\"app\",2202,25],[\"app\",2203,118],[\"app\",2204,2018],[\"app\",2205,2020],[\"app\",2206,2022],[\"app\",2207,129],[\"app\",2208,2009],[\"app\",2209,2070],[\"app\",2210,290],[\"app\",2211,2160],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"ContMDiffOn\"],\"mdifferentiableOn\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",2213,31],[\"app\",2214,36],[\"app\",2215,328],[\"app\",2216,332],[\"app\",2217,341],[\"app\",2218,328],[\"app\",2219,351],[\"app\",2220,698],[\"app\",2221,328],[\"app\",2222,427],[\"app\",2223,430],[\"app\",2224,42],[\"app\",2225,73],[\"app\",2226,112],[\"app\",2227,21],[\"app\",2228,25],[\"app\",2229,118],[\"app\",2230,2018],[\"app\",2231,2020],[\"app\",2232,2022],[\"app\",2233,290],[\"app\",2234,488],[\"app\",2235,127],[\"app\",2236,294],[\"app\",1413,127],[\"app\",1184,1903],[\"app\",1905,1183],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"WithTop\"],\"zero\"],[[\"zero\"]]],[\"app\",2241,121],[\"const\",[\"str\",[\"anonymous\"],\"instZeroENat\"],[]],[\"app\",2242,2243],[\"app\",2240,2244],[\"app\",2239,2245],[\"app\",2238,2246],[\"app\",1411,2247],[\"app\",1358,2248],[\"app\",1392,2248],[\"app\",2250,1419],[\"app\",2251,1403],[\"app\",1424,2247],[\"app\",2253,1418],[\"app\",2254,1411],[\"app\",1392,2247],[\"app\",1412,121],[\"app\",2257,126],[\"app\",6,121],[\"app\",2259,1903],[\"app\",1905,121],[\"app\",2261,2243],[\"app\",2260,2262],[\"app\",2258,2263],[\"app\",2256,2264],[\"app\",2265,1418],[\"const\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"WithTop\"],\"coe_eq_zero\"],\"_simp_1\"],[[\"zero\"]]],[\"app\",2267,121],[\"app\",2268,2243],[\"app\",2269,126],[\"app\",2266,2270],[\"const\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"ENat\"],\"top_ne_zero\"],\"_simp_1\"],[]],[\"app\",2271,2272],[\"app\",2255,2273],[\"app\",2252,2274],[\"app\",2275,1433],[\"app\",2249,2276],[\"app\",2237,2277],[\"app\",2278,252],[\"app\",2279,134],[\"app\",2212,2280],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"MDifferentiableAt\"],\"mdifferentiableWithinAt\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",2282,31],[\"app\",2283,36],[\"app\",2284,327],[\"app\",2285,171],[\"app\",2286,197],[\"app\",2287,327],[\"app\",2288,642],[\"app\",2289,646],[\"app\",2290,327],[\"app\",2291,426],[\"app\",2292,1482],[\"app\",2293,328],[\"app\",2294,332],[\"app\",2295,341],[\"app\",2296,328],[\"app\",2297,351],[\"app\",2298,698],[\"app\",2299,328],[\"app\",2300,427],[\"app\",2301,430],[\"app\",2302,129],[\"app\",2303,2009],[\"app\",2304,2070],[\"app\",2305,2],[\"app\",2281,2306],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Set\"],\"MapsTo\"],[[\"zero\"],[\"zero\"]]],[\"app\",2308,327],[\"app\",2309,328],[\"app\",2310,129],[\"app\",2311,2070],[\"app\",2312,488],[\"app\",674,327],[\"app\",299,327],[\"app\",2314,2315],[\"app\",677,327],[\"app\",2316,2317],[\"app\",2318,2154],[\"app\",2319,2],[\"app\",313,1527],[\"app\",2321,1116],[\"app\",686,2322],[\"app\",690,790],[\"app\",2323,2324],[\"app\",783,2325],[\"app\",142,1523],[\"app\",366,2327],[\"app\",2328,157],[\"app\",370,1523],[\"app\",2330,403],[\"app\",2329,2331],[\"app\",697,2332],[\"app\",706,790],[\"app\",2333,2334],[\"app\",2326,2335],[\"app\",690,145],[\"app\",2323,2337],[\"app\",805,2338],[\"app\",706,145],[\"app\",2333,2340],[\"app\",2339,2341],[\"app\",2342,321],[\"app\",2336,2343],[\"app\",2344,2],[\"lam\",[\"str\",[\"anonymous\"],\"hy\"],2320,2345,\"default\"],[\"lam\",[\"str\",[\"anonymous\"],\"y\"],327,2346,\"default\"],[\"let\",[\"str\",[\"anonymous\"],\"this\"],2313,2347,2,true],[\"app\",2307,2348],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"UniqueDiffWithinAt\"],\"uniqueMDiffWithinAt\"],[[\"zero\"],[\"zero\"]]],[\"app\",2350,31],[\"app\",2351,36],[\"app\",2352,327],[\"app\",2353,171],[\"app\",2354,197],[\"app\",2066,327],[\"app\",595,327],[\"app\",2357,2065],[\"app\",2358,1060],[\"app\",2359,36],[\"app\",2360,171],[\"app\",2361,197],[\"app\",2362,1065],[\"app\",263,1527],[\"app\",2363,2364],[\"app\",2365,1069],[\"app\",280,1527],[\"app\",2366,2367],[\"app\",2368,787],[\"app\",2356,2369],[\"app\",2355,2370],[\"app\",2371,2009],[\"app\",1082,327],[\"app\",2373,2065],[\"app\",2374,1060],[\"app\",2375,36],[\"app\",2376,171],[\"app\",2377,197],[\"app\",2378,1065],[\"app\",2379,2364],[\"app\",2380,1069],[\"app\",2381,2367],[\"app\",2382,787],[\"app\",2383,2009],[\"app\",313,1118],[\"app\",2385,725],[\"app\",686,2386],[\"app\",690,252],[\"app\",2387,2388],[\"app\",682,2389],[\"app\",697,2070],[\"app\",706,252],[\"app\",2391,2392],[\"app\",2390,2393],[\"app\",2394,134],[\"app\",2384,2395],[\"app\",2372,2396],[\"app\",2349,2397],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Eq\"],\"mp\"],[[\"zero\"]]],[\"app\",398,321],[\"app\",1644,2400],[\"app\",1464,2401],[\"app\",1649,2400],[\"app\",2402,2403],[\"app\",996,2401],[\"app\",1655,2400],[\"app\",2405,2406],[\"app\",2404,2407],[\"bvar\",25],[\"app\",1522,2409],[\"app\",2410,2018],[\"app\",2411,2020],[\"app\",2025,2409],[\"app\",2413,438],[\"app\",2414,134],[\"app\",2415,2400],[\"app\",2412,2416],[\"app\",2408,2417],[\"app\",1557,2409],[\"app\",2419,2018],[\"app\",2420,2020],[\"app\",2421,2416],[\"app\",2418,2422],[\"app\",996,2417],[\"app\",1569,2409],[\"app\",2425,2018],[\"app\",2426,2020],[\"app\",2427,2416],[\"app\",2424,2428],[\"app\",2423,2429],[\"app\",1700,2400],[\"app\",2430,2431],[\"app\",1595,2409],[\"app\",2433,2018],[\"app\",2434,2020],[\"app\",2435,2416],[\"app\",2432,2436],[\"app\",1412,2437],[\"app\",2060,2409],[\"app\",2439,2018],[\"app\",2440,2020],[\"app\",2441,2415],[\"app\",2442,2154],[\"app\",2443,2400],[\"app\",2438,2444],[\"app\",2079,2401],[\"app\",2446,2403],[\"app\",2447,2407],[\"app\",1322,787],[\"app\",2449,328],[\"app\",2450,427],[\"app\",2451,430],[\"app\",134,2400],[\"app\",2452,2453],[\"app\",2448,2454],[\"app\",1669,787],[\"app\",2456,328],[\"app\",2457,427],[\"app\",2458,430],[\"app\",2459,2453],[\"app\",2455,2460],[\"app\",996,2454],[\"app\",1681,787],[\"app\",2463,328],[\"app\",2464,427],[\"app\",2465,430],[\"app\",2466,2453],[\"app\",2462,2467],[\"app\",2461,2468],[\"app\",438,2453],[\"app\",2412,2470],[\"app\",2469,2471],[\"app\",2421,2470],[\"app\",2472,2473],[\"app\",996,2471],[\"app\",2427,2470],[\"app\",2475,2476],[\"app\",2474,2477],[\"app\",2478,2431],[\"app\",1707,787],[\"app\",2480,328],[\"app\",2481,427],[\"app\",2482,430],[\"app\",2483,2453],[\"app\",2479,2484],[\"app\",2435,2470],[\"app\",2485,2486],[\"app\",2487,2124],[\"app\",1727,787],[\"app\",2489,328],[\"app\",2490,427],[\"app\",2491,430],[\"app\",2492,42],[\"app\",2493,73],[\"app\",2494,112],[\"app\",2495,21],[\"app\",2496,25],[\"app\",2497,118],[\"app\",2498,2409],[\"app\",2499,2018],[\"app\",2500,2020],[\"app\",2501,438],[\"app\",2323,2146],[\"app\",2142,2503],[\"app\",2333,2156],[\"app\",2504,2505],[\"lam\",[\"str\",[\"anonymous\"],\"p\"],158,2506,\"default\"],[\"app\",2141,2507],[\"app\",2502,2508],[\"app\",2509,2453],[\"app\",2488,2510],[\"const\",[\"str\",[\"anonymous\"],\"mfderiv\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",2512,31],[\"app\",2513,36],[\"app\",2514,327],[\"app\",2515,171],[\"app\",2516,197],[\"app\",2517,327],[\"app\",2518,642],[\"app\",2519,646],[\"app\",2520,327],[\"app\",2521,642],[\"app\",2522,651],[\"app\",2523,328],[\"app\",2524,332],[\"app\",2525,341],[\"app\",2526,328],[\"app\",2527,351],[\"app\",2528,355],[\"app\",2529,328],[\"app\",2530,351],[\"app\",2531,430],[\"app\",2532,134],[\"app\",2533,2400],[\"app\",2511,2534],[\"app\",2445,2535],[\"app\",2399,2536],[\"app\",2511,1865],[\"app\",2445,2538],[\"app\",2537,2539],[\"app\",1642,642],[\"app\",2541,651],[\"app\",2542,2400],[\"app\",1464,2543],[\"app\",1647,642],[\"app\",2545,651],[\"app\",2546,2400],[\"app\",2544,2547],[\"app\",996,2543],[\"app\",1653,642],[\"app\",2550,651],[\"app\",2551,2400],[\"app\",2549,2552],[\"app\",2548,2553],[\"app\",1322,355],[\"app\",2555,328],[\"app\",2556,351],[\"app\",2557,430],[\"app\",2558,2453],[\"app\",2554,2559],[\"app\",1669,355],[\"app\",2561,328],[\"app\",2562,351],[\"app\",2563,430],[\"app\",2564,2453],[\"app\",2560,2565],[\"app\",996,2559],[\"app\",1681,355],[\"app\",2568,328],[\"app\",2569,351],[\"app\",2570,430],[\"app\",2571,2453],[\"app\",2567,2572],[\"app\",2566,2573],[\"app\",1698,642],[\"app\",2575,651],[\"app\",2576,2400],[\"app\",2574,2577],[\"app\",1707,355],[\"app\",2579,328],[\"app\",2580,351],[\"app\",2581,430],[\"app\",2582,2453],[\"app\",2578,2583],[\"app\",1422,2584],[\"app\",2585,1391],[\"app\",2586,2534],[\"app\",2587,1865],[\"app\",398,145],[\"app\",1644,2589],[\"app\",1464,2590],[\"app\",1649,2589],[\"app\",2591,2592],[\"app\",996,2590],[\"app\",1655,2589],[\"app\",2594,2595],[\"app\",2593,2596],[\"bvar\",26],[\"app\",1522,2598],[\"app\",2599,2409],[\"app\",2600,2018],[\"app\",2025,2598],[\"app\",2602,488],[\"app\",2603,252],[\"app\",2604,2589],[\"app\",2601,2605],[\"app\",2597,2606],[\"app\",1557,2598],[\"app\",2608,2409],[\"app\",2609,2018],[\"app\",2610,2605],[\"app\",2607,2611],[\"app\",996,2606],[\"app\",1569,2598],[\"app\",2614,2409],[\"app\",2615,2018],[\"app\",2616,2605],[\"app\",2613,2617],[\"app\",2612,2618],[\"app\",1700,2589],[\"app\",2619,2620],[\"app\",1595,2598],[\"app\",2622,2409],[\"app\",2623,2018],[\"app\",2624,2605],[\"app\",2621,2625],[\"app\",1412,2626],[\"app\",2060,2598],[\"app\",2628,2409],[\"app\",2629,2018],[\"app\",2630,2604],[\"app\",2631,2332],[\"app\",2632,2589],[\"app\",2627,2633],[\"app\",2079,2590],[\"app\",2635,2592],[\"app\",2636,2596],[\"app\",1322,408],[\"app\",2638,328],[\"app\",2639,427],[\"app\",2640,430],[\"app\",252,2589],[\"app\",2641,2642],[\"app\",2637,2643],[\"app\",1669,408],[\"app\",2645,328],[\"app\",2646,427],[\"app\",2647,430],[\"app\",2648,2642],[\"app\",2644,2649],[\"app\",996,2643],[\"app\",1681,408],[\"app\",2652,328],[\"app\",2653,427],[\"app\",2654,430],[\"app\",2655,2642],[\"app\",2651,2656],[\"app\",2650,2657],[\"app\",488,2642],[\"app\",2601,2659],[\"app\",2658,2660],[\"app\",2610,2659],[\"app\",2661,2662],[\"app\",996,2660],[\"app\",2616,2659],[\"app\",2664,2665],[\"app\",2663,2666],[\"app\",2667,2620],[\"app\",1707,408],[\"app\",2669,328],[\"app\",2670,427],[\"app\",2671,430],[\"app\",2672,2642],[\"app\",2668,2673],[\"app\",2624,2659],[\"app\",2674,2675],[\"app\",2676,2124],[\"app\",1727,408],[\"app\",2678,328],[\"app\",2679,427],[\"app\",2680,430],[\"app\",2681,42],[\"app\",2682,73],[\"app\",2683,112],[\"app\",2684,21],[\"app\",2685,25],[\"app\",2686,118],[\"app\",2687,2598],[\"app\",2688,2409],[\"app\",2689,2018],[\"app\",2690,488],[\"app\",313,1525],[\"app\",2692,1527],[\"app\",686,2693],[\"app\",2694,2146],[\"app\",2142,2695],[\"app\",142,2022],[\"app\",366,2697],[\"app\",2698,157],[\"app\",370,2022],[\"app\",2700,725],[\"app\",2699,2701],[\"app\",697,2702],[\"app\",2703,2156],[\"app\",2696,2704],[\"lam\",[\"str\",[\"anonymous\"],\"p\"],158,2705,\"default\"],[\"app\",2141,2706],[\"app\",2691,2707],[\"app\",2708,2642],[\"app\",2677,2709],[\"app\",2710,2],[\"app\",2634,2711],[\"lam\",[\"str\",[\"anonymous\"],\"_a\"],2584,2712,\"default\"],[\"app\",2588,2713],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"HasMFDerivAt\"],\"mfderiv\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",2715,31],[\"app\",2716,36],[\"app\",2717,327],[\"app\",2718,171],[\"app\",2719,197],[\"app\",2720,327],[\"app\",2721,642],[\"app\",2722,646],[\"app\",2723,327],[\"app\",2724,642],[\"app\",2725,651],[\"app\",2726,328],[\"app\",2727,332],[\"app\",2728,341],[\"app\",2729,328],[\"app\",2730,351],[\"app\",2731,355],[\"app\",2732,328],[\"app\",2733,351],[\"app\",2734,430],[\"app\",2735,134],[\"app\",2736,2400],[\"app\",2737,1865],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"HasFDerivAt\"],\"hasMFDerivAt\"],[[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",2739,31],[\"app\",2740,36],[\"app\",2741,327],[\"app\",2742,171],[\"app\",2743,197],[\"app\",2744,328],[\"app\",2745,332],[\"app\",2746,341],[\"app\",2747,134],[\"app\",2748,2400],[\"app\",2749,1865],[\"app\",2750,129],[\"app\",2738,2751],[\"app\",2714,2752],[\"app\",2540,2753],[\"app\",2052,642],[\"app\",2755,651],[\"app\",2756,328],[\"app\",2757,332],[\"app\",2758,341],[\"app\",2759,328],[\"app\",2760,351],[\"app\",2761,787],[\"app\",2762,328],[\"app\",2763,427],[\"app\",2764,430],[\"app\",2765,134],[\"app\",2150,327],[\"app\",2357,2149],[\"app\",2768,1060],[\"app\",2769,36],[\"app\",2770,171],[\"app\",2771,197],[\"app\",2772,1065],[\"app\",263,1525],[\"app\",2773,2774],[\"app\",2775,1069],[\"app\",280,1525],[\"app\",2776,2777],[\"app\",2778,408],[\"app\",2767,2779],[\"app\",2766,2780],[\"app\",2781,2400],[\"app\",2511,2782],[\"app\",2445,2783],[\"app\",2399,2784],[\"app\",2528,787],[\"app\",2786,328],[\"app\",2787,427],[\"app\",2788,430],[\"app\",2789,134],[\"app\",2790,2400],[\"app\",2511,2791],[\"app\",2445,2792],[\"app\",2785,2793],[\"app\",2554,2454],[\"app\",2795,2460],[\"app\",2796,2468],[\"app\",2797,2577],[\"app\",2798,2484],[\"app\",1422,2799],[\"app\",2800,1391],[\"app\",2801,2782],[\"app\",2802,2791],[\"lam\",[\"str\",[\"anonymous\"],\"_a\"],2799,2712,\"default\"],[\"app\",2803,2804],[\"const\",[\"str\",[\"anonymous\"],\"mfderivWithin_eq_mfderiv\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",2806,31],[\"app\",2807,36],[\"app\",2808,327],[\"app\",2809,171],[\"app\",2810,197],[\"app\",2811,327],[\"app\",2812,642],[\"app\",2813,646],[\"app\",2814,327],[\"app\",2815,642],[\"app\",2816,651],[\"app\",2817,328],[\"app\",2818,332],[\"app\",2819,341],[\"app\",2820,328],[\"app\",2821,351],[\"app\",2822,787],[\"app\",2823,328],[\"app\",2824,427],[\"app\",2825,430],[\"app\",2826,134],[\"app\",2827,2400],[\"app\",2828,2780],[\"app\",2355,2780],[\"app\",2830,2400],[\"app\",2373,2149],[\"app\",2832,1060],[\"app\",2833,36],[\"app\",2834,171],[\"app\",2835,197],[\"app\",2836,1065],[\"app\",2837,2774],[\"app\",2838,1069],[\"app\",2839,2777],[\"app\",2840,408],[\"app\",2841,2400],[\"app\",690,321],[\"app\",2145,2843],[\"app\",682,2844],[\"app\",706,321],[\"app\",2155,2846],[\"app\",2845,2847],[\"app\",2848,252],[\"app\",2842,2849],[\"app\",2831,2850],[\"app\",2829,2851],[\"app\",2852,27],[\"app\",2805,2853],[\"app\",2794,2854],[\"app\",2855,2],[\"app\",2754,2856],[\"let\",[\"str\",[\"anonymous\"],\"hchain\"],2177,2398,2857,true],[\"let\",[\"str\",[\"anonymous\"],\"hlift\"],1981,2008,2858,true],[\"let\",[\"str\",[\"anonymous\"],\"hliftD\"],1868,1957,2859,true],[\"let\",[\"str\",[\"anonymous\"],\"lift\"],1803,1807,2860,false],[\"lam\",[\"str\",[\"anonymous\"],\"hq\"],1440,2861,\"default\"],[\"lam\",[\"str\",[\"anonymous\"],\"q\"],328,2862,\"default\"],[\"app\",1096,328],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Bundle\"],\"TotalSpace\"],[[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",2865,1523],[\"app\",2866,42],[\"app\",2867,1528],[\"app\",2864,2868],[\"app\",2869,427],[\"app\",1235,1523],[\"app\",2871,1525],[\"app\",2872,1527],[\"app\",1247,1523],[\"app\",2874,1525],[\"app\",2875,1527],[\"app\",1259,1523],[\"app\",2877,1525],[\"app\",2878,1527],[\"app\",1271,1523],[\"app\",2880,1525],[\"app\",2881,1527],[\"app\",2882,1197],[\"app\",2883,1116],[\"app\",2884,1279],[\"app\",2879,2885],[\"app\",2876,2886],[\"app\",2873,2887],[\"app\",2870,2888],[\"const\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"Bundle\"],\"TotalSpace\"],\"mk\"],[[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",2890,2022],[\"app\",2891,42],[\"app\",1522,2022],[\"app\",2893,1523],[\"app\",2894,1525],[\"app\",2892,2895],[\"app\",294,2],[\"app\",2896,2897],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"DFunLike\"],\"coe\"],[[\"succ\",[\"zero\"]],[\"succ\",[\"zero\"]],[\"succ\",[\"zero\"]]]],[\"app\",1322,438],[\"app\",2900,328],[\"app\",2901,427],[\"app\",2902,430],[\"app\",2903,2],[\"app\",1464,2904],[\"app\",1669,438],[\"app\",2906,328],[\"app\",2907,427],[\"app\",2908,430],[\"app\",2909,2],[\"app\",2905,2910],[\"app\",996,2904],[\"app\",1681,438],[\"app\",2913,328],[\"app\",2914,427],[\"app\",2915,430],[\"app\",2916,2],[\"app\",2912,2917],[\"app\",2911,2918],[\"app\",2895,2897],[\"app\",2919,2920],[\"app\",1557,2022],[\"app\",2922,1523],[\"app\",2923,1525],[\"app\",2924,2897],[\"app\",2921,2925],[\"app\",996,2920],[\"app\",1569,2022],[\"app\",2928,1523],[\"app\",2929,1525],[\"app\",2930,2897],[\"app\",2927,2931],[\"app\",2926,2932],[\"app\",1707,438],[\"app\",2934,328],[\"app\",2935,427],[\"app\",2936,430],[\"app\",2937,2],[\"app\",2933,2938],[\"app\",1595,2022],[\"app\",2940,1523],[\"app\",2941,1525],[\"app\",2942,2897],[\"app\",2939,2943],[\"app\",2899,2944],[\"app\",2945,2904],[\"app\",1522,2020],[\"app\",2947,2022],[\"app\",2948,1523],[\"app\",292,27],[\"app\",2949,2950],[\"lam\",[\"num\",[\"str\",[\"str\",[\"num\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"x\"],\"_@\"],\"Mathlib\"],\"Data\"],\"FunLike\"],\"Basic\"],2582841819],\"_hygCtx\"],\"_hyg\"],11],2904,2951,\"default\"],[\"app\",2946,2952],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"ContinuousLinearMap\"],\"funLike\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",2954,31],[\"app\",2955,31],[\"app\",2956,1455],[\"app\",2957,1455],[\"app\",2958,1463],[\"app\",2959,2904],[\"app\",2960,2910],[\"app\",2961,2918],[\"app\",2962,2920],[\"app\",2963,2925],[\"app\",2964,2932],[\"app\",2965,2938],[\"app\",2966,2943],[\"app\",2953,2967],[\"app\",1727,438],[\"app\",2969,328],[\"app\",2970,427],[\"app\",2971,430],[\"app\",2972,42],[\"app\",2973,73],[\"app\",2974,112],[\"app\",2975,21],[\"app\",2976,25],[\"app\",2977,118],[\"app\",2978,2022],[\"app\",2979,1523],[\"app\",2980,1525],[\"app\",2981,294],[\"app\",2982,290],[\"app\",2983,2],[\"app\",2968,2984],[\"const\",[\"str\",[\"anonymous\"],\"ContinuousLinearEquiv\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",2986,31],[\"app\",2987,31],[\"app\",2988,1455],[\"app\",2989,1455],[\"app\",2990,1463],[\"app\",2991,1463],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"RingHomInvPair\"],\"ids\"],[[\"zero\"]]],[\"app\",2993,31],[\"app\",2994,1455],[\"app\",2992,2995],[\"app\",2996,2995],[\"app\",2997,328],[\"app\",2998,351],[\"app\",2999,1210],[\"app\",3000,2904],[\"app\",3001,2910],[\"app\",3002,2918],[\"app\",916,328],[\"app\",3004,84],[\"app\",3005,348],[\"app\",3006,341],[\"app\",3003,3007],[\"app\",3008,2938],[\"app\",2899,3009],[\"app\",3010,328],[\"app\",1322,488],[\"app\",3012,328],[\"app\",3013,427],[\"app\",3014,430],[\"app\",3015,27],[\"lam\",[\"num\",[\"str\",[\"str\",[\"num\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"x\"],\"_@\"],\"Mathlib\"],\"Data\"],\"FunLike\"],\"Basic\"],2582841819],\"_hygCtx\"],\"_hyg\"],11],328,3016,\"default\"],[\"app\",3011,3017],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"EquivLike\"],\"toFunLike\"],[[\"succ\",[\"zero\"]],[\"succ\",[\"zero\"]],[\"succ\",[\"zero\"]]]],[\"app\",3019,3009],[\"app\",3020,328],[\"app\",3021,2904],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"ContinuousLinearEquiv\"],\"equivLike\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",3023,31],[\"app\",3024,31],[\"app\",3025,1455],[\"app\",3026,1455],[\"app\",3027,1463],[\"app\",3028,1463],[\"app\",3029,2995],[\"app\",3030,2995],[\"app\",3031,328],[\"app\",3032,351],[\"app\",3033,1210],[\"app\",3034,2904],[\"app\",3035,2910],[\"app\",3036,2918],[\"app\",3037,3007],[\"app\",3038,2938],[\"app\",3022,3039],[\"app\",3018,3040],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"ContinuousLinearEquiv\"],\"symm\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",3042,31],[\"app\",3043,31],[\"app\",3044,1455],[\"app\",3045,1455],[\"app\",3046,1463],[\"app\",3047,1463],[\"app\",3048,2995],[\"app\",3049,2995],[\"app\",3050,2904],[\"app\",3051,2910],[\"app\",3052,2918],[\"app\",3053,328],[\"app\",3054,351],[\"app\",3055,1210],[\"app\",3056,2938],[\"app\",3057,3007],[\"const\",[\"str\",[\"anonymous\"],\"tangentSpaceCastModel\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",3059,31],[\"app\",3060,36],[\"app\",3061,328],[\"app\",3062,332],[\"app\",3063,341],[\"app\",3064,328],[\"app\",3065,351],[\"app\",3066,438],[\"app\",3067,328],[\"app\",3068,427],[\"app\",3069,430],[\"app\",3070,2],[\"app\",3058,3071],[\"app\",3041,3072],[\"app\",6,31],[\"app\",3074,1903],[\"app\",1905,31],[\"app\",3076,1018],[\"app\",3075,3077],[\"app\",1804,3078],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"EuclideanSpace\"],\"single\"],[[\"zero\"],[\"zero\"]]],[\"app\",3080,156],[\"app\",3081,31],[\"app\",3082,104],[\"const\",[\"str\",[\"anonymous\"],\"instDecidableEqFin\"],[]],[\"app\",3084,19],[\"app\",3083,3085],[\"app\",3086,27],[\"app\",3074,203],[\"app\",1370,31],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Real\"],\"instOne\"],[]],[\"app\",3089,3090],[\"app\",3088,3091],[\"app\",3087,3092],[\"app\",3079,3093],[\"app\",3073,3094],[\"app\",2985,3095],[\"app\",2898,3096],[\"lam\",[\"str\",[\"anonymous\"],\"q\"],328,3097,\"default\"],[\"app\",2889,3098],[\"app\",3099,292],[\"forall\",[\"str\",[\"anonymous\"],\"k\"],156,3100,\"default\"],[\"app\",1104,438],[\"app\",3102,328],[\"app\",3103,427],[\"app\",3104,430],[\"forall\",[\"num\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"a\"],\"_@\"],\"_internal\"],\"_hyg\"],0],328,3105,\"default\"],[\"const\",[\"str\",[\"anonymous\"],\"Homeomorph\"],[[\"zero\"],[\"zero\"]]],[\"app\",200,328],[\"app\",3108,328],[\"app\",3107,3109],[\"app\",3103,351],[\"app\",3111,430],[\"app\",3110,3112],[\"app\",211,328],[\"app\",3114,351],[\"app\",3115,328],[\"app\",3116,351],[\"app\",3113,3117],[\"app\",1129,438],[\"app\",3119,328],[\"app\",3120,351],[\"app\",3121,430],[\"app\",1241,328],[\"app\",3123,332],[\"app\",3124,341],[\"app\",3125,328],[\"app\",3126,351],[\"app\",3127,438],[\"app\",3128,328],[\"app\",3129,351],[\"app\",3130,430],[\"app\",1253,328],[\"app\",3132,332],[\"app\",3133,341],[\"app\",3134,328],[\"app\",3135,351],[\"app\",3136,438],[\"app\",3137,328],[\"app\",3138,351],[\"app\",3139,430],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"IsManifold\"],\"instOfTopWithTopENat\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",3141,31],[\"app\",3142,36],[\"app\",3143,328],[\"app\",3144,332],[\"app\",3145,341],[\"app\",3146,328],[\"app\",3147,351],[\"app\",3148,438],[\"app\",3149,328],[\"app\",3150,351],[\"app\",3151,430],[\"app\",3152,1197],[\"const\",[\"str\",[\"anonymous\"],\"instIsManifoldModelSpace\"],[[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",3154,31],[\"app\",3155,36],[\"app\",3156,328],[\"app\",3157,332],[\"app\",3158,341],[\"app\",3159,328],[\"app\",3160,351],[\"app\",3161,438],[\"app\",3162,1400],[\"app\",3153,3163],[\"app\",3140,3164],[\"app\",3131,3165],[\"app\",3122,3166],[\"app\",3118,3167],[\"app\",2899,3168],[\"app\",3169,3109],[\"app\",1104,488],[\"app\",3171,328],[\"app\",3172,351],[\"app\",3173,430],[\"lam\",[\"num\",[\"str\",[\"str\",[\"num\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"x\"],\"_@\"],\"Mathlib\"],\"Data\"],\"FunLike\"],\"Basic\"],2582841819],\"_hygCtx\"],\"_hyg\"],11],3109,3174,\"default\"],[\"app\",3170,3175],[\"app\",3019,3168],[\"app\",3177,3109],[\"app\",3178,3112],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Homeomorph\"],\"instEquivLike\"],[[\"zero\"],[\"zero\"]]],[\"app\",3180,3109],[\"app\",3181,3112],[\"app\",3182,3117],[\"app\",3183,3167],[\"app\",3179,3184],[\"app\",3176,3185],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Homeomorph\"],\"symm\"],[[\"zero\"],[\"zero\"]]],[\"app\",3187,3112],[\"app\",3188,3109],[\"app\",3189,3167],[\"app\",3190,3117],[\"const\",[\"str\",[\"anonymous\"],\"tangentBundleModelSpaceHomeomorph\"],[[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",3192,31],[\"app\",3193,36],[\"app\",3194,328],[\"app\",3195,332],[\"app\",3196,341],[\"app\",3197,328],[\"app\",3198,351],[\"app\",3199,438],[\"app\",3191,3200],[\"app\",3186,3201],[\"app\",378,328],[\"app\",3203,328],[\"app\",3204,2],[\"app\",3205,3094],[\"app\",3202,3206],[\"lam\",[\"str\",[\"anonymous\"],\"q\"],328,3207,\"default\"],[\"const\",[\"str\",[\"anonymous\"],\"Continuous\"],[[\"zero\"],[\"zero\"]]],[\"app\",3209,328],[\"app\",3210,3105],[\"app\",3211,427],[\"app\",3120,427],[\"app\",3213,430],[\"app\",1141,438],[\"app\",3215,328],[\"app\",3216,427],[\"app\",3217,430],[\"app\",1153,438],[\"app\",3219,328],[\"app\",3220,427],[\"app\",3221,430],[\"app\",1165,438],[\"app\",3223,328],[\"app\",3224,427],[\"app\",3225,430],[\"app\",1177,438],[\"app\",3227,1198],[\"app\",3228,328],[\"app\",3229,1213],[\"app\",3230,427],[\"app\",3231,430],[\"app\",3232,1223],[\"app\",3226,3233],[\"app\",3222,3234],[\"app\",3218,3235],[\"app\",3214,3236],[\"app\",3212,3237],[\"app\",3238,2],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Continuous\"],\"comp\"],[[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",3240,328],[\"app\",3241,3109],[\"app\",3242,3112],[\"app\",3243,427],[\"app\",3244,3117],[\"app\",3245,3167],[\"app\",3086,129],[\"app\",3247,3092],[\"app\",3079,3248],[\"app\",3205,3249],[\"lam\",[\"str\",[\"anonymous\"],\"q\"],328,3250,\"default\"],[\"app\",3246,3251],[\"app\",3252,3202],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Homeomorph\"],\"continuous\"],[[\"zero\"],[\"zero\"]]],[\"app\",3254,3109],[\"app\",3255,3112],[\"app\",3256,3117],[\"app\",3257,3167],[\"app\",3258,3201],[\"app\",3253,3259],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Continuous\"],\"prodMk\"],[[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",3261,328],[\"app\",3262,328],[\"app\",3263,328],[\"app\",3264,427],[\"app\",3265,351],[\"app\",3266,427],[\"const\",[\"str\",[\"anonymous\"],\"id\"],[[\"succ\",[\"zero\"]]]],[\"app\",3268,328],[\"app\",3267,3269],[\"lam\",[\"str\",[\"anonymous\"],\"q\"],328,3249,\"default\"],[\"app\",3270,3271],[\"const\",[\"str\",[\"anonymous\"],\"continuous_id\"],[[\"zero\"]]],[\"app\",3273,328],[\"app\",3274,427],[\"app\",3272,3275],[\"const\",[\"str\",[\"anonymous\"],\"continuous_const\"],[[\"zero\"],[\"zero\"]]],[\"app\",3277,328],[\"app\",3278,328],[\"app\",3279,427],[\"app\",3280,351],[\"app\",3281,3094],[\"app\",3276,3282],[\"app\",3260,3283],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"ContinuousOn\"],\"comp\"],[[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",3285,328],[\"app\",3172,427],[\"app\",3287,430],[\"app\",3286,3288],[\"app\",1115,2020],[\"app\",3290,2022],[\"app\",3291,1523],[\"app\",3289,3292],[\"app\",3293,427],[\"app\",1129,488],[\"app\",3295,328],[\"app\",3296,427],[\"app\",3297,430],[\"app\",1141,488],[\"app\",3299,328],[\"app\",3300,427],[\"app\",3301,430],[\"app\",1153,488],[\"app\",3303,328],[\"app\",3304,427],[\"app\",3305,430],[\"app\",1165,488],[\"app\",3307,328],[\"app\",3308,427],[\"app\",3309,430],[\"app\",1177,488],[\"app\",3311,1198],[\"app\",3312,328],[\"app\",3313,1213],[\"app\",3314,427],[\"app\",3315,430],[\"app\",3316,1223],[\"app\",3310,3317],[\"app\",3306,3318],[\"app\",3302,3319],[\"app\",3298,3320],[\"app\",3294,3321],[\"app\",1235,2020],[\"app\",3323,2022],[\"app\",3324,1523],[\"app\",1247,2020],[\"app\",3326,2022],[\"app\",3327,1523],[\"app\",1259,2020],[\"app\",3329,2022],[\"app\",3330,1523],[\"app\",1271,2020],[\"app\",3332,2022],[\"app\",3333,1523],[\"app\",3334,1197],[\"app\",3335,1525],[\"app\",3336,1279],[\"app\",3331,3337],[\"app\",3328,3338],[\"app\",3325,3339],[\"app\",3322,3340],[\"app\",3341,27],[\"app\",3342,438],[\"app\",1292,488],[\"app\",3344,328],[\"app\",3345,427],[\"app\",3346,430],[\"app\",3347,42],[\"app\",3348,73],[\"app\",3349,112],[\"app\",3350,21],[\"app\",3351,25],[\"app\",3352,118],[\"app\",3353,2020],[\"app\",3354,2022],[\"app\",3355,1523],[\"app\",3356,292],[\"app\",3357,438],[\"app\",3343,3358],[\"app\",1309,3288],[\"app\",3360,328],[\"app\",1314,3015],[\"app\",3361,3362],[\"app\",3363,438],[\"app\",3359,3364],[\"app\",3365,252],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Continuous\"],\"continuousOn\"],[[\"zero\"],[\"zero\"]]],[\"app\",3367,328],[\"app\",3368,3288],[\"app\",3369,427],[\"app\",3370,3321],[\"app\",3371,27],[\"app\",3372,438],[\"app\",3373,2],[\"app\",3366,3374],[\"app\",679,488],[\"app\",3376,2],[\"lam\",[\"str\",[\"anonymous\"],\"hq\"],3377,2,\"default\"],[\"lam\",[\"str\",[\"anonymous\"],\"q\"],328,3378,\"default\"],[\"app\",3375,3379],[\"let\",[\"str\",[\"anonymous\"],\"hins\"],3239,3284,3380,true],[\"let\",[\"str\",[\"anonymous\"],\"ins\"],3106,3208,3381,false],[\"lam\",[\"str\",[\"anonymous\"],\"k\"],156,3382,\"default\"],[\"app\",2864,31],[\"app\",3384,427],[\"app\",3385,261],[\"const\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"SeifertSurfaces\"],\"MetricFoundations\"],\"coordinateGram\"],[[\"zero\"],[\"zero\"]]],[\"app\",3387,2018],[\"app\",3388,2020],[\"app\",3389,2022],[\"app\",3390,1523],[\"app\",3391,1525],[\"app\",3392,1527],[\"app\",379,2149],[\"app\",3394,1757],[\"app\",3395,2],[\"app\",1527,3396],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2065,3397,\"default\"],[\"app\",3393,3398],[\"app\",3399,787],[\"app\",3400,399],[\"app\",3401,129],[\"app\",3402,27],[\"lam\",[\"str\",[\"anonymous\"],\"q\"],328,3403,\"default\"],[\"app\",3386,3404],[\"app\",3405,438],[\"forall\",[\"str\",[\"anonymous\"],\"j\"],156,3406,\"default\"],[\"forall\",[\"str\",[\"anonymous\"],\"i\"],156,3407,\"default\"],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"ContinuousOn\"],\"congr\"],[[\"zero\"],[\"zero\"]]],[\"app\",3409,328],[\"app\",3410,31],[\"app\",3411,427],[\"app\",3412,261],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Inner\"],\"inner\"],[[\"zero\"],[\"zero\"]]],[\"app\",3414,31],[\"app\",290,2],[\"app\",2023,3416],[\"app\",3415,3417],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"InnerProductSpace\"],\"toInner\"],[[\"zero\"],[\"zero\"]]],[\"app\",3419,31],[\"app\",3420,3417],[\"app\",3421,104],[\"app\",179,3417],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Bundle\"],\"instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal\"],[[\"zero\"],[\"zero\"]]],[\"app\",3424,2018],[\"app\",3425,2023],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Real\"],\"normedField\"],[]],[\"app\",81,3427],[\"app\",3428,99],[\"app\",3429,111],[\"app\",1553,3430],[\"app\",3431,21],[\"app\",3432,25],[\"app\",3433,118],[\"app\",3434,2018],[\"app\",3435,2020],[\"app\",3436,2022],[\"app\",3426,3437],[\"app\",1565,3430],[\"app\",3439,21],[\"app\",3440,25],[\"app\",3441,118],[\"app\",3442,2018],[\"app\",3443,2020],[\"app\",3444,2022],[\"app\",3438,3445],[\"app\",1591,3430],[\"app\",3447,21],[\"app\",3448,25],[\"app\",3449,118],[\"app\",3450,2018],[\"app\",3451,2020],[\"app\",3452,2022],[\"app\",3446,3453],[\"const\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"Bundle\"],\"RiemannianBundle\"],\"mk\"],[[\"zero\"],[\"zero\"]]],[\"app\",3455,2018],[\"app\",2412,2],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2018,3457,\"default\"],[\"app\",3456,3458],[\"app\",3459,3437],[\"app\",3460,3445],[\"app\",3461,3453],[\"const\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"Bundle\"],\"ContMDiffRiemannianMetric\"],\"toRiemannianMetric\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",3463,42],[\"app\",3464,73],[\"app\",3465,112],[\"const\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"SeifertSurfaces\"],\"MetricFoundations\"],\"SmoothMetric\"],\"_proof_1\"],[]],[\"app\",14,3467],[\"app\",3466,3468],[\"app\",24,3467],[\"app\",3469,3470],[\"app\",117,3467],[\"app\",3471,3472],[\"app\",3473,127],[\"app\",3474,2018],[\"app\",3475,2020],[\"app\",3476,2022],[\"app\",326,13],[\"app\",3477,3478],[\"app\",3479,73],[\"app\",3480,3430],[\"app\",1519,3468],[\"app\",3482,3470],[\"app\",3483,3472],[\"app\",3484,2409],[\"app\",3485,2018],[\"app\",3486,2020],[\"app\",3487,2],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2018,3488,\"default\"],[\"app\",3481,3489],[\"app\",1124,3478],[\"app\",3491,73],[\"app\",3492,112],[\"app\",3493,3468],[\"app\",3494,3470],[\"app\",3495,3472],[\"app\",3496,2018],[\"app\",3497,2020],[\"app\",3498,2022],[\"const\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"SeifertSurfaces\"],\"MetricFoundations\"],\"SmoothMetric\"],\"_proof_2\"],[[\"zero\"]]],[\"app\",3500,2018],[\"app\",3501,2020],[\"app\",3502,2022],[\"app\",3503,1523],[\"app\",3499,3504],[\"app\",3490,3505],[\"app\",3431,3468],[\"app\",3507,3470],[\"app\",3508,3472],[\"app\",3509,2018],[\"app\",3510,2020],[\"app\",3511,2022],[\"app\",3506,3512],[\"app\",3439,3468],[\"app\",3514,3470],[\"app\",3515,3472],[\"app\",3516,2018],[\"app\",3517,2020],[\"app\",3518,2022],[\"app\",3513,3519],[\"app\",3447,3468],[\"app\",3521,3470],[\"app\",3522,3472],[\"app\",3523,2018],[\"app\",3524,2020],[\"app\",3525,2022],[\"app\",3520,3526],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"TangentSpace\"],\"fiberBundle\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",3528,31],[\"app\",3529,36],[\"app\",3530,3478],[\"app\",3531,73],[\"app\",3532,112],[\"app\",3533,3468],[\"app\",3534,3470],[\"app\",3535,3472],[\"app\",3536,2018],[\"app\",3537,2020],[\"app\",3538,2022],[\"app\",3539,3504],[\"app\",3527,3540],[\"const\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"SeifertSurfaces\"],\"MetricFoundations\"],\"SmoothMetric\"],\"_proof_3\"],[[\"zero\"]]],[\"app\",3542,2018],[\"app\",3543,2020],[\"app\",3544,2022],[\"app\",3545,1523],[\"app\",3541,3546],[\"app\",3547,1525],[\"app\",3462,3548],[\"app\",3454,3549],[\"const\",[\"str\",[\"anonymous\"],\"instIsTopologicalAddGroupTangentSpace\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",3551,31],[\"app\",3552,36],[\"app\",3553,42],[\"app\",3554,73],[\"app\",3555,3430],[\"app\",3556,21],[\"app\",3557,25],[\"app\",3558,118],[\"app\",3559,2018],[\"app\",3560,2020],[\"app\",3561,2022],[\"app\",3550,3562],[\"const\",[\"str\",[\"anonymous\"],\"instContinuousConstSMulTangentSpace\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",3564,31],[\"app\",3565,36],[\"app\",3566,42],[\"app\",3567,73],[\"app\",3568,3430],[\"app\",3569,21],[\"app\",3570,25],[\"app\",3571,118],[\"app\",3572,2018],[\"app\",3573,2020],[\"app\",3574,2022],[\"app\",3563,3575],[\"app\",3576,3416],[\"app\",3423,3577],[\"app\",3422,3578],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Bundle\"],\"instInnerProductSpaceReal\"],[[\"zero\"],[\"zero\"]]],[\"app\",3580,2018],[\"app\",3581,2023],[\"app\",3582,3437],[\"app\",3583,3445],[\"app\",3584,3453],[\"app\",3585,3549],[\"app\",3586,3562],[\"app\",3587,3575],[\"app\",3588,3416],[\"app\",3579,3589],[\"app\",3418,3590],[\"app\",2086,2],[\"app\",1464,3592],[\"app\",2093,2],[\"app\",3593,3594],[\"app\",996,3592],[\"app\",2100,2],[\"app\",3596,3597],[\"app\",3595,3598],[\"app\",3599,3417],[\"app\",2034,3416],[\"app\",3600,3601],[\"app\",996,3417],[\"app\",2040,3416],[\"app\",3603,3604],[\"app\",3602,3605],[\"app\",2117,2],[\"app\",3606,3607],[\"app\",2048,3416],[\"app\",3608,3609],[\"app\",2899,3610],[\"app\",3611,3592],[\"app\",438,27],[\"app\",2412,3613],[\"lam\",[\"num\",[\"str\",[\"str\",[\"num\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"x\"],\"_@\"],\"Mathlib\"],\"Data\"],\"FunLike\"],\"Basic\"],2582841819],\"_hygCtx\"],\"_hyg\"],11],3592,3614,\"default\"],[\"app\",3612,3615],[\"app\",2959,3592],[\"app\",3617,3594],[\"app\",3618,3598],[\"app\",3619,3417],[\"app\",3620,3601],[\"app\",3621,3605],[\"app\",3622,3607],[\"app\",3623,3609],[\"app\",3616,3624],[\"app\",2139,488],[\"app\",3626,2],[\"app\",3625,3627],[\"app\",3000,3592],[\"app\",3629,3594],[\"app\",3630,3598],[\"app\",3631,3007],[\"app\",3632,3607],[\"app\",2899,3633],[\"app\",3634,328],[\"app\",2452,27],[\"lam\",[\"num\",[\"str\",[\"str\",[\"num\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"x\"],\"_@\"],\"Mathlib\"],\"Data\"],\"FunLike\"],\"Basic\"],2582841819],\"_hygCtx\"],\"_hyg\"],11],328,3636,\"default\"],[\"app\",3635,3637],[\"app\",3019,3633],[\"app\",3639,328],[\"app\",3640,3592],[\"app\",3034,3592],[\"app\",3642,3594],[\"app\",3643,3598],[\"app\",3644,3007],[\"app\",3645,3607],[\"app\",3641,3646],[\"app\",3638,3647],[\"app\",3050,3592],[\"app\",3649,3594],[\"app\",3650,3598],[\"app\",3651,328],[\"app\",3652,351],[\"app\",3653,1210],[\"app\",3654,3607],[\"app\",3655,3007],[\"app\",3066,698],[\"app\",3657,328],[\"app\",3658,427],[\"app\",3659,430],[\"app\",3660,2],[\"app\",3656,3661],[\"app\",3648,3662],[\"app\",3663,3249],[\"app\",3628,3664],[\"app\",3591,3665],[\"app\",3663,3094],[\"app\",3628,3667],[\"app\",3666,3668],[\"lam\",[\"str\",[\"anonymous\"],\"b\"],328,3669,\"default\"],[\"app\",3413,3670],[\"app\",3671,3404],[\"app\",3672,438],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"ContinuousOn\"],\"inner_bundle\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",3674,2020],[\"app\",3675,2022],[\"app\",3676,42],[\"app\",3677,73],[\"app\",3678,3430],[\"app\",3679,2949],[\"app\",3680,3340],[\"app\",3576,2],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2020,3682,\"default\"],[\"app\",3681,3683],[\"app\",3580,2020],[\"app\",3685,2949],[\"app\",3434,2020],[\"app\",3687,2022],[\"app\",3688,1523],[\"app\",3686,3689],[\"app\",3442,2020],[\"app\",3691,2022],[\"app\",3692,1523],[\"app\",3690,3693],[\"app\",3450,2020],[\"app\",3695,2022],[\"app\",3696,1523],[\"app\",3694,3697],[\"app\",3455,2020],[\"app\",2023,2],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2020,3700,\"default\"],[\"app\",3699,3701],[\"app\",3702,3689],[\"app\",3703,3693],[\"app\",3704,3697],[\"app\",3474,2020],[\"app\",3706,2022],[\"app\",3707,1523],[\"app\",3708,3478],[\"app\",3709,73],[\"app\",3710,3430],[\"app\",3484,2018],[\"app\",3712,2020],[\"app\",3713,2022],[\"app\",3714,2],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2020,3715,\"default\"],[\"app\",3711,3716],[\"app\",3496,2020],[\"app\",3718,2022],[\"app\",3719,1523],[\"app\",3500,2020],[\"app\",3721,2022],[\"app\",3722,1523],[\"app\",3723,1525],[\"app\",3720,3724],[\"app\",3717,3725],[\"app\",3509,2020],[\"app\",3727,2022],[\"app\",3728,1523],[\"app\",3726,3729],[\"app\",3516,2020],[\"app\",3731,2022],[\"app\",3732,1523],[\"app\",3730,3733],[\"app\",3523,2020],[\"app\",3735,2022],[\"app\",3736,1523],[\"app\",3734,3737],[\"app\",3536,2020],[\"app\",3739,2022],[\"app\",3740,1523],[\"app\",3741,3724],[\"app\",3738,3742],[\"app\",3542,2020],[\"app\",3744,2022],[\"app\",3745,1523],[\"app\",3746,1525],[\"app\",3743,3747],[\"app\",3748,1527],[\"app\",3705,3749],[\"app\",3698,3750],[\"app\",3559,2020],[\"app\",3752,2022],[\"app\",3753,1523],[\"app\",3751,3754],[\"app\",3572,2020],[\"app\",3756,2022],[\"app\",3757,1523],[\"app\",3755,3758],[\"app\",3684,3759],[\"app\",3530,42],[\"app\",3761,73],[\"app\",3762,112],[\"app\",3763,21],[\"app\",3764,25],[\"app\",3765,118],[\"app\",3766,2020],[\"app\",3767,2022],[\"app\",3768,1523],[\"app\",3769,3339],[\"app\",3760,3770],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"TangentSpace\"],\"vectorBundle\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",3772,31],[\"app\",3773,36],[\"app\",3774,42],[\"app\",3775,73],[\"app\",3776,112],[\"app\",3777,21],[\"app\",3778,25],[\"app\",3779,118],[\"app\",3780,2020],[\"app\",3781,2022],[\"app\",3782,1523],[\"app\",3783,3339],[\"app\",3771,3784],[\"app\",3785,328],[\"app\",3786,427],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"IsContinuousRiemannianBundle\"],\"mk\"],[[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",3788,2020],[\"app\",3789,2022],[\"app\",3790,3478],[\"app\",3791,73],[\"app\",3792,3430],[\"app\",3793,3701],[\"app\",3493,21],[\"app\",3795,25],[\"app\",3796,118],[\"app\",3797,2020],[\"app\",3798,2022],[\"app\",3799,1523],[\"app\",1241,3478],[\"app\",3801,73],[\"app\",3802,112],[\"app\",3803,21],[\"app\",3804,25],[\"app\",3805,118],[\"app\",3806,2020],[\"app\",3807,2022],[\"app\",3808,1523],[\"app\",1253,3478],[\"app\",3810,73],[\"app\",3811,112],[\"app\",3812,21],[\"app\",3813,25],[\"app\",3814,118],[\"app\",3815,2020],[\"app\",3816,2022],[\"app\",3817,1523],[\"app\",1265,3478],[\"app\",3819,73],[\"app\",3820,112],[\"app\",3821,21],[\"app\",3822,25],[\"app\",3823,118],[\"app\",3824,2020],[\"app\",3825,2022],[\"app\",3826,1523],[\"app\",3827,1197],[\"app\",3828,1525],[\"app\",3829,1279],[\"app\",3818,3830],[\"app\",3809,3831],[\"app\",3800,3832],[\"app\",3794,3833],[\"app\",3834,3683],[\"app\",3835,3759],[\"app\",3533,21],[\"app\",3837,25],[\"app\",3838,118],[\"app\",3839,2020],[\"app\",3840,2022],[\"app\",3841,1523],[\"app\",3842,3832],[\"app\",3836,3843],[\"app\",3774,3478],[\"app\",3845,73],[\"app\",3846,112],[\"app\",3847,21],[\"app\",3848,25],[\"app\",3849,118],[\"app\",3850,2020],[\"app\",3851,2022],[\"app\",3852,1523],[\"app\",3853,3832],[\"app\",3844,3854],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Exists\"],\"intro\"],[[\"succ\",[\"zero\"]]]],[\"app\",1443,849],[\"app\",3857,849],[\"app\",3858,1638],[\"app\",3859,3700],[\"app\",213,3700],[\"app\",215,3700],[\"app\",217,3700],[\"app\",179,3700],[\"app\",3864,3682],[\"app\",3863,3865],[\"app\",3862,3866],[\"app\",3861,3867],[\"app\",3860,3868],[\"app\",996,3700],[\"app\",911,3700],[\"app\",3871,3682],[\"app\",3870,3872],[\"app\",3869,3873],[\"app\",3874,31],[\"app\",3875,261],[\"app\",3876,1848],[\"app\",916,3700],[\"app\",3878,3427],[\"app\",3879,3865],[\"app\",102,3700],[\"app\",3881,104],[\"app\",3882,3865],[\"app\",3588,2],[\"app\",3883,3884],[\"app\",3880,3885],[\"app\",3877,3886],[\"app\",3887,855],[\"app\",3874,3888],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"ContinuousLinearMap\"],\"topologicalSpace\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",3890,31],[\"app\",3891,31],[\"app\",3892,3427],[\"app\",3893,3427],[\"app\",3894,1638],[\"app\",3895,3700],[\"app\",3896,31],[\"app\",3897,3872],[\"app\",3898,3886],[\"app\",3899,851],[\"app\",3900,855],[\"app\",3901,3868],[\"app\",3902,261],[\"const\",[\"str\",[\"anonymous\"],\"instIsTopologicalAddGroupReal\"],[]],[\"app\",3903,3904],[\"app\",3889,3905],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"ContinuousLinearMap\"],\"addCommMonoid\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",3907,31],[\"app\",3908,31],[\"app\",3909,849],[\"app\",3910,849],[\"app\",3911,1638],[\"app\",3912,3700],[\"app\",3913,3868],[\"app\",3914,3873],[\"app\",3915,31],[\"app\",3916,261],[\"app\",3917,1848],[\"app\",3918,3886],[\"app\",3919,855],[\"app\",3920,886],[\"app\",3906,3921],[\"app\",3922,3886],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"ContinuousLinearMap\"],\"module\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",3924,31],[\"app\",3925,31],[\"app\",3926,31],[\"app\",3927,849],[\"app\",3928,849],[\"app\",3929,849],[\"app\",3930,3700],[\"app\",3931,3868],[\"app\",3932,3873],[\"app\",3933,3886],[\"app\",3934,31],[\"app\",3935,261],[\"app\",3936,1848],[\"app\",3937,855],[\"app\",3938,855],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Algebra\"],\"to_smulCommClass\"],[[\"zero\"],[\"zero\"]]],[\"app\",3940,31],[\"app\",3941,31],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Real\"],\"instCommSemiring\"],[]],[\"app\",3942,3943],[\"app\",1445,3943],[\"app\",3944,3945],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Algebra\"],\"id\"],[[\"zero\"]]],[\"app\",3947,31],[\"app\",3948,3943],[\"app\",3946,3949],[\"app\",3939,3950],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Real\"],\"instMul\"],[]],[\"app\",890,3952],[\"app\",3953,908],[\"app\",3951,3954],[\"app\",3955,1638],[\"app\",3956,886],[\"app\",3923,3957],[\"forall\",[\"str\",[\"anonymous\"],\"x\"],2020,3958,\"default\"],[\"app\",3856,3959],[\"app\",3209,2018],[\"app\",2865,2018],[\"app\",3859,3478],[\"app\",213,3478],[\"app\",215,3478],[\"app\",217,3478],[\"app\",179,3478],[\"app\",3967,73],[\"app\",3966,3968],[\"app\",3965,3969],[\"app\",3964,3970],[\"app\",3963,3971],[\"app\",996,3478],[\"app\",911,3478],[\"app\",3974,73],[\"app\",3973,3975],[\"app\",3972,3976],[\"app\",3977,31],[\"app\",3978,261],[\"app\",3979,1848],[\"app\",916,3478],[\"app\",3981,3427],[\"app\",3982,3968],[\"app\",3983,3430],[\"app\",3980,3984],[\"app\",3985,855],[\"app\",3977,3986],[\"app\",3895,3478],[\"app\",3988,31],[\"app\",3989,3975],[\"app\",3990,3984],[\"app\",3991,851],[\"app\",3992,855],[\"app\",3993,3971],[\"app\",3994,261],[\"app\",3995,3904],[\"app\",3987,3996],[\"app\",3912,3478],[\"app\",3998,3971],[\"app\",3999,3976],[\"app\",4000,31],[\"app\",4001,261],[\"app\",4002,1848],[\"app\",4003,3984],[\"app\",4004,855],[\"app\",4005,886],[\"app\",3997,4006],[\"app\",4007,3984],[\"app\",3930,3478],[\"app\",4009,3971],[\"app\",4010,3976],[\"app\",4011,3984],[\"app\",4012,31],[\"app\",4013,261],[\"app\",4014,1848],[\"app\",4015,855],[\"app\",4016,855],[\"app\",4017,3950],[\"app\",4018,3954],[\"app\",4019,1638],[\"app\",4020,886],[\"app\",4008,4021],[\"app\",3962,4022],[\"app\",3859,3457],[\"app\",213,3457],[\"app\",215,3457],[\"app\",217,3457],[\"app\",179,3457],[\"app\",3424,2409],[\"app\",4029,2412],[\"app\",3434,2409],[\"app\",4031,2018],[\"app\",4032,2020],[\"app\",4030,4033],[\"app\",3442,2409],[\"app\",4035,2018],[\"app\",4036,2020],[\"app\",4034,4037],[\"app\",3450,2409],[\"app\",4039,2018],[\"app\",4040,2020],[\"app\",4038,4041],[\"app\",3455,2409],[\"app\",2601,2],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2409,4044,\"default\"],[\"app\",4043,4045],[\"app\",4046,4033],[\"app\",4047,4037],[\"app\",4048,4041],[\"app\",3474,2409],[\"app\",4050,2018],[\"app\",4051,2020],[\"app\",4052,3478],[\"app\",4053,73],[\"app\",4054,3430],[\"app\",3484,2598],[\"app\",4056,2409],[\"app\",4057,2018],[\"app\",4058,2],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2409,4059,\"default\"],[\"app\",4055,4060],[\"app\",3496,2409],[\"app\",4062,2018],[\"app\",4063,2020],[\"app\",3500,2409],[\"app\",4065,2018],[\"app\",4066,2020],[\"app\",4067,2022],[\"app\",4064,4068],[\"app\",4061,4069],[\"app\",3509,2409],[\"app\",4071,2018],[\"app\",4072,2020],[\"app\",4070,4073],[\"app\",3516,2409],[\"app\",4075,2018],[\"app\",4076,2020],[\"app\",4074,4077],[\"app\",3523,2409],[\"app\",4079,2018],[\"app\",4080,2020],[\"app\",4078,4081],[\"app\",3536,2409],[\"app\",4083,2018],[\"app\",4084,2020],[\"app\",4085,4068],[\"app\",4082,4086],[\"app\",3542,2409],[\"app\",4088,2018],[\"app\",4089,2020],[\"app\",4090,2022],[\"app\",4087,4091],[\"app\",4092,1523],[\"app\",4049,4093],[\"app\",4042,4094],[\"app\",3559,2409],[\"app\",4096,2018],[\"app\",4097,2020],[\"app\",4095,4098],[\"app\",3572,2409],[\"app\",4100,2018],[\"app\",4101,2020],[\"app\",4099,4102],[\"app\",4103,2],[\"app\",4028,4104],[\"app\",4027,4105],[\"app\",4026,4106],[\"app\",4025,4107],[\"app\",4024,4108],[\"app\",996,3457],[\"app\",911,3457],[\"app\",4111,4104],[\"app\",4110,4112],[\"app\",4109,4113],[\"app\",4114,31],[\"app\",4115,261],[\"app\",4116,1848],[\"app\",916,3457],[\"app\",4118,3427],[\"app\",4119,4105],[\"app\",102,3457],[\"app\",4121,104],[\"app\",4122,4105],[\"app\",3580,2409],[\"app\",4124,2412],[\"app\",4125,4033],[\"app\",4126,4037],[\"app\",4127,4041],[\"app\",4128,4094],[\"app\",4129,4098],[\"app\",4130,4102],[\"app\",4131,2],[\"app\",4123,4132],[\"app\",4120,4133],[\"app\",4117,4134],[\"app\",4135,855],[\"app\",4114,4136],[\"app\",3895,3457],[\"app\",4138,31],[\"app\",4139,4112],[\"app\",4140,4134],[\"app\",4141,851],[\"app\",4142,855],[\"app\",4143,4108],[\"app\",4144,261],[\"app\",4145,3904],[\"app\",4137,4146],[\"app\",3912,3457],[\"app\",4148,4108],[\"app\",4149,4113],[\"app\",4150,31],[\"app\",4151,261],[\"app\",4152,1848],[\"app\",4153,4134],[\"app\",4154,855],[\"app\",4155,886],[\"app\",4147,4156],[\"app\",4157,4134],[\"app\",3930,3457],[\"app\",4159,4108],[\"app\",4160,4113],[\"app\",4161,4134],[\"app\",4162,31],[\"app\",4163,261],[\"app\",4164,1848],[\"app\",4165,855],[\"app\",4166,855],[\"app\",4167,3950],[\"app\",4168,3954],[\"app\",4169,1638],[\"app\",4170,886],[\"app\",4158,4171],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2018,4172,\"default\"],[\"app\",4023,4173],[\"app\",3961,4174],[\"app\",4175,2020],[\"const\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"Bundle\"],\"ContinuousLinearMap\"],\"topologicalSpaceTotalSpace\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",4177,31],[\"app\",4178,36],[\"app\",4179,31],[\"app\",4180,36],[\"app\",4181,1638],[\"app\",4182,2018],[\"app\",4183,3478],[\"app\",4184,73],[\"app\",4185,3430],[\"app\",4186,3458],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2018,4112,\"default\"],[\"app\",4187,4188],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2018,4134,\"default\"],[\"app\",4189,4190],[\"app\",3797,2018],[\"app\",4192,2020],[\"app\",4193,2022],[\"app\",3806,2018],[\"app\",4195,2020],[\"app\",4196,2022],[\"app\",3815,2018],[\"app\",4198,2020],[\"app\",4199,2022],[\"app\",3824,2018],[\"app\",4201,2020],[\"app\",4202,2022],[\"app\",4203,1197],[\"app\",4204,1523],[\"app\",4205,1279],[\"app\",4200,4206],[\"app\",4197,4207],[\"app\",4194,4208],[\"app\",4191,4209],[\"app\",4210,3986],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"ContinuousLinearMap\"],\"toNormedAddCommGroup\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",4212,31],[\"app\",4213,31],[\"app\",4214,3478],[\"app\",4215,31],[\"app\",4216,73],[\"app\",4217,71],[\"app\",4218,36],[\"app\",4219,36],[\"app\",4220,3430],[\"app\",4221,187],[\"app\",4222,1638],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"RingHomIsometric\"],\"ids\"],[[\"zero\"]]],[\"app\",4224,31],[\"app\",4225,1046],[\"app\",4223,4226],[\"app\",4211,4227],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"ContinuousLinearMap\"],\"toNormedSpace\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",4229,31],[\"app\",4230,31],[\"app\",4231,3478],[\"app\",4232,31],[\"app\",4233,3968],[\"app\",4234,98],[\"app\",4235,36],[\"app\",4236,36],[\"app\",4237,3430],[\"app\",4238,110],[\"app\",4239,1638],[\"app\",4240,4226],[\"app\",4241,31],[\"app\",4242,84],[\"app\",4243,110],[\"app\",4244,3950],[\"app\",4228,4245],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2018,4136,\"default\"],[\"app\",4246,4247],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"ContinuousLinearMap\"],\"addCommGroup\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",4249,31],[\"app\",4250,1828],[\"app\",4251,31],[\"app\",4252,1828],[\"app\",4253,3457],[\"app\",4254,4108],[\"app\",4255,4112],[\"app\",4256,31],[\"app\",4257,261],[\"app\",4258,851],[\"app\",4259,4134],[\"app\",4260,855],[\"app\",4261,1638],[\"app\",4262,3904],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2018,4263,\"default\"],[\"app\",4248,4264],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2018,4171,\"default\"],[\"app\",4265,4266],[\"app\",4210,31],[\"app\",4268,71],[\"app\",4269,187],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2018,31,\"default\"],[\"app\",4270,4271],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2018,851,\"default\"],[\"app\",4272,4273],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2018,855,\"default\"],[\"app\",4274,4275],[\"const\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"Bundle\"],\"Trivial\"],\"topologicalSpace\"],[[\"zero\"],[\"zero\"]]],[\"app\",4277,2018],[\"app\",4278,31],[\"app\",4279,2020],[\"app\",4280,261],[\"app\",4276,4281],[\"app\",4282,2020],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2018,4108,\"default\"],[\"app\",4283,4284],[\"app\",3839,2018],[\"app\",4286,2020],[\"app\",4287,2022],[\"app\",4288,4208],[\"app\",4285,4289],[\"app\",3850,2018],[\"app\",4291,2020],[\"app\",4292,2022],[\"app\",4293,4208],[\"app\",4290,4294],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2018,261,\"default\"],[\"app\",4295,4296],[\"const\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"Bundle\"],\"Trivial\"],\"fiberBundle\"],[[\"zero\"],[\"zero\"]]],[\"app\",4298,2018],[\"app\",4299,31],[\"app\",4300,2020],[\"app\",4301,221],[\"app\",4297,4302],[\"const\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"Bundle\"],\"Trivial\"],\"vectorBundle\"],[[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",4304,31],[\"app\",4305,2018],[\"app\",4306,31],[\"app\",4307,36],[\"app\",4308,71],[\"app\",4309,187],[\"app\",4310,2020],[\"app\",4303,4311],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2018,3904,\"default\"],[\"app\",4312,4313],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"PolynormableSpace\"],\"continuousSMul\"],[[\"zero\"],[\"zero\"]]],[\"app\",4315,31],[\"app\",4316,31],[\"app\",4317,3427],[\"app\",4318,851],[\"app\",1451,3427],[\"app\",1449,4320],[\"app\",1447,4321],[\"app\",1445,4322],[\"app\",854,4323],[\"app\",4319,4324],[\"app\",4325,261],[\"const\",[\"str\",[\"anonymous\"],\"instPolynormableSpace\"],[[\"zero\"],[\"zero\"]]],[\"app\",4327,31],[\"app\",4328,31],[\"app\",4329,3427],[\"app\",4330,98],[\"app\",4331,110],[\"app\",4326,4332],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2018,4333,\"default\"],[\"app\",4314,4334],[\"app\",4335,4226],[\"app\",4267,4336],[\"app\",4337,2020],[\"app\",4338,4284],[\"app\",4339,4289],[\"app\",4340,4294],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2018,4146,\"default\"],[\"app\",4341,4342],[\"const\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"Bundle\"],\"ContinuousLinearMap\"],\"fiberBundle\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",4344,31],[\"app\",4345,36],[\"app\",4346,31],[\"app\",4347,36],[\"app\",4348,1638],[\"app\",4349,2018],[\"app\",4350,3478],[\"app\",4351,73],[\"app\",4352,3430],[\"app\",4353,3458],[\"app\",4354,4188],[\"app\",4355,4190],[\"app\",4356,4209],[\"app\",4357,31],[\"app\",4358,71],[\"app\",4359,187],[\"app\",4360,4271],[\"app\",4361,4273],[\"app\",4362,4275],[\"app\",4363,4281],[\"app\",4364,2020],[\"app\",4365,4284],[\"app\",4366,4289],[\"app\",4367,4294],[\"app\",4368,4296],[\"app\",4369,4302],[\"app\",4370,4311],[\"app\",4371,4313],[\"app\",4372,4334],[\"app\",4373,4226],[\"app\",4343,4374],[\"const\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"Bundle\"],\"ContinuousLinearMap\"],\"vectorBundle\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",4376,31],[\"app\",4377,36],[\"app\",4378,31],[\"app\",4379,36],[\"app\",4380,1638],[\"app\",4381,2018],[\"app\",4382,3478],[\"app\",4383,73],[\"app\",4384,3430],[\"app\",4385,3458],[\"app\",4386,4188],[\"app\",4387,4190],[\"app\",4388,4209],[\"app\",4389,31],[\"app\",4390,71],[\"app\",4391,187],[\"app\",4392,4271],[\"app\",4393,4273],[\"app\",4394,4275],[\"app\",4395,4281],[\"app\",4396,2020],[\"app\",4397,4284],[\"app\",4398,4289],[\"app\",4399,4294],[\"app\",4400,4296],[\"app\",4401,4302],[\"app\",4402,4311],[\"app\",4403,4313],[\"app\",4404,4334],[\"app\",4405,4226],[\"app\",4375,4406],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"ContinuousLinearMap\"],\"isTopologicalAddGroup\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",4408,31],[\"app\",4409,31],[\"app\",4410,3427],[\"app\",4411,3427],[\"app\",4412,1638],[\"app\",4413,3457],[\"app\",4414,31],[\"app\",4415,4112],[\"app\",4416,4134],[\"app\",4417,851],[\"app\",4418,855],[\"app\",4419,4108],[\"app\",4420,261],[\"app\",4421,3904],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2018,4422,\"default\"],[\"app\",4407,4423],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"ContinuousLinearMap\"],\"continuousSMul\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",4425,31],[\"app\",4426,31],[\"app\",4427,3427],[\"app\",4428,3427],[\"app\",4429,1638],[\"app\",4430,3457],[\"app\",4431,31],[\"app\",4432,4112],[\"app\",4433,4134],[\"app\",4434,851],[\"app\",4435,855],[\"app\",4436,4108],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"RingHomSurjective\"],\"ids\"],[[\"zero\"]]],[\"app\",4438,31],[\"app\",4439,4323],[\"app\",4437,4440],[\"app\",4441,4226],[\"app\",4442,261],[\"app\",4443,3904],[\"app\",4444,4333],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2018,4445,\"default\"],[\"app\",4424,4446],[\"app\",4447,4226],[\"app\",4176,4448],[\"const\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"Bundle\"],\"TotalSpace\"],\"mk'\"],[[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",4450,2409],[\"app\",3859,4044],[\"app\",213,4044],[\"app\",215,4044],[\"app\",217,4044],[\"app\",179,4044],[\"app\",3424,2598],[\"app\",4457,2601],[\"app\",3434,2598],[\"app\",4459,2409],[\"app\",4460,2018],[\"app\",4458,4461],[\"app\",3442,2598],[\"app\",4463,2409],[\"app\",4464,2018],[\"app\",4462,4465],[\"app\",3450,2598],[\"app\",4467,2409],[\"app\",4468,2018],[\"app\",4466,4469],[\"app\",3455,2598],[\"bvar\",27],[\"app\",1522,4472],[\"app\",4473,2598],[\"app\",4474,2409],[\"app\",4475,2],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2598,4476,\"default\"],[\"app\",4471,4477],[\"app\",4478,4461],[\"app\",4479,4465],[\"app\",4480,4469],[\"app\",3474,2598],[\"app\",4482,2409],[\"app\",4483,2018],[\"app\",4484,3478],[\"app\",4485,73],[\"app\",4486,3430],[\"app\",3484,4472],[\"app\",4488,2598],[\"app\",4489,2409],[\"app\",4490,2],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2598,4491,\"default\"],[\"app\",4487,4492],[\"app\",3496,2598],[\"app\",4494,2409],[\"app\",4495,2018],[\"app\",3500,2598],[\"app\",4497,2409],[\"app\",4498,2018],[\"app\",4499,2020],[\"app\",4496,4500],[\"app\",4493,4501],[\"app\",3509,2598],[\"app\",4503,2409],[\"app\",4504,2018],[\"app\",4502,4505],[\"app\",3516,2598],[\"app\",4507,2409],[\"app\",4508,2018],[\"app\",4506,4509],[\"app\",3523,2598],[\"app\",4511,2409],[\"app\",4512,2018],[\"app\",4510,4513],[\"app\",3536,2598],[\"app\",4515,2409],[\"app\",4516,2018],[\"app\",4517,4500],[\"app\",4514,4518],[\"app\",3542,2598],[\"app\",4520,2409],[\"app\",4521,2018],[\"app\",4522,2020],[\"app\",4519,4523],[\"app\",4524,2022],[\"app\",4481,4525],[\"app\",4470,4526],[\"app\",3559,2598],[\"app\",4528,2409],[\"app\",4529,2018],[\"app\",4527,4530],[\"app\",3572,2598],[\"app\",4532,2409],[\"app\",4533,2018],[\"app\",4531,4534],[\"app\",4535,2],[\"app\",4456,4536],[\"app\",4455,4537],[\"app\",4454,4538],[\"app\",4453,4539],[\"app\",4452,4540],[\"app\",996,4044],[\"app\",911,4044],[\"app\",4543,4536],[\"app\",4542,4544],[\"app\",4541,4545],[\"app\",4546,31],[\"app\",4547,261],[\"app\",4548,1848],[\"app\",916,4044],[\"app\",4550,3427],[\"app\",4551,4537],[\"app\",102,4044],[\"app\",4553,104],[\"app\",4554,4537],[\"app\",3580,2598],[\"app\",4556,2601],[\"app\",4557,4461],[\"app\",4558,4465],[\"app\",4559,4469],[\"app\",4560,4526],[\"app\",4561,4530],[\"app\",4562,4534],[\"app\",4563,2],[\"app\",4555,4564],[\"app\",4552,4565],[\"app\",4549,4566],[\"app\",4567,855],[\"app\",4546,4568],[\"app\",3895,4044],[\"app\",4570,31],[\"app\",4571,4544],[\"app\",4572,4566],[\"app\",4573,851],[\"app\",4574,855],[\"app\",4575,4540],[\"app\",4576,261],[\"app\",4577,3904],[\"app\",4569,4578],[\"app\",3912,4044],[\"app\",4580,4540],[\"app\",4581,4545],[\"app\",4582,31],[\"app\",4583,261],[\"app\",4584,1848],[\"app\",4585,4566],[\"app\",4586,855],[\"app\",4587,886],[\"app\",4579,4588],[\"app\",4589,4566],[\"app\",3930,4044],[\"app\",4591,4540],[\"app\",4592,4545],[\"app\",4593,4566],[\"app\",4594,31],[\"app\",4595,261],[\"app\",4596,1848],[\"app\",4597,855],[\"app\",4598,855],[\"app\",4599,3950],[\"app\",4600,3954],[\"app\",4601,1638],[\"app\",4602,886],[\"app\",4590,4603],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2409,4604,\"default\"],[\"app\",4451,4605],[\"app\",4606,4022],[\"app\",4607,2],[\"app\",27,2],[\"app\",4608,4609],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2018,4610,\"default\"],[\"app\",4449,4611],[\"app\",2142,4612],[\"app\",2601,27],[\"app\",1412,31],[\"app\",4475,129],[\"app\",3415,4616],[\"app\",3420,4616],[\"app\",4618,104],[\"app\",179,4616],[\"app\",3424,4472],[\"app\",4621,4475],[\"app\",3434,4472],[\"app\",4623,2598],[\"app\",4624,2409],[\"app\",4622,4625],[\"app\",3442,4472],[\"app\",4627,2598],[\"app\",4628,2409],[\"app\",4626,4629],[\"app\",3450,4472],[\"app\",4631,2598],[\"app\",4632,2409],[\"app\",4630,4633],[\"app\",3455,4472],[\"bvar\",28],[\"app\",1522,4636],[\"app\",4637,4472],[\"app\",4638,2598],[\"app\",4639,2],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],4472,4640,\"default\"],[\"app\",4635,4641],[\"app\",4642,4625],[\"app\",4643,4629],[\"app\",4644,4633],[\"app\",3474,4472],[\"app\",4646,2598],[\"app\",4647,2409],[\"app\",4648,3478],[\"app\",4649,73],[\"app\",4650,3430],[\"app\",3484,4636],[\"app\",4652,4472],[\"app\",4653,2598],[\"app\",4654,2],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],4472,4655,\"default\"],[\"app\",4651,4656],[\"app\",3496,4472],[\"app\",4658,2598],[\"app\",4659,2409],[\"app\",3500,4472],[\"app\",4661,2598],[\"app\",4662,2409],[\"app\",4663,2018],[\"app\",4660,4664],[\"app\",4657,4665],[\"app\",3509,4472],[\"app\",4667,2598],[\"app\",4668,2409],[\"app\",4666,4669],[\"app\",3516,4472],[\"app\",4671,2598],[\"app\",4672,2409],[\"app\",4670,4673],[\"app\",3523,4472],[\"app\",4675,2598],[\"app\",4676,2409],[\"app\",4674,4677],[\"app\",3536,4472],[\"app\",4679,2598],[\"app\",4680,2409],[\"app\",4681,4664],[\"app\",4678,4682],[\"app\",3542,4472],[\"app\",4684,2598],[\"app\",4685,2409],[\"app\",4686,2018],[\"app\",4683,4687],[\"app\",4688,2020],[\"app\",4645,4689],[\"app\",4634,4690],[\"app\",3559,4472],[\"app\",4692,2598],[\"app\",4693,2409],[\"app\",4691,4694],[\"app\",3572,4472],[\"app\",4696,2598],[\"app\",4697,2409],[\"app\",4695,4698],[\"app\",4699,129],[\"app\",4620,4700],[\"app\",4619,4701],[\"app\",3580,4472],[\"app\",4703,4475],[\"app\",4704,4625],[\"app\",4705,4629],[\"app\",4706,4633],[\"app\",4707,4690],[\"app\",4708,4694],[\"app\",4709,4698],[\"app\",4710,129],[\"app\",4702,4711],[\"app\",4617,4712],[\"app\",4713,27],[\"app\",4714,2],[\"app\",4615,4715],[\"app\",3859,4616],[\"app\",213,4616],[\"app\",215,4616],[\"app\",217,4616],[\"app\",4720,4701],[\"app\",4719,4721],[\"app\",4718,4722],[\"app\",4717,4723],[\"app\",996,4616],[\"app\",911,4616],[\"app\",4726,4700],[\"app\",4725,4727],[\"app\",4724,4728],[\"app\",4729,31],[\"app\",4730,261],[\"app\",4731,1848],[\"app\",916,4616],[\"app\",4733,3427],[\"app\",4734,4701],[\"app\",102,4616],[\"app\",4736,104],[\"app\",4737,4701],[\"app\",4738,4711],[\"app\",4735,4739],[\"app\",4732,4740],[\"app\",4741,855],[\"app\",2899,4742],[\"app\",4743,4616],[\"lam\",[\"num\",[\"str\",[\"str\",[\"num\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"x\"],\"_@\"],\"Mathlib\"],\"Data\"],\"FunLike\"],\"Basic\"],2582841819],\"_hygCtx\"],\"_hyg\"],11],4616,31,\"default\"],[\"app\",4744,4745],[\"app\",2956,849],[\"app\",4747,849],[\"app\",4748,1638],[\"app\",4749,4616],[\"app\",4750,4723],[\"app\",4751,4728],[\"app\",4752,31],[\"app\",4753,261],[\"app\",4754,1848],[\"app\",4755,4740],[\"app\",4756,855],[\"app\",4746,4757],[\"app\",4729,4742],[\"app\",3895,4616],[\"app\",4760,31],[\"app\",4761,4727],[\"app\",4762,4740],[\"app\",4763,851],[\"app\",4764,855],[\"app\",4765,4723],[\"app\",4766,261],[\"app\",4767,3904],[\"app\",4759,4768],[\"app\",3912,4616],[\"app\",4770,4723],[\"app\",4771,4728],[\"app\",4772,31],[\"app\",4773,261],[\"app\",4774,1848],[\"app\",4775,4740],[\"app\",4776,855],[\"app\",4777,886],[\"app\",4769,4778],[\"app\",4779,4740],[\"app\",3930,4616],[\"app\",4781,4723],[\"app\",4782,4728],[\"app\",4783,4740],[\"app\",4784,31],[\"app\",4785,261],[\"app\",4786,1848],[\"app\",4787,855],[\"app\",4788,855],[\"app\",4789,3950],[\"app\",4790,3954],[\"app\",4791,1638],[\"app\",4792,886],[\"app\",4780,4793],[\"app\",2899,4794],[\"app\",4795,4616],[\"app\",4639,134],[\"app\",3859,4797],[\"app\",213,4797],[\"app\",215,4797],[\"app\",217,4797],[\"app\",179,4797],[\"app\",3424,4636],[\"app\",4803,4639],[\"app\",3434,4636],[\"app\",4805,4472],[\"app\",4806,2598],[\"app\",4804,4807],[\"app\",3442,4636],[\"app\",4809,4472],[\"app\",4810,2598],[\"app\",4808,4811],[\"app\",3450,4636],[\"app\",4813,4472],[\"app\",4814,2598],[\"app\",4812,4815],[\"app\",3455,4636],[\"bvar\",29],[\"app\",1522,4818],[\"app\",4819,4636],[\"app\",4820,4472],[\"app\",4821,2],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],4636,4822,\"default\"],[\"app\",4817,4823],[\"app\",4824,4807],[\"app\",4825,4811],[\"app\",4826,4815],[\"app\",3474,4636],[\"app\",4828,4472],[\"app\",4829,2598],[\"app\",4830,3478],[\"app\",4831,73],[\"app\",4832,3430],[\"app\",3484,4818],[\"app\",4834,4636],[\"app\",4835,4472],[\"app\",4836,2],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],4636,4837,\"default\"],[\"app\",4833,4838],[\"app\",3496,4636],[\"app\",4840,4472],[\"app\",4841,2598],[\"app\",3500,4636],[\"app\",4843,4472],[\"app\",4844,2598],[\"app\",4845,2409],[\"app\",4842,4846],[\"app\",4839,4847],[\"app\",3509,4636],[\"app\",4849,4472],[\"app\",4850,2598],[\"app\",4848,4851],[\"app\",3516,4636],[\"app\",4853,4472],[\"app\",4854,2598],[\"app\",4852,4855],[\"app\",3523,4636],[\"app\",4857,4472],[\"app\",4858,2598],[\"app\",4856,4859],[\"app\",3536,4636],[\"app\",4861,4472],[\"app\",4862,2598],[\"app\",4863,4846],[\"app\",4860,4864],[\"app\",3542,4636],[\"app\",4866,4472],[\"app\",4867,2598],[\"app\",4868,2409],[\"app\",4865,4869],[\"app\",4870,2018],[\"app\",4827,4871],[\"app\",4816,4872],[\"app\",3559,4636],[\"app\",4874,4472],[\"app\",4875,2598],[\"app\",4873,4876],[\"app\",3572,4636],[\"app\",4878,4472],[\"app\",4879,2598],[\"app\",4877,4880],[\"app\",4881,134],[\"app\",4802,4882],[\"app\",4801,4883],[\"app\",4800,4884],[\"app\",4799,4885],[\"app\",4798,4886],[\"app\",996,4797],[\"app\",911,4797],[\"app\",4889,4882],[\"app\",4888,4890],[\"app\",4887,4891],[\"app\",4892,31],[\"app\",4893,261],[\"app\",4894,1848],[\"app\",916,4797],[\"app\",4896,3427],[\"app\",4897,4883],[\"app\",102,4797],[\"app\",4899,104],[\"app\",4900,4883],[\"app\",3580,4636],[\"app\",4902,4639],[\"app\",4903,4807],[\"app\",4904,4811],[\"app\",4905,4815],[\"app\",4906,4872],[\"app\",4907,4876],[\"app\",4908,4880],[\"app\",4909,134],[\"app\",4901,4910],[\"app\",4898,4911],[\"app\",4895,4912],[\"app\",4913,855],[\"lam\",[\"num\",[\"str\",[\"str\",[\"num\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"x\"],\"_@\"],\"Mathlib\"],\"Data\"],\"FunLike\"],\"Basic\"],2582841819],\"_hygCtx\"],\"_hyg\"],11],4616,4914,\"default\"],[\"app\",4796,4915],[\"app\",4752,4742],[\"app\",4917,4768],[\"app\",4918,4778],[\"app\",4919,4740],[\"app\",4920,4793],[\"app\",4916,4921],[\"app\",134,129],[\"app\",4922,4923],[\"app\",4924,27],[\"app\",4758,4925],[\"app\",4926,2],[\"app\",4716,4927],[\"forall\",[\"str\",[\"anonymous\"],\"w\"],4614,4928,\"default\"],[\"forall\",[\"str\",[\"anonymous\"],\"v\"],3457,4929,\"default\"],[\"forall\",[\"str\",[\"anonymous\"],\"x\"],2018,4930,\"default\"],[\"app\",4613,4931],[\"lam\",[\"str\",[\"anonymous\"],\"g\"],3959,4932,\"default\"],[\"app\",3960,4933],[\"const\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"Bundle\"],\"ContMDiffRiemannianMetric\"],\"inner\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",4935,42],[\"app\",4936,73],[\"app\",4937,112],[\"app\",4938,3468],[\"app\",4939,3470],[\"app\",4940,3472],[\"app\",4941,127],[\"app\",4942,2020],[\"app\",4943,2022],[\"app\",4944,1523],[\"app\",4945,3478],[\"app\",4946,73],[\"app\",4947,3430],[\"app\",4948,3716],[\"app\",4949,3725],[\"app\",4950,3729],[\"app\",4951,3733],[\"app\",4952,3737],[\"app\",4953,3742],[\"app\",4954,3747],[\"app\",4955,1527],[\"app\",4934,4956],[\"app\",3209,2020],[\"app\",2865,2020],[\"app\",4959,4022],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2020,3958,\"default\"],[\"app\",4960,4961],[\"app\",4958,4962],[\"app\",4963,2022],[\"app\",4182,2020],[\"app\",4965,3478],[\"app\",4966,73],[\"app\",4967,3430],[\"app\",4968,3701],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2020,3872,\"default\"],[\"app\",4969,4970],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2020,3886,\"default\"],[\"app\",4971,4972],[\"app\",4973,3833],[\"app\",4974,3986],[\"app\",4975,4227],[\"app\",4976,4245],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2020,3888,\"default\"],[\"app\",4977,4978],[\"app\",4253,3700],[\"app\",4980,3868],[\"app\",4981,3872],[\"app\",4982,31],[\"app\",4983,261],[\"app\",4984,851],[\"app\",4985,3886],[\"app\",4986,855],[\"app\",4987,1638],[\"app\",4988,3904],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2020,4989,\"default\"],[\"app\",4979,4990],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2020,3957,\"default\"],[\"app\",4991,4992],[\"app\",4974,31],[\"app\",4994,71],[\"app\",4995,187],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2020,31,\"default\"],[\"app\",4996,4997],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2020,851,\"default\"],[\"app\",4998,4999],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2020,855,\"default\"],[\"app\",5000,5001],[\"app\",4277,2020],[\"app\",5003,31],[\"app\",5004,2022],[\"app\",5005,261],[\"app\",5002,5006],[\"app\",5007,2022],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2020,3868,\"default\"],[\"app\",5008,5009],[\"app\",5010,3843],[\"app\",5011,3854],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2020,261,\"default\"],[\"app\",5012,5013],[\"app\",4298,2020],[\"app\",5015,31],[\"app\",5016,2022],[\"app\",5017,221],[\"app\",5014,5018],[\"app\",4305,2020],[\"app\",5020,31],[\"app\",5021,36],[\"app\",5022,71],[\"app\",5023,187],[\"app\",5024,2022],[\"app\",5019,5025],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2020,3904,\"default\"],[\"app\",5026,5027],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2020,4333,\"default\"],[\"app\",5028,5029],[\"app\",5030,4226],[\"app\",4993,5031],[\"app\",5032,2022],[\"app\",5033,5009],[\"app\",5034,3843],[\"app\",5035,3854],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2020,3905,\"default\"],[\"app\",5036,5037],[\"app\",4349,2020],[\"app\",5039,3478],[\"app\",5040,73],[\"app\",5041,3430],[\"app\",5042,3701],[\"app\",5043,4970],[\"app\",5044,4972],[\"app\",5045,3833],[\"app\",5046,31],[\"app\",5047,71],[\"app\",5048,187],[\"app\",5049,4997],[\"app\",5050,4999],[\"app\",5051,5001],[\"app\",5052,5006],[\"app\",5053,2022],[\"app\",5054,5009],[\"app\",5055,3843],[\"app\",5056,3854],[\"app\",5057,5013],[\"app\",5058,5018],[\"app\",5059,5025],[\"app\",5060,5027],[\"app\",5061,5029],[\"app\",5062,4226],[\"app\",5038,5063],[\"app\",4381,2020],[\"app\",5065,3478],[\"app\",5066,73],[\"app\",5067,3430],[\"app\",5068,3701],[\"app\",5069,4970],[\"app\",5070,4972],[\"app\",5071,3833],[\"app\",5072,31],[\"app\",5073,71],[\"app\",5074,187],[\"app\",5075,4997],[\"app\",5076,4999],[\"app\",5077,5001],[\"app\",5078,5006],[\"app\",5079,2022],[\"app\",5080,5009],[\"app\",5081,3843],[\"app\",5082,3854],[\"app\",5083,5013],[\"app\",5084,5018],[\"app\",5085,5025],[\"app\",5086,5027],[\"app\",5087,5029],[\"app\",5088,4226],[\"app\",5064,5089],[\"app\",4413,3700],[\"app\",5091,31],[\"app\",5092,3872],[\"app\",5093,3886],[\"app\",5094,851],[\"app\",5095,855],[\"app\",5096,3868],[\"app\",5097,261],[\"app\",5098,3904],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2020,5099,\"default\"],[\"app\",5090,5100],[\"app\",4430,3700],[\"app\",5102,31],[\"app\",5103,3872],[\"app\",5104,3886],[\"app\",5105,851],[\"app\",5106,855],[\"app\",5107,3868],[\"app\",5108,4440],[\"app\",5109,4226],[\"app\",5110,261],[\"app\",5111,3904],[\"app\",5112,4333],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2020,5113,\"default\"],[\"app\",5101,5114],[\"app\",5115,4226],[\"app\",4964,5116],[\"app\",4450,2018],[\"app\",5118,4173],[\"app\",5119,4022],[\"app\",5120,2],[\"app\",4942,2018],[\"app\",5122,2020],[\"app\",5123,2022],[\"app\",5124,3478],[\"app\",5125,73],[\"app\",5126,3430],[\"app\",5127,3489],[\"app\",5128,3505],[\"app\",5129,3512],[\"app\",5130,3519],[\"app\",5131,3526],[\"app\",5132,3540],[\"app\",5133,3546],[\"app\",5134,1525],[\"app\",5135,2],[\"app\",5121,5136],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2020,5137,\"default\"],[\"app\",5117,5138],[\"app\",783,5139],[\"app\",2412,27],[\"app\",2601,129],[\"app\",3415,5142],[\"app\",3420,5142],[\"app\",5144,104],[\"app\",179,5142],[\"app\",4535,129],[\"app\",5146,5147],[\"app\",5145,5148],[\"app\",4563,129],[\"app\",5149,5150],[\"app\",5143,5151],[\"app\",5152,27],[\"app\",5153,2],[\"app\",4615,5154],[\"app\",3859,5142],[\"app\",213,5142],[\"app\",215,5142],[\"app\",217,5142],[\"app\",5159,5148],[\"app\",5158,5160],[\"app\",5157,5161],[\"app\",5156,5162],[\"app\",996,5142],[\"app\",911,5142],[\"app\",5165,5147],[\"app\",5164,5166],[\"app\",5163,5167],[\"app\",5168,31],[\"app\",5169,261],[\"app\",5170,1848],[\"app\",916,5142],[\"app\",5172,3427],[\"app\",5173,5148],[\"app\",102,5142],[\"app\",5175,104],[\"app\",5176,5148],[\"app\",5177,5150],[\"app\",5174,5178],[\"app\",5171,5179],[\"app\",5180,855],[\"app\",2899,5181],[\"app\",5182,5142],[\"lam\",[\"num\",[\"str\",[\"str\",[\"num\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"x\"],\"_@\"],\"Mathlib\"],\"Data\"],\"FunLike\"],\"Basic\"],2582841819],\"_hygCtx\"],\"_hyg\"],11],5142,31,\"default\"],[\"app\",5183,5184],[\"app\",4749,5142],[\"app\",5186,5162],[\"app\",5187,5167],[\"app\",5188,31],[\"app\",5189,261],[\"app\",5190,1848],[\"app\",5191,5179],[\"app\",5192,855],[\"app\",5185,5193],[\"app\",5168,5181],[\"app\",3895,5142],[\"app\",5196,31],[\"app\",5197,5166],[\"app\",5198,5179],[\"app\",5199,851],[\"app\",5200,855],[\"app\",5201,5162],[\"app\",5202,261],[\"app\",5203,3904],[\"app\",5195,5204],[\"app\",3912,5142],[\"app\",5206,5162],[\"app\",5207,5167],[\"app\",5208,31],[\"app\",5209,261],[\"app\",5210,1848],[\"app\",5211,5179],[\"app\",5212,855],[\"app\",5213,886],[\"app\",5205,5214],[\"app\",5215,5179],[\"app\",3930,5142],[\"app\",5217,5162],[\"app\",5218,5167],[\"app\",5219,5179],[\"app\",5220,31],[\"app\",5221,261],[\"app\",5222,1848],[\"app\",5223,855],[\"app\",5224,855],[\"app\",5225,3950],[\"app\",5226,3954],[\"app\",5227,1638],[\"app\",5228,886],[\"app\",5216,5229],[\"app\",2899,5230],[\"app\",5231,5142],[\"app\",4475,134],[\"app\",3859,5233],[\"app\",213,5233],[\"app\",215,5233],[\"app\",217,5233],[\"app\",179,5233],[\"app\",4699,134],[\"app\",5238,5239],[\"app\",5237,5240],[\"app\",5236,5241],[\"app\",5235,5242],[\"app\",5234,5243],[\"app\",996,5233],[\"app\",911,5233],[\"app\",5246,5239],[\"app\",5245,5247],[\"app\",5244,5248],[\"app\",5249,31],[\"app\",5250,261],[\"app\",5251,1848],[\"app\",916,5233],[\"app\",5253,3427],[\"app\",5254,5240],[\"app\",102,5233],[\"app\",5256,104],[\"app\",5257,5240],[\"app\",4710,134],[\"app\",5258,5259],[\"app\",5255,5260],[\"app\",5252,5261],[\"app\",5262,855],[\"lam\",[\"num\",[\"str\",[\"str\",[\"num\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"x\"],\"_@\"],\"Mathlib\"],\"Data\"],\"FunLike\"],\"Basic\"],2582841819],\"_hygCtx\"],\"_hyg\"],11],5142,5263,\"default\"],[\"app\",5232,5264],[\"app\",5188,5181],[\"app\",5266,5204],[\"app\",5267,5214],[\"app\",5268,5179],[\"app\",5269,5229],[\"app\",5265,5270],[\"app\",4942,2598],[\"app\",5272,2409],[\"app\",5273,2018],[\"app\",5274,3478],[\"app\",5275,73],[\"app\",5276,3430],[\"app\",5277,4492],[\"app\",5278,4501],[\"app\",5279,4505],[\"app\",5280,4509],[\"app\",5281,4513],[\"app\",5282,4518],[\"app\",5283,4523],[\"app\",5284,2022],[\"app\",5285,129],[\"app\",5271,5286],[\"app\",5287,27],[\"app\",5194,5288],[\"app\",5289,2],[\"app\",5155,5290],[\"forall\",[\"str\",[\"anonymous\"],\"w\"],5141,5291,\"default\"],[\"forall\",[\"str\",[\"anonymous\"],\"v\"],3700,5292,\"default\"],[\"forall\",[\"str\",[\"anonymous\"],\"x\"],2020,5293,\"default\"],[\"app\",5140,5294],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"ContMDiff\"],\"continuous\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",5296,31],[\"app\",5297,36],[\"app\",5298,42],[\"app\",5299,73],[\"app\",5300,112],[\"app\",5301,3468],[\"app\",5302,3470],[\"app\",5303,3472],[\"app\",5304,2020],[\"app\",5305,2022],[\"app\",5306,1523],[\"app\",140,42],[\"app\",5308,4022],[\"app\",5307,5309],[\"app\",160,42],[\"app\",5311,4022],[\"app\",5312,73],[\"app\",4215,3986],[\"app\",5314,73],[\"app\",5315,4227],[\"app\",5316,36],[\"app\",5317,36],[\"app\",5318,3430],[\"app\",5319,4245],[\"app\",5320,1638],[\"app\",5321,4226],[\"app\",5313,5322],[\"app\",5310,5323],[\"app\",175,42],[\"app\",5325,4022],[\"app\",5326,84],[\"app\",179,42],[\"app\",5328,73],[\"app\",5327,5329],[\"app\",179,4022],[\"app\",5331,5322],[\"app\",5330,5332],[\"app\",5333,112],[\"app\",4232,3986],[\"app\",5335,3968],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"ContinuousLinearMap\"],\"toSeminormedAddCommGroup\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",5337,31],[\"app\",5338,31],[\"app\",5339,3478],[\"app\",5340,31],[\"app\",5341,3968],[\"app\",5342,98],[\"app\",5343,36],[\"app\",5344,36],[\"app\",5345,3430],[\"app\",5346,110],[\"app\",5347,1638],[\"app\",5348,4226],[\"app\",5336,5349],[\"app\",5350,36],[\"app\",5351,36],[\"app\",5352,3430],[\"app\",5353,4245],[\"app\",5354,1638],[\"app\",5355,4226],[\"app\",5356,31],[\"app\",5357,84],[\"app\",5358,4245],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"ContinuousLinearMap\"],\"smulCommClass\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",5360,31],[\"app\",5361,31],[\"app\",5362,849],[\"app\",5363,849],[\"app\",5364,1638],[\"app\",5365,3478],[\"app\",5366,3971],[\"app\",5367,3976],[\"app\",5368,31],[\"app\",5369,261],[\"app\",5370,1848],[\"app\",5371,3984],[\"app\",5372,855],[\"app\",5373,31],[\"app\",5374,31],[\"app\",988,31],[\"app\",898,1455],[\"app\",5376,5377],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"AddCommMonoid\"],\"toAddMonoid\"],[[\"zero\"]]],[\"app\",5379,31],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"SeminormedAddCommGroup\"],\"toAddCommGroup\"],[[\"zero\"]]],[\"app\",5381,31],[\"app\",5382,98],[\"app\",1889,5383],[\"app\",5380,5384],[\"app\",5378,5385],[\"app\",993,31],[\"app\",5387,1455],[\"app\",5388,5384],[\"app\",1898,98],[\"app\",5390,110],[\"app\",5389,5391],[\"app\",5386,5392],[\"app\",5375,5393],[\"app\",5394,3950],[\"const\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"ContinuousLinearMap\"],\"toNormedSpace\"],\"_proof_1\"],[[\"zero\"],[\"zero\"]]],[\"app\",5396,31],[\"app\",5397,98],[\"app\",5398,31],[\"app\",5399,84],[\"app\",5400,110],[\"app\",5395,5401],[\"app\",5402,5393],[\"app\",5403,3950],[\"app\",5404,5401],[\"app\",5405,3950],[\"app\",5359,5406],[\"app\",5334,5407],[\"app\",5324,5408],[\"app\",200,3468],[\"app\",5410,4022],[\"app\",5409,5411],[\"app\",211,3468],[\"app\",5413,3470],[\"app\",5414,4022],[\"app\",213,4022],[\"app\",215,4022],[\"app\",217,4022],[\"app\",5418,5332],[\"app\",5417,5419],[\"app\",5416,5420],[\"app\",5415,5421],[\"app\",5412,5422],[\"app\",230,42],[\"app\",5424,73],[\"app\",5425,112],[\"app\",5426,3468],[\"app\",5427,3470],[\"app\",5428,3472],[\"app\",5429,4022],[\"app\",5430,5322],[\"app\",5431,5407],[\"app\",5432,4022],[\"app\",5433,5421],[\"app\",238,4022],[\"app\",5435,5322],[\"app\",5436,5407],[\"app\",5434,5437],[\"app\",5423,5438],[\"app\",3859,3715],[\"app\",3512,2],[\"app\",5440,5441],[\"app\",996,3715],[\"app\",3519,2],[\"app\",5443,5444],[\"app\",5442,5445],[\"app\",5446,31],[\"app\",5447,261],[\"app\",5448,1848],[\"app\",3526,2],[\"app\",5449,5450],[\"app\",5451,855],[\"app\",5446,5452],[\"app\",3895,3715],[\"app\",5454,31],[\"app\",5455,5444],[\"app\",5456,5450],[\"app\",5457,851],[\"app\",5458,855],[\"app\",5459,5441],[\"app\",5460,261],[\"app\",5461,3904],[\"app\",5453,5462],[\"app\",3912,3715],[\"app\",5464,5441],[\"app\",5465,5445],[\"app\",5466,31],[\"app\",5467,261],[\"app\",5468,1848],[\"app\",5469,5450],[\"app\",5470,855],[\"app\",5471,886],[\"app\",5463,5472],[\"app\",5473,5450],[\"app\",3930,3715],[\"app\",5475,5441],[\"app\",5476,5445],[\"app\",5477,5450],[\"app\",5478,31],[\"app\",5479,261],[\"app\",5480,1848],[\"app\",5481,855],[\"app\",5482,855],[\"app\",5483,3950],[\"app\",5484,3954],[\"app\",5485,1638],[\"app\",5486,886],[\"app\",5474,5487],[\"lam\",[\"str\",[\"anonymous\"],\"b\"],2020,5488,\"default\"],[\"app\",4960,5489],[\"app\",5439,5490],[\"app\",4968,3716],[\"app\",5492,3733],[\"app\",5493,3737],[\"app\",5494,3725],[\"app\",5495,3986],[\"app\",5496,4227],[\"app\",5497,4245],[\"lam\",[\"str\",[\"anonymous\"],\"b\"],2020,5452,\"default\"],[\"app\",5498,5499],[\"app\",4253,3715],[\"app\",5501,5441],[\"app\",5502,5444],[\"app\",5503,31],[\"app\",5504,261],[\"app\",5505,851],[\"app\",5506,5450],[\"app\",5507,855],[\"app\",5508,1638],[\"app\",5509,3904],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2020,5510,\"default\"],[\"app\",5500,5511],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2020,5487,\"default\"],[\"app\",5512,5513],[\"app\",5495,31],[\"app\",5515,71],[\"app\",5516,187],[\"lam\",[\"str\",[\"anonymous\"],\"b\"],2020,31,\"default\"],[\"app\",5517,5518],[\"app\",5519,4999],[\"app\",5520,5001],[\"app\",5521,5006],[\"app\",5522,2022],[\"app\",5523,3729],[\"app\",5524,3742],[\"app\",5525,3747],[\"app\",5526,5013],[\"app\",5527,5018],[\"app\",5528,5025],[\"app\",5529,5027],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"IsModuleTopology\"],\"toContinuousSMul\"],[[\"zero\"],[\"zero\"]]],[\"app\",5531,31],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"SeminormedRing\"],\"toPseudoMetricSpace\"],[[\"zero\"]]],[\"app\",5533,31],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"NormedField\"],\"toNormedCommRing\"],[[\"zero\"]]],[\"app\",5535,31],[\"app\",5536,84],[\"app\",93,5537],[\"app\",1045,5538],[\"app\",5534,5539],[\"app\",216,5540],[\"app\",214,5541],[\"app\",5532,5542],[\"app\",5543,31],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Real\"],\"instAdd\"],[]],[\"app\",5544,5545],[\"app\",964,31],[\"app\",966,31],[\"app\",968,31],[\"app\",970,31],[\"app\",972,31],[\"app\",974,31],[\"app\",926,31],[\"app\",5553,851],[\"app\",5552,5554],[\"app\",5551,5555],[\"app\",5550,5556],[\"app\",5549,5557],[\"app\",5548,5558],[\"app\",5547,5559],[\"app\",984,31],[\"app\",5561,5557],[\"app\",5378,5556],[\"app\",5388,1890],[\"app\",5564,855],[\"app\",5563,5565],[\"app\",5562,5566],[\"app\",5560,5567],[\"app\",5546,5568],[\"app\",5569,261],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"IsTopologicalSemiring\"],\"toIsModuleTopology\"],[[\"zero\"]]],[\"app\",5571,31],[\"app\",5572,849],[\"app\",5573,5542],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"IsTopologicalRing\"],\"toIsTopologicalSemiring\"],[[\"zero\"]]],[\"app\",5575,31],[\"app\",5576,5542],[\"app\",5577,872],[\"app\",5578,883],[\"app\",5574,5579],[\"app\",5570,5580],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2020,5581,\"default\"],[\"app\",5530,5582],[\"app\",5583,4226],[\"app\",5514,5584],[\"app\",5585,2022],[\"app\",5586,3729],[\"app\",5587,3742],[\"app\",5588,3747],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2020,5462,\"default\"],[\"app\",5589,5590],[\"app\",5042,3716],[\"app\",5592,3733],[\"app\",5593,3737],[\"app\",5594,3725],[\"app\",5595,31],[\"app\",5596,71],[\"app\",5597,187],[\"app\",5598,5518],[\"app\",5599,4999],[\"app\",5600,5001],[\"app\",5601,5006],[\"app\",5602,2022],[\"app\",5603,3729],[\"app\",5604,3742],[\"app\",5605,3747],[\"app\",5606,5013],[\"app\",5607,5018],[\"app\",5608,5025],[\"app\",5609,5027],[\"app\",5610,5582],[\"app\",5611,4226],[\"app\",5591,5612],[\"app\",5068,3716],[\"app\",5614,3733],[\"app\",5615,3737],[\"app\",5616,3725],[\"app\",5617,31],[\"app\",5618,71],[\"app\",5619,187],[\"app\",5620,5518],[\"app\",5621,4999],[\"app\",5622,5001],[\"app\",5623,5006],[\"app\",5624,2022],[\"app\",5625,3729],[\"app\",5626,3742],[\"app\",5627,3747],[\"app\",5628,5013],[\"app\",5629,5018],[\"app\",5630,5025],[\"app\",5631,5027],[\"app\",5632,5582],[\"app\",5633,4226],[\"app\",5613,5634],[\"app\",4413,3715],[\"app\",5636,31],[\"app\",5637,5444],[\"app\",5638,5450],[\"app\",5639,851],[\"app\",5640,855],[\"app\",5641,5441],[\"app\",5642,261],[\"app\",5643,3904],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2020,5644,\"default\"],[\"app\",5635,5645],[\"app\",4430,3715],[\"app\",5647,31],[\"app\",5648,5444],[\"app\",5649,5450],[\"app\",5650,851],[\"app\",5651,855],[\"app\",5652,5441],[\"app\",5653,4440],[\"app\",5654,4226],[\"app\",5655,261],[\"app\",5656,3904],[\"app\",5536,3427],[\"app\",93,5658],[\"app\",1045,5659],[\"app\",5534,5660],[\"app\",216,5661],[\"app\",214,5662],[\"app\",5532,5663],[\"app\",5664,31],[\"app\",5665,5545],[\"app\",898,4323],[\"app\",5376,5667],[\"app\",5668,5556],[\"app\",5387,4323],[\"app\",5670,1890],[\"app\",5671,855],[\"app\",5669,5672],[\"app\",5562,5673],[\"app\",5560,5674],[\"app\",5666,5675],[\"app\",5676,261],[\"app\",5573,5663],[\"app\",5576,5663],[\"app\",5679,872],[\"app\",5680,883],[\"app\",5678,5681],[\"app\",5677,5682],[\"app\",5657,5683],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2020,5684,\"default\"],[\"app\",5646,5685],[\"app\",5686,4226],[\"app\",5491,5687],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"FiberBundle\"],\"chartedSpace\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",5689,2020],[\"app\",5690,4022],[\"app\",5691,5489],[\"app\",5692,5421],[\"app\",5693,5687],[\"app\",5454,5452],[\"app\",5695,5444],[\"app\",5696,5450],[\"app\",5697,5510],[\"app\",5698,5487],[\"app\",5699,5441],[\"app\",5700,5462],[\"app\",5701,5644],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2020,5702,\"default\"],[\"app\",5694,5703],[\"app\",5704,3468],[\"app\",5705,3470],[\"app\",5706,2022],[\"app\",5707,1523],[\"app\",5595,3986],[\"app\",5709,4227],[\"app\",5710,4245],[\"app\",5711,5499],[\"app\",5712,5511],[\"app\",5713,5513],[\"app\",5714,5584],[\"app\",5715,2022],[\"app\",5716,3729],[\"app\",5717,3742],[\"app\",5718,3747],[\"app\",5719,5590],[\"app\",5720,5612],[\"app\",5721,5634],[\"app\",5722,5645],[\"app\",5723,5685],[\"app\",5724,4226],[\"app\",5708,5725],[\"app\",5688,5726],[\"app\",3859,3488],[\"app\",4073,2],[\"app\",5728,5729],[\"app\",996,3488],[\"app\",4077,2],[\"app\",5731,5732],[\"app\",5730,5733],[\"app\",5734,31],[\"app\",5735,261],[\"app\",5736,1848],[\"app\",4081,2],[\"app\",5737,5738],[\"app\",5739,855],[\"app\",5734,5740],[\"app\",3895,3488],[\"app\",5742,31],[\"app\",5743,5732],[\"app\",5744,5738],[\"app\",5745,851],[\"app\",5746,855],[\"app\",5747,5729],[\"app\",5748,261],[\"app\",5749,3904],[\"app\",5741,5750],[\"app\",3912,3488],[\"app\",5752,5729],[\"app\",5753,5733],[\"app\",5754,31],[\"app\",5755,261],[\"app\",5756,1848],[\"app\",5757,5738],[\"app\",5758,855],[\"app\",5759,886],[\"app\",5751,5760],[\"app\",5761,5738],[\"app\",3930,3488],[\"app\",5763,5729],[\"app\",5764,5733],[\"app\",5765,5738],[\"app\",5766,31],[\"app\",5767,261],[\"app\",5768,1848],[\"app\",5769,855],[\"app\",5770,855],[\"app\",5771,3950],[\"app\",5772,3954],[\"app\",5773,1638],[\"app\",5774,886],[\"app\",5762,5775],[\"lam\",[\"str\",[\"anonymous\"],\"b\"],2018,5776,\"default\"],[\"app\",5118,5777],[\"app\",5778,4022],[\"app\",5779,2],[\"app\",5780,5136],[\"lam\",[\"str\",[\"anonymous\"],\"b\"],2020,5781,\"default\"],[\"app\",5727,5782],[\"app\",5783,127],[\"const\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"Bundle\"],\"ContMDiffRiemannianMetric\"],\"contMDiff\"],[[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",5785,42],[\"app\",5786,73],[\"app\",5787,112],[\"app\",5788,3468],[\"app\",5789,3470],[\"app\",5790,3472],[\"app\",5791,127],[\"app\",5792,2020],[\"app\",5793,2022],[\"app\",5794,1523],[\"app\",5795,3478],[\"app\",5796,73],[\"app\",5797,3430],[\"app\",5798,3716],[\"app\",5799,3725],[\"app\",5800,3729],[\"app\",5801,3733],[\"app\",5802,3737],[\"app\",5803,3742],[\"app\",5804,3747],[\"app\",5805,1527],[\"app\",5784,5806],[\"app\",5295,5807],[\"const\",[\"str\",[\"anonymous\"],\"rfl\"],[[\"succ\",[\"zero\"]]]],[\"app\",5809,31],[\"app\",5810,5154],[\"lam\",[\"num\",[\"str\",[\"str\",[\"num\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"x\"],\"_@\"],\"OriginalB2B5V480\"],3706074420],\"_hygCtx\"],\"_hyg\"],1251],5141,5811,\"default\"],[\"lam\",[\"num\",[\"str\",[\"str\",[\"num\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"x\"],\"_@\"],\"OriginalB2B5V480\"],3706074420],\"_hygCtx\"],\"_hyg\"],1249],3700,5812,\"default\"],[\"lam\",[\"num\",[\"str\",[\"str\",[\"num\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"x\"],\"_@\"],\"OriginalB2B5V480\"],3706074420],\"_hygCtx\"],\"_hyg\"],1247],2020,5813,\"default\"],[\"app\",5808,5814],[\"app\",4957,5815],[\"app\",3855,5816],[\"app\",3787,5817],[\"app\",5818,292],[\"lam\",[\"str\",[\"anonymous\"],\"q\"],328,3665,\"default\"],[\"app\",5819,5820],[\"lam\",[\"str\",[\"anonymous\"],\"m\"],328,3668,\"default\"],[\"app\",5821,5822],[\"app\",5823,438],[\"app\",129,27],[\"app\",5824,5825],[\"app\",129,2],[\"app\",5826,5827],[\"app\",3673,5828],[\"const\",[\"str\",[\"anonymous\"],\"id\"],[[\"zero\"]]],[\"app\",3387,2598],[\"app\",5831,2409],[\"app\",5832,2018],[\"app\",5833,2020],[\"app\",5834,2022],[\"app\",5835,1523],[\"app\",379,2697],[\"app\",5837,1757],[\"app\",5838,2],[\"app\",1523,5839],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2327,5840,\"default\"],[\"app\",5836,5841],[\"app\",5842,403],[\"app\",5843,399],[\"app\",5844,252],[\"app\",5845,134],[\"lam\",[\"str\",[\"anonymous\"],\"q\"],328,5846,\"default\"],[\"app\",5847,27],[\"app\",4615,5848],[\"app\",488,2],[\"app\",2601,5850],[\"app\",3415,5851],[\"app\",3420,5851],[\"app\",5853,104],[\"app\",179,5851],[\"app\",4535,5850],[\"app\",5855,5856],[\"app\",5854,5857],[\"app\",4563,5850],[\"app\",5858,5859],[\"app\",5852,5860],[\"app\",2641,2],[\"app\",1464,5862],[\"app\",2648,2],[\"app\",5863,5864],[\"app\",996,5862],[\"app\",2655,2],[\"app\",5866,5867],[\"app\",5865,5868],[\"app\",5869,5851],[\"app\",2610,5850],[\"app\",5870,5871],[\"app\",996,5851],[\"app\",2616,5850],[\"app\",5873,5874],[\"app\",5872,5875],[\"app\",2672,2],[\"app\",5876,5877],[\"app\",2624,5850],[\"app\",5878,5879],[\"app\",2899,5880],[\"app\",5881,5862],[\"app\",698,27],[\"app\",4475,5883],[\"lam\",[\"num\",[\"str\",[\"str\",[\"num\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"x\"],\"_@\"],\"Mathlib\"],\"Data\"],\"FunLike\"],\"Basic\"],2582841819],\"_hygCtx\"],\"_hyg\"],11],5862,5884,\"default\"],[\"app\",5882,5885],[\"app\",2959,5862],[\"app\",5887,5864],[\"app\",5888,5868],[\"app\",5889,5851],[\"app\",5890,5871],[\"app\",5891,5875],[\"app\",5892,5877],[\"app\",5893,5879],[\"app\",5886,5894],[\"app\",2691,787],[\"app\",5896,2],[\"app\",5895,5897],[\"app\",3000,5862],[\"app\",5899,5864],[\"app\",5900,5868],[\"app\",5901,3007],[\"app\",5902,5877],[\"app\",2899,5903],[\"app\",5904,328],[\"app\",1322,403],[\"app\",5906,328],[\"app\",5907,427],[\"app\",5908,430],[\"app\",5909,27],[\"lam\",[\"num\",[\"str\",[\"str\",[\"num\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"x\"],\"_@\"],\"Mathlib\"],\"Data\"],\"FunLike\"],\"Basic\"],2582841819],\"_hygCtx\"],\"_hyg\"],11],328,5910,\"default\"],[\"app\",5905,5911],[\"app\",3019,5903],[\"app\",5913,328],[\"app\",5914,5862],[\"app\",3034,5862],[\"app\",5916,5864],[\"app\",5917,5868],[\"app\",5918,3007],[\"app\",5919,5877],[\"app\",5915,5920],[\"app\",5912,5921],[\"app\",3050,5862],[\"app\",5923,5864],[\"app\",5924,5868],[\"app\",5925,328],[\"app\",5926,351],[\"app\",5927,1210],[\"app\",5928,5877],[\"app\",5929,3007],[\"app\",3066,408],[\"app\",5931,328],[\"app\",5932,427],[\"app\",5933,430],[\"app\",5934,2],[\"app\",5930,5935],[\"app\",5922,5936],[\"app\",3086,252],[\"app\",5938,3092],[\"app\",3079,5939],[\"app\",5937,5940],[\"app\",5898,5941],[\"app\",5861,5942],[\"app\",3086,134],[\"app\",5944,3092],[\"app\",3079,5945],[\"app\",5937,5946],[\"app\",5898,5947],[\"app\",5943,5948],[\"lam\",[\"str\",[\"anonymous\"],\"b\"],328,5949,\"default\"],[\"app\",5950,27],[\"app\",5849,5951],[\"app\",5830,5952],[\"app\",387,2327],[\"app\",389,2327],[\"app\",5955,157],[\"app\",596,2327],[\"const\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"SeifertSurfaces\"],\"MetricFoundations\"],\"ProperSmoothEmbedding\"],\"ofNeat\"],\"_proof_1\"],[]],[\"app\",202,5958],[\"app\",5957,5959],[\"app\",5960,36],[\"app\",5961,171],[\"app\",5962,197],[\"app\",224,5958],[\"app\",5963,5964],[\"app\",263,1523],[\"app\",5965,5966],[\"app\",248,5958],[\"app\",5967,5968],[\"app\",280,1523],[\"app\",5969,5970],[\"app\",5971,403],[\"app\",5956,5972],[\"app\",5954,5973],[\"app\",5974,399],[\"app\",5841,5975],[\"app\",4058,5976],[\"app\",3859,5977],[\"app\",4505,5976],[\"app\",5978,5979],[\"app\",996,5977],[\"app\",4509,5976],[\"app\",5981,5982],[\"app\",5980,5983],[\"app\",5984,31],[\"app\",5985,261],[\"app\",5986,1848],[\"app\",4513,5976],[\"app\",5987,5988],[\"app\",5989,855],[\"app\",2899,5990],[\"app\",5991,5977],[\"lam\",[\"num\",[\"str\",[\"str\",[\"num\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"x\"],\"_@\"],\"Mathlib\"],\"Data\"],\"FunLike\"],\"Basic\"],2582841819],\"_hygCtx\"],\"_hyg\"],11],5977,31,\"default\"],[\"app\",5992,5993],[\"app\",4749,5977],[\"app\",5995,5979],[\"app\",5996,5983],[\"app\",5997,31],[\"app\",5998,261],[\"app\",5999,1848],[\"app\",6000,5988],[\"app\",6001,855],[\"app\",5994,6002],[\"app\",5984,5990],[\"app\",3895,5977],[\"app\",6005,31],[\"app\",6006,5982],[\"app\",6007,5988],[\"app\",6008,851],[\"app\",6009,855],[\"app\",6010,5979],[\"app\",6011,261],[\"app\",6012,3904],[\"app\",6004,6013],[\"app\",3912,5977],[\"app\",6015,5979],[\"app\",6016,5983],[\"app\",6017,31],[\"app\",6018,261],[\"app\",6019,1848],[\"app\",6020,5988],[\"app\",6021,855],[\"const\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"SeifertSurfaces\"],\"MetricFoundations\"],\"coordinateGram\"],\"_proof_1\"],[]],[\"app\",6022,6023],[\"app\",6014,6024],[\"app\",6025,5988],[\"app\",3930,5977],[\"app\",6027,5979],[\"app\",6028,5983],[\"app\",6029,5988],[\"app\",6030,31],[\"app\",6031,261],[\"app\",6032,1848],[\"app\",6033,855],[\"app\",6034,855],[\"const\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"SeifertSurfaces\"],\"MetricFoundations\"],\"coordinateGram\"],\"_proof_2\"],[]],[\"app\",6035,6036],[\"const\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"SeifertSurfaces\"],\"MetricFoundations\"],\"coordinateGram\"],\"_proof_3\"],[]],[\"app\",6037,6038],[\"app\",6039,1638],[\"app\",6040,6023],[\"app\",6026,6041],[\"app\",2899,6042],[\"app\",6043,5977],[\"app\",142,2020],[\"app\",379,6045],[\"app\",6046,1535],[\"app\",6047,2],[\"app\",2022,6048],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2697,6049,\"default\"],[\"app\",387,2697],[\"app\",389,2697],[\"app\",6052,157],[\"app\",596,2697],[\"app\",6054,5959],[\"app\",6055,36],[\"app\",6056,171],[\"app\",6057,197],[\"app\",6058,5964],[\"app\",263,2022],[\"app\",6059,6060],[\"app\",6061,5968],[\"app\",280,2022],[\"app\",6062,6063],[\"app\",6064,725],[\"app\",6053,6065],[\"app\",6051,6066],[\"app\",6067,1484],[\"app\",6050,6068],[\"app\",4490,6069],[\"app\",3859,6070],[\"app\",4669,6069],[\"app\",6071,6072],[\"app\",996,6070],[\"app\",4673,6069],[\"app\",6074,6075],[\"app\",6073,6076],[\"app\",6077,31],[\"app\",6078,261],[\"app\",6079,1848],[\"app\",4677,6069],[\"app\",6080,6081],[\"app\",6082,855],[\"lam\",[\"num\",[\"str\",[\"str\",[\"num\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"x\"],\"_@\"],\"Mathlib\"],\"Data\"],\"FunLike\"],\"Basic\"],2582841819],\"_hygCtx\"],\"_hyg\"],11],5977,6083,\"default\"],[\"app\",6044,6084],[\"app\",5997,5990],[\"app\",6086,6013],[\"app\",6087,6024],[\"app\",6088,5988],[\"app\",6089,6041],[\"app\",6085,6090],[\"app\",5285,5976],[\"app\",6091,6092],[\"app\",1472,651],[\"app\",6094,399],[\"app\",1464,6095],[\"app\",1497,651],[\"app\",6097,399],[\"app\",6096,6098],[\"app\",996,6095],[\"app\",1512,651],[\"app\",6101,399],[\"app\",6100,6102],[\"app\",6099,6103],[\"app\",1529,2327],[\"app\",6105,2598],[\"app\",6106,5841],[\"app\",6107,5974],[\"app\",6108,399],[\"app\",4058,6109],[\"app\",6104,6110],[\"app\",1554,3468],[\"app\",6112,3470],[\"app\",6113,3472],[\"app\",6114,2598],[\"app\",6115,2409],[\"app\",6116,2018],[\"app\",6117,6109],[\"app\",6111,6118],[\"app\",996,6110],[\"app\",1566,3468],[\"app\",6121,3470],[\"app\",6122,3472],[\"app\",6123,2598],[\"app\",6124,2409],[\"app\",6125,2018],[\"app\",6126,6109],[\"app\",6120,6127],[\"app\",6119,6128],[\"app\",1586,651],[\"app\",6130,399],[\"app\",6129,6131],[\"app\",1592,3468],[\"app\",6133,3470],[\"app\",6134,3472],[\"app\",6135,2598],[\"app\",6136,2409],[\"app\",6137,2018],[\"app\",6138,6109],[\"app\",6132,6139],[\"app\",2899,6140],[\"app\",6141,6095],[\"app\",1529,2697],[\"app\",6143,4472],[\"app\",6144,6050],[\"app\",6145,6067],[\"app\",6146,1484],[\"app\",4490,6147],[\"lam\",[\"num\",[\"str\",[\"str\",[\"num\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"x\"],\"_@\"],\"Mathlib\"],\"Data\"],\"FunLike\"],\"Basic\"],2582841819],\"_hygCtx\"],\"_hyg\"],11],6095,6148,\"default\"],[\"app\",6142,6149],[\"app\",2959,6095],[\"app\",6151,6098],[\"app\",6152,6103],[\"app\",6153,6110],[\"app\",6154,6118],[\"app\",6155,6128],[\"app\",6156,6131],[\"app\",6157,6139],[\"app\",6150,6158],[\"app\",1612,651],[\"app\",6160,42],[\"app\",6161,73],[\"app\",6162,112],[\"app\",6163,3468],[\"app\",6164,3470],[\"app\",6165,3472],[\"app\",6166,2598],[\"app\",6167,2409],[\"app\",6168,2018],[\"app\",6169,6108],[\"app\",2329,5972],[\"app\",6170,6171],[\"app\",6172,399],[\"app\",6159,6173],[\"const\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"SeifertSurfaces\"],\"MetricFoundations\"],\"coordinateGram\"],\"_proof_4\"],[]],[\"app\",2992,6175],[\"app\",6176,6175],[\"app\",6177,327],[\"app\",6178,642],[\"app\",911,327],[\"app\",6180,171],[\"app\",1850,6181],[\"app\",6179,6182],[\"app\",1643,651],[\"app\",6184,399],[\"app\",6183,6185],[\"app\",1648,651],[\"app\",6187,399],[\"app\",6186,6188],[\"app\",996,6185],[\"app\",1654,651],[\"app\",6191,399],[\"app\",6190,6192],[\"app\",6189,6193],[\"app\",6194,1895],[\"app\",1699,651],[\"app\",6196,399],[\"app\",6195,6197],[\"app\",2899,6198],[\"app\",6199,327],[\"app\",6184,1484],[\"lam\",[\"num\",[\"str\",[\"str\",[\"num\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"x\"],\"_@\"],\"Mathlib\"],\"Data\"],\"FunLike\"],\"Basic\"],2582841819],\"_hygCtx\"],\"_hyg\"],11],327,6201,\"default\"],[\"app\",6200,6202],[\"app\",3019,6198],[\"app\",6204,327],[\"app\",6205,6185],[\"app\",3029,6175],[\"app\",6207,6175],[\"app\",6208,327],[\"app\",6209,642],[\"app\",6210,6182],[\"app\",6211,6185],[\"app\",6212,6188],[\"app\",6213,6193],[\"app\",6214,1895],[\"app\",6215,6197],[\"app\",6206,6216],[\"app\",6203,6217],[\"app\",3048,6175],[\"app\",6219,6175],[\"app\",6220,6185],[\"app\",6221,6188],[\"app\",6222,6193],[\"app\",6223,327],[\"app\",6224,642],[\"app\",6225,6182],[\"app\",6226,6197],[\"app\",6227,1895],[\"app\",3061,327],[\"app\",6229,171],[\"app\",6230,197],[\"app\",6231,327],[\"app\",6232,642],[\"app\",6233,646],[\"app\",6234,327],[\"app\",6235,426],[\"app\",6236,651],[\"app\",6237,399],[\"app\",6228,6238],[\"app\",6218,6239],[\"app\",6240,5939],[\"app\",6174,6241],[\"app\",6093,6242],[\"app\",6003,6243],[\"app\",6240,5945],[\"app\",6174,6245],[\"app\",6244,6246],[\"lam\",[\"str\",[\"anonymous\"],\"q\"],328,6247,\"default\"],[\"app\",6248,27],[\"app\",4615,6249],[\"app\",6250,5951],[\"app\",5830,6251],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Eq\"],\"mpr\"],[[\"zero\"]]],[\"app\",387,2149],[\"app\",389,2149],[\"app\",6255,157],[\"app\",596,2149],[\"app\",6257,5959],[\"app\",6258,36],[\"app\",6259,171],[\"app\",6260,197],[\"app\",6261,5964],[\"app\",6262,2774],[\"app\",6263,5968],[\"app\",6264,2777],[\"app\",6265,408],[\"app\",6256,6266],[\"app\",6254,6267],[\"app\",6268,1484],[\"app\",3395,6269],[\"app\",1527,6270],[\"app\",3487,6271],[\"app\",3859,6272],[\"app\",379,2327],[\"app\",6274,1535],[\"app\",6275,2],[\"app\",1525,6276],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2149,6277,\"default\"],[\"app\",6278,6269],[\"app\",4073,6279],[\"app\",6273,6280],[\"app\",3487,6279],[\"app\",996,6282],[\"app\",4077,6279],[\"app\",6283,6284],[\"app\",6281,6285],[\"app\",6286,31],[\"app\",6287,261],[\"app\",6288,1848],[\"app\",4081,6279],[\"app\",6289,6290],[\"app\",6291,855],[\"app\",2899,6292],[\"app\",6293,6272],[\"lam\",[\"num\",[\"str\",[\"str\",[\"num\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"x\"],\"_@\"],\"Mathlib\"],\"Data\"],\"FunLike\"],\"Basic\"],2582841819],\"_hygCtx\"],\"_hyg\"],11],6272,31,\"default\"],[\"app\",6294,6295],[\"app\",4749,6282],[\"app\",6297,6280],[\"app\",6298,6285],[\"app\",6299,31],[\"app\",6300,261],[\"app\",6301,1848],[\"app\",6302,6290],[\"app\",6303,855],[\"app\",6296,6304],[\"app\",6286,6292],[\"app\",3895,6282],[\"app\",6307,31],[\"app\",6308,6284],[\"app\",6309,6290],[\"app\",6310,851],[\"app\",6311,855],[\"app\",6312,6280],[\"app\",6313,261],[\"app\",6314,3904],[\"app\",6306,6315],[\"app\",3912,6282],[\"app\",6317,6280],[\"app\",6318,6285],[\"app\",6319,31],[\"app\",6320,261],[\"app\",6321,1848],[\"app\",6322,6290],[\"app\",6323,855],[\"app\",6324,6023],[\"app\",6316,6325],[\"app\",6326,6290],[\"app\",3930,6282],[\"app\",6328,6280],[\"app\",6329,6285],[\"app\",6330,6290],[\"app\",6331,31],[\"app\",6332,261],[\"app\",6333,1848],[\"app\",6334,855],[\"app\",6335,855],[\"app\",6336,6036],[\"app\",6337,6038],[\"app\",6338,1638],[\"app\",6339,6023],[\"app\",6327,6340],[\"app\",2899,6341],[\"app\",6342,6272],[\"app\",5974,1867],[\"app\",6275,6344],[\"app\",1525,6345],[\"app\",4058,6346],[\"app\",3859,6347],[\"app\",5837,1881],[\"app\",6349,2],[\"app\",1523,6350],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2327,6351,\"default\"],[\"app\",6352,6344],[\"app\",4505,6353],[\"app\",6348,6354],[\"app\",4058,6353],[\"app\",996,6356],[\"app\",4509,6353],[\"app\",6357,6358],[\"app\",6355,6359],[\"app\",6360,31],[\"app\",6361,261],[\"app\",6362,1848],[\"app\",4513,6353],[\"app\",6363,6364],[\"app\",6365,855],[\"lam\",[\"num\",[\"str\",[\"str\",[\"num\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"x\"],\"_@\"],\"Mathlib\"],\"Data\"],\"FunLike\"],\"Basic\"],2582841819],\"_hygCtx\"],\"_hyg\"],11],6272,6366,\"default\"],[\"app\",6343,6367],[\"app\",3859,6282],[\"app\",6369,6280],[\"app\",6370,6285],[\"app\",6371,31],[\"app\",6372,261],[\"app\",6373,1848],[\"app\",6374,6290],[\"app\",6375,855],[\"app\",6299,6376],[\"app\",6377,6315],[\"app\",6378,6325],[\"app\",6379,6290],[\"app\",6380,6340],[\"app\",6368,6381],[\"app\",4942,2409],[\"app\",6383,2018],[\"app\",6384,2020],[\"app\",6385,3478],[\"app\",6386,73],[\"app\",6387,3430],[\"app\",6388,4060],[\"app\",6389,4069],[\"app\",6390,4073],[\"app\",6391,4077],[\"app\",6392,4081],[\"app\",6393,4086],[\"app\",6394,4091],[\"app\",6395,1523],[\"app\",6396,6271],[\"app\",6382,6397],[\"app\",6094,1484],[\"app\",1464,6399],[\"app\",6097,1484],[\"app\",6400,6401],[\"app\",996,6399],[\"app\",6101,1484],[\"app\",6403,6404],[\"app\",6402,6405],[\"app\",1529,2149],[\"app\",6407,2409],[\"app\",6408,6278],[\"app\",6409,6268],[\"app\",6410,1484],[\"app\",3487,6411],[\"app\",6406,6412],[\"app\",6114,2409],[\"app\",6414,2018],[\"app\",6415,2020],[\"app\",6416,6411],[\"app\",6413,6417],[\"app\",996,6412],[\"app\",6123,2409],[\"app\",6420,2018],[\"app\",6421,2020],[\"app\",6422,6411],[\"app\",6419,6423],[\"app\",6418,6424],[\"app\",6130,1484],[\"app\",6425,6426],[\"app\",6135,2409],[\"app\",6428,2018],[\"app\",6429,2020],[\"app\",6430,6411],[\"app\",6427,6431],[\"app\",2899,6432],[\"app\",6433,6399],[\"app\",6106,6352],[\"app\",6435,5974],[\"app\",6436,1867],[\"app\",4058,6437],[\"lam\",[\"num\",[\"str\",[\"str\",[\"num\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"x\"],\"_@\"],\"Mathlib\"],\"Data\"],\"FunLike\"],\"Basic\"],2582841819],\"_hygCtx\"],\"_hyg\"],11],6399,6438,\"default\"],[\"app\",6434,6439],[\"app\",2959,6399],[\"app\",6441,6401],[\"app\",6442,6405],[\"app\",6443,6412],[\"app\",6444,6417],[\"app\",6445,6424],[\"app\",6446,6426],[\"app\",6447,6431],[\"app\",6440,6448],[\"app\",6166,2409],[\"app\",6450,2018],[\"app\",6451,2020],[\"app\",6452,6410],[\"app\",2151,6266],[\"app\",6453,6454],[\"app\",6455,1484],[\"app\",6449,6456],[\"app\",6183,6201],[\"app\",6187,1484],[\"app\",6458,6459],[\"app\",996,6201],[\"app\",6191,1484],[\"app\",6461,6462],[\"app\",6460,6463],[\"app\",6464,1895],[\"app\",6196,1484],[\"app\",6465,6466],[\"app\",2899,6467],[\"app\",6468,327],[\"app\",6184,1867],[\"lam\",[\"num\",[\"str\",[\"str\",[\"num\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"x\"],\"_@\"],\"Mathlib\"],\"Data\"],\"FunLike\"],\"Basic\"],2582841819],\"_hygCtx\"],\"_hyg\"],11],327,6470,\"default\"],[\"app\",6469,6471],[\"app\",3019,6467],[\"app\",6473,327],[\"app\",6474,6201],[\"app\",6211,6201],[\"app\",6476,6459],[\"app\",6477,6463],[\"app\",6478,1895],[\"app\",6479,6466],[\"app\",6475,6480],[\"app\",6472,6481],[\"app\",6220,6201],[\"app\",6483,6459],[\"app\",6484,6463],[\"app\",6485,327],[\"app\",6486,642],[\"app\",6487,6182],[\"app\",6488,6466],[\"app\",6489,1895],[\"app\",6237,1484],[\"app\",6490,6491],[\"app\",6482,6492],[\"app\",6493,5945],[\"app\",6457,6494],[\"app\",6398,6495],[\"app\",6305,6496],[\"app\",6493,3248],[\"app\",6457,6498],[\"app\",6497,6499],[\"app\",4615,6500],[\"app\",3415,3614],[\"app\",3420,3614],[\"app\",6503,104],[\"app\",179,3614],[\"app\",4103,3613],[\"app\",6505,6506],[\"app\",6504,6507],[\"app\",4131,3613],[\"app\",6508,6509],[\"app\",6502,6510],[\"app\",1464,3636],[\"app\",2459,27],[\"app\",6512,6513],[\"app\",996,3636],[\"app\",2466,27],[\"app\",6515,6516],[\"app\",6514,6517],[\"app\",6518,3614],[\"app\",2421,3613],[\"app\",6519,6520],[\"app\",996,3614],[\"app\",2427,3613],[\"app\",6522,6523],[\"app\",6521,6524],[\"app\",2483,27],[\"app\",6525,6526],[\"app\",2435,3613],[\"app\",6527,6528],[\"app\",2899,6529],[\"app\",6530,3636],[\"app\",488,129],[\"app\",2601,6532],[\"lam\",[\"num\",[\"str\",[\"str\",[\"num\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"x\"],\"_@\"],\"Mathlib\"],\"Data\"],\"FunLike\"],\"Basic\"],2582841819],\"_hygCtx\"],\"_hyg\"],11],3636,6533,\"default\"],[\"app\",6531,6534],[\"app\",2959,3636],[\"app\",6536,6513],[\"app\",6537,6517],[\"app\",6538,3614],[\"app\",6539,6520],[\"app\",6540,6524],[\"app\",6541,6526],[\"app\",6542,6528],[\"app\",6535,6543],[\"app\",2502,698],[\"app\",6545,27],[\"app\",6544,6546],[\"app\",3000,3636],[\"app\",6548,6513],[\"app\",6549,6517],[\"app\",6550,3007],[\"app\",6551,6526],[\"app\",2899,6552],[\"app\",6553,328],[\"app\",2641,129],[\"lam\",[\"num\",[\"str\",[\"str\",[\"num\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"x\"],\"_@\"],\"Mathlib\"],\"Data\"],\"FunLike\"],\"Basic\"],2582841819],\"_hygCtx\"],\"_hyg\"],11],328,6555,\"default\"],[\"app\",6554,6556],[\"app\",3019,6552],[\"app\",6558,328],[\"app\",6559,3636],[\"app\",3034,3636],[\"app\",6561,6513],[\"app\",6562,6517],[\"app\",6563,3007],[\"app\",6564,6526],[\"app\",6560,6565],[\"app\",6557,6566],[\"app\",3050,3636],[\"app\",6568,6513],[\"app\",6569,6517],[\"app\",6570,328],[\"app\",6571,351],[\"app\",6572,1210],[\"app\",6573,6526],[\"app\",6574,3007],[\"app\",3066,787],[\"app\",6576,328],[\"app\",6577,427],[\"app\",6578,430],[\"app\",6579,27],[\"app\",6575,6580],[\"app\",6567,6581],[\"app\",6582,5946],[\"app\",6547,6583],[\"app\",6511,6584],[\"app\",6582,3249],[\"app\",6547,6586],[\"app\",6585,6587],[\"app\",6501,6588],[\"app\",6253,6589],[\"app\",1658,3636],[\"app\",6591,6513],[\"app\",6592,6517],[\"app\",6593,3614],[\"app\",6594,6520],[\"app\",6595,6524],[\"app\",6596,1701],[\"app\",6597,6526],[\"app\",6598,6528],[\"app\",6599,1721],[\"app\",6600,6546],[\"app\",6601,1798],[\"app\",6449,6602],[\"app\",6603,6494],[\"app\",6398,6604],[\"app\",6305,6605],[\"app\",6603,6498],[\"app\",6606,6607],[\"app\",4615,6608],[\"app\",6609,6588],[\"app\",6590,6610],[\"app\",1412,1391],[\"app\",6612,6589],[\"app\",6613,6610],[\"app\",5830,6614],[\"app\",6256,2153],[\"app\",6254,6616],[\"app\",6409,6617],[\"app\",6618,1484],[\"app\",2412,6619],[\"app\",1516,6620],[\"app\",2421,6619],[\"app\",6621,6622],[\"app\",996,6620],[\"app\",2427,6619],[\"app\",6624,6625],[\"app\",6623,6626],[\"app\",6627,1588],[\"app\",2435,6619],[\"app\",6628,6629],[\"app\",1422,6630],[\"app\",6631,1391],[\"app\",1619,2409],[\"app\",6633,2018],[\"app\",6634,2020],[\"app\",6635,6618],[\"app\",6636,2154],[\"app\",6637,1484],[\"app\",6632,6638],[\"app\",6639,6602],[\"app\",2899,6366],[\"app\",6641,6347],[\"lam\",[\"num\",[\"str\",[\"str\",[\"num\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"x\"],\"_@\"],\"Mathlib\"],\"Data\"],\"FunLike\"],\"Basic\"],2582841819],\"_hygCtx\"],\"_hyg\"],11],6347,31,\"default\"],[\"app\",6642,6643],[\"app\",4749,6356],[\"app\",6645,6354],[\"app\",6646,6359],[\"app\",6647,31],[\"app\",6648,261],[\"app\",6649,1848],[\"app\",6650,6364],[\"app\",6651,855],[\"app\",6644,6652],[\"app\",6360,6366],[\"app\",3895,6356],[\"app\",6655,31],[\"app\",6656,6358],[\"app\",6657,6364],[\"app\",6658,851],[\"app\",6659,855],[\"app\",6660,6354],[\"app\",6661,261],[\"app\",6662,3904],[\"app\",6654,6663],[\"app\",3912,6356],[\"app\",6665,6354],[\"app\",6666,6359],[\"app\",6667,31],[\"app\",6668,261],[\"app\",6669,1848],[\"app\",6670,6364],[\"app\",6671,855],[\"app\",6672,6023],[\"app\",6664,6673],[\"app\",6674,6364],[\"app\",3930,6356],[\"app\",6676,6354],[\"app\",6677,6359],[\"app\",6678,6364],[\"app\",6679,31],[\"app\",6680,261],[\"app\",6681,1848],[\"app\",6682,855],[\"app\",6683,855],[\"app\",6684,6036],[\"app\",6685,6038],[\"app\",6686,1638],[\"app\",6687,6023],[\"app\",6675,6688],[\"app\",2899,6689],[\"app\",6690,6347],[\"app\",6067,1980],[\"app\",6349,6692],[\"app\",1523,6693],[\"app\",4490,6694],[\"app\",3859,6695],[\"app\",383,252],[\"app\",6046,6697],[\"app\",6698,2],[\"app\",2022,6699],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2697,6700,\"default\"],[\"app\",6701,6692],[\"app\",4669,6702],[\"app\",6696,6703],[\"app\",4490,6702],[\"app\",996,6705],[\"app\",4673,6702],[\"app\",6706,6707],[\"app\",6704,6708],[\"app\",6709,31],[\"app\",6710,261],[\"app\",6711,1848],[\"app\",4677,6702],[\"app\",6712,6713],[\"app\",6714,855],[\"lam\",[\"num\",[\"str\",[\"str\",[\"num\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"x\"],\"_@\"],\"Mathlib\"],\"Data\"],\"FunLike\"],\"Basic\"],2582841819],\"_hygCtx\"],\"_hyg\"],11],6347,6715,\"default\"],[\"app\",6691,6716],[\"app\",3859,6356],[\"app\",6718,6354],[\"app\",6719,6359],[\"app\",6720,31],[\"app\",6721,261],[\"app\",6722,1848],[\"app\",6723,6364],[\"app\",6724,855],[\"app\",6647,6725],[\"app\",6726,6663],[\"app\",6727,6673],[\"app\",6728,6364],[\"app\",6729,6688],[\"app\",6717,6730],[\"app\",5285,6346],[\"app\",6731,6732],[\"app\",6094,1867],[\"app\",1464,6734],[\"app\",6097,1867],[\"app\",6735,6736],[\"app\",996,6734],[\"app\",6101,1867],[\"app\",6738,6739],[\"app\",6737,6740],[\"app\",6741,6438],[\"app\",6117,6437],[\"app\",6742,6743],[\"app\",996,6438],[\"app\",6126,6437],[\"app\",6745,6746],[\"app\",6744,6747],[\"app\",6130,1867],[\"app\",6748,6749],[\"app\",6138,6437],[\"app\",6750,6751],[\"app\",2899,6752],[\"app\",6753,6734],[\"app\",6144,6701],[\"app\",6755,6067],[\"app\",6756,1980],[\"app\",4490,6757],[\"lam\",[\"num\",[\"str\",[\"str\",[\"num\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"x\"],\"_@\"],\"Mathlib\"],\"Data\"],\"FunLike\"],\"Basic\"],2582841819],\"_hygCtx\"],\"_hyg\"],11],6734,6758,\"default\"],[\"app\",6754,6759],[\"app\",2959,6734],[\"app\",6761,6736],[\"app\",6762,6740],[\"app\",6763,6438],[\"app\",6764,6743],[\"app\",6765,6747],[\"app\",6766,6749],[\"app\",6767,6751],[\"app\",6760,6768],[\"app\",6769,2],[\"app\",6183,6470],[\"app\",6187,1867],[\"app\",6771,6772],[\"app\",996,6470],[\"app\",6191,1867],[\"app\",6774,6775],[\"app\",6773,6776],[\"app\",6777,1895],[\"app\",6196,1867],[\"app\",6778,6779],[\"app\",2899,6780],[\"app\",6781,327],[\"app\",6184,1980],[\"lam\",[\"num\",[\"str\",[\"str\",[\"num\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"x\"],\"_@\"],\"Mathlib\"],\"Data\"],\"FunLike\"],\"Basic\"],2582841819],\"_hygCtx\"],\"_hyg\"],11],327,6783,\"default\"],[\"app\",6782,6784],[\"app\",3019,6780],[\"app\",6786,327],[\"app\",6787,6470],[\"app\",6211,6470],[\"app\",6789,6772],[\"app\",6790,6776],[\"app\",6791,1895],[\"app\",6792,6779],[\"app\",6788,6793],[\"app\",6785,6794],[\"app\",6220,6470],[\"app\",6796,6772],[\"app\",6797,6776],[\"app\",6798,327],[\"app\",6799,642],[\"app\",6800,6182],[\"app\",6801,6779],[\"app\",6802,1895],[\"app\",6237,1867],[\"app\",6803,6804],[\"app\",6795,6805],[\"app\",6806,5939],[\"app\",6770,6807],[\"app\",6733,6808],[\"app\",6653,6809],[\"app\",6806,5945],[\"app\",6770,6811],[\"app\",6810,6812],[\"app\",4615,6813],[\"app\",3415,6533],[\"app\",3420,6533],[\"app\",6816,104],[\"app\",179,6533],[\"app\",4535,6532],[\"app\",6818,6819],[\"app\",6817,6820],[\"app\",4563,6532],[\"app\",6821,6822],[\"app\",6815,6823],[\"app\",1464,6555],[\"app\",2648,129],[\"app\",6825,6826],[\"app\",996,6555],[\"app\",2655,129],[\"app\",6828,6829],[\"app\",6827,6830],[\"app\",6831,6533],[\"app\",2610,6532],[\"app\",6832,6833],[\"app\",996,6533],[\"app\",2616,6532],[\"app\",6835,6836],[\"app\",6834,6837],[\"app\",2672,129],[\"app\",6838,6839],[\"app\",2624,6532],[\"app\",6840,6841],[\"app\",2899,6842],[\"app\",6843,6555],[\"app\",698,134],[\"app\",4475,6845],[\"lam\",[\"num\",[\"str\",[\"str\",[\"num\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"x\"],\"_@\"],\"Mathlib\"],\"Data\"],\"FunLike\"],\"Basic\"],2582841819],\"_hygCtx\"],\"_hyg\"],11],6555,6846,\"default\"],[\"app\",6844,6847],[\"app\",2959,6555],[\"app\",6849,6826],[\"app\",6850,6830],[\"app\",6851,6533],[\"app\",6852,6833],[\"app\",6853,6837],[\"app\",6854,6839],[\"app\",6855,6841],[\"app\",6848,6856],[\"app\",5896,129],[\"app\",6857,6858],[\"app\",3000,6555],[\"app\",6860,6826],[\"app\",6861,6830],[\"app\",6862,3007],[\"app\",6863,6839],[\"app\",2899,6864],[\"app\",6865,328],[\"app\",5909,134],[\"lam\",[\"num\",[\"str\",[\"str\",[\"num\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"x\"],\"_@\"],\"Mathlib\"],\"Data\"],\"FunLike\"],\"Basic\"],2582841819],\"_hygCtx\"],\"_hyg\"],11],328,6867,\"default\"],[\"app\",6866,6868],[\"app\",3019,6864],[\"app\",6870,328],[\"app\",6871,6555],[\"app\",3034,6555],[\"app\",6873,6826],[\"app\",6874,6830],[\"app\",6875,3007],[\"app\",6876,6839],[\"app\",6872,6877],[\"app\",6869,6878],[\"app\",3050,6555],[\"app\",6880,6826],[\"app\",6881,6830],[\"app\",6882,328],[\"app\",6883,351],[\"app\",6884,1210],[\"app\",6885,6839],[\"app\",6886,3007],[\"app\",5934,129],[\"app\",6887,6888],[\"app\",6879,6889],[\"app\",6890,5940],[\"app\",6859,6891],[\"app\",6824,6892],[\"app\",6890,5946],[\"app\",6859,6894],[\"app\",6893,6895],[\"app\",6814,6896],[\"lam\",[\"str\",[\"anonymous\"],\"_a\"],6630,6897,\"default\"],[\"app\",6640,6898],[\"app\",321,27],[\"app\",6900,2],[\"app\",6899,6901],[\"app\",6615,6902],[\"app\",6611,6903],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Eq\"],\"refl\"],[[\"succ\",[\"zero\"]]]],[\"app\",6905,31],[\"app\",6906,6608],[\"app\",6904,6907],[\"app\",6252,6908],[\"app\",5953,6909],[\"lam\",[\"str\",[\"anonymous\"],\"hq\"],3377,6910,\"default\"],[\"lam\",[\"str\",[\"anonymous\"],\"q\"],328,6911,\"strictImplicit\"],[\"app\",5829,6912],[\"lam\",[\"str\",[\"anonymous\"],\"j\"],156,6913,\"default\"],[\"lam\",[\"str\",[\"anonymous\"],\"i\"],156,6914,\"default\"],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"ContinuousOn\"],\"sqrt\"],[[\"zero\"]]],[\"app\",6916,328],[\"app\",6917,427],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Matrix\"],\"det\"],[[\"zero\"],[\"zero\"]]],[\"app\",6919,156],[\"app\",6920,3085],[\"app\",6921,168],[\"app\",6922,31],[\"app\",6923,869],[\"app\",3387,2020],[\"app\",6925,2022],[\"app\",6926,1523],[\"app\",6927,1525],[\"app\",6928,1527],[\"app\",6929,1116],[\"app\",142,1116],[\"app\",379,2065],[\"app\",6932,1757],[\"app\",6933,2],[\"app\",1116,6934],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],6931,6935,\"default\"],[\"app\",6930,6936],[\"app\",6937,698],[\"app\",6938,399],[\"app\",6924,6939],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],328,6940,\"default\"],[\"app\",6918,6941],[\"app\",313,403],[\"app\",6943,408],[\"app\",362,6944],[\"app\",366,1533],[\"app\",6946,157],[\"app\",370,1118],[\"app\",6948,488],[\"app\",6947,6949],[\"app\",6945,6950],[\"app\",6942,6951],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Continuous\"],\"comp_continuousOn\"],[[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",6953,328],[\"const\",[\"str\",[\"anonymous\"],\"Matrix\"],[[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",6955,156],[\"app\",6956,156],[\"app\",6957,31],[\"app\",6954,6958],[\"app\",6959,31],[\"app\",6960,427],[\"const\",[\"str\",[\"anonymous\"],\"instTopologicalSpaceMatrix\"],[[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",6962,156],[\"app\",6963,156],[\"app\",6964,31],[\"app\",6965,261],[\"app\",6961,6966],[\"app\",6967,261],[\"app\",3268,6958],[\"app\",6969,2],[\"app\",6924,6970],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],6958,6971,\"default\"],[\"app\",6968,6972],[\"const\",[\"str\",[\"anonymous\"],\"PartialEquiv\"],[[\"zero\"],[\"zero\"]]],[\"app\",6974,6931],[\"app\",6975,157],[\"app\",596,6931],[\"app\",6977,5959],[\"app\",6978,36],[\"app\",6979,171],[\"app\",6980,197],[\"app\",6981,5964],[\"app\",263,1116],[\"app\",6982,6983],[\"app\",6984,5968],[\"app\",280,1116],[\"app\",6985,6986],[\"app\",6987,698],[\"app\",3394,1535],[\"app\",6989,2],[\"app\",1527,6990],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2065,6991,\"default\"],[\"app\",387,2065],[\"app\",389,2065],[\"app\",6994,157],[\"app\",6995,2],[\"app\",6993,6996],[\"app\",6997,1484],[\"app\",6992,6998],[\"app\",6274,1881],[\"app\",7000,2],[\"app\",1525,7001],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2149,7002,\"default\"],[\"app\",6408,7003],[\"app\",6256,27],[\"app\",6254,7005],[\"app\",7004,7006],[\"app\",7007,1867],[\"app\",3487,7008],[\"app\",6741,7009],[\"app\",6416,7008],[\"app\",7010,7011],[\"app\",996,7009],[\"app\",6422,7008],[\"app\",7013,7014],[\"app\",7012,7015],[\"app\",7016,6749],[\"app\",6430,7008],[\"app\",7017,7018],[\"app\",6452,7007],[\"app\",2151,27],[\"app\",7020,7021],[\"app\",7022,1867],[\"app\",4654,134],[\"app\",3859,7024],[\"app\",4851,134],[\"app\",7025,7026],[\"app\",996,7024],[\"app\",4855,134],[\"app\",7028,7029],[\"app\",7027,7030],[\"app\",7031,31],[\"app\",7032,261],[\"app\",7033,1848],[\"app\",4859,134],[\"app\",7034,7035],[\"app\",7036,855],[\"app\",2899,7037],[\"app\",7038,7024],[\"lam\",[\"num\",[\"str\",[\"str\",[\"num\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"x\"],\"_@\"],\"Mathlib\"],\"Data\"],\"FunLike\"],\"Basic\"],2582841819],\"_hygCtx\"],\"_hyg\"],11],7024,31,\"default\"],[\"app\",7039,7040],[\"app\",4749,7024],[\"app\",7042,7026],[\"app\",7043,7030],[\"app\",7044,31],[\"app\",7045,261],[\"app\",7046,1848],[\"app\",7047,7035],[\"app\",7048,855],[\"app\",7041,7049],[\"app\",7031,7037],[\"app\",3895,7024],[\"app\",7052,31],[\"app\",7053,7029],[\"app\",7054,7035],[\"app\",7055,851],[\"app\",7056,855],[\"app\",7057,7026],[\"app\",7058,261],[\"app\",7059,3904],[\"app\",7051,7060],[\"app\",3912,7024],[\"app\",7062,7026],[\"app\",7063,7030],[\"app\",7064,31],[\"app\",7065,261],[\"app\",7066,1848],[\"app\",7067,7035],[\"app\",7068,855],[\"app\",7069,6023],[\"app\",7061,7070],[\"app\",7071,7035],[\"app\",3930,7024],[\"app\",7073,7026],[\"app\",7074,7030],[\"app\",7075,7035],[\"app\",7076,31],[\"app\",7077,261],[\"app\",7078,1848],[\"app\",7079,855],[\"app\",7080,855],[\"app\",7081,6036],[\"app\",7082,6038],[\"app\",7083,1638],[\"app\",7084,6023],[\"app\",7072,7085],[\"app\",2899,7086],[\"app\",7087,7024],[\"app\",4836,252],[\"app\",3859,7089],[\"app\",3509,4818],[\"app\",7091,4636],[\"app\",7092,4472],[\"app\",7093,252],[\"app\",7090,7094],[\"app\",996,7089],[\"app\",3516,4818],[\"app\",7097,4636],[\"app\",7098,4472],[\"app\",7099,252],[\"app\",7096,7100],[\"app\",7095,7101],[\"app\",7102,31],[\"app\",7103,261],[\"app\",7104,1848],[\"app\",3523,4818],[\"app\",7106,4636],[\"app\",7107,4472],[\"app\",7108,252],[\"app\",7105,7109],[\"app\",7110,855],[\"lam\",[\"num\",[\"str\",[\"str\",[\"num\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"x\"],\"_@\"],\"Mathlib\"],\"Data\"],\"FunLike\"],\"Basic\"],2582841819],\"_hygCtx\"],\"_hyg\"],11],7024,7111,\"default\"],[\"app\",7088,7112],[\"app\",7044,7037],[\"app\",7114,7060],[\"app\",7115,7070],[\"app\",7116,7035],[\"app\",7117,7085],[\"app\",7113,7118],[\"app\",4942,4636],[\"app\",7120,4472],[\"app\",7121,2598],[\"app\",7122,3478],[\"app\",7123,73],[\"app\",7124,3430],[\"app\",7125,4838],[\"app\",7126,4847],[\"app\",7127,4851],[\"app\",7128,4855],[\"app\",7129,4859],[\"app\",7130,4864],[\"app\",7131,4869],[\"app\",7132,2018],[\"app\",7133,134],[\"app\",7119,7134],[\"app\",6094,2400],[\"app\",1464,7136],[\"app\",6097,2400],[\"app\",7137,7138],[\"app\",996,7136],[\"app\",6101,2400],[\"app\",7140,7141],[\"app\",7139,7142],[\"app\",1529,6045],[\"app\",7144,4636],[\"app\",142,2018],[\"app\",379,7146],[\"app\",383,145],[\"app\",7147,7148],[\"app\",7149,2],[\"app\",2020,7150],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],6045,7151,\"default\"],[\"app\",7145,7152],[\"app\",387,6045],[\"app\",389,6045],[\"app\",7155,157],[\"app\",7156,252],[\"app\",7154,7157],[\"app\",7153,7158],[\"app\",7159,2400],[\"app\",4654,7160],[\"app\",7143,7161],[\"app\",6114,4636],[\"app\",7163,4472],[\"app\",7164,2598],[\"app\",7165,7160],[\"app\",7162,7166],[\"app\",996,7161],[\"app\",6123,4636],[\"app\",7169,4472],[\"app\",7170,2598],[\"app\",7171,7160],[\"app\",7168,7172],[\"app\",7167,7173],[\"app\",6130,2400],[\"app\",7174,7175],[\"app\",6135,4636],[\"app\",7177,4472],[\"app\",7178,2598],[\"app\",7179,7160],[\"app\",7176,7180],[\"app\",2899,7181],[\"app\",7182,7136],[\"app\",1529,7146],[\"app\",7184,4818],[\"app\",142,2409],[\"app\",379,7186],[\"app\",383,294],[\"app\",7187,7188],[\"app\",7189,2],[\"app\",2018,7190],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],7146,7191,\"default\"],[\"app\",7185,7192],[\"app\",387,7146],[\"app\",389,7146],[\"app\",7195,157],[\"app\",7196,321],[\"app\",7194,7197],[\"app\",7193,7198],[\"app\",7199,2589],[\"app\",4836,7200],[\"lam\",[\"num\",[\"str\",[\"str\",[\"num\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"x\"],\"_@\"],\"Mathlib\"],\"Data\"],\"FunLike\"],\"Basic\"],2582841819],\"_hygCtx\"],\"_hyg\"],11],7136,7201,\"default\"],[\"app\",7183,7202],[\"app\",2959,7136],[\"app\",7204,7138],[\"app\",7205,7142],[\"app\",7206,7161],[\"app\",7207,7166],[\"app\",7208,7173],[\"app\",7209,7175],[\"app\",7210,7180],[\"app\",7203,7211],[\"app\",7212,129],[\"app\",6184,2400],[\"app\",6183,7214],[\"app\",6187,2400],[\"app\",7215,7216],[\"app\",996,7214],[\"app\",6191,2400],[\"app\",7218,7219],[\"app\",7217,7220],[\"app\",7221,1895],[\"app\",6196,2400],[\"app\",7222,7223],[\"app\",2899,7224],[\"app\",7225,327],[\"app\",6184,2589],[\"lam\",[\"num\",[\"str\",[\"str\",[\"num\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"x\"],\"_@\"],\"Mathlib\"],\"Data\"],\"FunLike\"],\"Basic\"],2582841819],\"_hygCtx\"],\"_hyg\"],11],327,7227,\"default\"],[\"app\",7226,7228],[\"app\",3019,7224],[\"app\",7230,327],[\"app\",7231,7214],[\"app\",6211,7214],[\"app\",7233,7216],[\"app\",7234,7220],[\"app\",7235,1895],[\"app\",7236,7223],[\"app\",7232,7237],[\"app\",7229,7238],[\"app\",6220,7214],[\"app\",7240,7216],[\"app\",7241,7220],[\"app\",7242,327],[\"app\",7243,642],[\"app\",7244,6182],[\"app\",7245,7223],[\"app\",7246,1895],[\"app\",6237,2400],[\"app\",7247,7248],[\"app\",7239,7249],[\"app\",7250,3093],[\"app\",7213,7251],[\"app\",7135,7252],[\"app\",7050,7253],[\"app\",3086,2],[\"app\",7255,3092],[\"app\",7250,7256],[\"app\",7213,7257],[\"app\",7254,7258],[\"lam\",[\"str\",[\"anonymous\"],\"j\"],156,7259,\"default\"],[\"lam\",[\"str\",[\"anonymous\"],\"i\"],156,7260,\"default\"],[\"let\",[\"str\",[\"anonymous\"],\"d\"],7019,7023,7261,true],[\"let\",[\"str\",[\"anonymous\"],\"q\"],2018,6999,7262,true],[\"let\",[\"str\",[\"anonymous\"],\"e\"],6976,6988,7263,true],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],328,7264,\"default\"],[\"app\",6973,7265],[\"app\",7266,6951],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Continuous\"],\"matrix_det\"],[[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",7268,6958],[\"app\",7269,156],[\"app\",7270,31],[\"app\",7271,6966],[\"app\",7272,261],[\"app\",7273,168],[\"app\",7274,3085],[\"app\",7275,869],[\"app\",7276,883],[\"app\",7277,6969],[\"app\",3273,6958],[\"app\",7279,6966],[\"app\",7278,7280],[\"app\",7267,7281],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Iff\"],\"mpr\"],[]],[\"forall\",[\"str\",[\"anonymous\"],\"j\"],156,31,\"default\"],[\"forall\",[\"str\",[\"anonymous\"],\"i\"],156,7284,\"default\"],[\"app\",2864,7285],[\"app\",7286,427],[\"const\",[\"str\",[\"str\",[\"anonymous\"],\"Pi\"],\"topologicalSpace\"],[[\"zero\"],[\"zero\"]]],[\"app\",7288,156],[\"lam\",[\"str\",[\"anonymous\"],\"i\"],156,7284,\"default\"],[\"app\",7289,7290],[\"lam\",[\"num\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"a\"],\"_@\"],\"_internal\"],\"_hyg\"],0],156,31,\"default\"],[\"app\",7289,7292],[\"app\",7293,425],[\"lam\",[\"str\",[\"anonymous\"],\"i\"],156,7294,\"default\"],[\"app\",7291,7295],[\"app\",7287,7296],[\"app\",7297,7265],[\"app\",7298,6951],[\"app\",7283,7299],[\"app\",2864,7284],[\"app\",7301,427],[\"app\",7302,7294],[\"app\",2899,6376],[\"app\",7304,6282],[\"lam\",[\"num\",[\"str\",[\"str\",[\"num\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"x\"],\"_@\"],\"Mathlib\"],\"Data\"],\"FunLike\"],\"Basic\"],2582841819],\"_hygCtx\"],\"_hyg\"],11],6282,31,\"default\"],[\"app\",7305,7306],[\"app\",7307,6304],[\"app\",6371,6376],[\"app\",7309,6315],[\"app\",7310,6325],[\"app\",7311,6290],[\"app\",7312,6340],[\"app\",2899,7313],[\"app\",7314,6282],[\"lam\",[\"num\",[\"str\",[\"str\",[\"num\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"x\"],\"_@\"],\"Mathlib\"],\"Data\"],\"FunLike\"],\"Basic\"],2582841819],\"_hygCtx\"],\"_hyg\"],11],6282,6725,\"default\"],[\"app\",7315,7316],[\"app\",7317,6381],[\"app\",6396,6279],[\"app\",7318,7319],[\"app\",7320,6499],[\"app\",7308,7321],[\"app\",6493,7256],[\"app\",6457,7323],[\"app\",7322,7324],[\"lam\",[\"str\",[\"anonymous\"],\"j\"],156,7325,\"default\"],[\"lam\",[\"str\",[\"anonymous\"],\"y\"],328,7326,\"default\"],[\"app\",7303,7327],[\"app\",313,725],[\"app\",7329,403],[\"app\",362,7330],[\"app\",366,6931],[\"app\",7332,157],[\"app\",370,1116],[\"app\",7334,698],[\"app\",7333,7335],[\"app\",7331,7336],[\"app\",7328,7337],[\"forall\",[\"str\",[\"anonymous\"],\"i\"],156,7338,\"default\"],[\"app\",7300,7339],[\"const\",[\"str\",[\"anonymous\"],\"continuousOn_pi\"],[[\"zero\"],[\"zero\"],[\"zero\"]]],[\"app\",7341,328],[\"app\",7342,427],[\"app\",7343,156],[\"app\",7344,7290],[\"app\",7345,7295],[\"app\",7346,7265],[\"app\",7347,6951],[\"app\",7340,7348],[\"forall\",[\"str\",[\"anonymous\"],\"i\"],156,31,\"default\"],[\"app\",2864,7350],[\"app\",7351,427],[\"lam\",[\"str\",[\"anonymous\"],\"i\"],156,31,\"default\"],[\"app\",7289,7353],[\"app\",7354,425],[\"app\",7352,7355],[\"app\",7356,7327],[\"app\",7357,7337],[\"app\",7283,7358],[\"app\",6274,1757],[\"app\",7360,2],[\"app\",1525,7361],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2149,7362,\"default\"],[\"app\",6268,399],[\"app\",7363,7364],[\"app\",3487,7365],[\"app\",3859,7366],[\"app\",4073,7365],[\"app\",7367,7368],[\"app\",996,7366],[\"app\",4077,7365],[\"app\",7370,7371],[\"app\",7369,7372],[\"app\",7373,31],[\"app\",7374,261],[\"app\",7375,1848],[\"app\",4081,7365],[\"app\",7376,7377],[\"app\",7378,855],[\"app\",2899,7379],[\"app\",7380,7366],[\"lam\",[\"num\",[\"str\",[\"str\",[\"num\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"x\"],\"_@\"],\"Mathlib\"],\"Data\"],\"FunLike\"],\"Basic\"],2582841819],\"_hygCtx\"],\"_hyg\"],11],7366,31,\"default\"],[\"app\",7381,7382],[\"app\",4749,7366],[\"app\",7384,7368],[\"app\",7385,7372],[\"app\",7386,31],[\"app\",7387,261],[\"app\",7388,1848],[\"app\",7389,7377],[\"app\",7390,855],[\"app\",7383,7391],[\"app\",7373,7379],[\"app\",3895,7366],[\"app\",7394,31],[\"app\",7395,7371],[\"app\",7396,7377],[\"app\",7397,851],[\"app\",7398,855],[\"app\",7399,7368],[\"app\",7400,261],[\"app\",7401,3904],[\"app\",7393,7402],[\"app\",3912,7366],[\"app\",7404,7368],[\"app\",7405,7372],[\"app\",7406,31],[\"app\",7407,261],[\"app\",7408,1848],[\"app\",7409,7377],[\"app\",7410,855],[\"app\",7411,6023],[\"app\",7403,7412],[\"app\",7413,7377],[\"app\",3930,7366],[\"app\",7415,7368],[\"app\",7416,7372],[\"app\",7417,7377],[\"app\",7418,31],[\"app\",7419,261],[\"app\",7420,1848],[\"app\",7421,855],[\"app\",7422,855],[\"app\",7423,6036],[\"app\",7424,6038],[\"app\",7425,1638],[\"app\",7426,6023],[\"app\",7414,7427],[\"app\",2899,7428],[\"app\",7429,7366],[\"app\",5837,1535],[\"app\",7431,2],[\"app\",1523,7432],[\"lam\",[\"str\",[\"anonymous\"],\"x\"],2327,7433,\"default\"],[\"app\",5974,1484],[\"app\",7434,7435],[\"app\",4058,7436],[\"app\",3859,7437],[\"app\",4505,7436],[\"app\",7438,7439],[\"app\",996,7437],[\"app\",4509,7436],[\"app\",7441,7442],[\"app\",7440,7443],[\"app\",7444,31],[\"app\",7445,261],[\"app\",7446,1848],[\"app\",4513,7436],[\"app\",7447,7448],[\"app\",7449,855],[\"lam\",[\"num\",[\"str\",[\"str\",[\"num\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"x\"],\"_@\"],\"Mathlib\"],\"Data\"],\"FunLike\"],\"Basic\"],2582841819],\"_hygCtx\"],\"_hyg\"],11],7366,7450,\"default\"],[\"app\",7430,7451],[\"app\",7386,7379],[\"app\",7453,7402],[\"app\",7454,7412],[\"app\",7455,7377],[\"app\",7456,7427],[\"app\",7452,7457],[\"app\",6396,7365],[\"app\",7458,7459],[\"app\",6408,7363],[\"app\",7461,6268],[\"app\",7462,399],[\"app\",3487,7463],[\"app\",6104,7464],[\"app\",6416,7463],[\"app\",7465,7466],[\"app\",996,7464],[\"app\",6422,7463],[\"app\",7468,7469],[\"app\",7467,7470],[\"app\",7471,6131],[\"app\",6430,7463],[\"app\",7472,7473],[\"app\",2899,7474],[\"app\",7475,6095],[\"app\",6106,7434],[\"app\",7477,5974],[\"app\",7478,1484],[\"app\",4058,7479],[\"lam\",[\"num\",[\"str\",[\"str\",[\"num\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"x\"],\"_@\"],\"Mathlib\"],\"Data\"],\"FunLike\"],\"Basic\"],2582841819],\"_hygCtx\"],\"_hyg\"],11],6095,7480,\"default\"],[\"app\",7476,7481],[\"app\",6153,7464],[\"app\",7483,7466],[\"app\",7484,7470],[\"app\",7485,6131],[\"app\",7486,7473],[\"app\",7482,7487],[\"app\",6452,7462],[\"app\",7489,6454],[\"app\",7490,399],[\"app\",7488,7491],[\"app\",6240,3248],[\"app\",7492,7493],[\"app\",7460,7494],[\"app\",7392,7495],[\"app\",6240,3093],[\"app\",7492,7497],[\"app\",7496,7498],[\"lam\",[\"str\",[\"anonymous\"],\"y\"],328,7499,\"default\"],[\"app\",3386,7500],[\"app\",362,2386],[\"app\",7502,2070],[\"app\",7501,7503],[\"forall\",[\"str\",[\"anonymous\"],\"i\"],156,7504,\"default\"],[\"app\",7359,7505],[\"app\",7344,7353],[\"app\",7507,425],[\"app\",7508,7327],[\"app\",7509,7337],[\"app\",7506,7510],[\"app\",5825,2],[\"lam\",[\"str\",[\"anonymous\"],\"j\"],156,7512,\"default\"],[\"app\",7511,7513],[\"lam\",[\"str\",[\"anonymous\"],\"i\"],156,7514,\"default\"],[\"app\",7349,7515],[\"app\",7282,7516],[\"app\",6952,7517],[\"let\",[\"str\",[\"anonymous\"],\"hgram\"],3408,6915,7518,true],[\"let\",[\"str\",[\"anonymous\"],\"hv\"],3101,3383,7519,true],[\"let\",[\"str\",[\"anonymous\"],\"hd\"],1802,2863,7520,true],[\"let\",[\"str\",[\"anonymous\"],\"ht\"],1330,1438,7521,true],[\"let\",[\"str\",[\"anonymous\"],\"hUD\"],837,1095,7522,true],[\"let\",[\"str\",[\"anonymous\"],\"h\\u03a6\"],731,824,7523,true],[\"let\",[\"str\",[\"anonymous\"],\"hpre\"],454,714,7524,true],[\"let\",[\"str\",[\"anonymous\"],\"\\u03a6\"],404,411,7525,false],[\"let\",[\"str\",[\"anonymous\"],\"pre\"],377,402,7526,false],[\"let\",[\"str\",[\"anonymous\"],\"D\"],356,374,7527,false],[\"let\",[\"str\",[\"anonymous\"],\"I\"],352,355,7528,false],[\"lam\",[\"str\",[\"anonymous\"],\"p\"],322,7529,\"default\"],[\"lam\",[\"str\",[\"anonymous\"],\"hH\"],320,7530,\"default\"],[\"lam\",[\"str\",[\"anonymous\"],\"hab\"],152,7531,\"default\"],[\"lam\",[\"str\",[\"anonymous\"],\"b\"],31,7532,\"implicit\"],[\"lam\",[\"str\",[\"anonymous\"],\"a\"],31,7533,\"implicit\"],[\"lam\",[\"str\",[\"anonymous\"],\"H\"],146,7534,\"default\"],[\"lam\",[\"str\",[\"anonymous\"],\"S\"],139,7535,\"implicit\"],[\"lam\",[\"str\",[\"anonymous\"],\"g\"],138,7536,\"default\"],[\"lam\",[\"num\",[\"str\",[\"str\",[\"num\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"inst\"],\"_@\"],\"OriginalB2B5V480\"],3706074420],\"_hygCtx\"],\"_hyg\"],13],132,7537,\"instImplicit\"],[\"lam\",[\"num\",[\"str\",[\"str\",[\"num\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"inst\"],\"_@\"],\"OriginalB2B5V480\"],3706074420],\"_hygCtx\"],\"_hyg\"],6],29,7538,\"instImplicit\"],[\"lam\",[\"num\",[\"str\",[\"str\",[\"num\",[\"str\",[\"str\",[\"str\",[\"anonymous\"],\"inst\"],\"_@\"],\"OriginalB2B5V480\"],3706074420],\"_hygCtx\"],\"_hyg\"],3],3,7539,\"instImplicit\"],[\"lam\",[\"str\",[\"anonymous\"],\"M\"],0,7540,\"implicit\"]],\"root\":7541}}"

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
end

-- Exact source from B2CompactIntegralContinuityV480.lean

noncomputable section
open Set Topology Function Filter MeasureTheory
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

/-- A jointly continuous integrand over an arbitrary measurable subset of a
compact coordinate domain has a continuous parameter integral. -/
theorem compact_coordinate_setIntegral_continuous_v480
    {a b : ℝ} (F : ℝ × Euc 2 → ℝ) {K B : Set (Euc 2)}
    (hK : IsCompact K) (hB : MeasurableSet B) (hBK : B ⊆ K)
    (hF : ContinuousOn F (Icc a b ×ˢ K)) :
    Continuous (fun t : Icc a b => ∫ y in B, F (t.val,y)) := by
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod hK).bddAbove_image hF.norm
  rw [continuous_iff_continuousAt]
  intro t0
  apply continuousAt_of_dominated (bound := fun _ : Euc 2 => C)
  · exact Filter.Eventually.of_forall (fun t =>
      ((hF.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun y hy => ⟨t.property,hBK hy⟩))).aestronglyMeasurable hB)
  · exact Filter.Eventually.of_forall (fun t => by
      filter_upwards [ae_restrict_mem hB] with y hy
      exact hC (mem_image_of_mem _ ⟨t.property,hBK hy⟩))
  · exact integrableOn_const (measure_mono hBK |>.trans_lt hK.measure_lt_top).ne
  · filter_upwards [ae_restrict_mem hB] with y hy
    exact (hF.comp_continuous (continuous_subtype_val.prodMk continuous_const)
      (fun t => ⟨t.property,hBK hy⟩)).continuousAt.tendsto

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
end

-- Exact source from B2ActualAreaContinuityV480.lean

noncomputable section
open Set Topology Function Filter MeasureTheory
open scoped Manifold ContDiff BigOperators
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.MetricFoundations.AreaAnalysis
variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

/-- The frozen common-refinement proof applies to every smooth map, without
requiring an embedding or a positive density. -/
theorem smooth_map_partition_area_independent_v480
    (g : SmoothMetric M) {S : CompactOrientedSurface.{0}} (f : S → M)
    (hf : ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ f) (P Q : ChartPartition S) :
    partitionArea g f P = partitionArea g f Q := by
  have hsum := partitionArea_pairwise_sum g f hf P Q
  rw [hsum.1,hsum.2,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  exact coordinateIntegral_overlap g f hf (P.center i) (Q.center j) _
    (commonPiece_measurable P Q i j) (commonPiece_subordinate P Q i j)

/-- Continuity of the actual canonical-partition geometric area for a jointly
smooth family, up to the closed parameter slab and surface boundary. -/
theorem jointly_smooth_actual_area_continuous_v480
    (g : SmoothMetric M) {S : CompactOrientedSurface.{0}}
    (H : ℝ × S → M) {a b : ℝ} (hab : a < b)
    (hH : ContMDiffOn (𝓘(ℝ).prod (𝓡∂ 2)) (𝓡∂ 3) ∞ H (Icc a b ×ˢ univ)) :
    Continuous (fun t : Icc a b => area g (fun x => H (t.val,x))) := by
  classical
  let C := Classical.choice (compactChartCover_exists S)
  have hcover := compactChartCover_disjoint_refinement C
  let P : ChartPartition S := {
    count := C.count
    center := C.center
    piece := compactCoverPiece C
    measurable := hcover.1
    subordinate := fun k => (hcover.2.1 k).2.trans (C.subordinate k)
    disjoint := hcover.2.2.1
    covers := hcover.2.2.2 }
  have hslice (t : Icc a b) : ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ (fun x => H (t.val,x)) :=
    hH.comp_contMDiff (contMDiff_const.prodMk contMDiff_id) (fun x => ⟨t.property,mem_univ x⟩)
  have hpart (k : Fin C.count) : Continuous (fun t : Icc a b =>
      coordinateIntegral g (fun x => H (t.val,x)) (C.center k) (compactCoverPiece C k)) := by
    let K := (surfaceChart (C.center k)) '' C.compactSet k
    let B := (surfaceChart (C.center k)) '' compactCoverPiece C k
    have hK : IsCompact K := (C.isCompact k).image_of_continuousOn
      ((continuousOn_extChartAt (C.center k)).mono (C.subordinate k))
    have hB : MeasurableSet B := extChart_image_measurable _ _ (hcover.1 k)
      ((hcover.2.1 k).2.trans (C.subordinate k))
    have hBK : B ⊆ K := image_mono (hcover.2.1 k).2
    change Continuous (fun t : Icc a b => ∫ y in B,
      coordinateAreaDensity g (fun x => H (t.val,x)) (C.center k) y)
    apply compact_coordinate_setIntegral_continuous_v480
      (fun q => coordinateAreaDensity g (fun x => H (q.1,x)) (C.center k) q.2) hK hB hBK
    exact (jointly_smooth_coordinate_density_continuous_v480 g H hab hH (C.center k)).mono
      (fun q hq => ⟨hq.1,extChart_image_subset_target _ _ (C.subordinate k) hq.2⟩)
  have hsum : Continuous (fun t : Icc a b =>
      ∑ k : Fin C.count, coordinateIntegral g (fun x => H (t.val,x))
        (C.center k) (compactCoverPiece C k)) := continuous_finset_sum _ (fun k _ => hpart k)
  apply hsum.congr
  intro t
  change partitionArea g (fun x => H (t.val,x)) P =
    partitionArea g (fun x => H (t.val,x)) (canonicalPartition S)
  exact smooth_map_partition_area_independent_v480 g _ (hslice t) P _

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
end

-- Exact source from B2CollarActualAreaV480.lean

noncomputable section
open Set Topology Function Filter MeasureTheory
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

/-- The literal area of the supplied collar slices is continuous at time zero,
including the source surface boundary. -/
theorem actual_collar_area_continuous_v480
    (g : SmoothMetric M) {S : CompactOrientedSurface.{0}}
    {F : NeatEmbedding S M} {U : Set M} (collar : OneSidedCollar F U) :
    Continuous (fun t : Icc (0 : ℝ) (collar.epsilon / 2) =>
      area g (fun x => collar.map (x,t.val))) := by
  apply jointly_smooth_actual_area_continuous_v480 g
    (fun q : ℝ × S => collar.map (q.2,q.1)) (half_pos collar.epsilon_pos)
  apply collar.smooth.comp (contMDiff_snd.prodMk contMDiff_fst).contMDiffOn
  intro q hq
  exact ⟨mem_univ q.2, hq.1.1,
    hq.1.2.trans_lt (half_lt_self collar.epsilon_pos)⟩

/-- Every positive requested error can be met at a positive actual collar
time; no area rate or joint regularity of the choice is assumed. -/
theorem actual_collar_positive_time_area_cost_v480
    (g : SmoothMetric M) {S : CompactOrientedSurface.{0}}
    {F : NeatEmbedding S M} {U : Set M} (collar : OneSidedCollar F U)
    {sigma : ℝ} (hsigma : 0 < sigma) :
    ∃ t : ℝ, t ∈ Ioo (0 : ℝ) collar.epsilon ∧
      area g (fun x => collar.map (x,t)) - area g F.toFun ≤ sigma := by
  let z : Icc (0 : ℝ) (collar.epsilon / 2) :=
    ⟨0,⟨le_rfl,(half_pos collar.epsilon_pos).le⟩⟩
  obtain ⟨delta,hdelta,hclose⟩ := Metric.continuousAt_iff.mp
    (actual_collar_area_continuous_v480 g collar).continuousAt sigma hsigma
  let t := min (delta / 2) (collar.epsilon / 4)
  have htpos : 0 < t := lt_min (half_pos hdelta) (div_pos collar.epsilon_pos (by norm_num))
  have hteps : t < collar.epsilon :=
    (min_le_right _ _).trans_lt (by linarith [collar.epsilon_pos])
  let t' : Icc (0 : ℝ) (collar.epsilon / 2) :=
    ⟨t,⟨htpos.le,(min_le_right _ _).trans (by linarith [collar.epsilon_pos])⟩⟩
  have hdist : dist t' z < delta := by
    change dist t (0 : ℝ) < delta
    rw [Real.dist_eq,sub_zero,abs_of_pos htpos]
    exact (min_le_left _ _).trans_lt (half_lt_self hdelta)
  have h := hclose hdist
  change dist (area g (fun x => collar.map (x,t)))
    (area g (fun x => collar.map (x,0))) < sigma at h
  rw [collar_slice_zero collar,Real.dist_eq] at h
  exact ⟨t,⟨htpos,hteps⟩,(abs_lt.mp h).2.le⟩

/-- All geometric and quantitative B2 clauses for the actual collar-slice
family. The longitude correction is a separate construction. -/
theorem actual_collar_push_off_area_family_v480 [T2Space M] [SecondCountableTopology M]
    (g : SmoothMetric M) {S : CompactOrientedSurface.{0}}
    (F : NeatEmbedding S M) (U : Set M) (collar : OneSidedCollar F U) :
    ∃ sigma0 C : ℝ, 0 < sigma0 ∧ 0 ≤ C ∧
      ∃ pushed : ℝ → NeatEmbedding S M,
        (∀ sigma ∈ Ioc (0 : ℝ) sigma0,
          (pushed sigma).image ⊆ U ∧
          SmoothAmbientIsotopy.Rel F.image (pushed sigma).image ∧
          area g (pushed sigma).toFun - area g F.toFun ≤ C * sigma) ∧
        (∀ sigma ∈ Ioc (0 : ℝ) sigma0, ∀ sigma' ∈ Ioc (0 : ℝ) sigma0,
          SmoothAmbientIsotopy.Rel (pushed sigma).image (pushed sigma').image) := by
  classical
  have htime (sigma : ℝ) (hs : 0 < sigma) :=
    actual_collar_positive_time_area_cost_v480 g collar hs
  let time (sigma : ℝ) (hs : 0 < sigma) := Classical.choose (htime sigma hs)
  have htimelegal (sigma : ℝ) (hs : 0 < sigma) :
      time sigma hs ∈ Ico (0 : ℝ) collar.epsilon :=
    ⟨(Classical.choose_spec (htime sigma hs)).1.1.le,
      (Classical.choose_spec (htime sigma hs)).1.2⟩
  let pushed : ℝ → NeatEmbedding S M := fun sigma =>
    if hs : 0 < sigma then collar_slice_neat collar (htimelegal sigma hs) else F
  refine ⟨1,1,by norm_num,by norm_num,pushed,?_,?_⟩
  · intro sigma hs
    dsimp only [pushed]
    rw [dif_pos hs.1,one_mul]
    exact ⟨collar_slice_image_subset collar (Classical.choose_spec (htime sigma hs.1)).1,
      collar_initial_ambient_related collar (htimelegal sigma hs.1),
      (Classical.choose_spec (htime sigma hs.1)).2⟩
  · intro sigma hs sigma' hs'
    dsimp only [pushed]
    rw [dif_pos hs.1,dif_pos hs'.1]
    exact collar_slices_ambient_related collar (htimelegal sigma hs.1) (htimelegal sigma' hs'.1)

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
end

-- Exact source from B2VariableCollarGeometryV480.lean

noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.OriginalEndpoints.A7Support
variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]
variable {S : CompactOrientedSurface.{0}} {F : NeatEmbedding S M} {U : Set M}
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- Smooth variable time in the actual supplied collar gives an embedded
surface, with the literal half-space tangent derivative. -/
theorem collar_variable_time_differential_v480 (collar : OneSidedCollar F U)
    (tau : S → ℝ) (htau : ContMDiff (𝓡∂ 2) 𝓘(ℝ) ∞ tau)
    (hlegal : ∀ x, tau x ∈ Ico (0 : ℝ) collar.epsilon) (x : S) :
    mfderiv (𝓡∂ 2) (𝓡∂ 3) (fun y => collar.map (y,tau y)) x =
      (mfderivWithin ((𝓡∂ 2).prod 𝓘(ℝ)) (𝓡∂ 3) collar.map
        (univ ×ˢ Ico (0 : ℝ) collar.epsilon) (x,tau x)).comp
        ((ContinuousLinearMap.id ℝ (TangentSpace (𝓡∂ 2) x)).prod
          (mfderiv (𝓡∂ 2) 𝓘(ℝ) tau x)) := by
  let lift : S → S × ℝ := fun y => (y,tau y)
  have hlift : MDifferentiableAt (𝓡∂ 2) ((𝓡∂ 2).prod 𝓘(ℝ)) lift x :=
    (contMDiff_id.prodMk htau).mdifferentiableAt (by simp)
  have hc := (collar.smooth (x,tau x) ⟨mem_univ x,hlegal x⟩).mdifferentiableWithinAt (by simp)
  have h := mfderivWithin_comp x hc hlift.mdifferentiableWithinAt
    (show MapsTo lift univ (univ ×ˢ Ico (0 : ℝ) collar.epsilon) from
      fun y _ => ⟨mem_univ y,hlegal y⟩) (uniqueMDiffWithinAt_univ (𝓡∂ 2))
  rw [mfderivWithin_univ,mfderivWithin_univ] at h
  have hd : mfderiv (𝓡∂ 2) ((𝓡∂ 2).prod 𝓘(ℝ)) lift x =
      (ContinuousLinearMap.id ℝ (TangentSpace (𝓡∂ 2) x)).prod
        (mfderiv (𝓡∂ 2) 𝓘(ℝ) tau x) := by
    simpa only [lift,mfderiv_id,id_eq] using
      (mfderiv_prodMk (I := 𝓡∂ 2) (I' := 𝓡∂ 2) (I'' := 𝓘(ℝ))
        (f := id) (g := tau) (x := x) mdifferentiableAt_id
        (htau.mdifferentiableAt (by simp)))
  change mfderiv (𝓡∂ 2) (𝓡∂ 3) (fun y => collar.map (y,tau y)) x =
    (mfderivWithin ((𝓡∂ 2).prod 𝓘(ℝ)) (𝓡∂ 3) collar.map
      (univ ×ˢ Ico (0 : ℝ) collar.epsilon) (x,tau x)).comp
      (mfderiv (𝓡∂ 2) ((𝓡∂ 2).prod 𝓘(ℝ)) lift x) at h
  rw [hd] at h
  exact h

def collar_variable_time_neat_v480 (collar : OneSidedCollar F U)
    (tau : S → ℝ) (htau : ContMDiff (𝓡∂ 2) 𝓘(ℝ) ∞ tau)
    (hlegal : ∀ x, tau x ∈ Ico (0 : ℝ) collar.epsilon) : NeatEmbedding S M := by
  let H : S → M := fun x => collar.map (x,tau x)
  have hs : ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ H :=
    collar.smooth.comp_contMDiff (contMDiff_id.prodMk htau)
      (fun x => ⟨mem_univ x,hlegal x⟩)
  have he : IsEmbedding H := by
    let lift : S → univ ×ˢ Ico (0 : ℝ) collar.epsilon :=
      fun x => ⟨(x,tau x),⟨mem_univ x,hlegal x⟩⟩
    have hlift : IsEmbedding lift :=
      (IsEmbedding.of_comp_iff IsEmbedding.subtypeVal).mp (isEmbedding_graph htau.continuous)
    exact collar.embedding.comp hlift
  have hb (x : S) : H x ∈ (𝓡∂ 3).boundary M ↔ x ∈ S.boundary :=
    collar.boundary_strata x (tau x) (hlegal x)
  have hi (x : S) : Injective (mfderiv (𝓡∂ 2) (𝓡∂ 3) H x) := by
    rw [collar_variable_time_differential_v480 collar tau htau hlegal x]
    exact (collar.immersion (x,tau x) ⟨mem_univ x,hlegal x⟩).comp
      (fun v w h => congrArg Prod.fst h)
  have htrans (x : S) (hx : x ∈ S.boundary) :
      ∃ w : TangentSpace (𝓡∂ 2) x,
        inwardCoordinate (H x) (mfderiv (𝓡∂ 2) (𝓡∂ 3) H x w) ≠ 0 := by
    obtain ⟨w,hw⟩ := collar_slice_boundary_transverse collar (hlegal x) hx
    refine ⟨w,?_⟩
    rw [inwardCoordinate_eq_coordinate,collar_variable_time_differential_v480 collar tau htau hlegal x]
    rw [inwardCoordinate_eq_coordinate,collar_slice_mfderiv_eq collar (hlegal x) x] at hw
    let L := mfderivWithin ((𝓡∂ 2).prod 𝓘(ℝ)) (𝓡∂ 3) collar.map
      (univ ×ˢ Ico (0 : ℝ) collar.epsilon) (x,tau x)
    let d : ℝ := show ℝ from mfderiv (𝓡∂ 2) 𝓘(ℝ) tau x w
    have hz : (show Euc 3 from L (0,d)) 0 = 0 := by
      have h := collar_time_normal_zero collar (hlegal x) hx
      have heq : (0,d) = d • (show Euc 2 × ℝ from (0,1)) := by simp
      rw [heq,map_smul]
      change d * (show Euc 3 from L (0,1)) 0 = 0
      rw [show (show Euc 3 from L (0,1)) 0 = 0 from h,mul_zero]
    change (show Euc 3 from L (w,d)) 0 ≠ 0
    have heq : (w,d) = (w,0) + (0,d) := by ext <;> simp
    rw [heq,map_add,PiLp.add_apply,hz,add_zero]
    exact hw
  exact {
    toFun := H
    smoothEmbedding := ⟨native_transverse_isImmersion hs hi hb htrans,he⟩
    boundary_preimage := by ext x; exact hb x
    boundary_transverse := htrans }

/-- Every positive smooth time function stays on the selected side. -/
theorem collar_variable_time_image_subset_v480 (collar : OneSidedCollar F U)
    (tau : S → ℝ) (htau : ContMDiff (𝓡∂ 2) 𝓘(ℝ) ∞ tau)
    (hlegal : ∀ x, tau x ∈ Ico (0 : ℝ) collar.epsilon)
    (hpositive : ∀ x, 0 < tau x) :
    (collar_variable_time_neat_v480 collar tau htau hlegal).image ⊆ U := by
  rintro _ ⟨x,rfl⟩
  exact collar.into_region x (tau x) (hpositive x) (hlegal x).2

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
end

-- Exact source from B2VariableCollarFamilyV480.lean

noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]
variable {S : CompactOrientedSurface.{0}} {F : NeatEmbedding S M} {U : Set M}
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- Variable smooth times are joined by the literal convex collar isotopy. -/
def variable_collar_normal_isotopy_v480 (collar : OneSidedCollar F U)
    (tau tau' : S → ℝ) (htau : ContMDiff (𝓡∂ 2) 𝓘(ℝ) ∞ tau)
    (htau' : ContMDiff (𝓡∂ 2) 𝓘(ℝ) ∞ tau')
    (hlegal : ∀ x, tau x ∈ Ico (0 : ℝ) collar.epsilon)
    (hlegal' : ∀ x, tau' x ∈ Ico (0 : ℝ) collar.epsilon) :
    SmoothNormalIsotopy S M (collar_variable_time_neat_v480 collar tau htau hlegal)
      (collar_variable_time_neat_v480 collar tau' htau' hlegal') := by
  let l (u : Time) (x : S) : ℝ := (1-(u : ℝ))*tau x+(u : ℝ)*tau' x
  have hlC (u : Time) (x : S) : l u x ∈ Ico (0 : ℝ) collar.epsilon :=
    (convex_Ico (𝕜 := ℝ) (0 : ℝ) collar.epsilon) (hlegal x) (hlegal' x)
      (sub_nonneg.mpr u.property.2) u.property.1 (sub_add_cancel 1 (u : ℝ))
  have hl (u : Time) : ContMDiff (𝓡∂ 2) 𝓘(ℝ) ∞ (l u) :=
    (contMDiff_const.mul htau).add (contMDiff_const.mul htau')
  have hlfamily : ContMDiff ((𝓡∂ 1).prod (𝓡∂ 2)) 𝓘(ℝ) ∞
      (fun q : Time × S => l q.1 q.2) :=
    ((contMDiff_const.sub (contMDiff_subtypeVal_Icc.comp contMDiff_fst)).mul
      (htau.comp contMDiff_snd)).add
        ((contMDiff_subtypeVal_Icc.comp contMDiff_fst).mul (htau'.comp contMDiff_snd))
  refine {
    stage := fun u => collar_variable_time_neat_v480 collar (l u) (hl u) (hlC u)
    smooth_family := ?_
    initial := ?_
    final := ?_ }
  · exact collar.smooth.comp_contMDiff (contMDiff_snd.prodMk hlfamily)
      (fun q => ⟨mem_univ q.2,hlC q.1 q.2⟩)
  · funext x
    change collar.map (x,l 0 x) = collar.map (x,tau x)
    congr 1
    dsimp only [l]
    norm_num
  · funext x
    change collar.map (x,l 1 x) = collar.map (x,tau' x)
    congr 1
    dsimp only [l]
    norm_num

theorem variable_collar_ambient_related_v480 [T2Space M] [SecondCountableTopology M]
    (collar : OneSidedCollar F U)
    (tau tau' : S → ℝ) (htau : ContMDiff (𝓡∂ 2) 𝓘(ℝ) ∞ tau)
    (htau' : ContMDiff (𝓡∂ 2) 𝓘(ℝ) ∞ tau')
    (hlegal : ∀ x, tau x ∈ Ico (0 : ℝ) collar.epsilon)
    (hlegal' : ∀ x, tau' x ∈ Ico (0 : ℝ) collar.epsilon) :
    SmoothAmbientIsotopy.Rel (collar_variable_time_neat_v480 collar tau htau hlegal).image
      (collar_variable_time_neat_v480 collar tau' htau' hlegal').image := by
  obtain ⟨H,hH⟩ := smooth_isotopy_extension
    (variable_collar_normal_isotopy_v480 collar tau tau' htau htau' hlegal hlegal')
  refine ⟨H,?_⟩
  change H.stage 1 '' range (fun x : S => collar.map (x,tau x)) =
    range (fun x : S => collar.map (x,tau' x))
  rw [← range_comp]
  congr 1
  funext x
  exact hH x

theorem variable_collar_initial_ambient_related_v480 [T2Space M] [SecondCountableTopology M]
    (collar : OneSidedCollar F U) (tau : S → ℝ)
    (htau : ContMDiff (𝓡∂ 2) 𝓘(ℝ) ∞ tau)
    (hlegal : ∀ x, tau x ∈ Ico (0 : ℝ) collar.epsilon) :
    SmoothAmbientIsotopy.Rel F.image
      (collar_variable_time_neat_v480 collar tau htau hlegal).image := by
  have hzero (x : S) : (0 : ℝ) ∈ Ico (0 : ℝ) collar.epsilon := ⟨le_rfl,collar.epsilon_pos⟩
  have h := variable_collar_ambient_related_v480 collar (fun _ => 0) tau
    contMDiff_const htau hzero hlegal
  have himage : (collar_variable_time_neat_v480 collar (fun _ => 0) contMDiff_const hzero).image =
      F.image := by
    change range (fun x : S => collar.map (x,0)) = range F.toFun
    rw [collar_slice_zero collar]
  rwa [himage] at h

/-- The actual area stays continuous for a jointly smooth variable-time
correction, without replacing it by the raw constant-time area. -/
theorem variable_collar_actual_area_continuous_v480 (g : SmoothMetric M)
    (collar : OneSidedCollar F U) (tau : ℝ × S → ℝ) {b : ℝ} (hb : 0 < b)
    (htau : ContMDiffOn (𝓘(ℝ).prod (𝓡∂ 2)) 𝓘(ℝ) ∞ tau (Icc (0 : ℝ) b ×ˢ univ))
    (hlegal : ∀ t ∈ Icc (0 : ℝ) b, ∀ x, tau (t,x) ∈ Ico (0 : ℝ) collar.epsilon) :
    Continuous (fun t : Icc (0 : ℝ) b =>
      area g (fun x => collar.map (x,tau (t.val,x)))) := by
  apply jointly_smooth_actual_area_continuous_v480 g
    (fun q : ℝ × S => collar.map (q.2,tau q)) hb
  apply collar.smooth.comp (contMDiff_snd.contMDiffOn.prodMk htau)
  intro q hq
  exact ⟨mem_univ q.2,hlegal q.1 hq.1 q.2⟩

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
end

-- Exact source from B2BoundaryPullbackV489.lean

noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {S : CompactOrientedSurface.{0}} {F : NeatEmbedding S E.Carrier}
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- The supplied whole-leaf boundary equality determines its source parametrization. -/
theorem b2_boundary_parameter_exists_v489 (J : LongitudeFoliation.{0} E)
    {a : Circle} (ha : F.toFun '' S.boundary = J.leaf a) :
    ∃ p : Circle → S,
      (∀ z, p z ∈ S.boundary) ∧
      (∀ z, F.toFun (p z) = J.torus (a,z)) ∧
      ContMDiff (𝓡 1) (𝓡∂ 2) ∞ p ∧
      IsEmbedding p ∧ range p = S.boundary := by
  classical
  have hex (z : Circle) : ∃ x : S, x ∈ S.boundary ∧ F.toFun x = J.torus (a,z) := by
    have hz : J.torus (a,z) ∈ F.toFun '' S.boundary := by
      rw [ha]
      exact mem_range_self z
    exact hz
  let p : Circle → S := fun z => (hex z).choose
  have hp (z : Circle) := (hex z).choose_spec
  have hcomp : F.toFun ∘ p = fun z => J.torus (a,z) := by
    funext z
    exact (hp z).2
  have he : IsEmbedding (fun z : Circle => J.torus (a,z)) :=
    J.smoothEmbedding.isEmbedding.comp (isEmbedding_prodMkRight a)
  have hpc : Continuous p := F.smoothEmbedding.isEmbedding.continuous_iff.mpr
    (by rw [hcomp]; exact he.continuous)
  have hps : ContMDiff (𝓡 1) (𝓡∂ 2) ∞ p :=
    (ContMDiff.iff_comp_isImmersion F.smoothEmbedding.isImmersion).mpr
      ⟨hpc,by
        rw [hcomp]
        exact J.smoothEmbedding.contMDiff.comp (contMDiff_const.prodMk contMDiff_id)⟩
  refine ⟨p,fun z => (hp z).1,fun z => (hp z).2,hps,?_,?_⟩
  · apply (IsEmbedding.of_comp_iff F.smoothEmbedding.isEmbedding).mp
    rwa [hcomp]
  · apply subset_antisymm
    · rintro _ ⟨z,rfl⟩
      exact (hp z).1
    · intro x hx
      have hxF : F.toFun x ∈ J.leaf a := by
        rw [← ha]
        exact mem_image_of_mem F.toFun hx
      obtain ⟨z,hz⟩ := hxF
      exact ⟨z,F.smoothEmbedding.isEmbedding.injective ((hp z).2.trans hz)⟩

/-- Pulling the actual boundary collar through the given torus yields a smooth,
injective map of a compact parameter strip, including its initial boundary. -/
theorem b2_boundary_collar_torus_pullback_v489 (J : LongitudeFoliation.{0} E)
    {U : Set E.Carrier} (collar : OneSidedCollar F U)
    (p : Circle → S) (hp : ContMDiff (𝓡 1) (𝓡∂ 2) ∞ p)
    (hpe : IsEmbedding p) (hpb : ∀ z, p z ∈ S.boundary)
    {a : Circle} (hpa : ∀ z, F.toFun (p z) = J.torus (a,z)) :
    ∃ phi : Time × Circle → Circle × Circle,
      ContMDiff ((𝓡∂ 1).prod (𝓡 1)) ((𝓡 1).prod (𝓡 1)) ∞ phi ∧
      IsEmbedding phi ∧
      (∀ q, J.torus (phi q) = collar.map (p q.2,collar.epsilon / 2 * (q.1 : ℝ))) ∧
      (∀ z, phi (0,z) = (a,z)) := by
  classical
  let k := collar.epsilon / 2
  have hk : 0 < k := half_pos collar.epsilon_pos
  have hlegal (t : Time) : k * (t : ℝ) ∈ Ico (0 : ℝ) collar.epsilon := by
    refine ⟨mul_nonneg hk.le t.property.1,?_⟩
    calc k * (t : ℝ) ≤ k * 1 := mul_le_mul_of_nonneg_left t.property.2 hk.le
      _ < collar.epsilon := by simpa only [mul_one,k] using half_lt_self collar.epsilon_pos
  let G : Time × Circle → E.Carrier := fun q => collar.map (p q.2,k * (q.1 : ℝ))
  have hGs : ContMDiff ((𝓡∂ 1).prod (𝓡 1)) (𝓡∂ 3) ∞ G :=
    collar.smooth.comp_contMDiff
      ((hp.comp contMDiff_snd).prodMk
        (contMDiff_const.mul (contMDiff_subtypeVal_Icc.comp contMDiff_fst)))
      (fun q => ⟨mem_univ _,hlegal q.1⟩)
  have hex (q : Time × Circle) : ∃ r : Circle × Circle, J.torus r = G q := by
    have hGboundary : G q ∈ (𝓡∂ 3).boundary E.Carrier :=
      (collar.boundary_strata (p q.2) _ (hlegal q.1)).mpr (hpb q.2)
    rw [← J.covers_boundary] at hGboundary
    exact hGboundary
  let phi : Time × Circle → Circle × Circle := fun q => (hex q).choose
  have hcomp : J.torus ∘ phi = G := by
    funext q
    exact (hex q).choose_spec
  have hpc : Continuous phi := J.smoothEmbedding.isEmbedding.continuous_iff.mpr
    (by rw [hcomp]; exact hGs.continuous)
  have hps : ContMDiff ((𝓡∂ 1).prod (𝓡 1)) ((𝓡 1).prod (𝓡 1)) ∞ phi :=
    (ContMDiff.iff_comp_isImmersion J.smoothEmbedding.isImmersion).mpr
      ⟨hpc,by rwa [hcomp]⟩
  have hGe : IsEmbedding G := by
    let lift : Time × Circle → univ ×ˢ Ico (0 : ℝ) collar.epsilon :=
      fun q => ⟨(p q.2,k * (q.1 : ℝ)),⟨mem_univ _,hlegal q.1⟩⟩
    have hks : IsEmbedding (fun t : Time => k * (t : ℝ)) := by
      exact (Homeomorph.mulLeft₀ k hk.ne').isEmbedding.comp IsEmbedding.subtypeVal
    have hl : IsEmbedding lift := by
      apply (IsEmbedding.of_comp_iff IsEmbedding.subtypeVal).mp
      exact (hpe.prodMap hks).comp (Homeomorph.prodComm Time Circle).isEmbedding
    exact collar.embedding.comp hl
  refine ⟨phi,hps,?_,fun q => (hex q).choose_spec,?_⟩
  · apply (IsEmbedding.of_comp_iff J.smoothEmbedding.isEmbedding).mp
    rwa [hcomp]
  · intro z
    apply J.smoothEmbedding.isEmbedding.injective
    rw [(hex (0,z)).choose_spec]
    dsimp only [G]
    change collar.map (p z, k * 0) = J.torus (a,z)
    rw [mul_zero,collar.initial,hpa]

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
end

-- Exact source from B2BoundaryRankV489.lean

noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {S : CompactOrientedSurface.{0}} {F : NeatEmbedding S E.Carrier}
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem b2_boundary_parameter_rank_v489 (J : LongitudeFoliation.{0} E)
    (p : Circle → S) (hp : ContMDiff (𝓡 1) (𝓡∂ 2) ∞ p)
    {a : Circle} (hpa : ∀ z, F.toFun (p z) = J.torus (a,z)) (z : Circle) :
    Injective (mfderiv (𝓡 1) (𝓡∂ 2) p z) := by
  have hcomp : F.toFun ∘ p = J.torus ∘ (fun z : Circle => (a,z)) := funext hpa
  have hchain := mfderiv_comp z (F.smoothEmbedding.contMDiff.mdifferentiableAt (by simp))
    (hp.mdifferentiableAt (by simp))
  change (show Euc 1 →L[ℝ] Euc 3 from mfderiv (𝓡 1) (𝓡∂ 3) (F.toFun ∘ p) z) =
    (show Euc 2 →L[ℝ] Euc 3 from mfderiv (𝓡∂ 2) (𝓡∂ 3) F.toFun (p z)).comp
      (mfderiv (𝓡 1) (𝓡∂ 2) p z) at hchain
  have hpair : MDifferentiableAt (𝓡 1) ((𝓡 1).prod (𝓡 1))
      (fun z : Circle => (a,z)) z :=
    (show ContMDiff (𝓡 1) ((𝓡 1).prod (𝓡 1)) ∞
      (fun z : Circle => (a,z)) from contMDiff_const.prodMk contMDiff_id).mdifferentiableAt (by simp)
  rw [hcomp,mfderiv_comp z (J.smoothEmbedding.contMDiff.mdifferentiableAt (by simp))
    hpair,mfderiv_prod_right] at hchain
  have hi : Injective ((mfderiv ((𝓡 1).prod (𝓡 1)) (𝓡∂ 3) J.torus (a,z)).comp
      (ContinuousLinearMap.inr ℝ (TangentSpace (𝓡 1) a) (TangentSpace (𝓡 1) z))) :=
    (J.smoothEmbedding.isImmersion.mfderiv_injective (by simp) _).comp
      (fun u v h => congrArg Prod.snd h)
  intro u v huv
  apply hi
  exact (congrArg (fun D : Euc 1 →L[ℝ] Euc 3 => D u) hchain).trans
    ((congrArg (mfderiv (𝓡∂ 2) (𝓡∂ 3) F.toFun (p z)) huv).trans
      (congrArg (fun D : Euc 1 →L[ℝ] Euc 3 => D v) hchain).symm)

theorem b2_boundary_collar_pullback_rank_v489 (J : LongitudeFoliation.{0} E)
    {U : Set E.Carrier} (collar : OneSidedCollar F U)
    (p : Circle → S) (hp : ContMDiff (𝓡 1) (𝓡∂ 2) ∞ p)
    {a : Circle} (hpa : ∀ z, F.toFun (p z) = J.torus (a,z))
    (phi : Time × Circle → Circle × Circle)
    (hphi : ContMDiff ((𝓡∂ 1).prod (𝓡 1)) ((𝓡 1).prod (𝓡 1)) ∞ phi)
    (heq : ∀ q, J.torus (phi q) = collar.map (p q.2,collar.epsilon / 2 * (q.1 : ℝ)))
    (q : Time × Circle) :
    Injective (mfderiv ((𝓡∂ 1).prod (𝓡 1)) ((𝓡 1).prod (𝓡 1)) phi q) := by
  let k := collar.epsilon / 2
  let A : Set (S × ℝ) := univ ×ˢ Ico (0 : ℝ) collar.epsilon
  let L : ℝ →L[ℝ] ℝ := k • ContinuousLinearMap.id ℝ ℝ
  let c : Time → ℝ := fun t => L (t : ℝ)
  let lift : Time × Circle → S × ℝ := fun r => (p r.2,c r.1)
  have hk : 0 < k := half_pos collar.epsilon_pos
  have hlegal (t : Time) : c t ∈ Ico (0 : ℝ) collar.epsilon := by
    change k * (t : ℝ) ∈ Ico (0 : ℝ) collar.epsilon
    refine ⟨mul_nonneg hk.le t.property.1,?_⟩
    calc k * (t : ℝ) ≤ k * 1 := mul_le_mul_of_nonneg_left t.property.2 hk.le
      _ < collar.epsilon := by simpa only [mul_one,k] using half_lt_self collar.epsilon_pos
  have hcs : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ c := L.contMDiff.comp contMDiff_subtypeVal_Icc
  have hcder : Injective (mfderiv (𝓡∂ 1) 𝓘(ℝ) c q.1) := by
    have hd := mfderiv_comp q.1 L.mdifferentiableAt
      ((contMDiff_subtypeVal_Icc (n := ∞)).mdifferentiableAt (by simp))
    change mfderiv (𝓡∂ 1) 𝓘(ℝ) c q.1 = _ at hd
    rw [hd,mfderiv_eq_fderiv,L.hasFDerivAt.fderiv]
    have hL : Injective L := by
      intro u v huv
      change k * u = k * v at huv
      exact mul_left_cancel₀ hk.ne' huv
    exact hL.comp ((isSmoothEmbedding_subtypeVal_Icc (n := ∞)).isImmersion.mfderiv_injective (by simp) _)
  have hls : ContMDiff ((𝓡∂ 1).prod (𝓡 1)) ((𝓡∂ 2).prod 𝓘(ℝ)) ∞ lift :=
    (hp.comp contMDiff_snd).prodMk (hcs.comp contMDiff_fst)
  have hlrank : Injective (mfderiv ((𝓡∂ 1).prod (𝓡 1)) ((𝓡∂ 2).prod 𝓘(ℝ)) lift q) := by
    have hpd := b2_boundary_parameter_rank_v489 J p hp hpa q.2
    change Injective (mfderiv ((𝓡∂ 1).prod (𝓡 1)) ((𝓡∂ 2).prod 𝓘(ℝ))
      (fun r : Time × Circle => ((p ∘ Prod.snd) r,(c ∘ Prod.fst) r)) q)
    rw [mfderiv_prodMk ((hp.comp contMDiff_snd).mdifferentiableAt (by simp))
      ((hcs.comp contMDiff_fst).mdifferentiableAt (by simp))]
    rw [mfderiv_comp q (hp.mdifferentiableAt (by simp)) mdifferentiableAt_snd,
      mfderiv_comp q (hcs.mdifferentiableAt (by simp)) mdifferentiableAt_fst,
      mfderiv_snd,mfderiv_fst]
    intro u v huv
    apply Prod.ext
    · exact hcder (congrArg Prod.snd huv)
    · exact hpd (congrArg Prod.fst huv)
  have hmaps : MapsTo lift univ A := fun r _ => ⟨mem_univ _,hlegal r.1⟩
  have hGchain := mfderivWithin_comp q
    (collar.smooth.mdifferentiableOn (by simp) (lift q) (hmaps (mem_univ q)))
    (hls.mdifferentiableAt (by simp)).mdifferentiableWithinAt hmaps
    (uniqueMDiffWithinAt_univ ((𝓡∂ 1).prod (𝓡 1)))
  rw [mfderivWithin_univ,mfderivWithin_univ] at hGchain
  have hGrank : Injective (mfderiv ((𝓡∂ 1).prod (𝓡 1)) (𝓡∂ 3) (collar.map ∘ lift) q) := by
    rw [hGchain]
    exact (collar.immersion (lift q) (hmaps (mem_univ q))).comp hlrank
  have hcomp : J.torus ∘ phi = collar.map ∘ lift := funext heq
  change Injective (show (Euc 1 × Euc 1) →L[ℝ] Euc 3 from
    mfderiv ((𝓡∂ 1).prod (𝓡 1)) (𝓡∂ 3) (collar.map ∘ lift) q) at hGrank
  rw [← hcomp,mfderiv_comp q (J.smoothEmbedding.contMDiff.mdifferentiableAt (by simp))
    (hphi.mdifferentiableAt (by simp))] at hGrank
  intro u v huv
  apply hGrank
  exact congrArg (mfderiv ((𝓡 1).prod (𝓡 1)) (𝓡∂ 3) J.torus (phi q)) huv

/-- The exact initial parametrization forces the leafwise derivative to be
identity. Full strip rank therefore forces a transverse label derivative. -/
theorem b2_strip_label_transverse_v489
    (phi : Time × Circle → Circle × Circle)
    (hphi : ContMDiff ((𝓡∂ 1).prod (𝓡 1)) ((𝓡 1).prod (𝓡 1)) ∞ phi)
    {a : Circle} (hzero : ∀ z, phi (0,z) = (a,z))
    (hrank : ∀ q, Injective (mfderiv ((𝓡∂ 1).prod (𝓡 1))
      ((𝓡 1).prod (𝓡 1)) phi q)) (z : Circle) :
    ((show Euc 1 × Euc 1 →L[ℝ] Euc 1 × Euc 1 from
        mfderiv ((𝓡∂ 1).prod (𝓡 1)) ((𝓡 1).prod (𝓡 1)) phi (0,z))
      (EuclideanSpace.single 0 1,0)).1 ≠ 0 := by
  let D : (Euc 1 × Euc 1) →L[ℝ] (Euc 1 × Euc 1) :=
    mfderiv ((𝓡∂ 1).prod (𝓡 1)) ((𝓡 1).prod (𝓡 1)) phi (0,z)
  have hpair : MDifferentiableAt (𝓡 1) ((𝓡∂ 1).prod (𝓡 1))
      (fun z : Circle => ((0 : Time),z)) z :=
    (show ContMDiff (𝓡 1) ((𝓡∂ 1).prod (𝓡 1)) ∞
      (fun z : Circle => ((0 : Time),z)) from
        contMDiff_const.prodMk contMDiff_id).mdifferentiableAt (by simp)
  have hslice := mfderiv_comp z (hphi.mdifferentiableAt (by simp)) hpair
  change (show Euc 1 →L[ℝ] (Euc 1 × Euc 1) from
    mfderiv (𝓡 1) ((𝓡 1).prod (𝓡 1)) (phi ∘ fun z => ((0 : Time),z)) z) =
      D.comp (mfderiv (𝓡 1) ((𝓡∂ 1).prod (𝓡 1)) (fun z => ((0 : Time),z)) z) at hslice
  have heq : (phi ∘ fun z => ((0 : Time),z)) = fun z : Circle => (a,z) := funext hzero
  rw [heq,mfderiv_prod_right,mfderiv_prod_right] at hslice
  have hD (w : Euc 1) : D (0,w) = (0,w) :=
    (congrArg (fun L : Euc 1 →L[ℝ] (Euc 1 × Euc 1) => L w) hslice).symm
  change (D (EuclideanSpace.single 0 1,0)).1 ≠ 0
  intro hz
  let w := (D (EuclideanSpace.single 0 1,0)).2
  have he : D (EuclideanSpace.single 0 1,0) = D (0,w) := by
    rw [hD]
    exact Prod.ext hz rfl
  have hn := congrArg Prod.fst (hrank (0,z) he)
  have hcoord := congrArg (fun u : Euc 1 => u 0) hn
  norm_num [EuclideanSpace.single] at hcoord

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
end

-- Exact source from B2PhaseExtensionV489.lean

noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- A real phase of the supplied label circle is constructed from a smooth
bump and the actual preferred chart. It agrees with that chart near the label. -/
theorem b2_smooth_label_phase_v489 (a : Circle) :
    ∃ ell : Circle → ℝ, ContMDiff (𝓡 1) 𝓘(ℝ) ∞ ell ∧ ell a = 0 ∧
      mfderiv (𝓡 1) 𝓘(ℝ) ell a = EuclideanSpace.proj 0 ∧
      ∃ W : Set Circle, IsOpen W ∧ a ∈ W ∧ InjOn ell W := by
  classical
  let beta : SmoothBumpFunction (𝓡 1) a := Classical.choice inferInstance
  let e := extChartAt (𝓡 1) a
  let L : Euc 1 →L[ℝ] ℝ := EuclideanSpace.proj 0
  let f : Circle → ℝ := fun z => L (e z) - L (e a)
  let ell : Circle → ℝ := fun z => beta z • f z
  have hf : ContMDiffOn (𝓡 1) 𝓘(ℝ) ∞ f (chartAt (EuclideanSpace ℝ (Fin 1)) a).source := by
    exact (L.contMDiff.comp_contMDiffOn
      (contMDiffOn_extChartAt (I := 𝓡 1) (x := a) (n := ∞))).sub contMDiffOn_const
  have hs : ContMDiff (𝓡 1) 𝓘(ℝ) ∞ ell := beta.contMDiff_smul hf
  have hnear : ell =ᶠ[𝓝 a] f := by
    filter_upwards [beta.eventuallyEq_one] with z hz
    change beta z • f z = f z
    simp only [hz,Pi.one_apply,one_smul]
  have hfa : ContMDiffAt (𝓡 1) 𝓘(ℝ) ∞ f a :=
    (L.contMDiff.contMDiffAt.comp a contMDiffAt_extChartAt).sub contMDiffAt_const
  have hd : mfderiv (𝓡 1) 𝓘(ℝ) f a = L := by
    have hbase : MDifferentiableAt (𝓡 1) 𝓘(ℝ) (L ∘ e) a :=
      (L.contMDiff.contMDiffAt.comp a
        (contMDiffAt_extChartAt (I := 𝓡 1) (n := ∞))).mdifferentiableAt (by simp)
    change (show Euc 1 →L[ℝ] ℝ from mfderiv (𝓡 1) 𝓘(ℝ)
      ((L ∘ e) - fun _ => L (e a)) a) = L
    rw [mfderiv_sub hbase
      mdifferentiableAt_const,mfderiv_const,sub_zero]
    rw [mfderiv_comp a L.mdifferentiableAt
      ((contMDiffAt_extChartAt (I := 𝓡 1) (n := ∞)).mdifferentiableAt (by simp)),
      mfderiv_eq_fderiv,L.hasFDerivAt.fderiv,mfderiv_extChartAt_self]
    exact ContinuousLinearMap.comp_id _
  obtain ⟨W,hWsub,hWopen,haW⟩ := mem_nhds_iff.mp
    (inter_mem beta.eventuallyEq_one (extChartAt_source_mem_nhds (I := 𝓡 1) a))
  refine ⟨ell,hs,by simp [ell,f],hnear.mfderiv_eq.trans hd,W,hWopen,haW,?_⟩
  intro z hz w hw heq
  have hz' := hWsub hz
  have hw' := hWsub hw
  have hL : L (e z) = L (e w) := by
    change beta z • f z = beta w • f w at heq
    have hzb : beta z = 1 := hz'.1
    have hwb : beta w = 1 := hw'.1
    rw [hzb,hwb,one_smul,one_smul] at heq
    change L (e z) - L (e a) = L (e w) - L (e a) at heq
    linarith
  apply e.injOn hz'.2 hw'.2
  ext i
  fin_cases i
  exact hL

theorem b2_real_phase_extension_v489 (ell : Circle → ℝ)
    (hell : ContMDiff (𝓡 1) 𝓘(ℝ) ∞ ell)
    (phi : Time × Circle → Circle × Circle)
    (hphi : ContMDiff ((𝓡∂ 1).prod (𝓡 1)) ((𝓡 1).prod (𝓡 1)) ∞ phi)
    {a : Circle} (hzero : ∀ z, phi (0,z) = (a,z)) (hella : ell a = 0) :
    ∃ f : ℝ × Circle → ℝ,
      ContMDiff (𝓘(ℝ).prod (𝓡 1)) 𝓘(ℝ) ∞ f ∧
      (∀ t : Time, ∀ z : Circle, f ((t : ℝ),z) = ell (phi (t,z)).1) ∧
      (∀ z, f (0,z) = 0) := by
  let G : ℝ × Circle → ℝ := fun q => ell (phi (projIcc 0 1 (by norm_num) q.1,q.2)).1
  have hG : ContMDiffOn (𝓘(ℝ).prod (𝓡 1)) 𝓘(ℝ) ∞ G (Icc (0 : ℝ) 1 ×ˢ univ) :=
    (hell.comp (contMDiff_fst.comp hphi)).comp_contMDiffOn
      ((contMDiffOn_projIcc.comp contMDiff_fst.contMDiffOn (fun q hq => hq.1)).prodMk
        contMDiff_snd.contMDiffOn)
  obtain ⟨f,hf,hfeq⟩ := Manifold.exists_contMDiff_extension_Icc hG
  have hmatch (t : Time) (z : Circle) : f ((t : ℝ),z) = ell (phi (t,z)).1 := by
    have he := hfeq (show ((t : ℝ),z) ∈ Icc (0 : ℝ) 1 ×ˢ univ from ⟨t.property,mem_univ z⟩)
    have ht : projIcc 0 1 (by norm_num) (t : ℝ) = t :=
      Subtype.ext (by simp [projIcc_of_mem (show (0 : ℝ) ≤ 1 by norm_num) t.property])
    simpa only [G,ht] using he
  refine ⟨f,hf,hmatch,?_⟩
  intro z
  have h := hmatch (0 : Time) z
  change f (0,z) = ell (phi (0,z)).1 at h
  rwa [hzero,hella] at h

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
end

-- Exact source from B2PhaseRankV489.lean

noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem b2_extended_phase_transverse_v489
    (phi : Time × Circle → Circle × Circle)
    (hphi : ContMDiff ((𝓡∂ 1).prod (𝓡 1)) ((𝓡 1).prod (𝓡 1)) ∞ phi)
    {a : Circle} (hzero : ∀ z, phi (0,z) = (a,z))
    (hrank : ∀ q, Injective (mfderiv ((𝓡∂ 1).prod (𝓡 1))
      ((𝓡 1).prod (𝓡 1)) phi q))
    (ell : Circle → ℝ) (hell : ContMDiff (𝓡 1) 𝓘(ℝ) ∞ ell)
    (hderell : mfderiv (𝓡 1) 𝓘(ℝ) ell a = EuclideanSpace.proj 0)
    (f : ℝ × Circle → ℝ) (hf : ContMDiff (𝓘(ℝ).prod (𝓡 1)) 𝓘(ℝ) ∞ f)
    (hmatch : ∀ t : Time, ∀ z : Circle, f ((t : ℝ),z) = ell (phi (t,z)).1)
    (z : Circle) : mfderiv (𝓘(ℝ).prod (𝓡 1)) 𝓘(ℝ) f (0,z) (1,0) ≠ 0 := by
  let v : Euc 1 := EuclideanSpace.single 0 1
  let P : Time × Circle → ℝ × Circle := fun q => ((q.1 : ℝ),q.2)
  have hP : ContMDiff ((𝓡∂ 1).prod (𝓡 1)) (𝓘(ℝ).prod (𝓡 1)) ∞ P :=
    (contMDiff_subtypeVal_Icc.comp contMDiff_fst).prodMk contMDiff_snd
  let Q : Time × Circle → ℝ := fun q => ell (phi q).1
  have hQ : ContMDiff ((𝓡∂ 1).prod (𝓡 1)) 𝓘(ℝ) ∞ Q :=
    hell.comp (contMDiff_fst.comp hphi)
  have heq : f ∘ P = Q := funext fun q => hmatch q.1 q.2
  have hleft := mfderiv_comp (0,z) (hf.mdifferentiableAt (by simp))
    (hP.mdifferentiableAt (by simp))
  change (show (Euc 1 × Euc 1) →L[ℝ] ℝ from
    mfderiv ((𝓡∂ 1).prod (𝓡 1)) 𝓘(ℝ) (f ∘ P) (0,z)) =
    (show (ℝ × Euc 1) →L[ℝ] ℝ from
      mfderiv (𝓘(ℝ).prod (𝓡 1)) 𝓘(ℝ) f (0,z)).comp
    (mfderiv ((𝓡∂ 1).prod (𝓡 1)) (𝓘(ℝ).prod (𝓡 1)) P (0,z)) at hleft
  rw [heq] at hleft
  have hright := mfderiv_comp (0,z) (hell.mdifferentiableAt (by simp))
    ((contMDiff_fst.comp hphi).mdifferentiableAt (by simp))
  change (show (Euc 1 × Euc 1) →L[ℝ] ℝ from
    mfderiv ((𝓡∂ 1).prod (𝓡 1)) 𝓘(ℝ) Q (0,z)) =
    (show Euc 1 →L[ℝ] ℝ from mfderiv (𝓡 1) 𝓘(ℝ) ell (phi (0,z)).1).comp
      (mfderiv ((𝓡∂ 1).prod (𝓡 1)) (𝓡 1) (Prod.fst ∘ phi) (0,z)) at hright
  rw [hzero,hderell,mfderiv_comp (0,z) mdifferentiableAt_fst
    (hphi.mdifferentiableAt (by simp)),mfderiv_fst] at hright
  have hPder : mfderiv ((𝓡∂ 1).prod (𝓡 1)) (𝓘(ℝ).prod (𝓡 1)) P (0,z) (v,0) =
      (mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : Time → ℝ) 0 v,0) := by
    change mfderiv ((𝓡∂ 1).prod (𝓡 1)) (𝓘(ℝ).prod (𝓡 1))
      (fun q : Time × Circle => ((Subtype.val ∘ Prod.fst) q,Prod.snd q)) (0,z) (v,0) = _
    rw [mfderiv_prodMk
      ((contMDiff_subtypeVal_Icc.comp contMDiff_fst :
        ContMDiff ((𝓡∂ 1).prod (𝓡 1)) 𝓘(ℝ) ∞ (Subtype.val ∘ Prod.fst)).mdifferentiableAt (by simp))
      mdifferentiableAt_snd,
      mfderiv_comp (0,z) ((contMDiff_subtypeVal_Icc (n := ∞)).mdifferentiableAt (by simp))
        mdifferentiableAt_fst,mfderiv_fst,mfderiv_snd]
    rfl
  have hn := b2_strip_label_transverse_v489 phi hphi hzero hrank z
  have hcoord :
      (((show (Euc 1 × Euc 1) →L[ℝ] (Euc 1 × Euc 1) from
        mfderiv ((𝓡∂ 1).prod (𝓡 1)) ((𝓡 1).prod (𝓡 1)) phi (0,z)) (v,0)).1) 0 ≠ 0 := by
    intro hc
    apply hn
    ext i
    fin_cases i
    exact hc
  have he := congrArg (fun D : (Euc 1 × Euc 1) →L[ℝ] ℝ => D (v,0))
    (hleft.symm.trans hright)
  change mfderiv (𝓘(ℝ).prod (𝓡 1)) 𝓘(ℝ) f (0,z)
      (mfderiv ((𝓡∂ 1).prod (𝓡 1)) (𝓘(ℝ).prod (𝓡 1)) P (0,z) (v,0)) = _ at he
  rw [hPder] at he
  intro hbad
  have hz : mfderiv (𝓘(ℝ).prod (𝓡 1)) 𝓘(ℝ) f (0,z)
      (mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : Time → ℝ) 0 v,0) = 0 := by
    let d : ℝ := mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : Time → ℝ) 0 v
    have hd : (d,(0 : Euc 1)) = d • ((1 : ℝ),(0 : Euc 1)) := by simp
    change mfderiv (𝓘(ℝ).prod (𝓡 1)) 𝓘(ℝ) f (0,z) (d,0) = 0
    rw [hd,map_smul,hbad,smul_zero]
  exact hcoord (he.symm.trans hz)

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
end

-- Exact source from B2CompactInverseV489.lean

noncomputable section
open Set Topology Function Filter Manifold
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

private theorem smooth_local_inverse_v489
    {f : ℝ × Circle → ℝ × Circle}
    (hf : ContMDiff (𝓘(ℝ).prod (𝓡 1)) (𝓘(ℝ).prod (𝓡 1)) ∞ f)
    {x : ℝ × Circle}
    (hinv : (mfderiv (𝓘(ℝ).prod (𝓡 1)) (𝓘(ℝ).prod (𝓡 1)) f x).IsInvertible) :
    IsLocalDiffeomorphAt (𝓘(ℝ).prod (𝓡 1)) (𝓘(ℝ).prod (𝓡 1)) ∞ f x := by
  obtain ⟨Phi,hxPhi,hEqPhi⟩ :=
    DifferentialGeometry.Coordinates.contMDiffAt_isLocalDiffeomorphAt_of_mfderiv
      (n := 1) le_rfl (by exact_mod_cast (WithTop.one_ne_top : (1 : ℕ∞) ≠ ⊤))
      (hf.contMDiffAt.of_le (by exact_mod_cast le_top)) hinv
  have hInvPhi : ∀ z ∈ Phi.source,
      (mfderiv (𝓘(ℝ).prod (𝓡 1)) (𝓘(ℝ).prod (𝓡 1)) f z).IsInvertible := by
    intro z hz
    exact (show IsLocalDiffeomorphAt (𝓘(ℝ).prod (𝓡 1)) (𝓘(ℝ).prod (𝓡 1)) 1 f z from
      ⟨Phi,hz,hEqPhi⟩).isInvertible_mfderiv (by norm_num)
  have hs : ContMDiffOn (𝓘(ℝ).prod (𝓡 1)) (𝓘(ℝ).prod (𝓡 1)) ∞
      (Phi.symm : ℝ × Circle → ℝ × Circle) Phi.target := by
    rw [contMDiffOn_infty]
    intro k y hy
    let z : ℝ × Circle := Phi.symm y
    have hz : z ∈ Phi.source := Phi.toPartialEquiv.map_target hy
    have hfz : f z = y := by
      rw [hEqPhi hz]
      exact Phi.toPartialEquiv.right_inv hy
    obtain ⟨Psi,hzPsi,hEqPsi⟩ :=
      DifferentialGeometry.Coordinates.contMDiffAt_isLocalDiffeomorphAt_of_mfderiv
        (n := ((max 1 k : ℕ) : ℕ∞ω)) (by exact_mod_cast le_max_left 1 k)
        (by exact_mod_cast ENat.natCast_ne_top (max 1 k))
        (hf.contMDiffAt.of_le (by exact_mod_cast le_top)) (hInvPhi z hz)
    have hyPsi : y ∈ Psi.target := by
      rw [← hfz,hEqPsi hzPsi]
      exact Psi.toPartialEquiv.map_source hzPsi
    have hPsiY : (Psi.symm : ℝ × Circle → ℝ × Circle) y = z := by
      rw [← hfz,hEqPsi hzPsi]
      exact Psi.toPartialEquiv.left_inv hzPsi
    have hnear : (Phi.symm : ℝ × Circle → ℝ × Circle) =ᶠ[𝓝 y] Psi.symm := by
      have hpre := (Psi.symm.contMDiffOn.continuousOn.continuousAt
        (Psi.open_target.mem_nhds hyPsi)).preimage_mem_nhds
          (by rw [hPsiY]; exact Phi.open_source.mem_nhds hz)
      filter_upwards [Psi.open_target.mem_nhds hyPsi,hpre,Phi.open_target.mem_nhds hy]
        with y' hy'Psi hy'pre hy'Phi
      have hz'Psi : Psi.symm y' ∈ Psi.source := Psi.toPartialEquiv.map_target hy'Psi
      have hfPsi : f (Psi.symm y') = y' := by
        rw [hEqPsi hz'Psi]
        exact Psi.toPartialEquiv.right_inv hy'Psi
      apply Phi.toPartialEquiv.injOn (Phi.toPartialEquiv.map_target hy'Phi) hy'pre
      rw [Phi.toPartialEquiv.right_inv hy'Phi,← hEqPhi hy'pre,hfPsi]
    have hPsi : ContMDiffAt (𝓘(ℝ).prod (𝓡 1)) (𝓘(ℝ).prod (𝓡 1)) (k : ℕ∞ω)
        (Psi.symm : ℝ × Circle → ℝ × Circle) y :=
      (Psi.symm.contMDiffOn.contMDiffAt (Psi.open_target.mem_nhds hyPsi)).of_le
        (by exact_mod_cast le_max_right 1 k)
    exact (hPsi.congr_of_eventuallyEq hnear).contMDiffWithinAt
  refine ⟨{ toPartialEquiv := Phi.toPartialEquiv
            open_source := Phi.open_source
            open_target := Phi.open_target
            contMDiffOn_toFun := hf.contMDiffOn.congr (fun z hz => (hEqPhi hz).symm)
            contMDiffOn_invFun := hs },hxPhi,hEqPhi⟩

/-- Injective finite rank of the phase-time map at the whole initial circle. -/
theorem b2_phase_graph_rank_v489 (f : ℝ × Circle → ℝ)
    (hf : ContMDiff (𝓘(ℝ).prod (𝓡 1)) 𝓘(ℝ) ∞ f)
    (htrans : ∀ z, mfderiv (𝓘(ℝ).prod (𝓡 1)) 𝓘(ℝ) f (0,z) (1,0) ≠ 0)
    (z : Circle) :
    (mfderiv (𝓘(ℝ).prod (𝓡 1)) (𝓘(ℝ).prod (𝓡 1))
      (fun q : ℝ × Circle => (f q,q.2)) (0,z)).IsInvertible := by
  let D : (ℝ × Euc 1) →L[ℝ] (ℝ × Euc 1) :=
    mfderiv (𝓘(ℝ).prod (𝓡 1)) (𝓘(ℝ).prod (𝓡 1))
      (fun q : ℝ × Circle => (f q,q.2)) (0,z)
  let d : (ℝ × Euc 1) →L[ℝ] ℝ := mfderiv (𝓘(ℝ).prod (𝓡 1)) 𝓘(ℝ) f (0,z)
  have hD : D = d.prod
      (ContinuousLinearMap.snd ℝ ℝ (Euc 1)) := by
    have he := mfderiv_prodMk (hf.mdifferentiableAt (x := (0,z)) (by simp))
      (mdifferentiableAt_snd (x := (0,z)))
    rw [mfderiv_snd] at he
    exact he
  have hi : Injective D := by
    intro u v huv
    have hw : u.2 = v.2 := by
      have h := congrArg Prod.snd huv
      rw [hD] at h
      exact h
    have hsub : D (u-v) = 0 := by rw [map_sub,huv,sub_self]
    have hd : u-v = (u.1-v.1) • ((1 : ℝ),(0 : Euc 1)) := by ext <;> simp [hw]
    have hs : (u.1-v.1) * d (1,0) = 0 := by
      have h := congrArg Prod.fst hsub
      rw [hd,map_smul,hD] at h
      exact h
    have hfirst : u.1 = v.1 := sub_eq_zero.mp ((mul_eq_zero.mp hs).resolve_right (htrans z))
    exact Prod.ext hfirst hw
  let e : (ℝ × Euc 1) ≃ₗ[ℝ] (ℝ × Euc 1) := D.toLinearMap.linearEquivOfInjective hi rfl
  let eL : (ℝ × Euc 1) ≃L[ℝ] (ℝ × Euc 1) := {
    toLinearEquiv := e
    continuous_toFun := D.continuous
    continuous_invFun := e.symm.toLinearMap.continuous_of_finiteDimensional }
  exact ⟨eL,rfl⟩

/-- The local smooth inverses glue around the entire compact initial circle,
with the phase map itself as the literal forward function. -/
theorem b2_phase_compact_partialDiffeomorph_v489 (f : ℝ × Circle → ℝ)
    (hf : ContMDiff (𝓘(ℝ).prod (𝓡 1)) 𝓘(ℝ) ∞ f)
    (hzero : ∀ z, f (0,z) = 0)
    (htrans : ∀ z, mfderiv (𝓘(ℝ).prod (𝓡 1)) 𝓘(ℝ) f (0,z) (1,0) ≠ 0) :
    ∃ e : PartialDiffeomorph (𝓘(ℝ).prod (𝓡 1)) (𝓘(ℝ).prod (𝓡 1))
        (ℝ × Circle) (ℝ × Circle) ∞,
      (e : ℝ × Circle → ℝ × Circle) = (fun q => (f q,q.2)) ∧
      ({0} ×ˢ (univ : Set Circle)) ⊆ e.source ∧
      ({0} ×ˢ (univ : Set Circle)) ⊆ e.target ∧
      (∀ z, (e.symm : ℝ × Circle → ℝ × Circle) (0,z) = (0,z)) := by
  classical
  let H : ℝ × Circle → ℝ × Circle := fun q => (f q,q.2)
  have hH : ContMDiff (𝓘(ℝ).prod (𝓡 1)) (𝓘(ℝ).prod (𝓡 1)) ∞ H :=
    hf.prodMk contMDiff_snd
  have hloc (z : Circle) : IsLocalDiffeomorphAt (𝓘(ℝ).prod (𝓡 1))
      (𝓘(ℝ).prod (𝓡 1)) ∞ H (0,z) :=
    smooth_local_inverse_v489 hH (b2_phase_graph_rank_v489 f hf htrans z)
  choose Phi hPhi hEq using hloc
  let O : Set (ℝ × Circle) := ⋃ z, (Phi z).source
  have hO : IsOpen O := isOpen_iUnion fun z => (Phi z).open_source
  let K : Set (ℝ × Circle) := {0} ×ˢ univ
  have hK : IsCompact K := isCompact_singleton.prod isCompact_univ
  have hKO : K ⊆ O := by
    rintro ⟨t,z⟩ ⟨ht,_⟩
    have ht0 : t = 0 := ht
    subst t
    exact mem_iUnion.mpr ⟨z,hPhi z⟩
  have hlocalO : ∀ p ∈ O, IsLocalDiffeomorphAt (𝓘(ℝ).prod (𝓡 1))
      (𝓘(ℝ).prod (𝓡 1)) ∞ H p := by
    intro p hp
    obtain ⟨z,hz⟩ := mem_iUnion.mp hp
    exact ⟨Phi z,hz,hEq z⟩
  have hKinj : InjOn H K := by
    intro u hu v hv huv
    have hfirst : u.1 = v.1 := (show u.1 = 0 from hu.1).trans (show v.1 = 0 from hv.1).symm
    have hsecond := congrArg (fun r : ℝ × Circle => r.2) huv
    exact Prod.ext hfirst hsecond
  obtain ⟨T,hT,hKT,hTinj⟩ := hKinj.exists_isOpen_superset hK
    (fun p _ => hH.continuous.continuousAt) (by
      intro p hp
      obtain ⟨Phi',hpPhi',hEqPhi'⟩ := hlocalO p (hKO hp)
      refine ⟨Phi'.source,Phi'.open_source.mem_nhds hpPhi',?_⟩
      intro u hu v hv huv
      exact Phi'.toPartialEquiv.injOn hu hv
        ((hEqPhi' hu).symm.trans (huv.trans (hEqPhi' hv))))
  let R : Set (ℝ × Circle) := T ∩ O
  have hR : IsOpen R := hT.inter hO
  have hKR : K ⊆ R := fun p hp => ⟨hKT hp,hKO hp⟩
  have hRinj : InjOn H R := hTinj.mono inter_subset_left
  have hlocalR : IsLocalDiffeomorphOn (𝓘(ℝ).prod (𝓡 1)) (𝓘(ℝ).prod (𝓡 1)) ∞ H R := by
    rintro ⟨p,hp⟩
    exact hlocalO p hp.2
  have hopen : IsOpenMap (R.domRestrict H) := by
    intro W hW
    rw [Set.domRestrict_eq,Set.image_comp]
    let V : Set (ℝ × Circle) := ((↑) : R → ℝ × Circle) '' W
    have hV : IsOpen V := hR.isOpenMap_subtype_val W hW
    have hVR : V ⊆ R := by rintro _ ⟨p,hp,rfl⟩; exact p.2
    change IsOpen (H '' V)
    rw [isOpen_iff_forall_mem_open]
    rintro _ ⟨p,hp,rfl⟩
    obtain ⟨Psi,hpPsi,hEqPsi⟩ := hlocalR ⟨p,hVR hp⟩
    refine ⟨Psi.toOpenPartialHomeomorph '' (V ∩ Psi.source),?_,?_,?_⟩
    · rintro _ ⟨q,hq,rfl⟩
      exact ⟨q,hq.1,hEqPsi hq.2⟩
    · exact Psi.toOpenPartialHomeomorph.isOpen_image_of_subset_source
        (hV.inter Psi.open_source) inter_subset_right
    · exact ⟨p,⟨hp,hpPsi⟩, (hEqPsi hpPsi).symm⟩
  let e : OpenPartialHomeomorph (ℝ × Circle) (ℝ × Circle) :=
    OpenPartialHomeomorph.ofContinuousOpenRestrict (hRinj.toPartialEquiv H R)
      (hH.continuous.continuousOn) hopen hR
  have he_coe : (e : ℝ × Circle → ℝ × Circle) = H := rfl
  have he_source : e.source = R := rfl
  have he_smooth : ContMDiffOn (𝓘(ℝ).prod (𝓡 1)) (𝓘(ℝ).prod (𝓡 1)) ∞ e.symm e.target := by
    intro y hy
    let p : ℝ × Circle := e.symm y
    have hp : p ∈ R := e.map_target hy
    obtain ⟨Psi,hpPsi,hEqPsi⟩ := hlocalR ⟨p,hp⟩
    have hpH : H p = y := e.right_inv hy
    have hyPsi : y ∈ Psi.target := by
      rw [← hpH,hEqPsi hpPsi]
      exact Psi.toPartialEquiv.map_source hpPsi
    have hPsiY : (Psi.symm : ℝ × Circle → ℝ × Circle) y = p := by
      rw [← hpH,hEqPsi hpPsi]
      exact Psi.toPartialEquiv.left_inv hpPsi
    have hnear : e.symm =ᶠ[𝓝 y] (Psi.symm : ℝ × Circle → ℝ × Circle) := by
      have hpre := (Psi.symm.contMDiffOn.continuousOn.continuousAt
        (Psi.open_target.mem_nhds hyPsi)).preimage_mem_nhds
          (by rw [hPsiY]; exact hR.mem_nhds hp)
      filter_upwards [Psi.open_target.mem_nhds hyPsi,hpre,e.open_target.mem_nhds hy]
        with y' hy'Psi hy'pre hy'e
      have hp'Psi : Psi.symm y' ∈ Psi.source := Psi.toPartialEquiv.map_target hy'Psi
      have hH' : H (Psi.symm y') = y' := by
        rw [hEqPsi hp'Psi]
        exact Psi.toPartialEquiv.right_inv hy'Psi
      apply e.injOn (e.map_target hy'e) hy'pre
      rw [e.right_inv hy'e,he_coe,hH']
    exact ((Psi.symm.contMDiffOn.contMDiffAt (Psi.open_target.mem_nhds hyPsi)).congr_of_eventuallyEq
      hnear).contMDiffWithinAt
  let E : PartialDiffeomorph (𝓘(ℝ).prod (𝓡 1)) (𝓘(ℝ).prod (𝓡 1))
      (ℝ × Circle) (ℝ × Circle) ∞ := {
    toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := hH.contMDiffOn
    contMDiffOn_invFun := he_smooth }
  have hEzero (z : Circle) : E (0,z) = (0,z) := by
    change (f (0,z),z) = (0,z)
    rw [hzero]
  refine ⟨E,rfl,hKR,?_,?_⟩
  · rintro ⟨t,z⟩ ⟨ht,_⟩
    have ht0 : t = 0 := ht
    subst t
    rw [← hEzero z]
    exact E.toPartialEquiv.map_source (hKR (show (0,z) ∈ K from ⟨by simp,mem_univ z⟩))
  · intro z
    calc (E.symm : ℝ × Circle → ℝ × Circle) (0,z) = E.symm (E (0,z)) :=
        congrArg E.symm (hEzero z).symm
      _ = (0,z) := E.toPartialEquiv.left_inv
        (hKR (show (0,z) ∈ K from ⟨by simp,mem_univ z⟩))

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
end

-- Exact source from B2PositiveInverseV489.lean

noncomputable section
open Set Topology Function Filter Manifold
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- Restricting the actual compact inverse to one side gives positive times
uniformly on the whole label circle. The side is chosen from the inverse, not
assumed as an orientation input. An arbitrary prescribed open source window
around the initial circle is retained. -/
theorem b2_positive_phase_inverse_v489 (f : ℝ × Circle → ℝ)
    (hzero : ∀ z, f (0,z) = 0)
    (e : PartialDiffeomorph (𝓘(ℝ).prod (𝓡 1)) (𝓘(ℝ).prod (𝓡 1))
      (ℝ × Circle) (ℝ × Circle) ∞)
    (he : (e : ℝ × Circle → ℝ × Circle) = fun q => (f q,q.2))
    (hsource : ({0} ×ˢ (univ : Set Circle)) ⊆ e.source)
    (htarget : ({0} ×ˢ (univ : Set Circle)) ⊆ e.target)
    (hinitial : ∀ z, (e.symm : ℝ × Circle → ℝ × Circle) (0,z) = (0,z))
    (R : Set (ℝ × Circle)) (hR : IsOpen R)
    (hRzero : ({0} ×ˢ (univ : Set Circle)) ⊆ R) :
    ∃ b sign : ℝ, 0 < b ∧ (sign = 1 ∨ sign = -1) ∧
      ∃ tau : ℝ × Circle → ℝ,
        ContMDiffOn (𝓘(ℝ).prod (𝓡 1)) 𝓘(ℝ) ∞ tau (Icc (0 : ℝ) b ×ˢ univ) ∧
        (∀ z, tau (0,z) = 0) ∧
        (∀ s ∈ Icc (0 : ℝ) b, ∀ z, (tau (s,z),z) ∈ R ∧ f (tau (s,z),z) = sign*s) ∧
        (∀ s ∈ Ioc (0 : ℝ) b, ∀ z, 0 < tau (s,z)) := by
  classical
  let N : Set (ℝ × Circle) := e.target ∩ (e.symm : ℝ × Circle → ℝ × Circle) ⁻¹' R
  have hN : IsOpen N :=
    e.symm.contMDiffOn.continuousOn.isOpen_inter_preimage e.open_target hR
  have hNzero : ({0} ×ˢ (univ : Set Circle)) ⊆ N := by
    rintro ⟨s,z⟩ ⟨hs,hz⟩
    have hs0 : s = 0 := hs
    subst s
    exact ⟨htarget ⟨by simp,hz⟩,by rw [mem_preimage,hinitial]; exact hRzero ⟨by simp,hz⟩⟩
  obtain ⟨V,W,hV,hW,h0V,hUW,hVW⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_univ hN hNzero
  obtain ⟨d,hd,hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds (show (0 : ℝ) ∈ V from h0V (by simp)))
  let c : ℝ := d/2
  have hc : 0 < c := half_pos hd
  have hcylinder : Icc (-c) c ×ˢ (univ : Set Circle) ⊆ N := by
    intro q hq
    apply hVW
    refine ⟨hball ?_,hUW hq.2⟩
    rw [Metric.mem_ball,Real.dist_eq,sub_zero]
    exact (abs_le.mpr hq.1).trans_lt (half_lt_self hd)
  let A : Set (ℝ × Circle) :=
    (e.source ∩ (e : ℝ × Circle → ℝ × Circle) ⁻¹' (Ioo (-c) c ×ˢ univ)) ∩ R
  have hA : IsOpen A :=
    (e.contMDiffOn.continuousOn.isOpen_inter_preimage e.open_source
      (isOpen_Ioo.prod isOpen_univ)).inter hR
  have h0A : ((0 : ℝ),(1 : Circle)) ∈ A := by
    refine ⟨⟨hsource ⟨by simp,mem_univ _⟩,?_⟩,hRzero ⟨by simp,mem_univ _⟩⟩
    rw [mem_preimage,he]
    exact ⟨⟨by simpa [hzero] using neg_lt_zero.mpr hc,by simpa [hzero] using hc⟩,mem_univ _⟩
  have hpre := (continuousAt_id.prodMk continuousAt_const).preimage_mem_nhds (hA.mem_nhds h0A)
  obtain ⟨eta,heta,hetaA⟩ := Metric.mem_nhds_iff.mp hpre
  let t : ℝ := eta/2
  have ht : 0 < t := half_pos heta
  have htA : (t,(1 : Circle)) ∈ A := hetaA (by
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos ht]
    exact half_lt_self heta)
  let y : ℝ := f (t,1)
  have hybound : y ∈ Ioo (-c) c := by
    have h := htA.1.2
    rw [mem_preimage,he] at h
    exact h.1
  have hy : y ≠ 0 := by
    intro hy0
    have hsame : e (t,(1 : Circle)) = e (0,(1 : Circle)) := by simp only [he,y,hzero,hy0]
    have heq := e.toPartialEquiv.injOn htA.1.1 (hsource ⟨by simp,mem_univ _⟩) hsame
    exact ht.ne' (congrArg (fun q : ℝ × Circle => q.1) heq)
  let sign : ℝ := if 0 < y then 1 else -1
  have hsign : sign = 1 ∨ sign = -1 := by dsimp only [sign]; split <;> simp
  have hsignabs (s : ℝ) : |sign*s| = |s| := by
    rcases hsign with hs | hs <;> rw [hs] <;> simp
  have hsigny : sign*|y| = y := by
    dsimp only [sign]
    split_ifs with hp
    · simp [abs_of_pos hp]
    · have hn : y < 0 := lt_of_le_of_ne (le_of_not_gt hp) hy
      simp [abs_of_neg hn]
  let P : ℝ × Circle → ℝ × Circle := fun q => (sign*q.1,q.2)
  let tau : ℝ × Circle → ℝ := fun q => (e.symm (P q)).1
  have hP : ContMDiff (𝓘(ℝ).prod (𝓡 1)) (𝓘(ℝ).prod (𝓡 1)) ∞ P :=
    (contMDiff_const.mul contMDiff_fst).prodMk contMDiff_snd
  have hPN (s : ℝ) (hs : |s| ≤ c) (z : Circle) : P (s,z) ∈ N :=
    hcylinder ⟨abs_le.mp (by rw [hsignabs]; exact hs),mem_univ z⟩
  have hright (s : ℝ) (hs : |s| ≤ c) (z : Circle) :
      (tau (s,z),z) ∈ R ∧ f (tau (s,z),z) = sign*s := by
    have hN' := hPN s hs z
    have heq := e.toPartialEquiv.right_inv hN'.1
    rw [he] at heq
    have hz : (e.symm (P (s,z))).2 = z := congrArg (fun q : ℝ × Circle => q.2) heq
    have hpair : e.symm (P (s,z)) = (tau (s,z),z) := Prod.ext rfl hz
    refine ⟨?_,?_⟩
    · rw [← hpair]
      exact hN'.2
    · have h := congrArg (fun q : ℝ × Circle => q.1) heq
      change f ((e.symm : ℝ × Circle → ℝ × Circle) (P (s,z))) = sign*s at h
      rw [hpair] at h
      exact h
  let D : Set (ℝ × Circle) := Ioo (0 : ℝ) c ×ˢ univ
  have hDc : ContinuousOn tau D :=
    (continuous_fst.comp_continuousOn e.symm.contMDiffOn.continuousOn).comp
      hP.continuous.continuousOn (fun q hq => (hPN q.1 (by rw [abs_of_pos hq.1.1]; exact hq.1.2.le) q.2).1)
  have hnonzero : ∀ q ∈ D, tau q ≠ 0 := by
    intro q hq hn
    have h := (hright q.1 (by rw [abs_of_pos hq.1.1]; exact hq.1.2.le) q.2).2
    rw [hn,hzero] at h
    have hsgn : sign ≠ 0 := by rcases hsign with hs | hs <;> rw [hs] <;> norm_num
    exact (mul_ne_zero hsgn hq.1.1.ne') h.symm
  have hanchor : ∃ q ∈ D, 0 < tau q := by
    have habs : |y| ∈ Ioo (0 : ℝ) c := ⟨abs_pos.mpr hy,abs_lt.mpr hybound⟩
    refine ⟨(|y|,(1 : Circle)),⟨habs,mem_univ _⟩,?_⟩
    have hp : P (|y|,(1 : Circle)) = e (t,(1 : Circle)) := by
      rw [he]
      exact Prod.ext hsigny rfl
    change 0 < (e.symm (P (|y|,(1 : Circle)))).1
    rw [hp]
    change 0 < (e.toPartialEquiv.symm (e.toPartialEquiv (t,(1 : Circle)))).1
    rw [e.toPartialEquiv.left_inv htA.1.1]
    exact ht
  have hpositive : ∀ q ∈ D, 0 < tau q := by
    intro q hq
    exact (isPreconnected_Ioo.prod isPreconnected_univ).lt_of_ne hDc hnonzero hanchor hq
  have hb : 0 < c/2 := half_pos hc
  have hsmall (s : ℝ) (hs : s ∈ Icc (0 : ℝ) (c/2)) : |s| ≤ c := by
    rw [abs_of_nonneg hs.1]
    exact hs.2.trans (half_le_self hc.le)
  refine ⟨c/2,sign,hb,hsign,tau,?_,?_,?_,?_⟩
  · exact (contMDiff_fst.comp_contMDiffOn e.symm.contMDiffOn).comp hP.contMDiffOn
      (fun q hq => (hPN q.1 (hsmall q.1 hq.1) q.2).1)
  · intro z
    change (e.symm (sign*0,z)).1 = 0
    rw [mul_zero,hinitial]
  · intro s hs z
    exact hright s (hsmall s hs) z
  · intro s hs z
    exact hpositive (s,z) ⟨⟨hs.1,hs.2.trans_lt (half_lt_self hc)⟩,mem_univ z⟩

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
end

-- Exact source from B2InverseDerivativeV489.lean

noncomputable section
open Set Topology Function Filter Manifold
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- The positive inverse branch has strictly positive initial speed. This
follows from its inverse identity and positivity, without an orientation premise. -/
theorem b2_positive_inverse_initial_derivative_v489
    (f G : ℝ × Circle → ℝ)
    (hf : ContMDiff (𝓘(ℝ).prod (𝓡 1)) 𝓘(ℝ) ∞ f)
    (hG : ContMDiff (𝓘(ℝ).prod (𝓡 1)) 𝓘(ℝ) ∞ G)
    {b sign : ℝ} (hb : 0 < b) (hsign : sign ≠ 0)
    (hzero : ∀ z, G (0,z) = 0)
    (hinverse : ∀ s ∈ Icc (0 : ℝ) b, ∀ z, f (G (s,z),z) = sign*s)
    (hpositive : ∀ s ∈ Ioc (0 : ℝ) b, ∀ z, 0 < G (s,z)) (z : Circle) :
    0 < deriv (fun s => G (s,z)) 0 := by
  let g : ℝ → ℝ := fun s => G (s,z)
  let l : ℝ → ℝ := fun t => f (t,z)
  have hg : ContDiff ℝ ∞ g := contMDiff_iff_contDiff.mp
    (hG.comp (contMDiff_id.prodMk contMDiff_const))
  have hl : ContDiff ℝ ∞ l := contMDiff_iff_contDiff.mp
    (hf.comp (contMDiff_id.prodMk contMDiff_const))
  have hg0 : g 0 = 0 := hzero z
  have hgD := (hg.differentiable (by simp) 0).hasDerivAt
  have hlD := (hl.differentiable (by simp) (g 0)).hasDerivAt
  have hchain := (hlD.comp 0 hgD).hasDerivWithinAt (s := Icc (0 : ℝ) b)
  have heq : EqOn (l ∘ g) (fun s : ℝ => sign*s) (Icc (0 : ℝ) b) := by
    intro s hs
    exact hinverse s hs z
  have hchain' : HasDerivWithinAt (fun s : ℝ => sign*s)
      (deriv l (g 0) * deriv g 0) (Icc (0 : ℝ) b) 0 :=
    hchain.congr (fun x hx => (heq hx).symm) ((heq (by simp [hb.le])).symm)
  have hDsign : HasDerivWithinAt (fun s : ℝ => sign*s) sign (Icc (0 : ℝ) b) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul sign).hasDerivWithinAt
  have hv : deriv l (g 0) * deriv g 0 = sign :=
    (hchain'.derivWithin (uniqueDiffOn_Icc hb 0 (by simp [hb.le]))).symm.trans
      (hDsign.derivWithin (uniqueDiffOn_Icc hb 0 (by simp [hb.le])))
  have hne : deriv g 0 ≠ 0 := by
    intro h
    rw [h,mul_zero] at hv
    exact hsign hv.symm
  have hnonneg : 0 ≤ deriv g 0 := by
    apply ge_of_tendsto (hgD.tendsto_slope.mono_left (nhdsGT_le_nhdsNE 0))
    filter_upwards [Ioo_mem_nhdsGT hb] with s hs
    rw [slope_def_field,hg0,sub_zero,sub_zero]
    exact div_nonneg (hpositive s ⟨hs.1,hs.2.le⟩ z).le hs.1.le
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
end

-- Exact source from B2EuclideanExtensionV489.lean

noncomputable section
open Set Topology Function Filter Manifold
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

/-- The literal exterior inclusion followed by the standard sphere inclusion. -/
def b2_euclidean_inclusion_v489 (E : SmoothExterior T) : E.Carrier → Euc 4 :=
  fun x => (E.toSphere x : Euc 4)

theorem b2_euclidean_inclusion_smooth_v489 :
    ContMDiff (𝓡∂ 3) 𝓘(ℝ,Euc 4) ∞ (b2_euclidean_inclusion_v489 E) := by
  letI : Fact (Module.finrank ℝ (Euc 4) = 3+1) := ⟨by simp [Euc]⟩
  have hinc : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  exact contMDiff_coe_sphere.comp hinc.contMDiff

theorem b2_leaf_euclidean_smoothEmbedding_v489 (J : LongitudeFoliation.{0} E) (a : Circle) :
    IsSmoothEmbedding (𝓡 1) 𝓘(ℝ,Euc 4) ∞
      (fun z => b2_euclidean_inclusion_v489 E (J.torus (a,z))) := by
  letI : Fact (Module.finrank ℝ (Euc 4) = 3+1) := ⟨by simp [Euc]⟩
  have hinc : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  let pair : Circle → Circle × Circle := fun z => (a,z)
  have hpair : ContMDiff (𝓡 1) ((𝓡 1).prod (𝓡 1)) ∞ pair :=
    contMDiff_const.prodMk contMDiff_id
  let l : Circle → E.Carrier := J.torus ∘ pair
  have hl : ContMDiff (𝓡 1) (𝓡∂ 3) ∞ l := J.smoothEmbedding.contMDiff.comp hpair
  have hlrank (z : Circle) : Injective (mfderiv (𝓡 1) (𝓡∂ 3) l z) := by
    rw [show l = J.torus ∘ pair from rfl,
      mfderiv_comp z (J.smoothEmbedding.contMDiff.mdifferentiableAt (by simp))
        (hpair.mdifferentiableAt (by simp))]
    have hr : Injective (mfderiv (𝓡 1) ((𝓡 1).prod (𝓡 1)) pair z) := by
      change Injective (mfderiv (𝓡 1) ((𝓡 1).prod (𝓡 1)) (fun z : Circle => (a,z)) z)
      rw [mfderiv_prod_right]
      exact fun u v h => congrArg Prod.snd h
    exact (J.smoothEmbedding.isImmersion.mfderiv_injective (by simp) _).comp hr
  let k : Circle → ThreeSphere := E.toSphere ∘ l
  have hk : ContMDiff (𝓡 1) (𝓡 3) ∞ k := hinc.contMDiff.comp hl
  have hkrank (z : Circle) : Injective (mfderiv (𝓡 1) (𝓡 3) k z) := by
    rw [show k = E.toSphere ∘ l from rfl,
      mfderiv_comp z (hinc.contMDiff.mdifferentiableAt (by simp))
        (hl.mdifferentiableAt (by simp))]
    exact (hinc.isImmersion.mfderiv_injective (by simp) _).comp (hlrank z)
  let j : Circle → Euc 4 := (Subtype.val : ThreeSphere → Euc 4) ∘ k
  have hs : ContMDiff (𝓡 1) 𝓘(ℝ,Euc 4) ∞ j := contMDiff_coe_sphere.comp hk
  have hrank (z : Circle) : Injective (mfderiv (𝓡 1) 𝓘(ℝ,Euc 4) j z) := by
    rw [show j = (Subtype.val : ThreeSphere → Euc 4) ∘ k from rfl,
      mfderiv_comp z ((contMDiff_coe_sphere (m := ∞)).mdifferentiableAt (by simp))
        (hk.mdifferentiableAt (by simp))]
    exact (mfderiv_coe_sphere_injective (k z)).comp (hkrank z)
  refine ⟨DifferentialGeometry.Topology.Manifold.isImmersion_of_injective_mfderiv
    (by simp) hs hrank,?_⟩
  exact IsEmbedding.subtypeVal.comp (hinc.isEmbedding.comp
    (J.smoothEmbedding.isEmbedding.comp (isEmbedding_prodMkRight a)))

/-- Extend the actual boundary inverse time in the fixed Euclidean inclusion.
The extension has no geometric input beyond the original longitude torus. -/
theorem b2_boundary_time_euclidean_extension_v489 (J : LongitudeFoliation.{0} E) (a : Circle)
    (tau : ℝ × Circle → ℝ)
    (htau : ContMDiff (𝓘(ℝ).prod (𝓡 1)) 𝓘(ℝ) ∞ tau) :
    ∃ G : ℝ × Euc 4 → ℝ, ContDiff ℝ ∞ G ∧
      ∀ s z, G (s,b2_euclidean_inclusion_v489 E (J.torus (a,z))) = tau (s,z) := by
  let j : Circle → Euc 4 := fun z => b2_euclidean_inclusion_v489 E (J.torus (a,z))
  have hj := b2_leaf_euclidean_smoothEmbedding_v489 J a
  have hemb : IsSmoothEmbedding (𝓘(ℝ).prod (𝓡 1)) 𝓘(ℝ,ℝ × Euc 4) ∞
      (Prod.map (id : ℝ → ℝ) j) := by
    rw [modelWithCornersSelf_prod,← chartedSpaceSelf_prod]
    exact (IsSmoothEmbedding.id (I := 𝓘(ℝ)) (M := ℝ)).prodMap hj
  have hclosed : IsClosed ((Prod.map (id : ℝ → ℝ) j) '' univ) := by
    rw [image_univ,range_prodMap]
    simpa only [range_id] using isClosed_univ.prod (isCompact_range hj.isEmbedding.continuous).isClosed
  obtain ⟨G,hG,hGeq⟩ := hemb.exists_contDiff_extension_of_isClosed_image htau hclosed
  exact ⟨G,hG,fun s z => hGeq (mem_univ (s,z))⟩

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
end

-- Exact source from B2LeafRangeV489.lean

noncomputable section
open Set Topology Function Filter Manifold
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {S : CompactOrientedSurface.{0}} {F : NeatEmbedding S E.Carrier}
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- A phase-corrected boundary strip covers its entire longitude leaf. The
second torus coordinate is surjective by invariance of domain on the circle. -/
theorem b2_corrected_strip_whole_leaf_v489 (J : LongitudeFoliation.{0} E)
    {U : Set E.Carrier} (collar : OneSidedCollar F U)
    (p : Circle → S)
    (phi : Time × Circle → Circle × Circle) (hephi : IsEmbedding phi)
    (hmap : ∀ q, J.torus (phi q) = collar.map (p q.2,collar.epsilon/2*(q.1 : ℝ)))
    (ell : Circle → ℝ) (W : Set Circle) (hell : InjOn ell W)
    (tau : Circle → Time) (htau : Continuous tau)
    (hW : ∀ z, (phi (tau z,z)).1 ∈ W)
    (hconstant : ∀ z, ell (phi (tau z,z)).1 = ell (phi (tau 1,1)).1) :
    range (fun z => collar.map (p z,collar.epsilon/2*(tau z : ℝ))) =
      J.leaf (phi (tau 1,1)).1 := by
  let c : Circle → Circle := fun z => (phi (tau z,z)).2
  have hc : Continuous c := continuous_snd.comp (hephi.continuous.comp (htau.prodMk continuous_id))
  have hlabel (z : Circle) : (phi (tau z,z)).1 = (phi (tau 1,1)).1 :=
    hell (hW z) (hW 1) (hconstant z)
  have hinj : Injective c := by
    intro z w hzw
    have hp : phi (tau z,z) = phi (tau w,w) :=
      Prod.ext ((hlabel z).trans (hlabel w).symm) hzw
    exact congrArg Prod.snd (hephi.injective hp)
  have hsurj : Surjective c :=
    DifferentialGeometry.Topology.surjective_of_continuous_injective (E := Euc 1) hc hinj
  apply subset_antisymm
  · rintro _ ⟨z,rfl⟩
    refine ⟨c z,?_⟩
    change J.torus ((phi (tau 1,1)).1,c z) = collar.map (p z,collar.epsilon/2*(tau z : ℝ))
    rw [← hmap (tau z,z)]
    congr 1
    exact Prod.ext (hlabel z).symm rfl
  · rintro _ ⟨w,rfl⟩
    obtain ⟨z,hz⟩ := hsurj w
    refine ⟨z,?_⟩
    change collar.map (p z,collar.epsilon/2*(tau z : ℝ)) = J.torus ((phi (tau 1,1)).1,w)
    rw [← hmap (tau z,z)]
    congr 1
    exact Prod.ext (hlabel z) hz

/-- Continuity of the actual pulled-back collar gives a uniform initial
strip inside an arbitrary label chart. -/
theorem b2_label_window_strip_v489
    (phi : Time × Circle → Circle × Circle) (hphi : Continuous phi)
    {a : Circle} (hzero : ∀ z, phi (0,z) = (a,z))
    {W : Set Circle} (hW : IsOpen W) (haW : a ∈ W) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      ∀ t : Time, (t : ℝ) < r → ∀ z, (phi (t,z)).1 ∈ W := by
  let O : Set (Time × Circle) := (Prod.fst ∘ phi) ⁻¹' W
  have hO : IsOpen O := hW.preimage (continuous_fst.comp hphi)
  have hK : ({(0 : Time)} ×ˢ (univ : Set Circle)) ⊆ O := by
    rintro ⟨t,z⟩ ⟨ht,hz⟩
    have ht0 : t = 0 := ht
    subst t
    change (phi (0,z)).1 ∈ W
    simpa only [hzero] using haW
  obtain ⟨V,Z,hV,hZ,h0V,hUZ,hVZO⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_univ hO hK
  obtain ⟨d,hd,hball⟩ := Metric.mem_nhds_iff.mp
    (hV.mem_nhds (show (0 : Time) ∈ V from h0V (by simp)))
  refine ⟨min d (1/2),lt_min hd (by norm_num),lt_of_le_of_lt (min_le_right _ _) (by norm_num),?_⟩
  intro t ht z
  apply hVZO
  refine ⟨hball ?_,hUZ (mem_univ z)⟩
  rw [Metric.mem_ball]
  change |(t : ℝ)-0| < d
  rw [sub_zero,abs_of_nonneg t.property.1]
  exact ht.trans_le (min_le_left _ _)

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
end

-- Exact source from B2BoundaryLeafTimeV489.lean

noncomputable section
open Set Topology Function Filter Manifold
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {S : CompactOrientedSurface.{0}} {F : NeatEmbedding S E.Carrier}
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- Construct the smooth positive longitude-corrected boundary time from the
original collar and the original torus. No corrected-time oracle is assumed. -/
theorem b2_boundary_leaf_time_v489 (J : LongitudeFoliation.{0} E)
    {U : Set E.Carrier} (collar : OneSidedCollar F U)
    (p : Circle → S) (hp : ContMDiff (𝓡 1) (𝓡∂ 2) ∞ p)
    (hpe : IsEmbedding p) (hpb : ∀ z, p z ∈ S.boundary)
    {a : Circle} (hpa : ∀ z, F.toFun (p z) = J.torus (a,z)) :
    ∃ b : ℝ, 0 < b ∧ ∃ tau : ℝ × Circle → ℝ,
      ContMDiff (𝓘(ℝ).prod (𝓡 1)) 𝓘(ℝ) ∞ tau ∧
      (∀ z, tau (0,z) = 0) ∧
      (∀ z, 0 < deriv (fun s => tau (s,z)) 0) ∧
      (∀ s ∈ Icc (0 : ℝ) b, ∀ z, tau (s,z) ∈ Ico (0 : ℝ) collar.epsilon) ∧
      (∀ s ∈ Ioc (0 : ℝ) b, ∀ z, 0 < tau (s,z)) ∧
      (∀ s ∈ Icc (0 : ℝ) b, ∃ a' : Circle,
        range (fun z => collar.map (p z,tau (s,z))) = J.leaf a') := by
  obtain ⟨phi,hphi,hephi,hmap,hphi0⟩ :=
    b2_boundary_collar_torus_pullback_v489 J collar p hp hpe hpb hpa
  obtain ⟨ell,hell,hell0,hderell,W,hW,haW,hellinj⟩ := b2_smooth_label_phase_v489 a
  obtain ⟨f,hf,hmatch,hf0⟩ := b2_real_phase_extension_v489 ell hell phi hphi hphi0 hell0
  have htrans := b2_extended_phase_transverse_v489 phi hphi hphi0
    (b2_boundary_collar_pullback_rank_v489 J collar p hp hpa phi hphi hmap)
    ell hell hderell f hf hmatch
  obtain ⟨e,he,hsource,htarget,hinitial⟩ :=
    b2_phase_compact_partialDiffeomorph_v489 f hf hf0 htrans
  obtain ⟨r,hr,hr1,hwindow⟩ := b2_label_window_strip_v489 phi hephi.continuous hphi0 hW haW
  let R : Set (ℝ × Circle) := Iio r ×ˢ univ
  have hR : IsOpen R := isOpen_Iio.prod isOpen_univ
  have hR0 : ({(0 : ℝ)} ×ˢ (univ : Set Circle)) ⊆ R := by
    rintro ⟨s,z⟩ ⟨hs,hz⟩
    have hs0 : s = 0 := hs
    subst s
    exact ⟨hr,hz⟩
  obtain ⟨b,sign,hb,hsign,tau0,htau0,htau00,htau0right,htau0pos⟩ :=
    b2_positive_phase_inverse_v489 f hf0 e he hsource htarget hinitial R hR hR0
  obtain ⟨G,hG,hGeq⟩ := Manifold.exists_contMDiff_extension_Icc htau0
  have hG0 (z : Circle) : G (0,z) = 0 := by
    rw [hGeq (show (0,z) ∈ Icc (0 : ℝ) b ×ˢ univ by simp [hb.le])]
    exact htau00 z
  have hGright (s : ℝ) (hs : s ∈ Icc (0 : ℝ) b) (z : Circle) :
      G (s,z) < r ∧ f (G (s,z),z) = sign*s := by
    rw [hGeq ⟨hs,mem_univ z⟩]
    exact ⟨(htau0right s hs z).1.1,(htau0right s hs z).2⟩
  have hGpos (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) b) (z : Circle) : 0 < G (s,z) := by
    rw [hGeq ⟨⟨hs.1.le,hs.2⟩,mem_univ z⟩]
    exact htau0pos s hs z
  have hGlegal (s : ℝ) (hs : s ∈ Icc (0 : ℝ) b) (z : Circle) : G (s,z) ∈ Icc (0 : ℝ) 1 := by
    refine ⟨?_,((hGright s hs z).1.trans hr1).le⟩
    rcases eq_or_lt_of_le hs.1 with hs0 | hsp
    · rw [← hs0,hG0]
    · exact (hGpos s ⟨hsp,hs.2⟩ z).le
  have hsign0 : sign ≠ 0 := by rcases hsign with hs | hs <;> rw [hs] <;> norm_num
  have hGder (z : Circle) : 0 < deriv (fun s => G (s,z)) 0 :=
    b2_positive_inverse_initial_derivative_v489 f G hf hG hb hsign0 hG0
      (fun s hs z => (hGright s hs z).2) hGpos z
  let k : ℝ := collar.epsilon/2
  let tau : ℝ × Circle → ℝ := fun q => k*G q
  have hk : 0 < k := half_pos collar.epsilon_pos
  have htau : ContMDiff (𝓘(ℝ).prod (𝓡 1)) 𝓘(ℝ) ∞ tau := contMDiff_const.mul hG
  refine ⟨b,hb,tau,htau,?_,?_,?_,?_,?_⟩
  · intro z
    simp [tau,hG0]
  · intro z
    have hd : HasDerivAt (fun s => G (s,z)) (deriv (fun s => G (s,z)) 0) 0 :=
      (contMDiff_iff_contDiff.mp (hG.comp (contMDiff_id.prodMk contMDiff_const))).differentiable
        (by simp) 0 |>.hasDerivAt
    rw [(hd.const_mul k).deriv]
    exact mul_pos hk (hGder z)
  · intro s hs z
    refine ⟨mul_nonneg hk.le (hGlegal s hs z).1,?_⟩
    calc k*G (s,z) ≤ k*1 := mul_le_mul_of_nonneg_left (hGlegal s hs z).2 hk.le
      _ < collar.epsilon := by simpa only [k,mul_one] using half_lt_self collar.epsilon_pos
  · intro s hs z
    exact mul_pos hk (hGpos s hs z)
  · intro s hs
    let t : Circle → Time := fun z => ⟨G (s,z),hGlegal s hs z⟩
    have ht : Continuous t :=
      (hG.continuous.comp (continuous_const.prodMk continuous_id)).subtype_mk _
    have hWin (z : Circle) : (phi (t z,z)).1 ∈ W :=
      hwindow (t z) (hGright s hs z).1 z
    have hphase (z : Circle) : ell (phi (t z,z)).1 = sign*s :=
      (hmatch (t z) z).symm.trans (hGright s hs z).2
    exact ⟨(phi (t 1,1)).1,b2_corrected_strip_whole_leaf_v489 J collar p phi hephi hmap
      ell W hellinj t ht hWin (fun z => (hphase z).trans (hphase 1).symm)⟩

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
end

-- Exact source from B2PositiveExtensionV489.lean

noncomputable section
open Set Topology Function Filter Manifold
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private theorem ambient_slice_hasDeriv_v489 {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (G : ℝ × V → ℝ) (hG : ContDiff ℝ ∞ G) (s : ℝ) (y : V) :
    HasDerivAt (fun t => G (t,y)) (fderiv ℝ G (s,y) (1,0)) s := by
  exact (hG.differentiable (by simp) (s,y)).hasFDerivAt.comp_hasDerivAt s
    ((hasDerivAt_id s).prodMk (hasDerivAt_const s y))

/-- A smooth Euclidean extension of positive boundary times is corrected by
a cutoff so that its initial speed is positive on a prescribed compact set.
Compactness then supplies one common interval of positive legal collar times. -/
theorem b2_positive_compact_extension_v489 {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (m : X → Euc 4) (hm : Continuous m) (j : Circle → Euc 4) (hj : Continuous j)
    (G : ℝ × Euc 4 → ℝ) (hG : ContDiff ℝ ∞ G)
    (hzero : ∀ z, G (0,j z) = 0)
    (hder : ∀ z, 0 < deriv (fun s => G (s,j z)) 0)
    {b0 epsilon : ℝ} (hb0 : 0 < b0) (hepsilon : 0 < epsilon) :
    ∃ b : ℝ, 0 < b ∧ b ≤ b0 ∧ ∃ H : ℝ × Euc 4 → ℝ,
      ContDiff ℝ ∞ H ∧ (∀ y, H (0,y) = 0) ∧
      (∀ s z, H (s,j z) = G (s,j z)) ∧
      (∀ s ∈ Icc (0 : ℝ) b, ∀ x, H (s,m x) ∈ Ico (0 : ℝ) epsilon) ∧
      (∀ s ∈ Ioc (0 : ℝ) b, ∀ x, 0 < H (s,m x)) := by
  classical
  let dG : ℝ × Euc 4 → ℝ := fun q => fderiv ℝ G q (1,0)
  have hdGc : Continuous dG :=
    ((hG.contDiff_fderiv_apply (m := 0) (by simp)).comp
      (contDiff_id.prodMk contDiff_const)).continuous
  have hdG0 (z : Circle) : 0 < dG (0,j z) := by
    change 0 < fderiv ℝ G (0,j z) (1,0)
    rw [← (ambient_slice_hasDeriv_v489 G hG 0 (j z)).deriv]
    exact hder z
  let O : Set (Euc 4) := {y | 0 < dG (0,y)}
  have hO : IsOpen O := isOpen_lt continuous_const (hdGc.comp (continuous_const.prodMk continuous_id))
  have hKO : range j ⊆ O := by rintro y ⟨z,rfl⟩; exact hdG0 z
  obtain ⟨chi,hchi,hchic,hchi1,hchiO,hchirange⟩ :=
    DifferentialGeometry.Analysis.exists_bump_compact (isCompact_range hj) hO hKO
  let H : ℝ × Euc 4 → ℝ := fun q =>
    chi q.2 * (G q-G (0,q.2)) + (1-chi q.2)*q.1
  have hH : ContDiff ℝ ∞ H :=
    (hchi.comp contDiff_snd).mul
      (hG.sub (hG.comp (contDiff_const.prodMk contDiff_snd))) |>.add
        ((contDiff_const.sub (hchi.comp contDiff_snd)).mul contDiff_fst)
  have hH0 (y : Euc 4) : H (0,y) = 0 := by simp [H]
  have hHj (s : ℝ) (z : Circle) : H (s,j z) = G (s,j z) := by
    have hc : chi (j z) = 1 := hchi1.self_of_nhdsSet (mem_range_self z)
    simp [H,hc,hzero]
  let dH : ℝ × Euc 4 → ℝ := fun q => fderiv ℝ H q (1,0)
  have hdHc : Continuous dH :=
    ((hH.contDiff_fderiv_apply (m := 0) (by simp)).comp
      (contDiff_id.prodMk contDiff_const)).continuous
  have hdH0 (y : Euc 4) : 0 < dH (0,y) := by
    have hD : HasDerivAt (fun s => H (s,y))
        (chi y*dG (0,y)+(1-chi y)) 0 := by
      change HasDerivAt (fun s => chi y * (G (s,y) - G (0,y)) + (1 - chi y) * s)
        (chi y*dG (0,y)+(1-chi y)) 0
      convert! (((ambient_slice_hasDeriv_v489 G hG 0 y).sub_const (G (0,y))).const_mul (chi y)).add
        ((hasDerivAt_id (0 : ℝ)).const_mul (1-chi y)) using 1 <;> simp [dG]
    have heq := (ambient_slice_hasDeriv_v489 H hH 0 y).unique hD
    change dH (0,y) = _ at heq
    rw [heq]
    have hr : chi y ∈ Icc (0 : ℝ) 1 := hchirange (mem_range_self y)
    by_cases hchi0 : chi y = 0
    · simp [hchi0]
    have hdGpos : 0 < dG (0,y) := hchiO (subset_tsupport _ (by exact hchi0))
    by_cases hchiOne : chi y = 1
    · simpa only [hchiOne,one_mul,sub_self,add_zero] using hdGpos
    have hfirst : 0 ≤ chi y*dG (0,y) := mul_nonneg hr.1 hdGpos.le
    have hlast : 0 < 1-chi y := sub_pos.mpr (lt_of_le_of_ne hr.2 hchiOne)
    linarith
  let K : Set (Euc 4) := range m
  have hK : IsCompact K := isCompact_range hm
  let N : Set (ℝ × Euc 4) := {q | 0 < dH q ∧ H q < epsilon}
  have hN : IsOpen N := (isOpen_lt continuous_const hdHc).inter
    (isOpen_lt hH.continuous continuous_const)
  have hKN : ({(0 : ℝ)} ×ˢ K) ⊆ N := by
    rintro ⟨s,y⟩ ⟨hs,hy⟩
    have hs0 : s = 0 := hs
    subst s
    exact ⟨hdH0 y,by simpa only [hH0] using hepsilon⟩
  obtain ⟨V,W,hV,hW,h0V,hKW,hVWN⟩ :=
    generalized_tube_lemma isCompact_singleton hK hN hKN
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp
    (hV.mem_nhds (show (0 : ℝ) ∈ V from h0V (by simp)))
  let b := min (r/2) b0
  have hb : 0 < b := lt_min (half_pos hr) hb0
  have hb0' : b ≤ b0 := min_le_right _ _
  have htime (s : ℝ) (hs : s ∈ Icc (0 : ℝ) b) (x : X) : (s,m x) ∈ N := by
    apply hVWN
    refine ⟨hball ?_,hKW (mem_range_self x)⟩
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg hs.1]
    exact hs.2.trans_lt ((min_le_left (r/2) b0).trans_lt (half_lt_self hr))
  have hpositive (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) b) (x : X) : 0 < H (s,m x) := by
    have hc : ContDiff ℝ ∞ (fun t => H (t,m x)) :=
      hH.comp (contDiff_id.prodMk contDiff_const)
    have hmono : StrictMonoOn (fun t => H (t,m x)) (Icc (0 : ℝ) b) :=
      strictMonoOn_of_deriv_pos (convex_Icc _ _) hc.continuous.continuousOn (by
        intro t ht
        rw [interior_Icc] at ht
        rw [(ambient_slice_hasDeriv_v489 H hH t (m x)).deriv]
        exact (htime t ⟨ht.1.le,ht.2.le⟩ x).1)
    simpa only [hH0] using hmono (by simp [hb.le]) ⟨hs.1.le,hs.2⟩ hs.1
  refine ⟨b,hb,hb0',H,hH,hH0,hHj,?_,hpositive⟩
  intro s hs x
  refine ⟨?_,(htime s hs x).2⟩
  rcases eq_or_lt_of_le hs.1 with hs0 | hsp
  · simpa only [← hs0,hH0] using (le_rfl : (0 : ℝ) ≤ 0)
  · exact (hpositive s ⟨hsp,hs.2⟩ x).le

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
end

-- Exact source from B2CorrectedFamilyV489.lean

noncomputable section
open Set Topology Function Filter Manifold
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {S : CompactOrientedSurface.{0}}
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- The actual smooth longitude correction on every point of the original
surface, positive for every positive family parameter and equal to zero at
initial time. The boundary equality uses the whole original longitude leaf. -/
theorem b2_longitude_corrected_time_family_v489 (J : LongitudeFoliation.{0} E)
    (F : NeatEmbedding S E.Carrier) (U : Set E.Carrier) (collar : OneSidedCollar F U)
    (hboundary : J.BoundaryIn F.toFun) :
    ∃ b : ℝ, 0 < b ∧ ∃ tau : ℝ × S → ℝ,
      ContMDiff (𝓘(ℝ).prod (𝓡∂ 2)) 𝓘(ℝ) ∞ tau ∧
      (∀ x, tau (0,x) = 0) ∧
      (∀ s ∈ Icc (0 : ℝ) b, ∀ x, tau (s,x) ∈ Ico (0 : ℝ) collar.epsilon) ∧
      (∀ s ∈ Ioc (0 : ℝ) b, ∀ x, 0 < tau (s,x)) ∧
      (∀ s ∈ Icc (0 : ℝ) b, J.BoundaryIn (fun x => collar.map (x,tau (s,x)))) := by
  obtain ⟨a,ha⟩ := hboundary
  obtain ⟨p,hpb,hpa,hp,hpe,hprange⟩ := b2_boundary_parameter_exists_v489 J ha
  obtain ⟨b0,hb0,tauB,htauB,htauB0,htauBD,htauBC,htauBpos,htauBleaf⟩ :=
    b2_boundary_leaf_time_v489 J collar p hp hpe hpb hpa
  obtain ⟨G,hG,hGeq⟩ := b2_boundary_time_euclidean_extension_v489 J a tauB htauB
  let m : S → Euc 4 := b2_euclidean_inclusion_v489 E ∘ F.toFun
  have hm : ContMDiff (𝓡∂ 2) 𝓘(ℝ,Euc 4) ∞ m :=
    b2_euclidean_inclusion_smooth_v489.comp F.smoothEmbedding.contMDiff
  let j : Circle → Euc 4 := fun z => b2_euclidean_inclusion_v489 E (J.torus (a,z))
  have hj : Continuous j := (b2_leaf_euclidean_smoothEmbedding_v489 J a).contMDiff.continuous
  have hGj0 (z : Circle) : G (0,j z) = 0 := (hGeq 0 z).trans (htauB0 z)
  have hGjD (z : Circle) : 0 < deriv (fun s => G (s,j z)) 0 := by
    rw [show (fun s => G (s,j z)) = (fun s => tauB (s,z)) from funext (fun s => hGeq s z)]
    exact htauBD z
  obtain ⟨b,hb,hbb0,H,hH,hH0,hHj,hHC,hHpos⟩ :=
    b2_positive_compact_extension_v489 m hm.continuous j hj G hG hGj0 hGjD hb0 collar.epsilon_pos
  let tau : ℝ × S → ℝ := fun q => H (q.1,m q.2)
  have htau : ContMDiff (𝓘(ℝ).prod (𝓡∂ 2)) 𝓘(ℝ) ∞ tau := by
    apply hH.contMDiff.comp
    rw [modelWithCornersSelf_prod,← chartedSpaceSelf_prod]
    exact contMDiff_fst.prodMk (hm.comp contMDiff_snd)
  have htauBoundary (s : ℝ) (z : Circle) : tau (s,p z) = tauB (s,z) := by
    change H (s,b2_euclidean_inclusion_v489 E (F.toFun (p z))) = tauB (s,z)
    rw [hpa]
    exact (hHj s z).trans (hGeq s z)
  refine ⟨b,hb,tau,htau,?_,hHC,hHpos,?_⟩
  · intro x
    exact hH0 (m x)
  · intro s hs
    obtain ⟨a',ha'⟩ := htauBleaf s ⟨hs.1,hs.2.trans hbb0⟩
    refine ⟨a',?_⟩
    rw [← ha',← hprange,← range_comp]
    congr 1
    funext z
    exact congrArg (fun t => collar.map (p z,t)) (htauBoundary s z)

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
end

-- Exact source from B2AreaSelectionV489.lean

noncomputable section
open Set Topology Function Filter Manifold
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]
variable {S : CompactOrientedSurface.{0}} {F : NeatEmbedding S M} {U : Set M}
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Positive parameters of the same corrected family achieve every requested
actual area cost. This selects a parameter after the family is constructed. -/
theorem b2_corrected_positive_parameter_area_v489 (g : SmoothMetric M)
    (collar : OneSidedCollar F U) (tau : ℝ × S → ℝ) {b : ℝ} (hb : 0 < b)
    (htau : ContMDiff (𝓘(ℝ).prod (𝓡∂ 2)) 𝓘(ℝ) ∞ tau)
    (hzero : ∀ x, tau (0,x) = 0)
    (hlegal : ∀ s ∈ Icc (0 : ℝ) b, ∀ x, tau (s,x) ∈ Ico (0 : ℝ) collar.epsilon)
    {sigma : ℝ} (hsigma : 0 < sigma) :
    ∃ t : ℝ, t ∈ Ioc (0 : ℝ) b ∧
      area g (fun x => collar.map (x,tau (t,x))) - area g F.toFun ≤ sigma := by
  let z : Icc (0 : ℝ) b := ⟨0,⟨le_rfl,hb.le⟩⟩
  obtain ⟨delta,hdelta,hclose⟩ := Metric.continuousAt_iff.mp
    (variable_collar_actual_area_continuous_v480 g collar tau hb htau.contMDiffOn hlegal).continuousAt
      sigma hsigma
  let t := min (delta/2) (b/2)
  have htpos : 0 < t := lt_min (half_pos hdelta) (half_pos hb)
  have htb : t ≤ b := (min_le_right _ _).trans (half_le_self hb.le)
  let t' : Icc (0 : ℝ) b := ⟨t,⟨htpos.le,htb⟩⟩
  have hdist : dist t' z < delta := by
    change dist t (0 : ℝ) < delta
    rw [Real.dist_eq,sub_zero,abs_of_pos htpos]
    exact (min_le_left _ _).trans_lt (half_lt_self hdelta)
  have h := hclose hdist
  change dist (area g (fun x => collar.map (x,tau (t,x))))
    (area g (fun x => collar.map (x,tau (0,x)))) < sigma at h
  have hinit : (fun x => collar.map (x,tau (0,x))) = F.toFun := by
    funext x
    rw [hzero,collar.initial]
  rw [hinit,Real.dist_eq] at h
  exact ⟨t,⟨htpos,htb⟩,(abs_lt.mp h).2.le⟩

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
end

noncomputable section
open Set Topology Function Filter MeasureTheory Bundle
open scoped Manifold ContDiff BigOperators ENNReal
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
/-- Appendix B.2: every clause of Lemma 5.5, with the uniform constants before σ. -/
theorem B2_original_push_off (g : SmoothMetric E.Carrier) (J : LongitudeFoliation.{0} E)
    {S : CompactOrientedSurface.{0}} (F : NeatEmbedding S E.Carrier)
    (U : Set E.Carrier) (hU : IsOpen U) (collar : OneSidedCollar F U)
    (hboundary : J.BoundaryIn F.toFun) :
    ∃ sigma0 C : ℝ, 0 < sigma0 ∧ 0 ≤ C ∧
      ∃ pushed : ℝ → NeatEmbedding S E.Carrier,
        (∀ sigma ∈ Ioc (0 : ℝ) sigma0,
          (pushed sigma).image ⊆ U ∧ J.BoundaryIn (pushed sigma).toFun ∧
          SmoothAmbientIsotopy.Rel F.image (pushed sigma).image ∧
          area g (pushed sigma).toFun - area g F.toFun ≤ C * sigma) ∧
        (∀ sigma ∈ Ioc (0 : ℝ) sigma0, ∀ sigma' ∈ Ioc (0 : ℝ) sigma0,
          SmoothAmbientIsotopy.Rel (pushed sigma).image (pushed sigma').image) := by
  classical
  obtain ⟨b,hb,tau,htau,hzero,hlegal,hpositive,hboundaryFamily⟩ :=
    b2_longitude_corrected_time_family_v489 J F U collar hboundary
  have hsmooth (t : ℝ) : ContMDiff (𝓡∂ 2) 𝓘(ℝ) ∞ (fun x => tau (t,x)) :=
    htau.comp (contMDiff_const.prodMk contMDiff_id)
  have htime (sigma : ℝ) (hs : 0 < sigma) :=
    b2_corrected_positive_parameter_area_v489 g collar tau hb htau hzero hlegal hs
  let time (sigma : ℝ) (hs : 0 < sigma) := Classical.choose (htime sigma hs)
  have htimeIcc (sigma : ℝ) (hs : 0 < sigma) : time sigma hs ∈ Icc (0 : ℝ) b :=
    ⟨(Classical.choose_spec (htime sigma hs)).1.1.le,(Classical.choose_spec (htime sigma hs)).1.2⟩
  let pushed : ℝ → NeatEmbedding S E.Carrier := fun sigma =>
    if hs : 0 < sigma then
      collar_variable_time_neat_v480 collar (fun x => tau (time sigma hs,x))
        (hsmooth (time sigma hs)) (hlegal _ (htimeIcc sigma hs)) else F
  refine ⟨1,1,by norm_num,by norm_num,pushed,?_,?_⟩
  · intro sigma hs
    dsimp only [pushed]
    rw [dif_pos hs.1,one_mul]
    exact ⟨collar_variable_time_image_subset_v480 collar _ (hsmooth _)
        (hlegal _ (htimeIcc sigma hs.1))
        (hpositive _ (Classical.choose_spec (htime sigma hs.1)).1),
      hboundaryFamily _ (htimeIcc sigma hs.1),
      variable_collar_initial_ambient_related_v480 collar _ (hsmooth _)
        (hlegal _ (htimeIcc sigma hs.1)),
      (Classical.choose_spec (htime sigma hs.1)).2⟩
  · intro sigma hs sigma' hs'
    dsimp only [pushed]
    rw [dif_pos hs.1,dif_pos hs'.1]
    exact variable_collar_ambient_related_v480 collar _ _ (hsmooth _) (hsmooth _)
      (hlegal _ (htimeIcc sigma hs.1)) (hlegal _ (htimeIcc sigma' hs'.1))




end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

end

section
/- PAID OWNED SUPPORT: B3InteriorCenteredChartV480 -/
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem interior_drift_continuous_v480
    (F : NativeInteriorChart_v475) (b : E2 → E2)
    (hb : ContinuousOn b F.chart.source) :
    ContinuousOn (F.bhat b) F.chart.target := by
  have hj (i j : Fin 2) : ContinuousOn (fun x => jacobian F.chart x i j) F.chart.source :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp_continuousOn
      ((F.forward_C1.continuousOn_fderiv_of_isOpen F.source_open (by simp)).clm_apply continuousOn_const)
  have hdet : ContinuousOn (fun x => Matrix.det (jacobian F.chart x)) F.chart.source := by
    simp only [Matrix.det_fin_two]
    exact ((hj 0 0).mul (hj 1 1)).sub ((hj 0 1).mul (hj 1 0))
  have hact : ContinuousOn (fun x => matrixAction (jacobian F.chart x) (b x)) F.chart.source := by
    apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp_continuousOn
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_finsetSum
    intro j hjj
    exact (hj i j).mul ((EuclideanSpace.proj (𝕜 := ℝ) j).continuous.comp_continuousOn hb)
  exact ((hdet.abs.inv₀ (fun x hx => abs_ne_zero.mpr (F.forward_det x hx))).smul hact).comp
    F.chart.continuousOn_symm (fun z hz => F.chart.map_target hz)

/-- Restrict an interior chart to a compact coordinate ball around its actual
working point and translate its target center to zero.  The drift bound is
obtained from compactness, without requiring any extra chart smoothness. -/
theorem interior_centered_chart_with_base_v480
    (F : NativeInteriorChart_v475) (p : E2) (hp : p ∈ F.chart.source)
    (a : E2 → Mat2) (b : E2 → E2)
    (hb : ContinuousOn b F.chart.source)
    (hdensity : ∀ z ∈ F.chart.target, densityLeading a F.chart (F.chart.symm z) = 1) :
    ∃ G : NativeInteriorChart_v475, ∃ r : ℝ,
      0 < r ∧ p ∈ G.chart.source ∧ G.chart.source ⊆ F.chart.source ∧
      G.chart.target = disc r ∧ BoundedOn (G.bhat b) G.chart.target ∧
      (∀ z ∈ G.chart.target, densityLeading a G.chart (G.chart.symm z) = 1) ∧
      G.chart p = 0 := by
  classical
  let z₀ := F.chart p
  have hz₀ : z₀ ∈ F.chart.target := F.chart.map_source hp
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp F.target_open z₀ hz₀
  let r := ε/2
  have hr : 0 < r := half_pos hε
  have hKT : Metric.closedBall z₀ r ⊆ F.chart.target := by
    intro z hz
    apply hball
    exact lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (by dsimp [r]; linarith)
  let S := F.chart.source ∩ F.chart ⁻¹' Metric.ball z₀ r
  have hS : IsOpen S := F.chart.continuousOn.isOpen_inter_preimage F.source_open Metric.isOpen_ball
  have hpS : p ∈ S := ⟨hp, by simp [z₀,hr]⟩
  have hshift (z : E2) : z ∈ disc r ↔ z+z₀ ∈ Metric.ball z₀ r := by
    simp only [disc,Metric.mem_ball,dist_eq_norm]
    simp
  let χ : PartialHomeomorph E2 E2 :=
    { toFun := fun x => F.chart x-z₀
      invFun := fun z => F.chart.symm (z+z₀)
      source := S
      target := disc r
      map_source' := by
        intro x hx
        rw [hshift]
        simpa only [sub_add_cancel] using (show F.chart x ∈ Metric.ball z₀ r from hx.2)
      map_target' := by
        intro z hz
        have hzt := hKT (Metric.ball_subset_closedBall (hshift z |>.mp hz))
        refine ⟨F.chart.map_target hzt,?_⟩
        change F.chart (F.chart.symm (z+z₀)) ∈ Metric.ball z₀ r
        rw [F.chart.right_inv hzt]
        exact (hshift z).mp hz
      left_inv' := by
        intro x hx
        simpa only [sub_add_cancel] using F.chart.left_inv hx.1
      right_inv' := by
        intro z hz
        have hzt := hKT (Metric.ball_subset_closedBall ((hshift z).mp hz))
        simp only [F.chart.right_inv hzt,add_sub_cancel_right]
      continuousOn_toFun := (F.chart.continuousOn.sub continuousOn_const).mono inter_subset_left
      continuousOn_invFun := F.chart.continuousOn_symm.comp
        (continuous_id.add continuous_const).continuousOn
        (fun z hz => hKT (Metric.ball_subset_closedBall ((hshift z).mp hz))) }
  have hjac (x : E2) (hx : x ∈ S) : jacobian χ x = jacobian F.chart x := by
    unfold jacobian
    change (fun i j => (fderiv ℝ (fun y => F.chart y-z₀) x (coordinateVector 2 j)) i) = _
    rw [fderiv_sub_const]
  let G : NativeInteriorChart_v475 :=
    { chart := χ
      source_open := hS
      target_open := Metric.isOpen_ball
      forward_C1 := (F.forward_C1.sub contDiffOn_const).mono inter_subset_left
      inverse_C1 := F.inverse_C1.comp (contDiff_id.add contDiff_const).contDiffOn
        (fun z hz => hKT (Metric.ball_subset_closedBall ((hshift z).mp hz)))
      forward_det := fun x hx => by rw [hjac x hx]; exact F.forward_det x hx.1 }
  have hbG (z : E2) (hz : z ∈ G.chart.target) : G.bhat b z = F.bhat b (z+z₀) := by
    unfold NativeInteriorChart_v475.bhat densityDrift
    rw [hjac _ (G.chart.map_target hz)]
    rfl
  obtain ⟨M,hM⟩ := (isCompact_closedBall z₀ r).exists_bound_of_continuousOn
    ((interior_drift_continuous_v480 F b hb).mono hKT)
  refine ⟨G,r,hr,hpS,inter_subset_left,rfl,⟨max M 0,le_max_right _ _,?_⟩,?_,?_⟩
  · intro z hz
    rw [hbG z hz]
    exact (hM _ (Metric.ball_subset_closedBall ((hshift z).mp hz))).trans (le_max_left _ _)
  · intro z hz
    unfold densityLeading
    rw [hjac _ (G.chart.map_target hz)]
    exact hdensity (z+z₀) (hKT (Metric.ball_subset_closedBall ((hshift z).mp hz)))

  · change F.chart p - F.chart p = 0
    exact sub_self _

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3TwoHeightActualPDEV480 -/
noncomputable section
open Set Topology Function Filter MeasureTheory
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- The original pair has actual area-flow minima on its literal neat maps. -/
theorem original_pair_actual_flow_minima (D : OriginalPair g J) :
    (∀ X : NativeInteriorSmoothVectorField_v475 E,
      IsLocalMin (fun t => area g
        (native_actual_exterior_flow_v475 X t ∘ D.A.1.embedding.toFun)) 0) ∧
    (∀ X : NativeInteriorSmoothVectorField_v475 E,
      IsLocalMin (fun t => area g
        (native_actual_exterior_flow_v475 X t ∘ D.B.1.embedding.toFun)) 0) := by
  obtain ⟨FA, hFA, hminA⟩ := native_relative_fixed_minimum_v475 D.A D.A_minimum
  obtain ⟨FB, hFB, hminB⟩ := native_relative_fixed_minimum_v475 D.B D.B_minimum
  exact ⟨fun X => native_actual_smooth_ambient_flow_minimum_v475
    (ProperSmoothEmbedding.ofNeat D.A.1.embedding) FA hFA hminA X,
    fun X => native_actual_smooth_ambient_flow_minimum_v475
      (ProperSmoothEmbedding.ofNeat D.B.1.embedding) FB hFB hminB X⟩

/-- Both arbitrary smooth heights of an actual common chart solve the same
literal coordinate metric graph equation.  The metric and source parameters
are constructed from the original minima. Neither height is replaced by zero. -/
theorem original_pair_two_height_actual_pdes (D : OriginalPair g J)
    (r : E.Carrier) (a0 : D.A.1.surface) (b0 : D.B.1.surface)
    (c : SmoothAmbientChart ThreeSphere)
    (hcE : c.chart.source ⊆ E.toSphere '' (𝓡∂ 3).interior E.Carrier)
    (O : Set E2) (hO : IsOpen O)
    (lower upper : E2 → ℝ)
    (hlower : ContDiffOn ℝ ∞ lower O) (hupper : ContDiffOn ℝ ∞ upper O)
    (hpoints : ∀ z ∈ O, jetPoint (z, lower z, 0) ∈ c.chart.target ∧
      jetPoint (z, upper z, 0) ∈ c.chart.target)
    (hlower_mem : ∀ z ∈ O, c.chart.symm (jetPoint (z, lower z, 0)) ∈
      range (E.toSphere ∘ D.B.1.embedding.toFun))
    (hupper_mem : ∀ z ∈ O, c.chart.symm (jetPoint (z, upper z, 0)) ∈
      range (E.toSphere ∘ D.A.1.embedding.toFun))
    (hgraph_lower : ∀ b : D.B.1.surface,
      E.toSphere (D.B.1.embedding.toFun b) ∈ c.chart.source →
      (c.chart (E.toSphere (D.B.1.embedding.toFun b))) 2 =
        lower (native_collar_base_v475 (c.chart (E.toSphere (D.B.1.embedding.toFun b)))))
    (hgraph_upper : ∀ a : D.A.1.surface,
      E.toSphere (D.A.1.embedding.toFun a) ∈ c.chart.source →
      (c.chart (E.toSphere (D.A.1.embedding.toFun a))) 2 =
        upper (native_collar_base_v475 (c.chart (E.toSphere (D.A.1.embedding.toFun a))))) :
    ∃ H : CoordinateMetric c.chart.target,
      (∀ z ∈ O, native_interior_graph_residual_v475 H lower z = 0) ∧
      (∀ z ∈ O, native_interior_graph_residual_v475 H upper z = 0) := by
  obtain ⟨χ, hχ, hχeq, hχI, hχright, hχleft⟩ :=
    native_actual_interior_chart_lift_v475 c r hcE
  obtain ⟨H, hH⟩ := native_actual_lift_coordinate_metric_v475 g c χ hχ hχeq
  have smoothgraph (u : E2 → ℝ) (hu : ContDiffOn ℝ ∞ u O)
      (ht : ∀ z ∈ O, jetPoint (z, u z, 0) ∈ c.chart.target) :
      ContMDiffOn 𝓘(ℝ, E2) (𝓡∂ 3) ∞
        (fun z => χ (jetPoint (z, u z, 0))) O := by
    have hs : ContDiffOn ℝ ∞ (fun z => jetPoint (z, u z, 0)) O :=
      native_interior_graph_splitting_v475.contDiff.comp_contDiffOn
        (contDiffOn_id.prodMk hu)
    exact hχ.comp hs.contMDiffOn ht
  have hlmap : ∀ z ∈ O, χ (jetPoint (z, lower z, 0)) ∈ D.B.1.embedding.image := by
    intro z hz
    obtain ⟨b, hb⟩ := hlower_mem z hz
    exact ⟨b, Subtype.ext (hb.trans (hχeq _ (hpoints z hz).1).symm)⟩
  have humap : ∀ z ∈ O, χ (jetPoint (z, upper z, 0)) ∈ D.A.1.embedding.image := by
    intro z hz
    obtain ⟨a, ha⟩ := hupper_mem z hz
    exact ⟨a, Subtype.ext (ha.trans (hχeq _ (hpoints z hz).2).symm)⟩
  obtain ⟨ql, hql, hqli, hqls⟩ := native_actual_interior_source_parameter_v475
    D.B.1.embedding b0 O hO (fun z => χ (jetPoint (z, lower z, 0)))
    (smoothgraph lower hlower (fun z hz => (hpoints z hz).1))
    hlmap (fun z hz => hχI _ (hpoints z hz).1)
  obtain ⟨qu, hqu, hqui, hqus⟩ := native_actual_interior_source_parameter_v475
    D.A.1.embedding a0 O hO (fun z => χ (jetPoint (z, upper z, 0)))
    (smoothgraph upper hupper (fun z hz => (hpoints z hz).2))
    humap (fun z hz => hχI _ (hpoints z hz).2)
  obtain ⟨hminA, hminB⟩ := original_pair_actual_flow_minima D
  exact ⟨H,
    native_interior_actual_graph_pde_from_flow_v475 g c hcE χ hχ hχeq H hH
      (ProperSmoothEmbedding.ofNeat D.B.1.embedding) hminB O hO lower hlower
      ql hqls hql (fun z hz => (hpoints z hz).1) hqli hgraph_lower,
    native_interior_actual_graph_pde_from_flow_v475 g c hcE χ hχ hχeq H hH
      (ProperSmoothEmbedding.ofNeat D.A.1.embedding) hminA O hO upper hupper
      qu hqus hqu (fun z hz => (hpoints z hz).2) hqui hgraph_upper⟩

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3InteriorGraphSphereChartV480 -/
noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- An actual interior exterior graph chart transports to the sphere through
the supplied neat inclusion, preserving its literal three coordinates. -/
theorem interior_graph_sphere_chart {A B : IncompressibleSpanningSurface.{0} E}
    {p : E.Carrier} (c : InteriorGraph A B p) :
    ∃ d : SmoothAmbientChart ThreeSphere,
      d.chart.source = E.toSphere '' c.coordinates.source ∧
      d.chart.target = c.coordinates.target ∧
      (∀ a ∈ c.coordinates.source, d.chart (E.toSphere a) = c.coordinates a) ∧
      (∀ y, d.chart.symm y = E.toSphere (c.coordinates.symm y)) := by
  classical
  letI : Nonempty E.Carrier := ⟨p⟩
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  let inverse : ThreeSphere → E.Carrier := Function.invFun E.toSphere
  have hinv (a : E.Carrier) : inverse (E.toSphere a) = a :=
    Function.leftInverse_invFun hinc.isEmbedding.injective a
  let U : Set ThreeSphere := E.toSphere '' c.coordinates.source
  have hU : IsOpen U := by
    obtain ⟨V, hV, hpre⟩ := hinc.isEmbedding.isInducing.isOpen_iff.mp c.coordinates.open_source
    have hEq : U = V ∩ (E.toSphere '' (𝓡∂ 3).interior E.Carrier) := by
      ext x
      constructor
      · rintro ⟨a, ha, rfl⟩
        refine ⟨?_, ⟨a, c.source_interior ha, rfl⟩⟩
        change a ∈ E.toSphere ⁻¹' V
        rwa [hpre]
      · rintro ⟨hx, a, ha, rfl⟩
        refine ⟨a, ?_, rfl⟩
        rw [← hpre]
        exact hx
    rw [hEq]
    exact hV.inter native_actual_exterior_interior_image_open_v475
  have hinverse_mem (x : ThreeSphere) (hx : x ∈ U) : inverse x ∈ c.coordinates.source := by
    obtain ⟨a, ha, rfl⟩ := hx
    simpa only [hinv] using ha
  have hcomp (x : ThreeSphere) (hx : x ∈ U) : E.toSphere (inverse x) = x := by
    obtain ⟨a, ha, rfl⟩ := hx
    rw [hinv]
  have hcont : ContinuousOn inverse U := by
    apply hinc.isEmbedding.isInducing.continuousOn_iff.mpr
    exact continuousOn_id.congr (fun x hx => hcomp x hx)
  have hsmooth : ContMDiffOn (𝓡 3) (𝓡∂ 3) ∞ inverse U := by
    intro x hx
    have hc : ContinuousAt inverse x := (hcont x hx).continuousAt (hU.mem_nhds hx)
    have hcs : ContMDiffAt (𝓡 3) (𝓡 3) ∞ (E.toSphere ∘ inverse) x := by
      apply contMDiffAt_id.congr_of_eventuallyEq
      exact Filter.eventuallyEq_of_mem (hU.mem_nhds hx) (fun y hy => hcomp y hy)
    exact ((ContMDiffAt.iff_comp_isImmersionAt (I := 𝓡 3)
      (hinc.isImmersion.isImmersionAt (inverse x))).mpr ⟨hc, hcs⟩).contMDiffWithinAt
  let d : OpenPartialHomeomorph ThreeSphere E3 := {
    toFun := c.coordinates ∘ inverse
    invFun := E.toSphere ∘ c.coordinates.symm
    source := U
    target := c.coordinates.target
    map_source' := fun x hx => c.coordinates.map_source (hinverse_mem x hx)
    map_target' := fun y hy => ⟨c.coordinates.symm y, c.coordinates.map_target hy, rfl⟩
    left_inv' := by
      intro x hx
      change E.toSphere (c.coordinates.symm (c.coordinates (inverse x))) = x
      rw [c.coordinates.left_inv (hinverse_mem x hx), hcomp x hx]
    right_inv' := by
      intro y hy
      change c.coordinates (inverse (E.toSphere (c.coordinates.symm y))) = y
      rw [hinv, c.coordinates.right_inv hy]
    open_source := hU
    open_target := c.coordinates.open_target
    continuousOn_toFun := c.coordinates.continuousOn.comp hcont hinverse_mem
    continuousOn_invFun := hinc.contMDiff.continuous.comp_continuousOn c.coordinates.continuousOn_symm }
  have hd : ContMDiffOn (𝓡 3) 𝓘(ℝ, E3) ∞ d d.source :=
    c.smooth.comp hsmooth hinverse_mem
  have hdi : ContMDiffOn 𝓘(ℝ, E3) (𝓡 3) ∞ d.symm d.target :=
    hinc.contMDiff.comp_contMDiffOn c.inverse_smooth
  refine ⟨⟨d, hd, hdi⟩, rfl, rfl, ?_, fun _ => rfl⟩
  intro a ha
  change c.coordinates (inverse (E.toSphere a)) = c.coordinates a
  rw [hinv]

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3InteriorGraphActualPDEV480 -/
noncomputable section
open Set Topology Function Filter MeasureTheory
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

private theorem graph_jet_point (x : E2) (z : ℝ) (v : E2) :
    jetPoint (x, z, v) = graphPoint x z := rfl
private theorem graph_point_plane (x : E2) (z : ℝ) :
    graphPlaneCoordinates (graphPoint x z) = x := by
  ext i
  fin_cases i <;> simp [graphPlaneCoordinates, graphPoint]
private theorem graph_point_height (x : E2) (z : ℝ) : graphPoint x z 2 = z := by
  simp [graphPoint]
private theorem native_graph_point_base (x : E2) (z : ℝ) :
    native_collar_base_v475 (graphPoint x z) = x := by
  ext i
  fin_cases i <;> simp [native_collar_base_v475, graphPoint]

/-- The same InteriorGraph lower and upper solve the same actual metric graph
PDE on its original ball. The sphere chart, lifts and source parameters are
constructed internally, preserving both literal heights. -/
theorem original_pair_interior_graph_actual_pdes (D : OriginalPair g J)
    {p : E.Carrier} (c : InteriorGraph D.A D.B p) :
    ∃ V : Set E3, V = c.coordinates.target ∧ IsOpen V ∧
      ∃ H : CoordinateMetric V,
        (∀ z ∈ Metric.ball (0 : E2) c.R,
          native_interior_graph_residual_v475 H c.lower z = 0) ∧
        (∀ z ∈ Metric.ball (0 : E2) c.R,
          native_interior_graph_residual_v475 H c.upper z = 0) := by
  obtain ⟨d, hdsource, hdtarget, hdcoord, hdinverse⟩ := interior_graph_sphere_chart c
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  have hpoint (u : E2 → ℝ) (hu : ∀ x ∈ Metric.ball (0 : E2) c.R, |u x| < c.eta)
      (x : E2) (hx : x ∈ Metric.ball (0 : E2) c.R) :
      graphPoint x (u x) ∈ c.coordinates.target :=
    c.cylinder_inside ⟨by simpa only [graph_point_plane, Metric.mem_ball, dist_zero_right] using hx,
      by simpa only [graph_point_height] using hu x hx⟩
  have hpoints : ∀ z ∈ Metric.ball (0 : E2) c.R,
      jetPoint (z, c.lower z, 0) ∈ d.chart.target ∧
      jetPoint (z, c.upper z, 0) ∈ d.chart.target := by
    intro z hz
    rw [hdtarget]
    exact ⟨hpoint c.lower c.lower_inside z hz, hpoint c.upper c.upper_inside z hz⟩
  have hgraph_mem (F : Set E.Carrier) (u : E2 → ℝ)
      (hg : F ∩ c.coordinates.source =
        (fun x : E2 => c.coordinates.symm (graphPoint x (u x))) '' Metric.ball 0 c.R)
      (x : E2) (hx : x ∈ Metric.ball (0 : E2) c.R) :
      c.coordinates.symm (graphPoint x (u x)) ∈ F := by
    have hh : c.coordinates.symm (graphPoint x (u x)) ∈ F ∩ c.coordinates.source := by
      rw [hg]
      exact ⟨x, hx, rfl⟩
    exact hh.1
  have hsource (a : E.Carrier) (ha : E.toSphere a ∈ d.chart.source) :
      a ∈ c.coordinates.source := by
    rw [hdsource] at ha
    obtain ⟨b, hb, hab⟩ := ha
    have hab' : a = b := hinc.isEmbedding.injective hab.symm
    simpa only [hab'] using hb
  have hcE : d.chart.source ⊆ E.toSphere '' (𝓡∂ 3).interior E.Carrier := by
    rw [hdsource]
    exact image_mono c.source_interior
  have hzero : (0 : E2) ∈ Metric.ball (0 : E2) c.R := Metric.mem_ball_self c.R_pos
  obtain ⟨a0, ha0⟩ := hgraph_mem D.A.1.image c.upper c.graph_A 0 hzero
  obtain ⟨b0, hb0⟩ := hgraph_mem D.B.1.image c.lower c.graph_B 0 hzero
  have hlower_mem : ∀ z ∈ Metric.ball (0 : E2) c.R,
      d.chart.symm (jetPoint (z, c.lower z, 0)) ∈ range (E.toSphere ∘ D.B.1.embedding.toFun) := by
    intro z hz
    obtain ⟨b, hb⟩ := hgraph_mem D.B.1.image c.lower c.graph_B z hz
    refine ⟨b, ?_⟩
    rw [hdinverse]
    exact congrArg E.toSphere hb
  have hupper_mem : ∀ z ∈ Metric.ball (0 : E2) c.R,
      d.chart.symm (jetPoint (z, c.upper z, 0)) ∈ range (E.toSphere ∘ D.A.1.embedding.toFun) := by
    intro z hz
    obtain ⟨a, ha⟩ := hgraph_mem D.A.1.image c.upper c.graph_A z hz
    refine ⟨a, ?_⟩
    rw [hdinverse]
    exact congrArg E.toSphere ha
  have hheight (F : Set E.Carrier) (u : E2 → ℝ)
      (hu : ∀ x ∈ Metric.ball (0 : E2) c.R, |u x| < c.eta)
      (hg : F ∩ c.coordinates.source =
        (fun x : E2 => c.coordinates.symm (graphPoint x (u x))) '' Metric.ball 0 c.R)
      (a : E.Carrier) (ha : a ∈ F) (hda : E.toSphere a ∈ d.chart.source) :
      (d.chart (E.toSphere a)) 2 =
        u (native_collar_base_v475 (d.chart (E.toSphere a))) := by
    have has := hsource a hda
    have ham : a ∈ F ∩ c.coordinates.source := ⟨ha, has⟩
    rw [hg] at ham
    obtain ⟨x, hx, rfl⟩ := ham
    rw [hdcoord _ has, c.coordinates.right_inv (hpoint u hu x hx),
      graph_point_height, native_graph_point_base]
  obtain ⟨H, hl, hu⟩ := original_pair_two_height_actual_pdes D p a0 b0 d hcE
    (Metric.ball 0 c.R) Metric.isOpen_ball c.lower c.upper c.lower_smooth c.upper_smooth
    hpoints hlower_mem hupper_mem
    (fun b hb => hheight D.B.1.image c.lower c.lower_inside c.graph_B
      (D.B.1.embedding.toFun b) ⟨b, rfl⟩ hb)
    (fun a ha => hheight D.A.1.image c.upper c.upper_inside c.graph_A
      (D.A.1.embedding.toFun a) ⟨a, rfl⟩ ha)
  exact ⟨d.chart.target, hdtarget, d.chart.open_target, H, hl, hu⟩

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3AffineMeanValueV480 -/
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped Manifold ContDiff BigOperators
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

private theorem affine_p_slice (f : Jet → ℝ) (j : Jet)
    (hf : DifferentiableAt ℝ f j) (p : E2) :
    fderiv ℝ (fun p : E2 => f (j.1, j.2.1, p)) j.2.2 p =
      fderiv ℝ f j (0, 0, p) := by
  have hs := (hasFDerivAt_const (𝕜 := ℝ) j.1 j.2.2).prodMk
    ((hasFDerivAt_const (𝕜 := ℝ) j.2.1 j.2.2).prodMk (hasFDerivAt_id (𝕜 := ℝ) j.2.2))
  exact congrArg (fun L : E2 →L[ℝ] ℝ => L p) (hf.hasFDerivAt.comp j.2.2 hs).fderiv

private theorem affine_z_slice (f : Jet → ℝ) (j : Jet)
    (hf : DifferentiableAt ℝ f j) :
    deriv (fun z : ℝ => f (j.1, z, j.2.2)) j.2.1 =
      fderiv ℝ f j (0, 1, 0) := by
  have hs := (hasFDerivAt_const (𝕜 := ℝ) j.1 j.2.1).prodMk
    ((hasFDerivAt_id (𝕜 := ℝ) j.2.1).prodMk (hasFDerivAt_const (𝕜 := ℝ) j.2.2 j.2.1))
  exact congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) (hf.hasFDerivAt.comp j.2.1 hs).fderiv

private theorem affine_partial_p_smooth (A : Set Jet) (hA : IsOpen A) (f : Jet → ℝ)
    (hf : ContDiffOn ℝ ∞ f A) (p : E2) :
    ContDiffOn ℝ ∞ (fun j : Jet =>
      fderiv ℝ (fun p : E2 => f (j.1, j.2.1, p)) j.2.2 p) A := by
  apply ((hf.fderiv_of_isOpen hA (by simp)).clm_apply
    (contDiffOn_const (c := ((0, (0, p)) : Jet)))).congr
  intro j hj
  exact affine_p_slice f j ((hf.contDiffAt (hA.mem_nhds hj)).differentiableAt (by simp)) p

private theorem affine_partial_z_smooth (A : Set Jet) (hA : IsOpen A) (f : Jet → ℝ)
    (hf : ContDiffOn ℝ ∞ f A) :
    ContDiffOn ℝ ∞ (fun j : Jet => deriv (fun z : ℝ => f (j.1, z, j.2.2)) j.2.1) A := by
  apply ((hf.fderiv_of_isOpen hA (by simp)).clm_apply
    (contDiffOn_const (c := ((0, (1, 0)) : Jet)))).congr
  intro j hj
  exact affine_z_slice f j ((hf.contDiffAt (hA.mem_nhds hj)).differentiableAt (by simp))

/-- Fundamental theorem of calculus on an affine two-height jet segment.
The baseline height and slope are arbitrary, and all integrations use the
literal segment through those values. -/
theorem scalar_affine_jet_mean_value
    (A : Set Jet) (hA : IsOpen A) (f : Jet → ℝ) (hf : ContDiffOn ℝ ∞ f A)
    (x p0 dp : E2) (z0 dz : ℝ)
    (hs : ∀ t ∈ Icc (0 : ℝ) 1, (x, z0 + t * dz, p0 + t • dp) ∈ A) :
    (∀ i : Fin 2, IntervalIntegrable (fun t : ℝ =>
      fderiv ℝ (fun p : E2 => f (x, z0 + t * dz, p))
        (p0 + t • dp) (coordinateVector 2 i)) volume 0 1) ∧
    IntervalIntegrable (fun t : ℝ => deriv
      (fun z : ℝ => f (x, z, p0 + t • dp)) (z0 + t * dz)) volume 0 1 ∧
    f (x, z0 + dz, p0 + dp) - f (x, z0, p0) =
      (∑ i : Fin 2, (∫ t in (0 : ℝ)..1,
        fderiv ℝ (fun p : E2 => f (x, z0 + t * dz, p))
          (p0 + t • dp) (coordinateVector 2 i)) * dp i) +
      (∫ t in (0 : ℝ)..1, deriv
        (fun z : ℝ => f (x, z, p0 + t • dp)) (z0 + t * dz)) * dz := by
  let S : ℝ → Jet := fun t => (x, z0 + t * dz, p0 + t • dp)
  let P : Fin 2 → ℝ → ℝ := fun i t =>
    fderiv ℝ (fun p : E2 => f (x, z0 + t * dz, p)) (p0 + t • dp) (coordinateVector 2 i)
  let Z : ℝ → ℝ := fun t => deriv
    (fun z : ℝ => f (x, z, p0 + t • dp)) (z0 + t * dz)
  have hc : Continuous S := by dsimp [S]; fun_prop
  have hp (i : Fin 2) : IntervalIntegrable (P i) volume 0 1 := by
    have hh := ((affine_partial_p_smooth A hA f hf (coordinateVector 2 i)).continuousOn.comp
      hc.continuousOn hs)
    exact (show ContinuousOn (P i) (uIcc (0 : ℝ) 1) by
      simpa [P, S, Function.comp_def] using hh).intervalIntegrable
  have hz : IntervalIntegrable Z volume 0 1 := by
    have hh := ((affine_partial_z_smooth A hA f hf).continuousOn.comp hc.continuousOn hs)
    exact (show ContinuousOn Z (uIcc (0 : ℝ) 1) by
      simpa [Z, S, Function.comp_def] using hh).intervalIntegrable
  refine ⟨hp, hz, ?_⟩
  have hex : dp = dp 0 • coordinateVector 2 0 + dp 1 • coordinateVector 2 1 := by
    ext i
    fin_cases i <;> simp [coordinateVector, EuclideanSpace.single]
  have hd : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun t => f (S t))
      (P 0 t * dp 0 + P 1 t * dp 1 + Z t * dz) t := by
    intro t ht
    have hft := (hf.contDiffAt (hA.mem_nhds (hs t (by simpa using ht)))).differentiableAt (by simp)
    have hst : HasDerivAt S (0, dz, dp) t := by
      simpa [S] using (hasDerivAt_const t x).prodMk
        (((hasDerivAt_const t z0).add ((hasDerivAt_id t).mul_const dz)).prodMk
          ((hasDerivAt_const t p0).add ((hasDerivAt_id t).smul_const dp)))
    have hh := hft.hasFDerivAt.comp_hasDerivAt t hst
    convert hh using 1 <;> try rfl
    rw [show ((0, dz, dp) : Jet) = (0, 0, dp) + dz • (0, 1, 0) by ext <;> simp]
    rw [map_add, map_smul, ← affine_p_slice f (S t) hft dp, ← affine_z_slice f (S t) hft]
    change _ = fderiv ℝ (fun p : E2 => f (x, z0 + t * dz, p))
      (p0 + t • dp) dp + dz * Z t
    conv_rhs => arg 1; arg 2; rw [hex]
    simp only [map_add, map_smul, smul_eq_mul]
    dsimp [P]
    ring
  have hi := ((hp 0).mul_const (dp 0)).add ((hp 1).mul_const (dp 1))
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hi.add (hz.mul_const dz))
  rw [intervalIntegral.integral_add hi (hz.mul_const dz),
    intervalIntegral.integral_add ((hp 0).mul_const (dp 0)) ((hp 1).mul_const (dp 1)),
    intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_mul_const] at heq
  simpa [S, P, Z, Fin.sum_univ_two] using heq.symm

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3TwoHeightCoefficientDataV480 -/
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates

/-- Actual metric jet data along the literal affine segment between two graph heights.
The compact base records the domain on which ellipticity is estimated. -/
structure TwoHeightGraphWindow where
  U : Set E2
  U_open : IsOpen U
  V : Set E3
  V_open : IsOpen V
  metric : CoordinateMetric V
  lowerHeightFunction : E2 → ℝ
  upperHeightFunction : E2 → ℝ
  lower_smooth : ContDiffOn ℝ ∞ lowerHeightFunction U
  upper_smooth : ContDiffOn ℝ ∞ upperHeightFunction U
  compactBase : Set E2
  compactBase_compact : IsCompact compactBase
  U_contains : compactBase ⊆ U
  jets_inside : ∀ x ∈ compactBase, ∀ t ∈ Icc (0 : ℝ) 1,
    jetPoint (x,lowerHeightFunction x+t*(upperHeightFunction x-lowerHeightFunction x),
      planarGradient lowerHeightFunction x+t • planarGradient (fun x => upperHeightFunction x-lowerHeightFunction x) x) ∈ V
namespace TwoHeightGraphWindow
def height (W : TwoHeightGraphWindow) : E2 → ℝ :=
  fun x => W.upperHeightFunction x - W.lowerHeightFunction x
def gram (W : TwoHeightGraphWindow) (j : Jet) : Mat2 :=
  fun i k => coordinateInner W.metric.tensor (jetPoint j)
    (jetTangent j.2.2 i) (jetTangent j.2.2 k)
def density (W : TwoHeightGraphWindow) (j : Jet) : ℝ := Real.sqrt (Matrix.det (W.gram j))
def flux (W : TwoHeightGraphWindow) (j : Jet) : E2 :=
  planarGradient (fun p : E2 => W.density (j.1, j.2.1, p)) j.2.2
def lower (W : TwoHeightGraphWindow) (j : Jet) : ℝ :=
  -deriv (fun z : ℝ => W.density (j.1, z, j.2.2)) j.2.1
def residual (W : TwoHeightGraphWindow) (u : E2 → ℝ) (x : E2) : ℝ :=
  (∑ i : Fin 2, fderiv ℝ (fun y : E2 => W.flux (y, u y, planarGradient u y) i) x
    (coordinateVector 2 i)) + W.lower (x, u x, planarGradient u x)

def segmentJet (W : TwoHeightGraphWindow) (x : E2) (t : ℝ) : Jet :=
  (x,W.lowerHeightFunction x+t*W.height x,
    planarGradient W.lowerHeightFunction x+t • planarGradient W.height x)
def a (W : TwoHeightGraphWindow) (x : E2) : Mat2 := fun i j =>
  ∫ t in (0 : ℝ)..1, fderiv ℝ
    (fun p : E2 => W.flux (x,(W.segmentJet x t).2.1,p) i)
    (W.segmentJet x t).2.2 (coordinateVector 2 j)
def q (W : TwoHeightGraphWindow) (x : E2) : E2 :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm fun i =>
    ∫ t in (0 : ℝ)..1, deriv
      (fun z : ℝ => W.flux (x,z,(W.segmentJet x t).2.2) i) (W.segmentJet x t).2.1
def lowerGradient (W : TwoHeightGraphWindow) (x : E2) : E2 :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm fun i =>
    ∫ t in (0 : ℝ)..1, fderiv ℝ
      (fun p : E2 => W.lower (x,(W.segmentJet x t).2.1,p))
      (W.segmentJet x t).2.2 (coordinateVector 2 i)
def lowerHeight (W : TwoHeightGraphWindow) (x : E2) : ℝ :=
  ∫ t in (0 : ℝ)..1, deriv
    (fun z : ℝ => W.lower (x,z,(W.segmentJet x t).2.2)) (W.segmentJet x t).2.1
def b (W : TwoHeightGraphWindow) (x : E2) : E2 := W.q x+W.lowerGradient x
def c (W : TwoHeightGraphWindow) (x : E2) : ℝ :=
  (∑ i : Fin 2, fderiv ℝ (fun y => W.q y i) x (coordinateVector 2 i))+W.lowerHeight x
end TwoHeightGraphWindow
end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3TwoHeightCoefficientTubeV480 -/
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped Manifold ContDiff BigOperators
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
theorem two_height_coefficient_open_tube (W : TwoHeightGraphWindow) :
    ∃ O : Set E2, IsOpen O ∧ W.compactBase ⊆ O ∧ O ⊆ W.U ∧
      (∀ x ∈ O, ∀ t ∈ Icc (0 : ℝ) 1, jetPoint (W.segmentJet x t) ∈ W.V) ∧
      ContDiffOn ℝ ∞ (W.height) O ∧
      ContDiffOn ℝ ∞ (planarGradient (W.height)) O ∧
      (∀ i j : Fin 2, ContDiffOn ℝ ∞ (fun x => W.a x i j) O) ∧
      ContDiffOn ℝ ∞ W.q O ∧ ContDiffOn ℝ ∞ W.lowerGradient O ∧
      ContDiffOn ℝ ∞ W.lowerHeight O ∧ ContDiffOn ℝ ∞ W.b O ∧
      ContDiffOn ℝ ∞ W.c O := by
  have hcal := native_interior_graph_jet_calculus_v475 W.V W.V_open W.metric
  have hd : ContDiffOn ℝ ∞ W.density (jetPoint ⁻¹' W.V) := hcal.1
  have hfl : ContDiffOn ℝ ∞ W.flux (jetPoint ⁻¹' W.V) ∧
      ContDiffOn ℝ ∞ W.lower (jetPoint ⁻¹' W.V) := hcal.2
  have hasFD : ∀ (G : Type) [NormedAddCommGroup G] [NormedSpace ℝ G]
    (O : Set E2) (Q : Set ℝ) (hO : IsOpen O) (hQ : IsOpen Q)
    (hIQ : Icc (0 : ℝ) 1 ⊆ Q) (F : E2 × ℝ → G)
    (hF : ContDiffOn ℝ ∞ F (O ×ˢ Q)) (x : E2) (hx : x ∈ O),
    HasFDerivAt (fun y => ∫ t in (0 : ℝ)..1, F (y,t))
      (∫ t in (0 : ℝ)..1,
        (fderiv ℝ F (x,t)).comp (ContinuousLinearMap.inl ℝ E2 ℝ)) x := by
    intro G _ _ O Q hO hQ hIQ F hF x hx
    let D : E2 × ℝ → E2 →L[ℝ] G := fun p =>
      (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ E2 ℝ)
    have hD : ContDiffOn ℝ ∞ D (O ×ˢ Q) :=
      (hF.fderiv_of_isOpen (hO.prod hQ) (by simp)).clm_comp contDiffOn_const
    have hslic (y : E2) (hy : y ∈ O) : ContinuousOn (fun t : ℝ => F (y,t)) (Icc (0 : ℝ) 1) :=
      hF.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun t ht => ⟨hy,hIQ ht⟩)
    have hslicD (y : E2) (hy : y ∈ O) : ContinuousOn (fun t : ℝ => D (y,t)) (Icc (0 : ℝ) 1) :=
      hD.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun t ht => ⟨hy,hIQ ht⟩)
    obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hO.mem_nhds hx)
    have hprod : Metric.closedBall x r ×ˢ Icc (0 : ℝ) 1 ⊆ O ×ˢ Q :=
      Set.prod_mono hball hIQ
    obtain ⟨C, hC⟩ := ((isCompact_closedBall x r).prod isCompact_Icc).exists_bound_of_continuousOn
      (hD.continuousOn.mono hprod)
    apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F := fun y t => F (y,t)) (F' := fun y t => D (y,t))
      (bound := fun _ => C) (s := Metric.closedBall x r)
      (Metric.closedBall_mem_nhds x hr)
    · filter_upwards [hO.mem_nhds hx] with y hy
      simpa only [uIoc_of_le zero_le_one] using
        ((hslic y hy).mono Ioc_subset_Icc_self).aestronglyMeasurable (μ := volume) measurableSet_Ioc
    · have h : ContinuousOn (fun t : ℝ => F (x,t)) (uIcc (0 : ℝ) 1) := by
        simpa only [uIcc_of_le zero_le_one] using hslic x hx
      exact h.intervalIntegrable
    · simpa only [uIoc_of_le zero_le_one] using
        ((hslicD x hx).mono Ioc_subset_Icc_self).aestronglyMeasurable (μ := volume) measurableSet_Ioc
    · exact Filter.Eventually.of_forall fun t ht y hy => hC (y,t) ⟨hy, uIoc_subset_uIcc.trans (by simp only [uIcc_of_le zero_le_one]; exact Subset.rfl) ht⟩
    · exact intervalIntegrable_const
    · apply Filter.Eventually.of_forall
      intro t ht y hy
      have hyt : (y,t) ∈ O ×ˢ Q := ⟨hball hy,hIQ (uIoc_subset_uIcc.trans (by simp only [uIcc_of_le zero_le_one]; exact Subset.rfl) ht)⟩
      exact ((hF.contDiffAt ((hO.prod hQ).mem_nhds hyt)).differentiableAt (by simp)).hasFDerivAt.comp y
        ((hasFDerivAt_id y).prodMk (hasFDerivAt_const t y))
  have integralN : ∀ (n : ℕ),
    ∀ (G : Type) [NormedAddCommGroup G] [NormedSpace ℝ G]
    (O : Set E2) (Q : Set ℝ) (hO : IsOpen O) (hQ : IsOpen Q)
    (hIQ : Icc (0 : ℝ) 1 ⊆ Q) (F : E2 × ℝ → G),
    ContDiffOn ℝ ∞ F (O ×ˢ Q) →
    ContDiffOn ℝ (n : ℕ∞ω) (fun x => ∫ t in (0 : ℝ)..1, F (x,t)) O := by
    intro n
    induction n with
    | zero =>
      intro G _ _ O Q hO hQ hIQ F hF
      apply contDiffOn_zero.mpr
      intro x hx
      exact (hasFD G O Q hO hQ hIQ F hF x hx).continuousAt.continuousWithinAt
    | succ n ih =>
      intro G _ _ O Q hO hQ hIQ F hF
      let D : E2 × ℝ → E2 →L[ℝ] G := fun p =>
        (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ E2 ℝ)
      have hD : ContDiffOn ℝ ∞ D (O ×ˢ Q) :=
        (hF.fderiv_of_isOpen (hO.prod hQ) (by simp)).clm_comp contDiffOn_const
      have hderiv (x : E2) (hx : x ∈ O) := hasFD G O Q hO hQ hIQ F hF x hx
      rw [Nat.cast_add, Nat.cast_one]
      apply (contDiffOn_succ_iff_fderiv_of_isOpen hO).mpr
      refine ⟨fun x hx => (hderiv x hx).differentiableAt.differentiableWithinAt, ?_, ?_⟩
      · simp
      · exact (ih (E2 →L[ℝ] G) O Q hO hQ hIQ D hD).congr fun x hx => (hderiv x hx).fderiv
  have integralSmooth : ∀ (G : Type) [NormedAddCommGroup G] [NormedSpace ℝ G]
      (O : Set E2) (Q : Set ℝ) (hO : IsOpen O) (hQ : IsOpen Q)
      (hIQ : Icc (0 : ℝ) 1 ⊆ Q) (F : E2 × ℝ → G),
      ContDiffOn ℝ ∞ F (O ×ˢ Q) →
      ContDiffOn ℝ ∞ (fun x => ∫ t in (0 : ℝ)..1, F (x,t)) O := by
    intro G _ _ O Q hO hQ hIQ F hF
    exact contDiffOn_infty.mpr fun n => integralN n G O Q hO hQ hIQ F hF
  have height_smooth : ContDiffOn ℝ ∞ W.height W.U := W.upper_smooth.sub W.lower_smooth
  have hg : ContDiffOn ℝ ∞ (planarGradient (W.height)) W.U := by
    unfold planarGradient
    have hd : ContDiffOn ℝ ∞ (fderiv ℝ (W.height)) W.U :=
      height_smooth.fderiv_of_isOpen W.U_open (by simp)
    exact ContDiffOn.sum (fun i _ => (hd.clm_apply contDiffOn_const).smul_const _)
  let P : Set (E2 × ℝ) := {p | p.1 ∈ W.U ∧ jetPoint (W.segmentJet p.1 p.2) ∈ W.V}
  have hp : ContDiffOn ℝ ∞ (fun p : E2 × ℝ => jetPoint (W.segmentJet p.1 p.2))
      (W.U ×ˢ univ) := by
    have hf : ContDiffOn ℝ ∞ (fun p : E2 × ℝ => W.height p.1) (W.U ×ˢ univ) :=
      height_smooth.comp contDiffOn_fst (fun p hp => hp.1)
    unfold jetPoint TwoHeightGraphWindow.segmentJet
    apply (EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff.comp_contDiffOn
    apply contDiffOn_pi.mpr
    intro i
    fin_cases i
    · exact (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff.comp_contDiffOn contDiffOn_fst
    · exact (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff.comp_contDiffOn contDiffOn_fst
    · exact (W.lower_smooth.comp contDiffOn_fst (fun p hp => hp.1)).add (contDiffOn_snd.mul hf)
  have hP : IsOpen P := by
    have h := hp.continuousOn.isOpen_inter_preimage (W.U_open.prod isOpen_univ) W.V_open
    simpa [P, Set.prod_univ, Set.preimage, Set.inter_def] using h
  have hH : IsCompact W.compactBase := W.compactBase_compact
  obtain ⟨O, Q, hO, hQ, hHO, hIQ, hOP⟩ := generalized_tube_lemma hH
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)) hP (by
      intro p hp
      exact ⟨W.U_contains hp.1, W.jets_inside p.1 hp.1 p.2 hp.2⟩)
  have hOU : O ⊆ W.U := by
    intro x hx
    exact (hOP (show (x, (0 : ℝ)) ∈ O ×ˢ Q from ⟨hx, hIQ (by simp)⟩)).1

  have hsegments : ∀ x ∈ O, ∀ t ∈ Q, jetPoint (W.segmentJet x t) ∈ W.V :=
    fun x hx t ht => (hOP (show (x,t) ∈ O ×ˢ Q from ⟨hx,ht⟩)).2
  have hheight := height_smooth.mono hOU
  have hgrad := hg.mono hOU
  have hsegment : ContDiffOn ℝ ∞ (fun p : E2 × ℝ => W.segmentJet p.1 p.2) (O ×ˢ Q) := by
    have hh : ContDiffOn ℝ ∞ (fun p : E2 × ℝ => W.height p.1) (O ×ˢ Q) :=
      hheight.comp contDiffOn_fst (fun p hp => hp.1)
    have hhg : ContDiffOn ℝ ∞ (fun p : E2 × ℝ => planarGradient (W.height) p.1) (O ×ˢ Q) :=
      hgrad.comp contDiffOn_fst (fun p hp => hp.1)
    have hl : ContDiffOn ℝ ∞ (fun p : E2 × ℝ => W.lowerHeightFunction p.1) (O ×ˢ Q) :=
      W.lower_smooth.comp contDiffOn_fst (fun p hp => hOU hp.1)
    have hlg : ContDiffOn ℝ ∞ (planarGradient W.lowerHeightFunction) W.U := by
      unfold planarGradient
      exact ContDiffOn.sum (fun i _ => ((W.lower_smooth.fderiv_of_isOpen W.U_open (by simp)).clm_apply contDiffOn_const).smul_const _)
    have hlgs : ContDiffOn ℝ ∞ (fun p : E2 × ℝ => planarGradient W.lowerHeightFunction p.1) (O ×ˢ Q) :=
      hlg.comp contDiffOn_fst (fun p hp => hOU hp.1)
    exact contDiffOn_fst.prodMk ((hl.add (contDiffOn_snd.mul hh)).prodMk
      (hlgs.add (contDiffOn_snd.smul hhg)))
  have hpoint : ContDiff ℝ ∞ jetPoint := by
    unfold jetPoint
    apply (EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff.comp
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff.comp contDiff_fst
    · exact (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff.comp contDiff_fst
    · exact contDiff_fst.comp contDiff_snd
  have hA : IsOpen (jetPoint ⁻¹' W.V) := W.V_open.preimage hpoint.continuous
  have partialP (F : Jet → ℝ) (hF : ContDiffOn ℝ ∞ F (jetPoint ⁻¹' W.V)) (i : Fin 2) :
      ContDiffOn ℝ ∞ (fun j : Jet => fderiv ℝ (fun p : E2 => F (j.1,j.2.1,p))
        j.2.2 (coordinateVector 2 i)) (jetPoint ⁻¹' W.V) := by
    intro j hj
    apply ContDiffAt.contDiffWithinAt
    have hD := hF.contDiffAt (hA.mem_nhds hj)
    have hpair : ContDiffAt ℝ ∞
        (fun p : Jet × E2 => (p.1.1, p.1.2.1, p.2)) (j,j.2.2) :=
      contDiffAt_fst.fst.prodMk (contDiffAt_fst.snd.fst.prodMk contDiffAt_snd)
    exact ((hD.comp (j,j.2.2) hpair).fderiv contDiffAt_snd.snd (by simp)).clm_apply contDiffAt_const
  have partialZ (F : Jet → ℝ) (hF : ContDiffOn ℝ ∞ F (jetPoint ⁻¹' W.V)) :
      ContDiffOn ℝ ∞ (fun j : Jet => deriv (fun z : ℝ => F (j.1,z,j.2.2))
        j.2.1) (jetPoint ⁻¹' W.V) := by
    intro j hj
    apply ContDiffAt.contDiffWithinAt
    have hD := hF.contDiffAt (hA.mem_nhds hj)
    have hpair : ContDiffAt ℝ ∞
        (fun p : Jet × ℝ => (p.1.1, p.2, p.1.2.2)) (j,j.2.1) :=
      contDiffAt_fst.fst.prodMk (contDiffAt_snd.prodMk contDiffAt_fst.snd.snd)
    exact ((hD.comp (j,j.2.1) hpair).fderiv contDiffAt_snd.fst (by simp)).clm_apply contDiffAt_const
  have hfluxi (i : Fin 2) : ContDiffOn ℝ ∞ (fun j : Jet => W.flux j i) (jetPoint ⁻¹' W.V) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp_contDiffOn hfl.1
  have ha (i j : Fin 2) : ContDiffOn ℝ ∞ (fun x => W.a x i j) O :=
    integralSmooth ℝ O Q hO hQ hIQ _
      ((partialP (fun j : Jet => W.flux j i) (hfluxi i) j).comp hsegment
        (fun p hp => hsegments p.1 hp.1 p.2 hp.2))
  have hq : ContDiffOn ℝ ∞ W.q O := by
    apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.contDiff.comp_contDiffOn
    apply contDiffOn_pi.mpr
    intro i
    exact integralSmooth ℝ O Q hO hQ hIQ _
      ((partialZ (fun j : Jet => W.flux j i) (hfluxi i)).comp hsegment
        (fun p hp => hsegments p.1 hp.1 p.2 hp.2))
  have hlg : ContDiffOn ℝ ∞ W.lowerGradient O := by
    apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.contDiff.comp_contDiffOn
    apply contDiffOn_pi.mpr
    intro i
    exact integralSmooth ℝ O Q hO hQ hIQ _
      ((partialP W.lower hfl.2 i).comp hsegment
        (fun p hp => hsegments p.1 hp.1 p.2 hp.2))
  have hlh : ContDiffOn ℝ ∞ W.lowerHeight O :=
    integralSmooth ℝ O Q hO hQ hIQ _
      ((partialZ W.lower hfl.2).comp hsegment
        (fun p hp => hsegments p.1 hp.1 p.2 hp.2))
  have hb : ContDiffOn ℝ ∞ W.b O := hq.add hlg
  have hc : ContDiffOn ℝ ∞ W.c O := by
    apply ContDiffOn.add _ hlh
    apply ContDiffOn.sum
    intro i hi
    have hqi : ContDiffOn ℝ ∞ (fun y => W.q y i) O :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp_contDiffOn hq
    exact (hqi.fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const
  exact ⟨O,hO,hHO,hOU,fun x hx t ht => hsegments x hx t (hIQ ht),
    hheight,hgrad,ha,hq,hlg,hlh,hb,hc⟩


end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3TwoHeightEndpointMeanValueV480 -/
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped Manifold ContDiff BigOperators
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- The affine two-height coefficients recover the literal upper-minus-lower
flux and lower-order differences. No baseline replacement is made. -/
theorem two_height_endpoint_mean_value (W : TwoHeightGraphWindow)
    (O : Set E2) (hO : IsOpen O) (hU : O ⊆ W.U)
    (hsegments : ∀ x ∈ O, ∀ t ∈ Icc (0 : ℝ) 1,
      jetPoint (W.segmentJet x t) ∈ W.V) :
    (∀ x ∈ O,
      W.flux (x, W.upperHeightFunction x, planarGradient W.upperHeightFunction x) -
        W.flux (x, W.lowerHeightFunction x, planarGradient W.lowerHeightFunction x) =
      matrixAction (W.a x) (planarGradient W.height x) + W.height x • W.q x) ∧
    (∀ x ∈ O,
      W.lower (x, W.upperHeightFunction x, planarGradient W.upperHeightFunction x) -
        W.lower (x, W.lowerHeightFunction x, planarGradient W.lowerHeightFunction x) =
      inner ℝ (W.lowerGradient x) (planarGradient W.height x) +
        W.lowerHeight x * W.height x) := by
  have hpoint : ContDiff ℝ ∞ jetPoint := by
    unfold jetPoint
    apply (EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff.comp
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> simp <;> fun_prop
  have hA : IsOpen (jetPoint ⁻¹' W.V) := W.V_open.preimage hpoint.continuous
  have hcal := native_interior_graph_jet_calculus_v475 W.V W.V_open W.metric
  have hfluxi (i : Fin 2) : ContDiffOn ℝ ∞ (fun j : Jet => W.flux j i) (jetPoint ⁻¹' W.V) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp_contDiffOn hcal.2.1
  have hdiff (x : E2) (hx : x ∈ O) :
      planarGradient W.height x =
        planarGradient W.upperHeightFunction x - planarGradient W.lowerHeightFunction x :=
    planarGradient_sub
      ((W.upper_smooth.contDiffAt (W.U_open.mem_nhds (hU hx))).differentiableAt (by simp))
      ((W.lower_smooth.contDiffAt (W.U_open.mem_nhds (hU hx))).differentiableAt (by simp))
  have hMVF (x : E2) (hx : x ∈ O) (i : Fin 2) :=
    scalar_affine_jet_mean_value _ hA (fun j => W.flux j i) (hfluxi i) x
      (planarGradient W.lowerHeightFunction x) (planarGradient W.height x)
      (W.lowerHeightFunction x) (W.height x) (hsegments x hx)
  have hMVL (x : E2) (hx : x ∈ O) :=
    scalar_affine_jet_mean_value _ hA W.lower hcal.2.2 x
      (planarGradient W.lowerHeightFunction x) (planarGradient W.height x)
      (W.lowerHeightFunction x) (W.height x) (hsegments x hx)
  constructor
  · intro x hx
    ext i
    have hh := (hMVF x hx i).2.2
    have he : W.lowerHeightFunction x + W.height x = W.upperHeightFunction x := by
      dsimp [TwoHeightGraphWindow.height]
      ring
    have hg : planarGradient W.lowerHeightFunction x + planarGradient W.height x =
        planarGradient W.upperHeightFunction x := by rw [hdiff x hx]; abel
    rw [he, hg] at hh
    simpa [matrixAction, TwoHeightGraphWindow.a, TwoHeightGraphWindow.q,
      TwoHeightGraphWindow.segmentJet, mul_comm] using hh
  · intro x hx
    have hh := (hMVL x hx).2.2
    have he : W.lowerHeightFunction x + W.height x = W.upperHeightFunction x := by
      dsimp [TwoHeightGraphWindow.height]
      ring
    have hg : planarGradient W.lowerHeightFunction x + planarGradient W.height x =
        planarGradient W.upperHeightFunction x := by rw [hdiff x hx]; abel
    rw [he, hg] at hh
    simpa [TwoHeightGraphWindow.lowerGradient, TwoHeightGraphWindow.lowerHeight,
      TwoHeightGraphWindow.segmentJet, EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct, mul_comm] using hh

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3TwoHeightResidualV480 -/
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped Manifold ContDiff BigOperators
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

theorem two_height_residual_mean_value (W : TwoHeightGraphWindow)
    (O : Set E2) (hO : IsOpen O) (hU : O ⊆ W.U)
    (hs : ∀ x ∈ O, ∀ t ∈ Icc (0 : ℝ) 1, jetPoint (W.segmentJet x t) ∈ W.V)
    (hq : ContDiffOn ℝ ∞ W.q O) :
    ∀ x ∈ O, W.residual W.upperHeightFunction x - W.residual W.lowerHeightFunction x =
      classicalL W.a W.b W.c W.height x := by
  have jp_smooth : ContDiff ℝ ∞ jetPoint := by
    unfold jetPoint
    apply (EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff.comp
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> simp <;> fun_prop
  have flux_lower_smooth (W : TwoHeightGraphWindow) :
      (∀ i : Fin 2, ContDiffOn ℝ ∞ (fun j => W.flux j i) (jetPoint ⁻¹' W.V)) ∧
      ContDiffOn ℝ ∞ W.lower (jetPoint ⁻¹' W.V) := by
    have hh := native_interior_graph_jet_calculus_v475 W.V W.V_open W.metric
    exact ⟨fun i => (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp_contDiffOn hh.2.1,hh.2.2⟩
  have grad_smooth (U : Set E2) (hU : IsOpen U) (u : E2 → ℝ)
      (hu : ContDiffOn ℝ ∞ u U) : ContDiffOn ℝ ∞ (planarGradient u) U := by
    unfold planarGradient
    apply ContDiffOn.sum
    intro i hi
    exact ((hu.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const).smul contDiffOn_const
  have smooth_coord (U : Set E2) (f : E2 → E2)
      (hf : ContDiffOn ℝ ∞ f U) (i : Fin 2) : ContDiffOn ℝ ∞ (fun x => f x i) U := by
    exact (show ContDiff ℝ ∞ (fun p : E2 => p i) by fun_prop).comp_contDiffOn hf
  have residual_identity (W : TwoHeightGraphWindow) (O : Set E2) (hO : IsOpen O) (hU : O ⊆ W.U)
      (hs : ∀ x ∈ O, ∀ t ∈ Icc (0 : ℝ) 1, jetPoint (W.segmentJet x t) ∈ W.V)
      (hq : ContDiffOn ℝ ∞ W.q O)
      (hF : ∀ x ∈ O, W.flux (x, W.upperHeightFunction x, planarGradient W.upperHeightFunction x) -
        W.flux (x, W.lowerHeightFunction x, planarGradient W.lowerHeightFunction x) = matrixAction (W.a x) (planarGradient (W.height) x) +
          W.height x • W.q x)
      (hL : ∀ x ∈ O, W.lower (x, W.upperHeightFunction x, planarGradient W.upperHeightFunction x) -
        W.lower (x, W.lowerHeightFunction x, planarGradient W.lowerHeightFunction x) = inner ℝ (W.lowerGradient x) (planarGradient (W.height) x) +
          W.lowerHeight x * W.height x) :
      ∀ x ∈ O, W.residual W.upperHeightFunction x - W.residual W.lowerHeightFunction x =
        classicalL W.a W.b W.c (W.height) x := by
    let u := W.height
    have hu : ContDiffOn ℝ ∞ u O := (W.upper_smooth.sub W.lower_smooth).mono hU
    have hg : ContDiffOn ℝ ∞ (planarGradient u) O := grad_smooth O hO u hu
    have hJ : IsOpen (jetPoint ⁻¹' W.V) := W.V_open.preimage jp_smooth.continuous
    have hf := (flux_lower_smooth W).1
    have hupp := W.upper_smooth.mono hU
    have hlow := W.lower_smooth.mono hU
    have hjet : ContDiffOn ℝ ∞ (fun x : E2 => (x,W.upperHeightFunction x,planarGradient W.upperHeightFunction x) : E2 → Jet) O :=
      contDiffOn_id.prodMk (hupp.prodMk (grad_smooth O hO W.upperHeightFunction hupp))
    have hzjet : ContDiffOn ℝ ∞ (fun x : E2 => (x,W.lowerHeightFunction x,planarGradient W.lowerHeightFunction x) : E2 → Jet) O :=
      contDiffOn_id.prodMk (hlow.prodMk (grad_smooth O hO W.lowerHeightFunction hlow))
    have hFi (i : Fin 2) : ContDiffOn ℝ ∞
        (fun x : E2 => W.flux (x,W.upperHeightFunction x,planarGradient W.upperHeightFunction x) i) O := by
      apply (hf i).comp hjet
      intro x hx
      have ht := hs x hx 1 (by norm_num)
      have hd := planarGradient_sub
        ((hupp.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp))
        ((hlow.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp))
      change planarGradient W.height x =
        planarGradient W.upperHeightFunction x - planarGradient W.lowerHeightFunction x at hd
      have he : W.lowerHeightFunction x + W.height x = W.upperHeightFunction x := by
        dsimp [TwoHeightGraphWindow.height]; ring
      have heG : planarGradient W.lowerHeightFunction x + planarGradient W.height x =
          planarGradient W.upperHeightFunction x := by rw [hd]; abel
      simpa [TwoHeightGraphWindow.segmentJet, he, heG] using ht
    have hZi (i : Fin 2) : ContDiffOn ℝ ∞ (fun x : E2 => W.flux (x,W.lowerHeightFunction x,planarGradient W.lowerHeightFunction x) i) O := by
      apply (hf i).comp hzjet
      intro x hx
      have ht := hs x hx 0 (by norm_num)
      simpa [TwoHeightGraphWindow.segmentJet] using ht
    have hqi (i : Fin 2) := smooth_coord O W.q hq i
    have hMi (i : Fin 2) : ContDiffOn ℝ ∞
        (fun x : E2 => matrixAction (W.a x) (planarGradient u x) i) O := by
      apply (((hFi i).sub (hZi i)).sub (hu.mul (hqi i))).congr
      intro x hx
      have he := congrArg (fun p : E2 => p i) (hF x hx)
      change W.flux (x,W.upperHeightFunction x,planarGradient W.upperHeightFunction x) i - W.flux (x,W.lowerHeightFunction x,planarGradient W.lowerHeightFunction x) i =
        matrixAction (W.a x) (planarGradient u x) i + u x * W.q x i at he
      dsimp only
      linarith
    have hgrad (x : E2) (i : Fin 2) : planarGradient u x i =
        fderiv ℝ u x (coordinateVector 2 i) := by
      fin_cases i <;> simp [planarGradient,Fin.sum_univ_two,coordinateVector,EuclideanSpace.single]
    intro x hx
    have hdu := (hu.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
    have hdF (i : Fin 2) := ((hFi i).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
    have hdZ (i : Fin 2) := ((hZi i).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
    have hdQ (i : Fin 2) := ((hqi i).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
    have hdM (i : Fin 2) := ((hMi i).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
    have he (i : Fin 2) :
        fderiv ℝ (fun y : E2 => W.flux (y,W.upperHeightFunction y,planarGradient W.upperHeightFunction y) i) x (coordinateVector 2 i) -
        fderiv ℝ (fun y : E2 => W.flux (y,W.lowerHeightFunction y,planarGradient W.lowerHeightFunction y) i) x (coordinateVector 2 i) =
        fderiv ℝ (fun y : E2 => matrixAction (W.a y) (planarGradient u y) i) x (coordinateVector 2 i) +
        u x * fderiv ℝ (fun y : E2 => W.q y i) x (coordinateVector 2 i) +
          W.q x i * planarGradient u x i := by
      have hev : (fun y : E2 => W.flux (y,W.upperHeightFunction y,planarGradient W.upperHeightFunction y) i - W.flux (y,W.lowerHeightFunction y,planarGradient W.lowerHeightFunction y) i) =ᶠ[𝓝 x]
          (fun y : E2 => matrixAction (W.a y) (planarGradient u y) i + u y * W.q y i) := by
        filter_upwards [hO.mem_nhds hx] with y hy
        exact congrArg (fun p : E2 => p i) (hF y hy)
      have hh := congrArg (fun L : E2 →L[ℝ] ℝ => L (coordinateVector 2 i)) hev.fderiv_eq
      have hr := (hdM i).hasFDerivAt.add (hdu.hasFDerivAt.mul (hdQ i).hasFDerivAt)
      have hl := (hdF i).hasFDerivAt.sub (hdZ i).hasFDerivAt
      have hl' : fderiv ℝ (fun y : E2 => W.flux (y,W.upperHeightFunction y,planarGradient W.upperHeightFunction y) i - W.flux (y,W.lowerHeightFunction y,planarGradient W.lowerHeightFunction y) i) x =
        fderiv ℝ (fun y : E2 => W.flux (y,W.upperHeightFunction y,planarGradient W.upperHeightFunction y) i) x -
        fderiv ℝ (fun y : E2 => W.flux (y,W.lowerHeightFunction y,planarGradient W.lowerHeightFunction y) i) x := hl.fderiv
      have hr' : fderiv ℝ (fun y : E2 => matrixAction (W.a y) (planarGradient u y) i + u y * W.q y i) x =
        fderiv ℝ (fun y : E2 => matrixAction (W.a y) (planarGradient u y) i) x +
        (u x • fderiv ℝ (fun y : E2 => W.q y i) x + W.q x i • fderiv ℝ u x) := hr.fderiv
      rw [hl',hr'] at hh
      simpa [hgrad,add_assoc] using hh
    have hl := hL x hx
    have he0 := he 0
    have he1 := he 1
    delta TwoHeightGraphWindow.residual classicalL TwoHeightGraphWindow.b TwoHeightGraphWindow.c
    simp only [Fin.sum_univ_two,
      EuclideanSpace.inner_eq_star_dotProduct,dotProduct,
      star_trivial,PiLp.add_apply] at *
    dsimp only [u] at *
    nlinarith
  obtain ⟨hF,hL⟩ := two_height_endpoint_mean_value W O hO hU hs
  exact residual_identity W O hO hU hs hq hF hL
end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3TwoHeightEllipticityV480 -/
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped Manifold ContDiff BigOperators
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.A3MetricVariationBridges
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
theorem two_height_slope_hessian_uniform_bounds (W : TwoHeightGraphWindow) :
    (∀ j : Jet, jetPoint j ∈ W.V → ∀ i k : Fin 2,
      fderiv ℝ (fun p : E2 => W.flux (j.1, j.2.1, p) i) j.2.2
          (coordinateVector 2 k) =
        Matrix.det (W.metric.tensor (jetPoint j)) / W.density j *
          (W.gram j)⁻¹ i k) ∧
    (∀ x ∈ W.compactBase, ∀ i j : Fin 2, W.a x i j = W.a x j i) ∧
    (∃ ell C : ℝ, 0 < ell ∧ 0 < C ∧
      ∀ x ∈ W.compactBase, ∀ p : E2,
        ell * ‖p‖ ^ 2 ≤ inner ℝ p (matrixAction (W.a x) p) ∧
        inner ℝ p (matrixAction (W.a x) p) ≤ C * ‖p‖ ^ 2) := by
  classical
  let L : E2 →L[ℝ] E3 :=
    (EuclideanSpace.proj 0).smulRight (coordinateVector 3 0) +
      (EuclideanSpace.proj 1).smulRight (coordinateVector 3 1)
  let n : E3 := coordinateVector 3 2
  have hL (i : Fin 2) : L (coordinateVector 2 i) = coordinateVector 3 (Fin.castSucc i) := by
    fin_cases i <;> ext k <;> fin_cases k <;>
      simp [L, coordinateVector, EuclideanSpace.single]
  have hsplit : Function.Bijective (fun z : E2 × ℝ => L z.1 + z.2 • n) := by
    constructor
    · intro z w h
      have h0 := congrArg (fun y : E3 => y 0) h
      have h1 := congrArg (fun y : E3 => y 1) h
      have h2 := congrArg (fun y : E3 => y 2) h
      simp [L,n,coordinateVector,EuclideanSpace.single] at h0 h1 h2
      apply Prod.ext
      · ext i
        fin_cases i
        · exact h0
        · exact h1
      · exact h2
    · intro y
      refine ⟨((EuclideanSpace.equiv (Fin 2) ℝ).symm ![y 0,y 1],y 2),?_⟩
      ext k
      fin_cases k <;> simp [L,n,coordinateVector,EuclideanSpace.single]
  have hsplitGram (B : Matrix (Fin 3) (Fin 3) ℝ) : splittingGram B L n = B := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [splittingGram,coordinateInner,L,n,coordinateVector,EuclideanSpace.single,
        Fin.sum_univ_three]
  have hmetric (y : E3) (hy : y ∈ W.V) : (W.metric.tensor y).PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · ext a c
      exact W.metric.symmetric y hy c a
    · intro x hx
      let w : E3 := WithLp.toLp 2 x
      have hw : w ≠ 0 := by
        intro he
        apply hx
        exact congrArg WithLp.ofLp he
      have hp := W.metric.positive y hy w hw
      convert hp using 1
      simp only [coordinateInner,dotProduct,Matrix.mulVec,Fin.sum_univ_three,
        Pi.star_apply,star_trivial]
      dsimp [w]
      ring
  have hgram_eq (x : E2) (z : ℝ) (p : E2) :
      slopeGram (W.metric.tensor (jetPoint (x,z,p))) L n p = W.gram (x,z,p) := by
    ext i k
    dsimp [slopeGram,TwoHeightGraphWindow.gram,jetTangent]
    rw [hL i,hL k]
    rfl
  have harea_eq (x : E2) (z : ℝ) :
      slopeArea (W.metric.tensor (jetPoint (x,z,0))) L n =
        (fun p : E2 => W.density (x,z,p)) := by
    funext p
    exact congrArg (fun A : Mat2 => Real.sqrt (Matrix.det A)) (hgram_eq x z p)
  have hflux_eq (x : E2) (z : ℝ) :
      slopeFlux (W.metric.tensor (jetPoint (x,z,0))) L n =
        (fun p : E2 => W.flux (x,z,p)) := by
    change planarGradient (slopeArea (W.metric.tensor (jetPoint (x,z,0))) L n) =
      (fun p => planarGradient (fun q => W.density (x,z,q)) p)
    rw [harea_eq]
  have hhessian_eq (j : Jet) :
      slopeHessian (W.metric.tensor (jetPoint j)) L n j.2.2 =
        (Matrix.of fun i k => fderiv ℝ (fun p : E2 => W.flux (j.1,j.2.1,p) i)
          j.2.2 (coordinateVector 2 k)) := by
    rcases j with ⟨x,z,p⟩
    ext i k
    dsimp [slopeHessian]
    change fderiv ℝ (fun q : E2 => slopeFlux (W.metric.tensor (jetPoint (x,z,0))) L n q i)
      p (coordinateVector 2 k) = _
    rw [hflux_eq x z]
  have hformula (j : Jet) (hj : jetPoint j ∈ W.V) (i k : Fin 2) :
      fderiv ℝ (fun p : E2 => W.flux (j.1,j.2.1,p) i) j.2.2
        (coordinateVector 2 k) = Matrix.det (W.metric.tensor (jetPoint j)) / W.density j *
          (W.gram j)⁻¹ i k := by
    have h := slope_area_hessian_formula (W.metric.tensor (jetPoint j))
      (hmetric _ hj) L n hsplit j.2.2 i k
    rw [hsplitGram, hhessian_eq] at h
    change _ = Matrix.det (W.metric.tensor (jetPoint j)) / Real.sqrt (Matrix.det (W.gram j)) *
      (W.gram j)⁻¹ i k
    simpa only [slopeArea,hgram_eq,Prod.eta,Matrix.of_apply] using h
  have hsym (j : Jet) (hj : jetPoint j ∈ W.V) (i k : Fin 2) :
      fderiv ℝ (fun p : E2 => W.flux (j.1,j.2.1,p) i) j.2.2
        (coordinateVector 2 k) =
      fderiv ℝ (fun p : E2 => W.flux (j.1,j.2.1,p) k) j.2.2
        (coordinateVector 2 i) := by
    have h := (slope_area_hessian_posDef (W.metric.tensor (jetPoint j))
      (hmetric _ hj) L n hsplit j.2.2).isHermitian.apply k i
    rw [hhessian_eq] at h
    simpa only [star_trivial,Matrix.of_apply] using h
  have hgrampos (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.PosDef) (q : E2) : (slopeGram B L n q).PosDef := by
    let v : Fin 2 → E3 := fun i => L (coordinateVector 2 i) + q i • n
    have hli : LinearIndependent ℝ v := by
      apply Fintype.linearIndependent_iff.mpr
      intro a ha
      have hs : L (∑ i : Fin 2, a i • coordinateVector 2 i) +
          (∑ i : Fin 2, a i * q i) • n = 0 := by
        simpa only [v, smul_add, Finset.sum_add_distrib,
          map_sum, map_smul, mul_smul, Finset.sum_smul] using ha
      have he : ((∑ i : Fin 2, a i • coordinateVector 2 i), ∑ i : Fin 2, a i * q i) =
          ((0 : E2), (0 : ℝ)) := by
        apply hsplit.injective
        simpa only [map_zero, zero_smul, add_zero] using hs
      have hz := congrArg Prod.fst he
      intro i
      have heval := congrArg (fun z : E2 => z i) hz
      fin_cases i <;> simpa [coordinateVector, EuclideanSpace.single, Pi.single_apply] using heval
    let V : Matrix (Fin 3) (Fin 2) ℝ := fun a i => v i a
    have hV : Function.Injective V.mulVec := by
      intro x y hxy
      have hsum : ∑ i, (x i - y i) • v i = 0 := by
        ext a
        have hh := congrFun hxy a
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hh
        simpa only [Fin.sum_univ_two, PiLp.add_apply, PiLp.smul_apply,
          smul_eq_mul, sub_mul, PiLp.zero_apply] using (by
            dsimp [V] at hh
            nlinarith [hh] : (x 0 - y 0) * v 0 a + (x 1 - y 1) * v 1 a = 0)
      have he := Fintype.linearIndependent_iff.mp hli _ hsum
      funext i
      exact sub_eq_zero.mp (he i)
    have heq : slopeGram B L n q = V.conjTranspose * B * V := by
      ext i j
      change (∑ a : Fin 3, ∑ b : Fin 3, B a b * v i a * v j b) =
        ∑ b : Fin 3, (∑ a : Fin 3, v i a * B a b) * v j b
      simp only [Fin.sum_univ_three]
      ring
    rw [heq]
    exact hB.conjTranspose_mul_mul_same hV
  have hinner (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.PosDef)
    (L : E2 →L[ℝ] E3) (n : E3)
    (hsplit : Function.Bijective (fun z : E2 × ℝ => L z.1 + z.2 • n))
    (p ξ : E2) :
    inner ℝ (fderiv ℝ (slopeFlux B L n) p ξ) ξ =
      ∑ i : Fin 2, ∑ j : Fin 2, slopeHessian B L n p i j * ξ i * ξ j := by
    classical
    have hc (i : Fin 2) : DifferentiableAt ℝ (fun q : E2 => slopeFlux B L n q i) p := by
      by_contra hn
      have hp : 0 < slopeHessian B L n p i i :=
        (slope_area_hessian_posDef B hB L n hsplit p).diag_pos
      change 0 < (fderiv ℝ (fun q : E2 => slopeFlux B L n q i) p) (coordinateVector 2 i) at hp
      rw [fderiv_zero_of_not_differentiableAt hn, ContinuousLinearMap.zero_apply] at hp
      exact (lt_irrefl 0) hp
    have hf : DifferentiableAt ℝ (slopeFlux B L n) p :=
      (differentiableAt_piLp 2).mpr hc
    have hi (i : Fin 2) : fderiv ℝ (fun q : E2 => slopeFlux B L n q i) p =
        (EuclideanSpace.proj i).comp (fderiv ℝ (slopeFlux B L n) p) := by
      exact ((EuclideanSpace.proj i).hasFDerivAt.comp p hf.hasFDerivAt).fderiv
    have hx : ξ = ∑ j : Fin 2, ξ j • coordinateVector 2 j := by
      ext i
      fin_cases i <;> simp [coordinateVector, EuclideanSpace.single]
    rw [PiLp.inner_apply, Fin.sum_univ_two]
    simp only [RCLike.inner_apply, conj_trivial]
    have hh (i : Fin 2) : (fderiv ℝ (slopeFlux B L n) p ξ) i =
        ∑ j : Fin 2, ξ j * slopeHessian B L n p i j := by
      change (EuclideanSpace.proj i) (fderiv ℝ (slopeFlux B L n) p ξ) = _
      rw [← ContinuousLinearMap.comp_apply, ← hi]
      conv_lhs => rw [hx]
      simp only [map_sum, map_smul, smul_eq_mul]
      rfl
    rw [hh 0, hh 1]
    simp only [Fin.sum_univ_two]
    ring
  have hclosed : IsCompact W.compactBase := W.compactBase_compact
  have height_smooth : ContDiffOn ℝ ∞ W.height W.U := W.upper_smooth.sub W.lower_smooth
  have hgradU : ContinuousOn (planarGradient (W.height)) W.U := by
    have hdu : ContinuousOn (fderiv ℝ (W.height)) W.U := by
      intro x hx
      exact (((height_smooth x hx).contDiffAt (W.U_open.mem_nhds hx)).fderiv_right
        (m := 0) (by simp)).continuousAt.continuousWithinAt
    unfold planarGradient
    apply continuousOn_finsetSum
    intro i hi
    exact (hdu.clm_apply continuousOn_const).smul continuousOn_const
  let X : Set (E2 × ℝ) := W.compactBase ×ˢ Icc (0 : ℝ) 1
  have hX : IsCompact X := hclosed.prod isCompact_Icc
  let jmap : E2 × ℝ → Jet := fun z => W.segmentJet z.1 z.2
  have hjmap : ContinuousOn jmap X := by
    have hgl : ContinuousOn (planarGradient W.lowerHeightFunction) W.U := by
      unfold planarGradient
      have hdl : ContDiffOn ℝ ∞ (fderiv ℝ W.lowerHeightFunction) W.U :=
        W.lower_smooth.fderiv_of_isOpen W.U_open (by simp)
      exact continuousOn_finsetSum _ (fun i _ =>
        (hdl.continuousOn.clm_apply continuousOn_const).smul continuousOn_const)
    exact continuousOn_fst.prodMk
      (((W.lower_smooth.continuousOn.comp continuousOn_fst
        (fun z hz => W.U_contains hz.1)).add
        (continuousOn_snd.mul (height_smooth.continuousOn.comp continuousOn_fst
          (fun z hz => W.U_contains hz.1)))).prodMk
        ((hgl.comp continuousOn_fst (fun z hz => W.U_contains hz.1)).add
          (continuousOn_snd.smul (hgradU.comp continuousOn_fst
            (fun z hz => W.U_contains hz.1)))))
  have hjV (z : E2 × ℝ) (hz : z ∈ X) : jetPoint (jmap z) ∈ W.V :=
    W.jets_inside z.1 hz.1 z.2 hz.2
  have hjpoint : Continuous jetPoint := by unfold jetPoint; fun_prop
  let B : E2 × ℝ → Matrix (Fin 3) (Fin 3) ℝ := fun z => W.metric.tensor (jetPoint (jmap z))
  have hBcont : ContinuousOn B X := by
    apply continuousOn_pi.mpr; intro i
    apply continuousOn_pi.mpr; intro k
    exact (W.metric.smooth i k).continuousOn.comp
      (hjpoint.continuousOn.comp hjmap (fun z hz => mem_univ _)) hjV
  have hBpositive : ∀ b ∈ B '' X, b.PosDef := by
    rintro b ⟨z,hz,rfl⟩
    exact hmetric _ (hjV z hz)
  let P : Set E2 := (fun z : E2 × ℝ => (jmap z).2.2) '' X
  have hP : IsCompact P := hX.image_of_continuousOn (continuousOn_snd.comp
    (continuousOn_snd.comp hjmap (fun z hz => mem_univ _)) (fun z hz => mem_univ _))
  obtain ⟨d,a₀,l₀,hd,ha₀,hl₀,hdet,hbound⟩ :=
    compact_metric_slope_hessian_lower_bound (B '' X) (hX.image_of_continuousOn hBcont)
      hBpositive P hP L n hsplit
  let ell : ℝ := d / (a₀*l₀)
  have hell : 0 < ell := div_pos hd (mul_pos ha₀ hl₀)
  let A : E2 × ℝ → Mat2 := fun z => slopeGram (B z) L n (jmap z).2.2
  let H : E2 × ℝ → Mat2 := fun z => slopeHessian (B z) L n (jmap z).2.2
  have hApositive (z : E2 × ℝ) (hz : z ∈ X) : (A z).PosDef :=
    hgrampos (B z) (hmetric _ (hjV z hz)) _
  have hAcont : ContinuousOn A X := by
    have hg : Continuous (fun z : Matrix (Fin 3) (Fin 3) ℝ × E2 => slopeGram z.1 L n z.2) := by
      apply continuous_pi; intro i
      apply continuous_pi; intro k
      unfold slopeGram coordinateInner
      simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
      fun_prop
    exact hg.continuousOn.comp (hBcont.prodMk (continuousOn_snd.comp
      (continuousOn_snd.comp hjmap (fun z hz => mem_univ _)) (fun z hz => mem_univ _)))
      (fun z hz => mem_univ _)
  have hinvcont : ContinuousOn (fun z => (A z)⁻¹) X := by
    intro z hz
    apply (continuousAt_matrix_inv (A z) ?_).comp_continuousWithinAt (hAcont z hz)
    have heq : (Ring.inverse : ℝ → ℝ) = Inv.inv := by
      funext r
      exact Ring.inverse_eq_inv r
    rw [heq]
    exact continuousAt_inv₀ (hApositive z hz).det_pos.ne'
  have hcoefcont : ContinuousOn (fun z => Matrix.det (B z) / Real.sqrt (Matrix.det (A z))) X :=
    (continuous_id.matrix_det.continuousOn.comp hBcont (fun z hz => mem_univ _)).div
      (Real.continuous_sqrt.continuousOn.comp
        (continuous_id.matrix_det.continuousOn.comp hAcont (fun z hz => mem_univ _))
      (fun z hz => mem_univ _)) (fun z hz => (Real.sqrt_pos.mpr (hApositive z hz).det_pos).ne')
  have hHcont : ContinuousOn H X := by
    apply (hcoefcont.smul hinvcont).congr
    intro z hz
    ext i k
    exact slope_area_hessian_formula (B z) (hmetric _ (hjV z hz)) L n hsplit
      (jmap z).2.2 i k |>.trans (by rw [hsplitGram]; rfl)
  let sumAbs : E2 × ℝ → ℝ := fun z => ∑ i : Fin 2, ∑ k : Fin 2, |H z i k|
  have hsumcont : ContinuousOn sumAbs X := by
    apply continuousOn_finsetSum
    intro i hi
    apply continuousOn_finsetSum
    intro k hk
    exact ((continuous_apply k).comp_continuousOn
      ((continuous_apply i).comp_continuousOn hHcont)).abs
  obtain ⟨C₀,hC₀⟩ := hX.bddAbove_image hsumcont
  let C : ℝ := max C₀ 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hquad (M : Mat2) (p : E2) :
      inner ℝ p (matrixAction M p) = ∑ i : Fin 2, ∑ k : Fin 2, M i k * p i * p k := by
    change inner ℝ p ((EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i => ∑ k, M i k * p k)) = _
    simp [PiLp.inner_apply,Fin.sum_univ_two,RCLike.inner_apply]
    ring
  have hpointwise (z : E2 × ℝ) (hz : z ∈ X) (p : E2) :
      ell*‖p‖^2 ≤ inner ℝ p (matrixAction (H z) p) ∧
        inner ℝ p (matrixAction (H z) p) ≤ C*‖p‖^2 := by
    constructor
    · have h := ((hbound (B z) (mem_image_of_mem B hz) (jmap z).2.2
        (mem_image_of_mem (fun z : E2 × ℝ => (jmap z).2.2) hz)).2 p).2
      rw [hinner (B z) (hmetric _ (hjV z hz)) L n hsplit, ← hquad] at h
      exact h
    · have hnorm (i : Fin 2) : |p i| ≤ ‖p‖ := by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le p i
      have hterm (i k : Fin 2) : H z i k * p i * p k ≤ |H z i k| * ‖p‖^2 := by
        calc
          _ ≤ |H z i k * p i * p k| := le_abs_self _
          _ = |H z i k| * (|p i| * |p k|) := by rw [abs_mul,abs_mul]; ring
          _ ≤ |H z i k| * (‖p‖*‖p‖) := mul_le_mul_of_nonneg_left
            (mul_le_mul (hnorm i) (hnorm k) (abs_nonneg _) (norm_nonneg _)) (abs_nonneg _)
          _ = _ := by ring
      rw [hquad]
      calc
        _ ≤ ∑ i : Fin 2, ∑ k : Fin 2, |H z i k| * ‖p‖^2 :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => hterm i k
        _ = sumAbs z * ‖p‖^2 := by simp only [sumAbs,Finset.sum_mul]
        _ ≤ C*‖p‖^2 := mul_le_mul_of_nonneg_right
          ((hC₀ (mem_image_of_mem sumAbs hz)).trans (le_max_left _ _)) (sq_nonneg _)
  refine ⟨hformula, ?_, ell,C,hell,hC,?_⟩
  · intro x hx i j
    apply intervalIntegral.integral_congr
    intro t ht
    exact hsym (W.segmentJet x t) (W.jets_inside x hx t (by simpa using ht)) i j
  · intro x hx p
    have htmap : Continuous (fun t : ℝ => (x,t)) := continuous_const.prodMk continuous_id
    have hentrycont (i k : Fin 2) : ContinuousOn (fun t : ℝ => H (x,t) i k) (Icc (0 : ℝ) 1) :=
      ((continuous_apply k).comp_continuousOn ((continuous_apply i).comp_continuousOn hHcont)).comp
        htmap.continuousOn (fun t ht => ⟨hx,ht⟩)
    have hint (i k : Fin 2) : IntervalIntegrable (fun t : ℝ => H (x,t) i k) volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      simpa only [uIcc_of_le zero_le_one] using hentrycont i k
    have hQint : IntervalIntegrable
        (fun t : ℝ => inner ℝ p (matrixAction (H (x,t)) p)) volume 0 1 := by
      simp_rw [hquad]
      exact IntervalIntegrable.sum Finset.univ fun i _ => IntervalIntegrable.sum Finset.univ fun k _ =>
        ((hint i k).mul_const (p i)).mul_const (p k)
    have haeq (i k : Fin 2) : W.a x i k = ∫ t in (0 : ℝ)..1, H (x,t) i k := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact (congrFun (congrFun (hhessian_eq (W.segmentJet x t)) i) k).symm
    have hQeq : inner ℝ p (matrixAction (W.a x) p) =
        ∫ t in (0 : ℝ)..1, inner ℝ p (matrixAction (H (x,t)) p) := by
      simp_rw [hquad,haeq]
      rw [intervalIntegral.integral_finsetSum (s := Finset.univ)
        (f := fun i t => ∑ k : Fin 2, H (x,t) i k * p i * p k)
        (fun i _ => IntervalIntegrable.sum Finset.univ fun k _ =>
          ((hint i k).mul_const (p i)).mul_const (p k))]
      apply Finset.sum_congr rfl
      intro i hi
      rw [intervalIntegral.integral_finsetSum (s := Finset.univ)
        (f := fun k t => H (x,t) i k * p i * p k)
        (fun k _ => ((hint i k).mul_const (p i)).mul_const (p k))]
      simp_rw [intervalIntegral.integral_mul_const]
    rw [hQeq]
    constructor
    · have h := intervalIntegral.integral_mono_on zero_le_one
        (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => ell*‖p‖^2) volume 0 1)
        hQint (fun t ht => (hpointwise (x,t) ⟨hx,ht⟩ p).1)
      simpa only [intervalIntegral.integral_const,sub_zero,one_smul] using h
    · have h := intervalIntegral.integral_mono_on zero_le_one hQint
        (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => C*‖p‖^2) volume 0 1)
        (fun t ht => (hpointwise (x,t) ⟨hx,ht⟩ p).2)
      simpa only [intervalIntegral.integral_const,sub_zero,one_smul] using h

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3TwoHeightLinearEquationV480 -/

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped Manifold ContDiff BigOperators
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def nativePartialDerivativeV480 (f : E2 → ℝ) (i : Fin 2) (x : E2) : ℝ :=
  fderiv ℝ f x (coordinateVector 2 i)

structure NativeLinearGraphEquationV480 (f : E2 → ℝ) (domain : Set E2) where
  principal : Fin 2 → Fin 2 → E2 → ℝ
  drift : Fin 2 → E2 → ℝ
  zeroth : E2 → ℝ
  principal_smooth : ∀ i j, ContDiffOn ℝ ∞ (principal i j) domain
  drift_smooth : ∀ i, ContDiffOn ℝ ∞ (drift i) domain
  zeroth_smooth : ContDiffOn ℝ ∞ zeroth domain
  symmetric : ∀ i j x, x ∈ domain → principal i j x = principal j i x
  ellipticity : ℝ
  ellipticity_pos : 0 < ellipticity
  elliptic : ∀ x ∈ domain, ∀ v : E2,
    ellipticity * ‖v‖ ^ 2 ≤ ∑ i : Fin 2, ∑ j : Fin 2, principal i j x * v i * v j
  equation : ∀ x ∈ domain,
    (∑ i : Fin 2, ∑ j : Fin 2,
      nativePartialDerivativeV480 (fun y => principal i j y * nativePartialDerivativeV480 f j y) i x) +
      (∑ i : Fin 2, drift i x * nativePartialDerivativeV480 f i x) + zeroth x * f x = 0

private theorem native_linear_graph_equation_of_native_operator
    (f : E2 → ℝ) (domain : Set E2) (hopen : IsOpen domain)
    (hf : ContDiffOn ℝ ∞ f domain)
    (a : E2 → Mat2) (b : E2 → E2) (c : E2 → ℝ)
    (hcoeff : SmoothEllipticOn a b c domain)
    (heq : ∀ x ∈ domain, classicalL a b c f x = 0) :
    Nonempty (NativeLinearGraphEquationV480 f domain) := by
  obtain ⟨ha, hb, hc, hsym, ell, C, hell, hC, hbounds⟩ := hcoeff
  have hgradient : ∀ x i, planarGradient f x i = nativePartialDerivativeV480 f i x := by
    intro x i
    fin_cases i <;> simp [planarGradient, nativePartialDerivativeV480, coordinateVector]
  have hflux : ∀ x i, matrixAction (a x) (planarGradient f x) i =
      ∑ j : Fin 2, a x i j * nativePartialDerivativeV480 f j x := by
    intro x i
    simp [matrixAction, hgradient]
  refine ⟨{
    principal := fun i j x => a x i j
    drift := fun i x => b x i
    zeroth := c
    principal_smooth := ha
    drift_smooth := ?_
    zeroth_smooth := hc
    symmetric := fun i j x hx => hsym x hx i j
    ellipticity := ell
    ellipticity_pos := hell
    elliptic := ?_
    equation := ?_ }⟩
  · intro i
    exact (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffOn.comp hb
      (fun _ _ => Set.mem_univ _)
  · intro x hx v
    have h := (hbounds x hx v).1
    convert h using 1
    simp [matrixAction, PiLp.inner_apply]
    ring
  · intro x hx
    have h := heq x hx
    unfold classicalL at h
    simp only [hflux] at h
    have hdiv : (∑ i : Fin 2, fderiv ℝ
        (fun y => ∑ j : Fin 2, a y i j * nativePartialDerivativeV480 f j y) x (coordinateVector 2 i)) =
        ∑ i : Fin 2, ∑ j : Fin 2,
          nativePartialDerivativeV480 (fun y => a y i j * nativePartialDerivativeV480 f j y) i x := by
      apply Finset.sum_congr rfl
      intro i hi
      have hd : ∀ j : Fin 2, DifferentiableAt ℝ
          (fun y => a y i j * nativePartialDerivativeV480 f j y) x := by
        intro j
        apply ((ha i j x hx).contDiffAt (hopen.mem_nhds hx)).differentiableAt (by simp) |>.mul
        exact (((hf x hx).contDiffAt (hopen.mem_nhds hx)).fderiv_right (m := 1)
          (by simp) |>.clm_apply contDiffAt_const).differentiableAt (by norm_num)
      have hsum := (HasFDerivAt.fun_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 2))) =>
        (hd j).hasFDerivAt)).fderiv
      have happ := congrArg (fun L : E2 →L[ℝ] ℝ => L (coordinateVector 2 i)) hsum
      simpa [nativePartialDerivativeV480] using happ
    rw [hdiv] at h
    simpa [PiLp.inner_apply, hgradient, mul_comm] using h

/-- Two actual nonlinear graph solutions yield one linear equation for their
literal difference, on any open set in the compact coefficient base. -/
theorem two_height_native_coefficients (W : TwoHeightGraphWindow)
    (domain : Set E2) (hopen : IsOpen domain) (hbase : domain ⊆ W.compactBase)
    (hupper : ∀ x ∈ domain, W.residual W.upperHeightFunction x = 0)
    (hlower : ∀ x ∈ domain, W.residual W.lowerHeightFunction x = 0) :
    ∃ a : E2 → Mat2, ∃ b : E2 → E2, ∃ c0 : E2 → ℝ,
      SmoothEllipticOn a b c0 domain ∧
      (∀ x ∈ domain, classicalL a b c0 W.height x = 0) := by
  obtain ⟨O, hO, hKO, hOU, hs, hf, hgrad, ha, hq, hlg, hlh, hb, hc⟩ :=
    two_height_coefficient_open_tube W
  obtain ⟨hformula, hsym, ell, C, hell, hC, hbounds⟩ :=
    two_height_slope_hessian_uniform_bounds W
  have hDO : domain ⊆ O := hbase.trans hKO
  have hcoeff : SmoothEllipticOn W.a W.b W.c domain :=
    ⟨fun i j => (ha i j).mono hDO, hb.mono hDO, hc.mono hDO,
      fun x hx i j => hsym x (hbase hx) i j, ell, C, hell, hC,
      fun x hx p => hbounds x (hbase hx) p⟩
  have heq : ∀ x ∈ domain, classicalL W.a W.b W.c W.height x = 0 := by
    intro x hx
    have h := two_height_residual_mean_value W O hO hOU hs hq x (hDO hx)
    rw [hupper x hx, hlower x hx, sub_self] at h
    exact h.symm
  exact ⟨W.a, W.b, W.c, hcoeff, heq⟩

theorem two_height_linear_equation (W : TwoHeightGraphWindow)
    (domain : Set E2) (hopen : IsOpen domain) (hbase : domain ⊆ W.compactBase)
    (hupper : ∀ x ∈ domain, W.residual W.upperHeightFunction x = 0)
    (hlower : ∀ x ∈ domain, W.residual W.lowerHeightFunction x = 0) :
    Nonempty (NativeLinearGraphEquationV480 W.height domain) := by
  obtain ⟨a, b, c0, hcoeff, heq⟩ :=
    two_height_native_coefficients W domain hopen hbase hupper hlower
  exact native_linear_graph_equation_of_native_operator W.height domain hopen
    ((W.upper_smooth.sub W.lower_smooth).mono (hbase.trans W.U_contains))
    a b c0 hcoeff heq

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3InteriorGraphLinearEquationV480 -/

noncomputable section
open Set Topology Function Filter MeasureTheory
open scoped Manifold ContDiff BigOperators
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- Every actual common graph of the original pair satisfies the native linear
graph equation for upper minus lower on a positive concentric ball. -/
theorem original_pair_interior_graph_linear_equation (D : OriginalPair g J)
    {p : E.Carrier} (c : InteriorGraph D.A D.B p) :
    ∃ r : ℝ, 0 < r ∧ r ≤ c.R ∧
      Nonempty (NativeLinearGraphEquationV480 (graphDifference c) (Metric.ball 0 r)) ∧
      ∃ a : E2 → Mat2, ∃ b : E2 → E2, ∃ c0 : E2 → ℝ,
        SmoothEllipticOn a b c0 (Metric.ball 0 r) ∧
        (∀ x ∈ Metric.ball 0 r, classicalL a b c0 (graphDifference c) x = 0) := by
  obtain ⟨V, hV, hVo, H, hlow, hupp⟩ := original_pair_interior_graph_actual_pdes D c
  have hr : 0 < c.R / 2 := half_pos c.R_pos
  have hrR : c.R / 2 < c.R := half_lt_self c.R_pos
  have hKU : Metric.closedBall (0 : E2) (c.R / 2) ⊆ Metric.ball 0 c.R := by
    intro x hx
    exact Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hx).trans_lt hrR)
  have hsegment : ∀ x ∈ Metric.closedBall (0 : E2) (c.R / 2),
      ∀ t ∈ Icc (0 : ℝ) 1,
      jetPoint (x, c.lower x + t * (c.upper x - c.lower x),
        planarGradient c.lower x + t • planarGradient (fun x => c.upper x - c.lower x) x) ∈ V := by
    intro x hx t ht
    have hL := c.lower_inside x (hKU hx)
    have hU := c.upper_inside x (hKU hx)
    have ht0 : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
    have habs : |c.lower x + t * (c.upper x - c.lower x)| < c.eta := by
      calc
        _ = |(1 - t) * c.lower x + t * c.upper x| := by congr 1; ring
        _ ≤ |(1 - t) * c.lower x| + |t * c.upper x| := abs_add_le _ _
        _ = (1 - t) * |c.lower x| + t * |c.upper x| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ht0, abs_of_nonneg ht.1]
        _ ≤ (1 - t) * max |c.lower x| |c.upper x| +
            t * max |c.lower x| |c.upper x| :=
          add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ht0)
            (mul_le_mul_of_nonneg_left (le_max_right _ _) ht.1)
        _ = max |c.lower x| |c.upper x| := by ring
        _ < c.eta := max_lt hL hU
    rw [hV]
    apply c.cylinder_inside
    constructor
    · have hp : graphPlaneCoordinates
          (jetPoint (x, c.lower x + t * (c.upper x - c.lower x),
            planarGradient c.lower x + t • planarGradient (fun x => c.upper x - c.lower x) x)) = x := by
        ext i
        fin_cases i <;> simp [graphPlaneCoordinates, jetPoint]
      rw [hp]
      simpa only [Metric.mem_ball, dist_zero_right] using hKU hx
    · simpa [jetPoint] using habs
  let W : TwoHeightGraphWindow := {
    U := Metric.ball 0 c.R
    U_open := Metric.isOpen_ball
    V := V
    V_open := hVo
    metric := H
    lowerHeightFunction := c.lower
    upperHeightFunction := c.upper
    lower_smooth := c.lower_smooth
    upper_smooth := c.upper_smooth
    compactBase := Metric.closedBall 0 (c.R / 2)
    compactBase_compact := isCompact_closedBall 0 (c.R / 2)
    U_contains := hKU
    jets_inside := hsegment }
  have hbase : Metric.ball (0 : E2) (c.R / 2) ⊆ W.compactBase :=
    Metric.ball_subset_closedBall
  have hlowW : ∀ x ∈ Metric.ball (0 : E2) (c.R / 2),
      W.residual W.lowerHeightFunction x = 0 := by
    intro x hx
    exact hlow x (hKU (hbase hx))
  have huppW : ∀ x ∈ Metric.ball (0 : E2) (c.R / 2),
      W.residual W.upperHeightFunction x = 0 := by
    intro x hx
    exact hupp x (hKU (hbase hx))
  refine ⟨c.R / 2, hr, hrR.le, ?_, ?_⟩
  · exact two_height_linear_equation W (Metric.ball 0 (c.R / 2)) Metric.isOpen_ball
      hbase huppW hlowW
  · exact two_height_native_coefficients W (Metric.ball 0 (c.R / 2)) Metric.isOpen_ball
      hbase huppW hlowW

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3InteriorGraphNoncoincidenceV480 -/

noncomputable section
open Set Topology Function Filter MeasureTheory
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- The original relative minima propagate an actual common interior image germ
to global equality, where the original distance-two assumption excludes it. -/
theorem original_pair_no_interior_agreement_germ (D : OriginalPair g J)
    {p : E.Carrier} (hp : p ∈ (𝓡∂ 3).interior E.Carrier)
    (hA : p ∈ D.A.1.image) (hB : p ∈ D.B.1.image) :
    ¬ native_surface_germ_eq_v475 D.A.1.image D.B.1.image p := by
  intro hg
  obtain ⟨hflowA, hflowB⟩ := original_pair_actual_flow_minima D
  let fA := ProperSmoothEmbedding.ofNeat D.A.1.embedding
  let fB := ProperSmoothEmbedding.ofNeat D.B.1.embedding
  letI : ConnectedSpace D.A.1.surface := D.A.1.connected_for_knot
  letI : ConnectedSpace D.B.1.surface := D.B.1.connected_for_knot
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  have source_interior {S : CompactOrientedSurface.{0}} (F : NeatEmbedding S E.Carrier)
      {x : S} (hx : F.toFun x = p) : x ∈ (𝓡∂ 2).interior S := by
    rw [← (𝓡∂ 2).compl_boundary]
    intro hxB
    change x ∈ S.boundary at hxB
    have hbd : F.toFun x ∈ (𝓡∂ 3).boundary E.Carrier := by
      rwa [← F.boundary_preimage] at hxB
    exact (ModelWithCorners.disjoint_interior_boundary (I := 𝓡∂ 3)
      (M := E.Carrier)).le_bot ⟨hp, hx ▸ hbd⟩
  have hAc : IsClosed D.A.1.image := (isCompact_range fA.smooth.continuous).isClosed
  have hBc : IsClosed D.B.1.image := (isCompact_range fB.smooth.continuous).isClosed
  have hAB : D.A.1.image ⊆ D.B.1.image :=
    native_connected_surface_germ_global_inclusion_v475 fA D.B.1.image hBc
      ⟨a, source_interior D.A.1.embedding ha, by
        change native_surface_germ_eq_v475 D.A.1.image D.B.1.image
          (D.A.1.embedding.toFun a)
        rwa [ha]⟩
      (native_actual_minimizer_germ_locus_closed_v475 g D.A.1.embedding D.B.1.embedding
        hflowA hflowB)
  have hBA : D.B.1.image ⊆ D.A.1.image := by
    obtain ⟨O, hO, hpO, hOeq⟩ := hg
    exact native_connected_surface_germ_global_inclusion_v475 fB D.A.1.image hAc
      ⟨b, source_interior D.B.1.embedding hb,
        O, hO, by
          change D.B.1.embedding.toFun b ∈ O
          rwa [hb], hOeq.symm⟩
      (native_actual_minimizer_germ_locus_closed_v475 g D.B.1.embedding D.A.1.embedding
        hflowB hflowA)
  have himage : D.A.1.image = D.B.1.image := Subset.antisymm hAB hBA
  have hsurface : surfaceImageOf E D.A = surfaceImageOf E D.B := Subtype.ext himage
  have hdist := D.distance_two
  unfold vertexOf at hdist
  rw [hsurface, SimpleGraph.dist_self] at hdist
  norm_num at hdist

/-- A zero germ of the literal graph difference is an actual ambient agreement
germ, using the entire two exact image clauses of the same graph chart. -/
theorem interior_graph_zero_germ_to_surface_germ
    {A B : IncompressibleSpanningSurface.{0} E} {p : E.Carrier}
    (c : InteriorGraph A B p) (V : Set E2) (hV : IsOpen V) (h0 : (0 : E2) ∈ V)
    (hVR : V ⊆ Metric.ball 0 c.R) (hzero : EqOn (graphDifference c) (fun _ => 0) V) :
    native_surface_germ_eq_v475 A.1.image B.1.image p := by
  have plane_cont : Continuous graphPlaneCoordinates := by
    unfold graphPlaneCoordinates
    fun_prop
  let O := c.coordinates.source ∩
    c.coordinates ⁻¹' (graphPlaneCoordinates ⁻¹' V)
  have hO : IsOpen O := c.coordinates.continuousOn.isOpen_inter_preimage
    c.coordinates.open_source (hV.preimage plane_cont)
  have hpO : p ∈ O := by
    refine ⟨c.base_mem, ?_⟩
    change graphPlaneCoordinates (c.coordinates p) ∈ V
    rw [c.base_zero]
    have hz : graphPlaneCoordinates (0 : E3) = (0 : E2) := by
      ext i
      fin_cases i <;> simp [graphPlaneCoordinates]
    rwa [hz]
  have graph_target (u : E2 → ℝ)
      (hu : ∀ x ∈ Metric.ball (0 : E2) c.R, |u x| < c.eta)
      {x : E2} (hx : x ∈ Metric.ball (0 : E2) c.R) :
      graphPoint x (u x) ∈ c.coordinates.target := by
    apply c.cylinder_inside
    have hp : graphPlaneCoordinates (graphPoint x (u x)) = x := by
      ext i
      fin_cases i <;> simp [graphPlaneCoordinates, graphPoint]
    have hh : graphPoint x (u x) 2 = u x := by simp [graphPoint]
    change ‖graphPlaneCoordinates (graphPoint x (u x))‖ < c.R ∧
      |(graphPoint x (u x)) 2| < c.eta
    rw [hp, hh]
    exact ⟨by simpa only [Metric.mem_ball, dist_zero_right] using hx, hu x hx⟩
  have hbase (u : E2 → ℝ)
      (hu : ∀ x ∈ Metric.ball (0 : E2) c.R, |u x| < c.eta)
      {x : E2} (hx : x ∈ Metric.ball (0 : E2) c.R)
      (hxo : c.coordinates.symm (graphPoint x (u x)) ∈ O) : x ∈ V := by
    change c.coordinates.symm (graphPoint x (u x)) ∈ c.coordinates.source ∧
      c.coordinates.symm (graphPoint x (u x)) ∈
        c.coordinates ⁻¹' (graphPlaneCoordinates ⁻¹' V) at hxo
    have ho := hxo.2
    change graphPlaneCoordinates (c.coordinates (c.coordinates.symm (graphPoint x (u x)))) ∈ V at ho
    rw [c.coordinates.right_inv (graph_target u hu hx)] at ho
    have hp : graphPlaneCoordinates (graphPoint x (u x)) = x := by
      ext i
      fin_cases i <;> simp [graphPlaneCoordinates, graphPoint]
    rwa [hp] at ho
  have hequal {x : E2} (hx : x ∈ V) : c.upper x = c.lower x :=
    sub_eq_zero.mp (hzero hx)
  refine ⟨O, hO, hpO, ?_⟩
  ext q
  constructor
  · rintro ⟨hqA, hqO⟩
    have hgraph : q ∈ A.1.image ∩ c.coordinates.source := ⟨hqA, hqO.1⟩
    rw [c.graph_A] at hgraph
    obtain ⟨x, hx, rfl⟩ := hgraph
    have hxV := hbase c.upper c.upper_inside hx hqO
    refine ⟨?_, hqO⟩
    have hBgraph : c.coordinates.symm (graphPoint x (c.upper x)) ∈
        B.1.image ∩ c.coordinates.source := by
      rw [c.graph_B, hequal hxV]
      exact ⟨x, hx, rfl⟩
    exact hBgraph.1
  · rintro ⟨hqB, hqO⟩
    have hgraph : q ∈ B.1.image ∩ c.coordinates.source := ⟨hqB, hqO.1⟩
    rw [c.graph_B] at hgraph
    obtain ⟨x, hx, rfl⟩ := hgraph
    have hxV := hbase c.lower c.lower_inside hx hqO
    refine ⟨?_, hqO⟩
    have hAgraph : c.coordinates.symm (graphPoint x (c.lower x)) ∈
        A.1.image ∩ c.coordinates.source := by
      rw [c.graph_A, ← hequal hxV]
      exact ⟨x, hx, rfl⟩
    exact hAgraph.1

/-- Every original common graph is nonzero on each neighborhood of its base;
this is derived from the original minima and graph distance, not an input. -/
theorem original_pair_interior_graph_no_zero_germ (D : OriginalPair g J)
    {p : E.Carrier} (c : InteriorGraph D.A D.B p) :
    ¬ native_planar_zero_germ_v475 (Metric.ball 0 c.R) (graphDifference c) 0 := by
  rintro ⟨V, hV, h0, hVR, hzero⟩
  have hpI := c.source_interior c.base_mem
  have graph_mem {A B : IncompressibleSpanningSurface.{0} E} {p : E.Carrier}
      (c : InteriorGraph A B p) : p ∈ A.1.image ∩ B.1.image := by
    have h0R : (0 : E2) ∈ Metric.ball 0 c.R := Metric.mem_ball_self c.R_pos
    have hpoint : graphPoint (0 : E2) 0 = (0 : E3) := by
      ext i
      fin_cases i <;> simp [graphPoint]
    have hmem (F : Set E.Carrier) (u : E2 → ℝ) (hu : u 0 = 0)
        (hg : F ∩ c.coordinates.source =
          (fun x : E2 => c.coordinates.symm (graphPoint x (u x))) '' Metric.ball 0 c.R) :
        p ∈ F := by
      have hh : p ∈ F ∩ c.coordinates.source := by
        rw [hg]
        refine ⟨0, h0R, ?_⟩
        change c.coordinates.symm (graphPoint 0 (u 0)) = p
        rw [hu, hpoint, ← c.base_zero, c.coordinates.left_inv c.base_mem]
      exact hh.1
    exact ⟨hmem A.1.image c.upper c.upper_zero c.graph_A,
      hmem B.1.image c.lower c.lower_zero c.graph_B⟩
  exact original_pair_no_interior_agreement_germ D hpI (graph_mem c).1 (graph_mem c).2
    (interior_graph_zero_germ_to_surface_germ c V hV h0 hVR hzero)

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3InteriorFiniteOrderV480 -/

noncomputable section
open Set Topology Function Filter MeasureTheory
open scoped Manifold ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.OriginalEndpoints.B1Tangency.WeakTransport
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- Interior finite order for the gradient in the actual normalized isothermal
coordinates. All positive normalization, chart, weak equation and similarity
objects are constructed from the original pair and the same graph. -/
theorem original_pair_graph_normalized_finite_order (D : OriginalPair g J)
    {p : E.Carrier} (c : InteriorGraph D.A D.B p) :
    ∃ N : InteriorNormalizationData_v475, ∃ F : NativeInteriorChart_v475,
    ∃ rho : ℝ, ∃ m : ℕ, ∃ delta c1 c2 : ℝ,
      N.u = graphDifference c ∧ N.O ⊆ Metric.ball 0 c.R ∧
      (0 : E2) ∈ F.chart.source ∧ F.chart.source ⊆ N.O ∧
      F.chart.target = disc rho ∧ F.chart (0 : E2) = 0 ∧
      (∀ x ∈ N.O, (1 / 2 : ℝ) ≤ N.h x) ∧
      ContDiffOn ℝ 1 (F.vhat N.v) (disc rho) ∧
      Nonempty (SimilarityFactorization rho (complexGradient (F.vhat N.v))) ∧
      0 < rho ∧ 1 ≤ m ∧ 0 < delta ∧ delta < rho ∧ 0 < c1 ∧ 0 < c2 ∧
      (∀ z ∈ Metric.ball (0 : ℂ) delta,
        c1 * ‖z‖ ^ m ≤ ‖complexGradient (F.vhat N.v) z‖ ∧
        ‖complexGradient (F.vhat N.v) z‖ ≤ c2 * ‖z‖ ^ m) := by
  classical
  obtain ⟨r, hr, hrR, hL, a, b, c0, hEll, heq⟩ :=
    original_pair_interior_graph_linear_equation D c
  let O := Metric.ball (0 : E2) r
  have h0O : (0 : E2) ∈ O := Metric.mem_ball_self hr
  have hOR : O ⊆ Metric.ball 0 c.R := Metric.ball_subset_ball hrR
  have hu : ContDiffOn ℝ ∞ (graphDifference c) O :=
    (c.upper_smooth.sub c.lower_smooth).mono hOR
  obtain ⟨V, hV, h0V, hVO, h, hhs, hhpos, hheq⟩ :=
    native_local_positive_classical_v475 O Metric.isOpen_ball 0 h0O a b c0 hEll
  have hEllV : SmoothEllipticOn a b c0 V := by
    obtain ⟨ha, hb, hc, hsym, ell, C, hell, hC, hbounds⟩ := hEll
    exact ⟨fun i j => (ha i j).mono hVO, hb.mono hVO, hc.mono hVO,
      fun x hx => hsym x (hVO hx), ell, C, hell, hC,
      fun x hx => hbounds x (hVO hx)⟩
  let N : InteriorNormalizationData_v475 := {
    O := V
    isOpen_O := hV
    a := a
    b := b
    c := c0
    u := graphDifference c
    h := h
    elliptic := hEllV
    smooth_u := hu.mono hVO
    smooth_h := hhs
    h_positive := fun x hx => lt_of_lt_of_le (by norm_num) (hhpos x hx)
    u_classical := fun x hx => heq x (hVO hx)
    h_classical := hheq }
  obtain ⟨F0, rho0, hrho0, h0F0, hF0V, hF0T, hBb0, hDensity0⟩ :=
    native_interior_normalized_chart_exists_v475 N 0 h0V
  obtain ⟨haN, hbN, hvN⟩ := native_interior_normalized_smooth_v475 N
  obtain ⟨F, rho, hrho, h0F, hFF0, hFT, hBb, hDensity, hFbase⟩ :=
    interior_centered_chart_with_base_v480 F0 0 h0F0 N.normalizedA N.normalizedB
      (hbN.continuousOn.mono hF0V) hDensity0
  have hFV : F.chart.source ⊆ N.O := hFF0.trans hF0V
  have hWeak := native_local_classical_linear_weak_v475 N.O N.isOpen_O N.normalizedA
    N.normalizedB (fun _ => 0) N.v haN hbN contDiffOn_const hvN
    (native_interior_normalized_classical_v475 N)
  obtain ⟨hvC1, hbcont, hweak⟩ := native_interior_density_weak_transport_v475 F N.O N.isOpen_O
    hFV N.normalizedA N.normalizedB N.v (fun i j => (haN i j).continuousOn)
    hbN.continuousOn (hvN.of_le (by simp)) hWeak hDensity
  haveI : IsFiniteMeasure (volume.restrict F.chart.target) := by
    rw [hFT]
    exact isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  obtain ⟨M, hM, hbound⟩ := hBb
  have hbLp : MemLp (F.bhat N.normalizedB) ⊤ (volume.restrict F.chart.target) :=
    MemLp.of_bound (hbcont.aestronglyMeasurable F.target_open.measurableSet) M
      ((ae_restrict_mem F.target_open.measurableSet).mono (fun z hz => hbound z hz))
  obtain ⟨hw, hveq, hright, hLp⟩ := C1_real_weak_to_vekua rho hrho (F.vhat N.v)
    (F.bhat N.normalizedB) (hFT ▸ hvC1) (hFT ▸ hweak)
    (hFT ▸ (show BoundedOn (F.bhat N.normalizedB) F.chart.target from ⟨M, hM, hbound⟩))
    (hFT ▸ hbLp)
  obtain ⟨S⟩ := weak_vekua_similarity rho hrho (complexGradient (F.vhat N.v))
    (vekuaA (F.bhat N.normalizedB)) (vekuaB (F.bhat N.normalizedB))
    hw hveq 3 (by norm_num) (hLp 3 (by norm_num)).1 (hLp 3 (by norm_num)).2
  have hFzero : F.chart.symm (0 : E2) = 0 := by
    simpa only [hFbase] using F.chart.left_inv h0F
  have hu0 : N.u 0 = 0 := by simp [N, graphDifference, c.lower_zero, c.upper_zero]
  have hdu0 : fderiv ℝ N.u 0 = 0 := by
    have hud := (c.upper_smooth.contDiffAt (Metric.isOpen_ball.mem_nhds
      (Metric.mem_ball_self c.R_pos))).differentiableAt (by simp)
    have hld := (c.lower_smooth.contDiffAt (Metric.isOpen_ball.mem_nhds
      (Metric.mem_ball_self c.R_pos))).differentiableAt (by simp)
    change fderiv ℝ (fun x => c.upper x - c.lower x) 0 = 0
    rw [fderiv_fun_sub hud hld, c.upper_tangent, c.lower_tangent, sub_self]
  have hNv0 : N.v 0 = 0 := by simp [InteriorNormalizationData_v475.v, hu0]
  have hdNv : fderiv ℝ N.v 0 = 0 := by
    have hud := (N.smooth_u.contDiffAt (N.isOpen_O.mem_nhds h0V)).differentiableAt (by simp)
    have hhd := (N.smooth_h.contDiffAt (N.isOpen_O.mem_nhds h0V)).differentiableAt (by simp)
    change fderiv ℝ (fun x => N.u x / N.h x) 0 = 0
    simp only [div_eq_mul_inv]
    simpa only [Pi.inv_apply, hdu0, hu0, zero_smul, smul_zero, add_zero] using
      fderiv_fun_mul hud (hhd.inv (N.h_positive 0 h0V).ne')
  have h0T : (0 : E2) ∈ F.chart.target := hFbase ▸ F.chart.map_source h0F
  have hvhat0 : F.vhat N.v 0 = 0 := by simp [NativeInteriorChart_v475.vhat, hFzero, hNv0]
  have hdvhat0 : fderiv ℝ (F.vhat N.v) 0 = 0 := by
    have hvd := (hvN.contDiffAt (N.isOpen_O.mem_nhds h0V)).differentiableAt (by simp)
    have hFd := (F.inverse_C1.contDiffAt (F.target_open.mem_nhds h0T)).differentiableAt (by simp)
    change fderiv ℝ (N.v ∘ F.chart.symm) 0 = 0
    rw [fderiv_comp 0 (hFzero.symm ▸ hvd) hFd, hFzero, hdNv, ContinuousLinearMap.zero_comp]
  have hw0 : complexGradient (F.vhat N.v) 0 = 0 := by
    have hz : complexPoint (0 : ℂ) = (0 : E2) := by
      ext i
      fin_cases i <;> simp [complexPoint]
    simp [complexGradient, hz, planarGradient, hdvhat0]
  obtain hzero | ⟨m, hm, delta, c1, c2, hd, hdr, hc1, hc2, hbounds⟩ :=
    similarity_finite_integer_order rho hrho (complexGradient (F.vhat N.v)) S hw0
  · let e : ℂ ≃ₗᵢ[ℝ] E2 := Complex.orthonormalBasisOneI.repr
    have he (z : ℂ) : e z = complexPoint z := rfl
    have hball (z : ℂ) : complexPoint z ∈ disc rho ↔ z ∈ Metric.ball (0 : ℂ) rho := by
      change e z ∈ Metric.ball 0 rho ↔ _
      simpa only [Metric.mem_ball, dist_zero_right, map_zero] using
        (show ‖e z‖ < rho ↔ ‖z‖ < rho by rw [e.norm_map])
    have hdAll (x : E2) (hx : x ∈ disc rho) : fderiv ℝ (F.vhat N.v) x = 0 := by
      let z := e.symm x
      have hzpoint : complexPoint z = x := by change e (e.symm x) = x; exact e.apply_symm_apply x
      have hwz := hzero z ((hball z).mp (hzpoint ▸ hx))
      have hgrad : planarGradient (F.vhat N.v) x = 0 := by
        have hr := congrArg Complex.re hwz
        have hi := congrArg Complex.im hwz
        ext i
        fin_cases i
        · simpa [complexGradient, hzpoint] using hr
        · simpa [complexGradient, hzpoint] using hi
      ext v
      have hv : v = ∑ i : Fin 2, v i • coordinateVector 2 i := by
        ext i
        fin_cases i <;> simp [Fin.sum_univ_two, coordinateVector, PiLp.single_apply]
      rw [hv, map_sum]
      apply Finset.sum_eq_zero
      intro i _
      have hcoord : planarGradient (F.vhat N.v) x i =
          fderiv ℝ (F.vhat N.v) x (coordinateVector 2 i) := by
        fin_cases i <;> simp [planarGradient, coordinateVector, Fin.sum_univ_two]
      rw [map_smul, ← hcoord, hgrad]
      simp
    have hvAll : EqOn (F.vhat N.v) (fun _ => 0) (disc rho) := by
      intro x hx
      have hh := (convex_ball (0 : E2) rho).is_const_of_fderivWithin_eq_zero
        ((hFT ▸ hvC1).differentiableOn (by norm_num))
        (fun y hy => (fderivWithin_of_isOpen Metric.isOpen_ball hy).trans (hdAll y hy))
        hx (Metric.mem_ball_self hrho)
      exact hh.trans hvhat0
    have hUZ : EqOn N.u (fun _ => 0) F.chart.source := by
      intro x hx
      have hz := hvAll (hFT ▸ F.chart.map_source hx)
      change N.u (F.chart.symm (F.chart x)) / N.h (F.chart.symm (F.chart x)) = 0 at hz
      rw [F.chart.left_inv hx] at hz
      exact (div_eq_zero_iff).mp hz |>.resolve_right (N.h_positive x (hFV hx)).ne'
    exact False.elim (original_pair_interior_graph_no_zero_germ D c
      ⟨F.chart.source, F.source_open, h0F, hFV.trans (hVO.trans hOR), hUZ⟩)
  · exact ⟨N, F, rho, m, delta, c1, c2, rfl, hVO.trans hOR, h0F, hFV, hFT,
      hFbase, hhpos, hFT ▸ hvC1, ⟨S⟩, hrho, hm, hd, hdr, hc1, hc2, hbounds⟩

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3InteriorFiniteOrderTransportV480 -/
noncomputable section
open Set Topology Function Filter MeasureTheory
open scoped Manifold ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
set_option maxHeartbeats 200000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
private theorem planarGradient_norm_v480 (u : E2 → ℝ) (x : E2) :
    ‖planarGradient u x‖ = ‖fderiv ℝ u x‖ := by
  have heq : innerSL ℝ (planarGradient u x) = fderiv ℝ u x := by
    apply ContinuousLinearMap.ext
    intro y
    have hy : y = ∑ i : Fin 2, y i • coordinateVector 2 i := by
      ext i
      fin_cases i <;> simp [Fin.sum_univ_two, coordinateVector]
    rw [hy]
    simp only [map_sum, map_smul]
    congr 1
    funext i
    congr 1
    simp [innerSL_apply_apply, EuclideanSpace.inner_eq_star_dotProduct,
      planarGradient, coordinateVector, dotProduct, Fin.sum_univ_two]
    fin_cases i <;> simp
  rw [← heq, innerSL_apply_norm]

private theorem complexGradient_norm_v480 (u : E2 → ℝ) (z : ℂ) :
    ‖complexGradient u z‖ = ‖fderiv ℝ u (complexPoint z)‖ := by
  rw [← planarGradient_norm_v480]
  rw [Complex.norm_def, EuclideanSpace.norm_eq]
  congr 1
  simp [complexGradient, Complex.normSq_apply, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs, pow_two]

private theorem complexPoint_norm_v480 (z : ℂ) : ‖complexPoint z‖ = ‖z‖ := by
  rw [Complex.norm_def, EuclideanSpace.norm_eq]
  simp [complexPoint, Complex.normSq_apply, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs, pow_two]

private theorem derivative_bound_compact_v480
    {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E2 → G} {U H : Set E2} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) (hH : IsCompact H) (hHU : H ⊆ U) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ H, ‖fderiv ℝ f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hH.exists_bound_of_continuousOn
    ((hf.continuousOn_fderiv_of_isOpen hU le_rfl).mono hHU)
  exact ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    fun x hx => (hC x hx).trans (le_max_left _ _)⟩

private theorem scalar_bound_of_complex_gradient_v480
    (f : E2 → ℝ) (rho d C : ℝ) (m : ℕ) (hd : 0 < d) (hdR : d < rho)
    (hC : 0 < C) (hf : ContDiffOn ℝ 1 f (disc rho)) (hf0 : f 0 = 0)
    (hb : ∀ z ∈ Metric.ball (0 : ℂ) d, ‖complexGradient f z‖ ≤ C * ‖z‖ ^ m) :
    ∀ z ∈ disc d, |f z| ≤ C * ‖z‖ ^ (m + 1) := by
  have hdiff : ∀ z ∈ disc rho, DifferentiableAt ℝ f z := by
    intro z hz
    exact (hf.contDiffAt (Metric.isOpen_ball.mem_nhds hz)).differentiableAt (by norm_num)
  have hbound : ∀ x ∈ disc d, ‖fderiv ℝ f x‖ ≤ C * ‖x‖ ^ m := by
    intro x hx
    let z : ℂ := ⟨x 0, x 1⟩
    have hp : complexPoint z = x := by ext i; fin_cases i <;> simp [complexPoint, z]
    have hn : ‖z‖ = ‖x‖ := by simpa only [hp] using (complexPoint_norm_v480 z).symm
    have h := hb z (by simpa only [disc, Metric.mem_ball, dist_zero_right, hn] using hx)
    simpa only [complexGradient_norm_v480, hp, hn] using h
  intro z hz
  have hsub : Metric.closedBall (0 : E2) ‖z‖ ⊆ disc d := by
    intro x hx
    exact (Metric.mem_closedBall.mp hx).trans_lt
      (by simpa only [disc, Metric.mem_ball, dist_zero_right] using hz)
  have hnorm := (convex_closedBall (0 : E2) ‖z‖).norm_image_sub_le_of_norm_fderiv_le
    (fun x hx => hdiff x (Metric.ball_subset_ball hdR.le (hsub hx)))
    (fun x hx => (hbound x (hsub hx)).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (by simpa using hx) m) hC.le))
    (Metric.mem_closedBall_self (norm_nonneg z))
    (by simp : z ∈ Metric.closedBall (0 : E2) ‖z‖)
  simpa only [hf0, sub_zero, Real.norm_eq_abs, pow_succ, mul_assoc] using hnorm

/-- Transfer the internally constructed integer order back to the original
upper-minus-lower graph, retaining the lower-order normalization error. -/
theorem graph_finite_order_transport_v480
    (N : InteriorNormalizationData_v475) (F : NativeInteriorChart_v475)
    (rho : ℝ) (hrho : 0 < rho) (h0S : (0 : E2) ∈ F.chart.source)
    (hSN : F.chart.source ⊆ N.O) (hT : F.chart.target = disc rho)
    (hF0 : F.chart (0 : E2) = 0) (hN0 : N.u 0 = 0)
    (hLower : ∀ x ∈ N.O, (1 / 2 : ℝ) ≤ N.h x)
    (hf : ContDiffOn ℝ 1 (F.vhat N.v) (disc rho))
    (m : ℕ) (d l u : ℝ) (hd : 0 < d) (hdR : d < rho)
    (hl : 0 < l) (hu : 0 < u)
    (hbound : ∀ z ∈ Metric.ball (0 : ℂ) d,
      l * ‖z‖ ^ m ≤ ‖complexGradient (F.vhat N.v) z‖ ∧
      ‖complexGradient (F.vhat N.v) z‖ ≤ u * ‖z‖ ^ m) :
    ∃ R a b C : ℝ, 0 < R ∧ 0 < a ∧ 0 < b ∧ 0 < C ∧
      Metric.closedBall (0 : E2) R ⊆ F.chart.source ∧
      ∀ x ∈ Metric.closedBall (0 : E2) R, x ≠ 0 →
        a * ‖x‖ ^ m - b * ‖x‖ ^ (m + 1) ≤ ‖fderiv ℝ N.u x‖ ∧
        0 < a * ‖x‖ ^ m - b * ‖x‖ ^ (m + 1) ∧
        |N.u x| ≤ C * ‖x‖ ^ (m + 1) := by
  classical
  have hI0 : F.chart.symm (0 : E2) = 0 := by
    simpa only [hF0] using F.chart.left_inv h0S
  have hKT : Metric.closedBall (0 : E2) (d / 2) ⊆ F.chart.target := by
    rw [hT]
    intro x hx
    exact (Metric.mem_closedBall.mp hx).trans_lt ((half_lt_self hd).trans hdR)
  obtain ⟨I, hI, hIbound⟩ := derivative_bound_compact_v480 F.target_open F.inverse_C1
    (isCompact_closedBall 0 (d / 2)) hKT
  let S : Set E2 := F.chart.source ∩ F.chart ⁻¹' Metric.ball (0 : E2) (d / 2)
  have hS : IsOpen S := F.chart.continuousOn.isOpen_inter_preimage
    F.source_open Metric.isOpen_ball
  have h0ball : F.chart (0 : E2) ∈ Metric.ball (0 : E2) (d / 2) :=
    hF0.symm ▸ Metric.mem_ball_self (half_pos hd)
  have h0 : (0 : E2) ∈ S := ⟨h0S, h0ball⟩
  obtain ⟨s, hs, hballS⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hS.mem_nhds h0)
  have hballF : Metric.closedBall (0 : E2) s ⊆ F.chart.source :=
    hballS.trans inter_subset_left
  obtain ⟨hi, hhi, hFderiv⟩ := derivative_bound_compact_v480 F.source_open F.forward_C1
    (isCompact_closedBall 0 s) hballF
  obtain ⟨Dh, hDh, hDhbound⟩ := derivative_bound_compact_v480 N.isOpen_O
    (N.smooth_h.of_le (by simp)) (isCompact_closedBall 0 s) (hballF.trans hSN)
  obtain ⟨H0, hH0⟩ := (isCompact_closedBall (0 : E2) s).exists_bound_of_continuousOn
    (N.smooth_h.continuousOn.mono (hballF.trans hSN))
  let H := max H0 1
  have hH : 0 < H := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hHbound : ∀ x ∈ Metric.closedBall (0 : E2) s, |N.h x| ≤ H :=
    fun x hx => (hH0 x hx).trans (le_max_left _ _)
  let lo := I⁻¹
  have hlo : 0 < lo := inv_pos.mpr hI
  have hnormbounds : ∀ x ∈ Metric.closedBall (0 : E2) s,
      lo * ‖x‖ ≤ ‖F.chart x‖ ∧ ‖F.chart x‖ ≤ hi * ‖x‖ := by
    intro x hx
    have hz : F.chart x ∈ Metric.closedBall (0 : E2) (d / 2) :=
      Metric.ball_subset_closedBall (hballS hx).2
    have hleft := (convex_closedBall (0 : E2) (d / 2)).norm_image_sub_le_of_norm_fderiv_le
      (fun z hz => (F.inverse_C1.contDiffAt (F.target_open.mem_nhds (hKT hz))).differentiableAt (by norm_num))
      hIbound (Metric.mem_closedBall_self (half_pos hd).le) hz
    have hright := (convex_closedBall (0 : E2) s).norm_image_sub_le_of_norm_fderiv_le
      (fun y hy => (F.forward_C1.contDiffAt (F.source_open.mem_nhds (hballF hy))).differentiableAt (by norm_num))
      hFderiv (Metric.mem_closedBall_self hs.le) hx
    simp only [hI0, F.chart.left_inv (hballF hx), sub_zero] at hleft
    simp only [hF0, sub_zero] at hright
    refine ⟨?_, hright⟩
    change I⁻¹ * ‖x‖ ≤ ‖F.chart x‖
    exact (inv_mul_le_iff₀ hI).mpr hleft
  have hf0 : F.vhat N.v 0 = 0 := by
    simp [NativeInteriorChart_v475.vhat, InteriorNormalizationData_v475.v, hI0, hN0]
  let V := u * hi ^ (m + 1)
  have hV : 0 < V := mul_pos hu (pow_pos hhi _)
  let a := l * lo ^ m / (2 * I)
  have ha : 0 < a := div_pos (mul_pos hl (pow_pos hlo _)) (mul_pos (by norm_num) hI)
  let b := V * Dh
  have hb : 0 < b := mul_pos hV hDh
  have hpre : ∀ x ∈ Metric.closedBall (0 : E2) s,
      a * ‖x‖ ^ m - b * ‖x‖ ^ (m + 1) ≤ ‖fderiv ℝ N.u x‖ ∧
      |N.u x| ≤ H * V * ‖x‖ ^ (m + 1) := by
    intro x hx
    have hxF := hballF hx
    have hxN := hSN hxF
    have hxh : 0 < N.h x := N.h_positive x hxN
    have hvd := (native_interior_normalized_smooth_v475 N).2.2.contDiffAt
      (N.isOpen_O.mem_nhds hxN) |>.differentiableAt (by simp)
    have hhd := N.smooth_h.contDiffAt (N.isOpen_O.mem_nhds hxN) |>.differentiableAt (by simp)
    let z := F.chart x
    have hzF : z ∈ F.chart.target := F.chart.map_source hxF
    have hzx : F.chart.symm z = x := F.chart.left_inv hxF
    have hzsmall : z ∈ disc d := Metric.ball_subset_ball (half_lt_self hd).le (hballS hx).2
    have hn := hnormbounds x hx
    have hvbound : |N.v x| ≤ V * ‖x‖ ^ (m + 1) := by
      have hh := scalar_bound_of_complex_gradient_v480 (F.vhat N.v) rho d u m hd hdR hu
        hf hf0 (fun z hz => (hbound z hz).2) z hzsmall
      change |N.v (F.chart.symm z)| ≤ _ at hh
      rw [hzx] at hh
      apply hh.trans
      calc
        u * ‖z‖ ^ (m + 1) ≤ u * (hi * ‖x‖) ^ (m + 1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hn.2 _) hu.le
        _ = V * ‖x‖ ^ (m + 1) := by simp only [V, mul_pow, mul_assoc]
    have hlowref : l * (lo * ‖x‖) ^ m ≤ ‖fderiv ℝ (F.vhat N.v) z‖ := by
      let q : ℂ := ⟨z 0, z 1⟩
      have hqp : complexPoint q = z := by ext i; fin_cases i <;> simp [complexPoint, q]
      have hqn : ‖q‖ = ‖z‖ := by simpa only [hqp] using (complexPoint_norm_v480 q).symm
      have hh := (hbound q (by simpa only [disc, Metric.mem_ball, dist_zero_right, hqn] using hzsmall)).1
      have hh' : l * ‖z‖ ^ m ≤ ‖fderiv ℝ (F.vhat N.v) z‖ := by
        simpa only [complexGradient_norm_v480, hqp, hqn] using hh
      exact (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (mul_nonneg hlo.le (norm_nonneg _)) hn.1 m) hl.le).trans hh'
    have hId := F.inverse_C1.contDiffAt (F.target_open.mem_nhds hzF) |>.differentiableAt (by simp)
    have hchain : fderiv ℝ (F.vhat N.v) z =
        (fderiv ℝ N.v x).comp (fderiv ℝ F.chart.symm z) := by
      change fderiv ℝ (N.v ∘ F.chart.symm) z = _
      rw [fderiv_comp z (hzx.symm ▸ hvd) hId, hzx]
    have hrefupper : ‖fderiv ℝ (F.vhat N.v) z‖ ≤ ‖fderiv ℝ N.v x‖ * I := by
      rw [hchain]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left
          (hIbound z (Metric.ball_subset_closedBall (hballS hx).2)) (norm_nonneg _))
    have hlownv : a * ‖x‖ ^ m ≤ N.h x * ‖fderiv ℝ N.v x‖ := by
      have hh := hlowref.trans hrefupper
      rw [mul_pow] at hh
      have haeq : a * (2 * I) = l * lo ^ m := div_mul_cancel₀ _ (mul_pos (by norm_num) hI).ne'
      have heq := congrArg (fun t : ℝ => t * ‖x‖ ^ m) haeq
      have hnorm := norm_nonneg (fderiv ℝ N.v x)
      have hhalf : (1 / 2 : ℝ) * ‖fderiv ℝ N.v x‖ ≤ N.h x * ‖fderiv ℝ N.v x‖ :=
        mul_le_mul_of_nonneg_right (hLower x hxN) hnorm
      have hdivide : a * ‖x‖ ^ m ≤ (1 / 2 : ℝ) * ‖fderiv ℝ N.v x‖ := by
        have hdiv : (l * lo ^ m * ‖x‖ ^ m) / I ≤ ‖fderiv ℝ N.v x‖ := by
          apply (div_le_iff₀ hI).mpr
          simpa only [mul_assoc] using hh
        calc
          a * ‖x‖ ^ m = ((l * lo ^ m * ‖x‖ ^ m) / I) / 2 := by dsimp [a]; ring
          _ ≤ ‖fderiv ℝ N.v x‖ / 2 := div_le_div_of_nonneg_right hdiv (by norm_num)
          _ = (1 / 2 : ℝ) * ‖fderiv ℝ N.v x‖ := by ring
      exact hdivide.trans hhalf
    have hprod : (fun y => N.h y * N.v y) =ᶠ[𝓝 x] N.u := by
      filter_upwards [N.isOpen_O.mem_nhds hxN] with y hy
      dsimp [InteriorNormalizationData_v475.v]
      exact mul_div_cancel₀ _ (N.h_positive y hy).ne'
    have hderprod := hprod.fderiv_eq (𝕜 := ℝ)
    rw [fderiv_fun_mul hhd hvd] at hderprod
    have hnormlower : N.h x * ‖fderiv ℝ N.v x‖ - |N.v x| * ‖fderiv ℝ N.h x‖ ≤
        ‖fderiv ℝ N.u x‖ := by
      have hh := norm_sub_norm_le (N.h x • fderiv ℝ N.v x) (-N.v x • fderiv ℝ N.h x)
      simpa only [neg_smul, sub_neg_eq_add, norm_neg, norm_smul, Real.norm_eq_abs, abs_neg,
        abs_of_pos hxh, hderprod] using hh
    have herr : |N.v x| * ‖fderiv ℝ N.h x‖ ≤ b * ‖x‖ ^ (m + 1) := by
      calc
        _ ≤ (V * ‖x‖ ^ (m + 1)) * Dh :=
          mul_le_mul hvbound (hDhbound x hx) (norm_nonneg _) (by positivity)
        _ = b * ‖x‖ ^ (m + 1) := by dsimp [b]; ring
    constructor
    · linarith only [hlownv, hnormlower, herr]
    · rw [← hprod.eq_of_nhds, abs_mul]
      calc
        _ ≤ H * (V * ‖x‖ ^ (m + 1)) :=
          mul_le_mul (hHbound x hx) hvbound (abs_nonneg _) hH.le
        _ = H * V * ‖x‖ ^ (m + 1) := by ring
  let R := min s (a / (2 * b))
  have hR : 0 < R := lt_min hs (div_pos ha (mul_pos (by norm_num) hb))
  have hRs : R ≤ s := min_le_left _ _
  refine ⟨R, a, b, H * V, hR, ha, hb, mul_pos hH hV,
    (Metric.closedBall_subset_closedBall hRs).trans hballF, ?_⟩
  intro x hx hne
  obtain ⟨hgrad, hval⟩ := hpre x (Metric.closedBall_subset_closedBall hRs hx)
  refine ⟨hgrad, ?_, hval⟩
  have hxnorm : ‖x‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  have hnormpos := norm_pos_iff.mpr hne
  have hsmall : b * ‖x‖ < a := by
    have hh := (le_div_iff₀ (mul_pos (by norm_num) hb)).mp (hxnorm.trans (min_le_right _ _))
    nlinarith only [hh, ha]
  rw [pow_succ]
  have hpos := mul_pos (sub_pos.mpr hsmall) (pow_pos hnormpos m)
  convert hpos using 1 <;> ring


variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}

/-- The original graph difference itself has the exact integer derivative
estimate and isolated critical zero required by B3. -/
theorem original_pair_graph_integer_derivative_estimate (D : OriginalPair g J)
    {p : E.Carrier} (c : InteriorGraph D.A D.B p) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ c1 c2 R : ℝ,
      0 < c1 ∧ 0 < c2 ∧ 0 < R ∧ R ≤ c.R ∧
      (∀ x : E2, 0 < ‖x‖ → ‖x‖ < R →
        c1 * ‖x‖ ^ m - c2 * ‖x‖ ^ (m + 1) ≤ ‖fderiv ℝ (graphDifference c) x‖ ∧
        0 < c1 * ‖x‖ ^ m - c2 * ‖x‖ ^ (m + 1)) ∧
      (∀ x ∈ Metric.ball (0 : E2) R,
        fderiv ℝ (graphDifference c) x = 0 ↔ x = 0) := by
  obtain ⟨N, F, rho, m, d, l, u, hNu, hNOR, h0S, hSN, hT, hF0, hLower, hf,
    hS, hrho, hm, hd, hdR, hl, hu, hbound⟩ := original_pair_graph_normalized_finite_order D c
  have hN0 : N.u 0 = 0 := by rw [hNu]; simp [graphDifference, c.lower_zero, c.upper_zero]
  obtain ⟨R0, a, b, C, hR0, ha, hb, hC, hRS, hestimate⟩ :=
    graph_finite_order_transport_v480 N F rho hrho h0S hSN hT hF0 hN0 hLower hf
      m d l u hd hdR hl hu hbound
  let R := min R0 (c.R / 2)
  have hR : 0 < R := lt_min hR0 (half_pos c.R_pos)
  have hRR0 : R ≤ R0 := min_le_left _ _
  have hRR : R ≤ c.R := (min_le_right _ _).trans (half_lt_self c.R_pos).le
  have hgrad0 : fderiv ℝ (graphDifference c) 0 = 0 := by
    have hU := (c.upper_smooth.contDiffAt (Metric.isOpen_ball.mem_nhds
      (Metric.mem_ball_self c.R_pos))).differentiableAt (by simp)
    have hL := (c.lower_smooth.contDiffAt (Metric.isOpen_ball.mem_nhds
      (Metric.mem_ball_self c.R_pos))).differentiableAt (by simp)
    unfold graphDifference
    rw [fderiv_fun_sub hU hL, c.upper_tangent, c.lower_tangent, sub_self]
  have hpoints : ∀ x : E2, 0 < ‖x‖ → ‖x‖ < R →
      a * ‖x‖ ^ m - b * ‖x‖ ^ (m + 1) ≤ ‖fderiv ℝ (graphDifference c) x‖ ∧
      0 < a * ‖x‖ ^ m - b * ‖x‖ ^ (m + 1) := by
    intro x hx0 hxR
    have hxR0 : x ∈ Metric.closedBall (0 : E2) R0 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hxR.le.trans hRR0
    obtain ⟨hgrad, hpos, hval⟩ := hestimate x hxR0 (norm_pos_iff.mp hx0)
    rw [hNu] at hgrad
    exact ⟨hgrad, hpos⟩
  refine ⟨m, hm, a, b, R, ha, hb, hR, hRR, hpoints, ?_⟩
  intro x hx
  constructor
  · intro hdzero
    by_contra hne
    obtain ⟨hgrad, hpos⟩ := hpoints x (norm_pos_iff.mpr hne)
      (by simpa only [Metric.mem_ball, dist_zero_right] using hx)
    rw [hdzero, norm_zero] at hgrad
    exact (not_lt_of_ge hgrad) hpos
  · rintro rfl
    exact hgrad0

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3InteriorSignsV480 -/

noncomputable section
open Set Topology Function Filter MeasureTheory
open scoped Manifold ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

private theorem complexPoint_zero_v480 : complexPoint (0 : ℂ) = (0 : E2) := by
  ext i
  fin_cases i <;> simp [complexPoint]

private theorem complexPoint_real_mul_v480 (t : ℝ) (q : ℂ) :
    complexPoint ((t : ℂ) * q) = t • complexPoint q := by
  ext i
  fin_cases i <;> simp [complexPoint, Complex.mul_re, Complex.mul_im]

private theorem complex_gradient_direction_v480 (f : E2 → ℝ) (z q : ℂ) :
    fderiv ℝ f (complexPoint z) (complexPoint q) = (complexGradient f z * q).re := by
  have hq : complexPoint q = q.re • coordinateVector 2 0 + q.im • coordinateVector 2 1 := by
    ext i
    fin_cases i <;> simp [complexPoint, coordinateVector, PiLp.single_apply]
  rw [hq, map_add, map_smul, map_smul]
  simp [complexGradient, planarGradient, Complex.mul_re, coordinateVector,
    Fin.sum_univ_two, PiLp.single_apply]
  ring

/-- A continuous nonzero leading complex-gradient coefficient supplies both
signs along two actual straight rays through the origin. -/
theorem scalar_signs_of_gradient_factor_v480
    (R : ℝ) (hR : 0 < R) (f : E2 → ℝ)
    (hf : ContDiffOn ℝ 1 f (disc R)) (hf0 : f 0 = 0)
    (m : ℕ) (k : ℂ → ℂ) (hk : ContinuousAt k 0) (hk0 : k 0 ≠ 0)
    (hw : complexGradient f =ᶠ[𝓝 (0 : ℂ)] fun z => z ^ m * k z) :
    ∀ V : Set E2, V ∈ 𝓝 (0 : E2) →
      (∃ x ∈ V ∩ disc R, 0 < f x) ∧ (∃ x ∈ V ∩ disc R, f x < 0) := by
  have hray (sign : ℝ) (hsg : sign = 1 ∨ sign = -1) (V : Set E2) (hV : V ∈ 𝓝 (0 : E2)) :
      ∃ x ∈ V ∩ disc R, 0 < sign * f x := by
    obtain ⟨q, hqpow⟩ := IsAlgClosed.exists_pow_nat_eq ((sign : ℂ) / k 0) (Nat.succ_pos m)
    have hkq : k 0 * q ^ (m + 1) = (sign : ℂ) := by
      rw [hqpow, mul_div_cancel₀ _ hk0]
    let γ : ℝ → E2 := fun t => t • complexPoint q
    let ζ : ℝ → ℂ := fun t => (t : ℂ) * q
    have hγ : Continuous γ := continuous_id.smul continuous_const
    have hζ : Continuous ζ := Complex.continuous_ofReal.mul_const q
    have hγ0 : γ 0 = 0 := by simp [γ]
    have hζ0 : ζ 0 = 0 := by simp [ζ]
    have hζat : Tendsto ζ (𝓝 (0 : ℝ)) (𝓝 (0 : ℂ)) := by
      simpa only [hζ0] using (hζ.continuousAt (x := (0 : ℝ))).tendsto
    have hγat : Tendsto γ (𝓝 (0 : ℝ)) (𝓝 (0 : E2)) := by
      simpa only [hγ0] using (hγ.continuousAt (x := (0 : ℝ))).tendsto
    have hkζ : ContinuousAt (fun t => k (ζ t)) (0 : ℝ) := by
      simpa only [ContinuousAt, hζ0, Function.comp_def] using hk.tendsto.comp hζat
    let A : ℝ → ℝ := fun t => sign * (k (ζ t) * q ^ (m + 1)).re
    have hA : ContinuousAt A 0 := continuousAt_const.mul
      (Complex.continuous_re.continuousAt.comp (hkζ.mul_const _))
    have hA0 : A 0 = 1 := by
      dsimp [A]
      rw [hζ0, hkq]
      rcases hsg with rfl | rfl <;> norm_num
    have hpos : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < A t :=
      hA.tendsto.eventually_const_lt (by rw [hA0]; norm_num)
    have hfactor : ∀ᶠ t in 𝓝 (0 : ℝ),
        complexGradient f (ζ t) = ζ t ^ m * k (ζ t) :=
      hζat.eventually hw
    have hinside : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ V ∩ disc R := by
      have hn : V ∩ disc R ∈ 𝓝 (0 : E2) :=
        inter_mem hV (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hR))
      exact hγat.eventually hn
    obtain ⟨e, he, hnear⟩ := Metric.eventually_nhds_iff.mp (hpos.and (hfactor.and hinside))
    let a := e / 2
    have ha : 0 < a := half_pos he
    have hae : a < e := half_lt_self he
    have hinterval : ∀ t ∈ Icc (0 : ℝ) a, γ t ∈ disc R := by
      intro t ht
      exact (hnear (by simpa only [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg ht.1]
        using ht.2.trans_lt hae)).2.2.2
    have hcont : ContinuousOn (fun t => sign * f (γ t)) (Icc (0 : ℝ) a) :=
      continuousOn_const.mul (hf.continuousOn.comp hγ.continuousOn hinterval)
    have hderiv : ∀ t ∈ interior (Icc (0 : ℝ) a),
        0 < deriv (fun t => sign * f (γ t)) t := by
      intro t ht
      rw [interior_Icc] at ht
      have hdist : dist t (0 : ℝ) < e := by
        simpa only [dist_zero_right, Real.norm_eq_abs, abs_of_pos ht.1] using (ht.2.trans hae)
      have hnearT := hnear hdist
      have hfd := (hf.contDiffAt (Metric.isOpen_ball.mem_nhds (hinterval t ⟨ht.1.le, ht.2.le⟩))).differentiableAt (by simp)
      have hγd : HasDerivAt γ (complexPoint q) t := by
        simpa only [γ, id_eq, one_smul] using (hasDerivAt_id t).smul_const (complexPoint q)
      have hfdγ := (hfd.hasFDerivAt.comp_hasDerivAt t hγd).const_mul sign
      change HasDerivAt (fun t => sign * f (γ t)) _ t at hfdγ
      have heval : fderiv ℝ f (γ t) (complexPoint q) = (complexGradient f (ζ t) * q).re := by
        simpa only [ζ, complexPoint_real_mul_v480] using complex_gradient_direction_v480 f ((t : ℂ) * q) q
      rw [hfdγ.deriv, heval, hnearT.2.1]
      have heq : sign * ((ζ t ^ m * k (ζ t)) * q).re = t ^ m * A t := by
        have heqC : (ζ t ^ m * k (ζ t)) * q =
            ((t ^ m : ℝ) : ℂ) * (k (ζ t) * q ^ (m + 1)) := by
          dsimp only [ζ]
          rw [mul_pow, Complex.ofReal_pow, pow_succ]
          ring
        rw [heqC]
        dsimp only [A]
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        ring
      rw [heq]
      exact mul_pos (pow_pos ht.1 m) hnearT.1
    have hmono := strictMonoOn_of_deriv_pos (convex_Icc 0 a) hcont hderiv
    have hv := hmono (left_mem_Icc.mpr ha.le) (right_mem_Icc.mpr ha.le) ha
    have hmem := (hnear (y := a) (by simpa only [dist_zero_right, Real.norm_eq_abs, abs_of_pos ha] using hae)).2.2
    refine ⟨γ a, hmem, ?_⟩
    simpa only [hγ0, hf0, mul_zero] using hv
  intro V hV
  obtain ⟨x, hx, hxp⟩ := hray 1 (Or.inl rfl) V hV
  obtain ⟨y, hy, hyn⟩ := hray (-1) (Or.inr rfl) V hV
  exact ⟨⟨x, hx, by simpa using hxp⟩, ⟨y, hy, by linarith⟩⟩


/-- The nonzero holomorphic similarity branch gives the actual leading
gradient factor, and hence both signs. -/
theorem scalar_signs_of_similarity_nonzero_v480
    (R : ℝ) (hR : 0 < R) (f : E2 → ℝ)
    (hf : ContDiffOn ℝ 1 f (disc R)) (hf0 : f 0 = 0)
    (S : SimilarityFactorization R (complexGradient f))
    (hnotzero : ∃ z ∈ Metric.ball (0 : ℂ) R, complexGradient f z ≠ 0) :
    ∀ V : Set E2, V ∈ 𝓝 (0 : E2) →
      (∃ x ∈ V ∩ disc R, 0 < f x) ∧ (∃ x ∈ V ∩ disc R, f x < 0) := by
  classical
  have hzR : (0 : ℂ) ∈ Metric.ball 0 R := Metric.mem_ball_self hR
  have han := S.holomorphic.analyticOnNhd Metric.isOpen_ball
  have hzero : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), S.Phi z = 0 := by
    intro hz
    have hglob := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball (0 : ℂ) R).isPreconnected hzR hz
    obtain ⟨z, hz, hn⟩ := hnotzero
    apply hn
    rw [S.same_w z hz, hglob hz, Pi.zero_apply, zero_mul]
  obtain ⟨m, q, hq, hq0, hfactor⟩ :=
    (han 0 hzR).exists_eventuallyEq_pow_smul_nonzero_iff.mpr hzero
  obtain ⟨L, hholder⟩ := S.omega_holder
  have homega : ContinuousAt S.omega 0 :=
    (hholder.continuousOn S.alpha_pos).continuousAt (Metric.isOpen_ball.mem_nhds hzR)
  let k : ℂ → ℂ := fun z => q z * Complex.exp (S.omega z)
  have hk : ContinuousAt k 0 := hq.continuousAt.mul
    (Complex.continuous_exp.continuousAt.comp homega)
  have hk0 : k 0 ≠ 0 := mul_ne_zero hq0 (Complex.exp_ne_zero _)
  have hw : complexGradient f =ᶠ[𝓝 (0 : ℂ)] fun z => z ^ m * k z := by
    filter_upwards [hfactor, Metric.isOpen_ball.mem_nhds hzR] with z hz hzR'
    rw [S.same_w z hzR', hz]
    simp only [sub_zero, smul_eq_mul, k, mul_assoc]
  exact scalar_signs_of_gradient_factor_v480 R hR f hf hf0 m k hk hk0 hw

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3InteriorSignTransportV480 -/

noncomputable section
open Set Topology Function Filter MeasureTheory
open scoped Manifold ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}
set_option maxHeartbeats 200000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

theorem graph_signs_transport_v480
    (N : InteriorNormalizationData_v475) (F : NativeInteriorChart_v475)
    (rho : ℝ) (hrho : 0 < rho) (h0S : (0 : E2) ∈ F.chart.source)
    (hSN : F.chart.source ⊆ N.O) (hT : F.chart.target = disc rho)
    (hF0 : F.chart (0 : E2) = 0)
    (hsigns : ∀ W : Set E2, W ∈ 𝓝 (0 : E2) →
      (∃ z ∈ W ∩ disc rho, 0 < F.vhat N.v z) ∧
      (∃ z ∈ W ∩ disc rho, F.vhat N.v z < 0)) :
    ∀ R : ℝ, 0 < R → ∀ V : Set E2, V ∈ 𝓝 (0 : E2) →
      (∃ x ∈ V ∩ Metric.ball 0 R, 0 < N.u x) ∧
      (∃ x ∈ V ∩ Metric.ball 0 R, N.u x < 0) := by
  have hI0 : F.chart.symm (0 : E2) = 0 := by
    simpa only [hF0] using F.chart.left_inv h0S
  have h0T : (0 : E2) ∈ F.chart.target := hF0 ▸ F.chart.map_source h0S
  have hIat : Tendsto F.chart.symm (𝓝 (0 : E2)) (𝓝 (0 : E2)) := by
    simpa only [hI0] using
      (F.inverse_C1.continuousOn.continuousAt (F.target_open.mem_nhds h0T)).tendsto
  intro R hR V hV
  let W := F.chart.target ∩ F.chart.symm ⁻¹' (V ∩ Metric.ball 0 R)
  have hW : W ∈ 𝓝 (0 : E2) := inter_mem (F.target_open.mem_nhds h0T)
    (hIat.eventually (inter_mem hV (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hR))))
  obtain ⟨⟨z, hz, hp⟩, ⟨w, hw, hn⟩⟩ := hsigns W hW
  have hzp : 0 < N.h (F.chart.symm z) :=
    N.h_positive _ (hSN (F.chart.map_target hz.1.1))
  have hwp : 0 < N.h (F.chart.symm w) :=
    N.h_positive _ (hSN (F.chart.map_target hw.1.1))
  refine ⟨⟨F.chart.symm z, hz.1.2, ?_⟩, ⟨F.chart.symm w, hw.1.2, ?_⟩⟩
  · have hh := mul_pos hp hzp
    simpa only [NativeInteriorChart_v475.vhat, Function.comp_apply,
      InteriorNormalizationData_v475.v, div_mul_cancel₀ _ hzp.ne'] using hh
  · have hh := mul_neg_of_neg_of_pos hn hwp
    simpa only [NativeInteriorChart_v475.vhat, Function.comp_apply,
      InteriorNormalizationData_v475.v, div_mul_cancel₀ _ hwp.ne'] using hh

/-- The original, unflattened upper-minus-lower graph changes sign in every
neighborhood of its tangency point, at every positive smaller radius. -/
theorem original_pair_graph_sign_changes (D : OriginalPair g J)
    {p : E.Carrier} (c : InteriorGraph D.A D.B p) :
    ∀ R : ℝ, 0 < R → ∀ V : Set E2, V ∈ 𝓝 (0 : E2) →
      (∃ x ∈ V ∩ Metric.ball 0 R, 0 < graphDifference c x) ∧
      (∃ x ∈ V ∩ Metric.ball 0 R, graphDifference c x < 0) := by
  obtain ⟨N, F, rho, m, delta, c1, c2, hu, hNR, h0S, hSN, hT, hF0,
    hh, hf, ⟨S⟩, hrho, hm, hd, hdr, hc1, hc2, hb⟩ :=
    original_pair_graph_normalized_finite_order D c
  have hI0 : F.chart.symm (0 : E2) = 0 := by
    simpa only [hF0] using F.chart.left_inv h0S
  have hN0 : N.u 0 = 0 := by rw [hu]; simp [graphDifference, c.upper_zero, c.lower_zero]
  have hf0 : F.vhat N.v 0 = 0 := by
    simp only [NativeInteriorChart_v475.vhat, Function.comp_apply,
      InteriorNormalizationData_v475.v, hI0, hN0, zero_div]
  have hnz : ∃ z ∈ Metric.ball (0 : ℂ) rho, complexGradient (F.vhat N.v) z ≠ 0 := by
    let z : ℂ := ((delta / 2 : ℝ) : ℂ)
    have hn : ‖z‖ = delta / 2 := by simp [z, Complex.norm_real, Real.norm_eq_abs, hd.le]
    have hz : z ∈ Metric.ball (0 : ℂ) delta := by
      rw [Metric.mem_ball, dist_zero_right, hn]
      exact half_lt_self hd
    refine ⟨z, Metric.ball_subset_ball hdr.le hz, ?_⟩
    have hp : 0 < c1 * ‖z‖ ^ m := mul_pos hc1 (pow_pos (hn ▸ half_pos hd) m)
    exact norm_pos_iff.mp (lt_of_lt_of_le hp (hb z hz).1)
  have hs := scalar_signs_of_similarity_nonzero_v480 rho hrho (F.vhat N.v) hf hf0 S hnz
  simpa only [hu] using graph_signs_transport_v480 N F rho hrho h0S hSN hT hF0 hs

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3InteriorAnalyticConclusionV480 -/

noncomputable section
open Set Topology Function Filter MeasureTheory
open scoped Manifold ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}

/-- All local analytic clauses of the original B3 conclusion, for the same
literal common graph of the original two minimizing surfaces. -/
theorem original_pair_graph_full_analytic_conclusion (D : OriginalPair g J)
    {p : E.Carrier} (c : InteriorGraph D.A D.B p) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ c1 c2 R : ℝ,
      0 < c1 ∧ 0 < c2 ∧ 0 < R ∧ R ≤ c.R ∧
      (∀ x : E2, 0 < ‖x‖ → ‖x‖ < R →
        c1 * ‖x‖ ^ m - c2 * ‖x‖ ^ (m + 1) ≤ ‖fderiv ℝ (graphDifference c) x‖ ∧
        0 < c1 * ‖x‖ ^ m - c2 * ‖x‖ ^ (m + 1)) ∧
      (∀ x ∈ Metric.ball (0 : E2) R,
        fderiv ℝ (graphDifference c) x = 0 ↔ x = 0) ∧
      (∀ V : Set E2, V ∈ 𝓝 (0 : E2) →
        (∃ x ∈ V ∩ Metric.ball 0 R, 0 < graphDifference c x) ∧
        (∃ x ∈ V ∩ Metric.ball 0 R, graphDifference c x < 0)) := by
  obtain ⟨m, hm, c1, c2, R, hc1, hc2, hR, hRR, hestimate, hcritical⟩ :=
    original_pair_graph_integer_derivative_estimate D c
  exact ⟨m, hm, c1, c2, R, hc1, hc2, hR, hRR, hestimate, hcritical,
    original_pair_graph_sign_changes D c R hR⟩

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3TangencySliceDerivativeV480 -/

noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
set_option maxHeartbeats 300000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- The actual tangent-plane equality transfers through the sphere inclusion
and every smooth ambient scalar coordinate. -/
theorem tangency_scalar_derivative_transfer_v480
    {S B : CompactOrientedSurface.{0}}
    (f : NeatEmbedding S E.Carrier) (g : NeatEmbedding B E.Carrier)
    (a : S) (b : B) (p : E.Carrier) (ha : f.toFun a = p) (hb : g.toFun b = p)
    (ht : tangentPlaneAt f a p ha = tangentPlaneAt g b p hb)
    (H : ThreeSphere → ℝ) (hH : MDifferentiableAt (𝓡 3) 𝓘(ℝ) H (E.toSphere p))
    (hzero : mfderiv (𝓡∂ 2) 𝓘(ℝ) (H ∘ E.toSphere ∘ f.toFun) a = 0) :
    mfderiv (𝓡∂ 2) 𝓘(ℝ) (H ∘ E.toSphere ∘ g.toFun) b = 0 := by
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  have hfd := f.smoothEmbedding.contMDiff.mdifferentiable (by simp) a
  have hgd := g.smoothEmbedding.contMDiff.mdifferentiable (by simp) b
  have hHf : MDifferentiableAt (𝓡 3) 𝓘(ℝ) H (E.toSphere (f.toFun a)) := ha.symm ▸ hH
  have hHg : MDifferentiableAt (𝓡 3) 𝓘(ℝ) H (E.toSphere (g.toFun b)) := hb.symm ▸ hH
  rw [mfderiv_comp a hHf (hinc.contMDiff.mdifferentiable (by simp) (f.toFun a) |>.comp a hfd),
    mfderiv_comp a (hinc.contMDiff.mdifferentiable (by simp) (f.toFun a)) hfd] at hzero
  rw [mfderiv_comp b hHg (hinc.contMDiff.mdifferentiable (by simp) (g.toFun b) |>.comp b hgd),
    mfderiv_comp b (hinc.contMDiff.mdifferentiable (by simp) (g.toFun b)) hgd]
  have hranges : LinearMap.range (mfderiv (𝓡∂ 2) (𝓡∂ 3) f.toFun a).toLinearMap =
      LinearMap.range (mfderiv (𝓡∂ 2) (𝓡∂ 3) g.toFun b).toLinearMap := by
    have htf : tangentPlaneAt f a p ha =
        LinearMap.range (mfderiv (𝓡∂ 2) (𝓡∂ 3) f.toFun a).toLinearMap := by cases ha; rfl
    have htg : tangentPlaneAt g b p hb =
        LinearMap.range (mfderiv (𝓡∂ 2) (𝓡∂ 3) g.toFun b).toLinearMap := by cases hb; rfl
    exact htf.symm.trans (ht.trans htg)
  ext v
  have hv : mfderiv (𝓡∂ 2) (𝓡∂ 3) g.toFun b v ∈
      LinearMap.range (mfderiv (𝓡∂ 2) (𝓡∂ 3) f.toFun a).toLinearMap :=
    hranges.symm ▸ LinearMap.mem_range_self _ v
  obtain ⟨w, hw⟩ := hv
  change (mfderiv (𝓡∂ 2) (𝓡∂ 3) f.toFun a) w =
    (mfderiv (𝓡∂ 2) (𝓡∂ 3) g.toFun b) v at hw
  have hz := congrArg (fun L => L w) hzero
  change (mfderiv (𝓡 3) 𝓘(ℝ) H (E.toSphere (f.toFun a)))
    ((mfderiv (𝓡∂ 3) (𝓡 3) E.toSphere (f.toFun a))
      ((mfderiv (𝓡∂ 2) (𝓡∂ 3) f.toFun a) w)) = 0 at hz
  change (mfderiv (𝓡 3) 𝓘(ℝ) H (E.toSphere (g.toFun b)))
    ((mfderiv (𝓡∂ 3) (𝓡 3) E.toSphere (g.toFun b))
      ((mfderiv (𝓡∂ 2) (𝓡∂ 3) g.toFun b) v)) = 0
  rw [hw] at hz
  convert hz using 1 <;> congr 2
  all_goals first
    | exact congrArg E.toSphere (hb.trans ha.symm)
    | congr 1 <;> exact hb.trans ha.symm


theorem actual_slice_normal_derivative_zero_v480
    {S : CompactOrientedSurface.{0}} (f : NeatEmbedding S E.Carrier)
    (a : S) (Φ : OpenPartialHomeomorph ThreeSphere (E2 × ℝ))
    (ha : E.toSphere (f.toFun a) ∈ Φ.source)
    (himage : Φ '' (Φ.source ∩ range (E.toSphere ∘ f.toFun)) =
      Φ.target ∩ (range (𝓡∂ 2) ×ˢ ({0} : Set ℝ))) :
    mfderiv (𝓡∂ 2) 𝓘(ℝ) (fun y => (Φ (E.toSphere (f.toFun y))).2) a = 0 := by
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  have hcont : Continuous (E.toSphere ∘ f.toFun) :=
    hinc.isEmbedding.continuous.comp f.smoothEmbedding.isEmbedding.continuous
  have heq : (fun y => (Φ (E.toSphere (f.toFun y))).2) =ᶠ[𝓝 a] fun _ => (0 : ℝ) := by
    filter_upwards [hcont.continuousAt.preimage_mem_nhds (Φ.open_source.mem_nhds ha)] with y hy
    have hh : Φ (E.toSphere (f.toFun y)) ∈ Φ.target ∩
        (range (𝓡∂ 2) ×ˢ ({0} : Set ℝ)) := by
      rw [← himage]
      exact mem_image_of_mem Φ ⟨hy, ⟨y, rfl⟩⟩
    exact hh.2.2
  rw [heq.mfderiv_eq]
  exact mfderiv_const (I := 𝓡∂ 2) (I' := 𝓘(ℝ)) (c := (0 : ℝ)) (x := a)

theorem smooth_slice_derivative_injective_v480
    (Φ : OpenPartialHomeomorph ThreeSphere (E2 × ℝ))
    (hΦ : ContMDiffOn (𝓡 3) 𝓘(ℝ, E2 × ℝ) ∞ Φ Φ.source)
    (hΦi : ContMDiffOn 𝓘(ℝ, E2 × ℝ) (𝓡 3) ∞ Φ.symm Φ.target)
    {p : ThreeSphere} (hp : p ∈ Φ.source) :
    Injective (mfderiv (𝓡 3) 𝓘(ℝ, E2 × ℝ) Φ p) := by
  have hfd := (hΦ.contMDiffAt (Φ.open_source.mem_nhds hp)).mdifferentiableAt (by simp)
  have hid := (hΦi.contMDiffAt (Φ.open_target.mem_nhds (Φ.map_source hp))).mdifferentiableAt (by simp)
  have heq : (Φ.symm : E2 × ℝ → ThreeSphere) ∘ Φ =ᶠ[𝓝 p] id := by
    filter_upwards [Φ.open_source.mem_nhds hp] with q hq
    exact Φ.left_inv hq
  have hchain := mfderiv_comp p hid hfd
  rw [heq.mfderiv_eq, mfderiv_id] at hchain
  simp only [tangentSpaceCast] at hchain
  intro v w hvw
  have hv := congrArg (fun L => L v) hchain
  have hw := congrArg (fun L => L w) hchain
  have hh := hv.trans
    ((congrArg (mfderiv 𝓘(ℝ, E2 × ℝ) (𝓡 3) Φ.symm (Φ p)) hvw).trans hw.symm)
  change v = w at hh
  exact hh

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3ArbitraryTangencyGraphV480 -/

noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
set_option maxHeartbeats 300000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- At an arbitrary original tangency, the second actual slice has zero
normal derivative in the first actual slice chart. -/
theorem arbitrary_tangency_slice_normal_derivative_v480
    {S B : CompactOrientedSurface.{0}}
    (f : NeatEmbedding S E.Carrier) (g : NeatEmbedding B E.Carrier)
    (a : S) (b : B) (p : E.Carrier) (ha : f.toFun a = p) (hb : g.toFun b = p)
    (ht : tangentPlaneAt f a p ha = tangentPlaneAt g b p hb)
    (Φ Ψ : OpenPartialHomeomorph ThreeSphere (E2 × ℝ))
    (hΦ : ContMDiffOn (𝓡 3) 𝓘(ℝ, E2 × ℝ) ∞ Φ Φ.source)
    (hΨ : ContMDiffOn (𝓡 3) 𝓘(ℝ, E2 × ℝ) ∞ Ψ Ψ.source)
    (hΨi : ContMDiffOn 𝓘(ℝ, E2 × ℝ) (𝓡 3) ∞ Ψ.symm Ψ.target)
    (hpΦ : E.toSphere p ∈ Φ.source) (hpΨ : E.toSphere p ∈ Ψ.source)
    (hA : Φ '' (Φ.source ∩ range (E.toSphere ∘ f.toFun)) =
      Φ.target ∩ (range (𝓡∂ 2) ×ˢ ({0} : Set ℝ)))
    (hB : Ψ '' (Ψ.source ∩ range (E.toSphere ∘ g.toFun)) =
      Ψ.target ∩ (range (𝓡∂ 2) ×ˢ ({0} : Set ℝ)))
    (hP : ContDiffOn ℝ ∞ (fun z : E2 => Φ (Ψ.symm (z, 0)))
      {z | (z, 0) ∈ Ψ.target ∧ Ψ.symm (z, 0) ∈ Φ.source}) :
    fderiv ℝ (fun z : E2 => (Φ (Ψ.symm (z, 0))).2) ((Ψ (E.toSphere p)).1) = 0 := by
  classical
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  let G : B → ThreeSphere := E.toSphere ∘ g.toFun
  let Q : B → E2 × ℝ := Ψ ∘ G
  let q : E2 := (Ψ (E.toSphere p)).1
  have hsnd : ContMDiff 𝓘(ℝ, E2 × ℝ) 𝓘(ℝ) ∞ (Prod.snd : E2 × ℝ → ℝ) :=
    (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : E2 × ℝ → ℝ)).contMDiff
  have hfstSmooth : ContMDiff 𝓘(ℝ, E2 × ℝ) 𝓘(ℝ, E2) ∞ (Prod.fst : E2 × ℝ → E2) :=
    (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : E2 × ℝ → E2)).contMDiff
  have hGd := hinc.contMDiff.mdifferentiable (by simp) (g.toFun b) |>.comp b
    (g.smoothEmbedding.contMDiff.mdifferentiable (by simp) b)
  have hbΨ : G b ∈ Ψ.source := by simpa only [G, Function.comp_apply, hb] using hpΨ
  have hΨd := (hΨ.contMDiffAt (Ψ.open_source.mem_nhds hbΨ)).mdifferentiableAt (by simp)
  have hQd : MDifferentiableAt (𝓡∂ 2) 𝓘(ℝ, E2 × ℝ) Q b := hΨd.comp b hGd
  have hQinj : Injective (mfderiv (𝓡∂ 2) 𝓘(ℝ, E2 × ℝ) Q b) := by
    dsimp only [Q, G]
    rw [mfderiv_comp b hΨd hGd,
      mfderiv_comp b (hinc.contMDiff.mdifferentiable (by simp) (g.toFun b))
        (g.smoothEmbedding.contMDiff.mdifferentiable (by simp) b)]
    exact (smooth_slice_derivative_injective_v480 Ψ hΨ hΨi hbΨ).comp
      (((hinc.isImmersion.isImmersionAt _).mfderiv_injective (by simp)).comp
        ((g.smoothEmbedding.isImmersion.isImmersionAt b).mfderiv_injective (by simp)))
  have hQn := actual_slice_normal_derivative_zero_v480 g b Ψ hbΨ hB
  have hQnormal : ∀ v, ((mfderiv (𝓡∂ 2) 𝓘(ℝ, E2 × ℝ) Q b) v).2 = 0 := by
    intro v
    have hd := mfderiv_comp b (hsnd.mdifferentiable (by simp) (Q b)) hQd
    change mfderiv (𝓡∂ 2) 𝓘(ℝ) (fun y => (Ψ (E.toSphere (g.toFun y))).2) b = _ at hd
    rw [hQn, mfderiv_eq_fderiv, fderiv_snd] at hd
    have hh := congrArg (fun T => T v) hd
    change 0 = ((mfderiv (𝓡∂ 2) 𝓘(ℝ, E2 × ℝ) Q b) v).2 at hh
    exact hh.symm
  let L : E2 →L[ℝ] (E2 × ℝ) :=
    (tangentSpaceCastModel 𝓘(ℝ, E2 × ℝ) (Q b)).toContinuousLinearMap.comp
      ((mfderiv (𝓡∂ 2) 𝓘(ℝ, E2 × ℝ) Q b).comp
        (tangentSpaceCastModel (𝓡∂ 2) b).symm.toContinuousLinearMap)
  have hLinj : Injective L :=
    (tangentSpaceCastModel 𝓘(ℝ, E2 × ℝ) (Q b)).injective.comp
      (hQinj.comp (tangentSpaceCastModel (𝓡∂ 2) b).symm.injective)
  have hLn : (ContinuousLinearMap.snd ℝ E2 ℝ).comp L = 0 := by
    ext v
    change (L v).2 = 0
    exact hQnormal ((tangentSpaceCastModel (𝓡∂ 2) b).symm v)
  obtain ⟨J, hJ⟩ := native_projected_derivative_invertible_v475 L hLinj hLn
  let H : ThreeSphere → ℝ := fun z => (Φ z).2
  have hHd : MDifferentiableAt (𝓡 3) 𝓘(ℝ) H (E.toSphere p) :=
    hsnd.mdifferentiableAt (by simp) |>.comp _
      ((hΦ.contMDiffAt (Φ.open_source.mem_nhds hpΦ)).mdifferentiableAt (by simp))
  have hHz : mfderiv (𝓡∂ 2) 𝓘(ℝ) (H ∘ E.toSphere ∘ f.toFun) a = 0 := by
    exact actual_slice_normal_derivative_zero_v480 f a Φ (ha.symm ▸ hpΦ) hA
  have hHg := tangency_scalar_derivative_transfer_v480 f g a b p ha hb ht H hHd hHz
  have hpair : Ψ (E.toSphere p) = (q, 0) := by
    have hh : Ψ (E.toSphere (g.toFun b)) ∈ Ψ.target ∩
        (range (𝓡∂ 2) ×ˢ ({0} : Set ℝ)) := by
      rw [← hB]
      exact mem_image_of_mem Ψ ⟨hbΨ, ⟨b, rfl⟩⟩
    refine Prod.ext rfl ?_
    simpa only [hb, Set.mem_singleton_iff] using hh.2.2
  let O : Set E2 := {z | (z, 0) ∈ Ψ.target ∧ Ψ.symm (z, 0) ∈ Φ.source}
  have hO : IsOpen O :=
    (Ψ.continuousOn_symm.isOpen_inter_preimage Ψ.open_target Φ.open_source).preimage
      (continuous_id.prodMk continuous_const)
  have hqO : q ∈ O := by
    refine ⟨hpair ▸ Ψ.map_source hpΨ, ?_⟩
    rw [← hpair, Ψ.left_inv hpΨ]
    exact hpΦ
  let n : E2 → ℝ := fun z => (Φ (Ψ.symm (z, 0))).2
  have hnd : DifferentiableAt ℝ n q :=
    (hP.snd.contDiffAt (hO.mem_nhds hqO)).differentiableAt (by simp)
  have heq : n ∘ (fun y => (Q y).1) =ᶠ[𝓝 b] H ∘ G := by
    have hGc : Continuous G := hinc.isEmbedding.continuous.comp g.smoothEmbedding.isEmbedding.continuous
    have hbΦ : G b ∈ Φ.source := by simpa only [G, Function.comp_apply, hb] using hpΦ
    filter_upwards [hGc.continuousAt.preimage_mem_nhds
      ((Ψ.open_source.inter Φ.open_source).mem_nhds ⟨hbΨ, hbΦ⟩)] with y hy
    have hh : Ψ (G y) ∈ Ψ.target ∩ (range (𝓡∂ 2) ×ˢ ({0} : Set ℝ)) := by
      rw [← hB]
      exact mem_image_of_mem Ψ ⟨hy.1, ⟨y, rfl⟩⟩
    have hzero : (Q y).2 = 0 := hh.2.2
    have hQpair : ((Q y).1, 0) = Q y := Prod.ext rfl hzero.symm
    change (Φ (Ψ.symm ((Q y).1, 0))).2 = (Φ (G y)).2
    rw [hQpair]
    exact congrArg (fun z => (Φ z).2) (Ψ.left_inv hy.1)
  have hfstd := hfstSmooth.mdifferentiableAt (by simp) |>.comp b hQd
  have hchain := mfderiv_comp b (show MDifferentiableAt 𝓘(ℝ, E2) 𝓘(ℝ) n ((Q b).1) from
    (show (Q b).1 = q by simp only [Q, G, q, Function.comp_apply, hb]).symm ▸ hnd.mdifferentiableAt) hfstd
  change mfderiv (𝓡∂ 2) 𝓘(ℝ) (n ∘ (fun y => (Q y).1)) b =
    (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ) n ((Q b).1)).comp
      (mfderiv (𝓡∂ 2) 𝓘(ℝ, E2) (fun y => (Q y).1) b) at hchain
  rw [heq.mfderiv_eq, hHg, mfderiv_eq_fderiv] at hchain
  ext v
  obtain ⟨w, hw⟩ := J.surjective v
  have hh := congrArg (fun T => T ((tangentSpaceCastModel (𝓡∂ 2) b).symm w)) hchain
  have hfstval (v : TangentSpace (𝓡∂ 2) b) :
      (mfderiv (𝓡∂ 2) 𝓘(ℝ, E2) (fun y => (Q y).1) b) v =
      ((mfderiv (𝓡∂ 2) 𝓘(ℝ, E2 × ℝ) Q b) v).1 := by
    have hd := mfderiv_comp b (hfstSmooth.mdifferentiableAt (by simp)) hQd
    rw [mfderiv_eq_fderiv, fderiv_fst] at hd
    have hv := congrArg (fun T => T v) hd
    exact hv
  change (fderiv ℝ n q) v = 0
  change 0 = (fderiv ℝ n ((Q b).1))
    ((mfderiv (𝓡∂ 2) 𝓘(ℝ, E2) (fun y => (Q y).1) b)
      ((tangentSpaceCastModel (𝓡∂ 2) b).symm w)) at hh
  have hbase : (Q b).1 = q := by simp only [Q, G, q, Function.comp_apply, hb]
  rw [hfstval] at hh
  change 0 = (fderiv ℝ n ((Q b).1)) ((L w).1) at hh
  have hJw : J w = (L w).1 := by
    have ht := congrArg (fun T : E2 →L[ℝ] E2 => T w) hJ
    exact ht
  rw [← hJw, hw] at hh
  simpa only [hbase] using hh.symm

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3BoundarySphereImmersionV480 -/

noncomputable section
open Set Function Filter Manifold
open scoped Manifold ContDiff Topology
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.A7Support
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}

/-- Native neat surface immersion in the sphere, including source boundary
points. The construction extends actual coordinates and retains the source
half-space; it needs neither an interior point nor an agreement germ. -/
theorem actual_neat_sphere_immersion_v480
    {S : CompactOrientedSurface.{0}} (f : NeatEmbedding S E.Carrier) (x : S) :
    IsImmersionAtOfComplement ℝ (𝓡∂ 2) (𝓡 3) ∞ (E.toSphere ∘ f.toFun) x := by
  let F : S → ThreeSphere := E.toSphere ∘ f.toFun
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  have hF : ContMDiff (𝓡∂ 2) (𝓡 3) ∞ F :=
    hinc.contMDiff.comp f.smoothEmbedding.contMDiff
  have hFi : Injective (mfderiv (𝓡∂ 2) (𝓡 3) F x) := by
    dsimp only [F]
    rw [mfderiv_comp x (hinc.contMDiff.mdifferentiableAt (by simp))
      (f.smoothEmbedding.contMDiff.mdifferentiableAt (by simp))]
    exact ((hinc.isImmersion.isImmersionAt _).mfderiv_injective (by simp)).comp
      ((f.smoothEmbedding.isImmersion.isImmersionAt x).mfderiv_injective (by simp))
  obtain ⟨g,hg,hge,hgd⟩ := native_coordinate_extension hF x
  let a := extChartAt (𝓡∂ 2) x x
  let D : E2 →L[ℝ] E3 :=
    (tangentSpaceCastModel (𝓡 3) (F x)).toContinuousLinearMap.comp
      ((mfderiv (𝓡∂ 2) (𝓡 3) F x).comp
        (tangentSpaceCastModel (𝓡∂ 2) x).symm.toContinuousLinearMap)
  have hD : Injective D := (tangentSpaceCastModel (𝓡 3) (F x)).injective.comp
    (hFi.comp (tangentSpaceCastModel (𝓡∂ 2) x).symm.injective)
  obtain ⟨n,hn,horth,A,hA⟩ := normal_completion D hD (innerSL ℝ)
    (fun v hv => real_inner_self_pos.mpr hv)
  obtain ⟨e,hae,he,hei,heq⟩ := local_normal_extension hg hgd n A hA
  let β := straighteningChart e
  obtain ⟨hβ,hβi⟩ := straighteningChart_smooth e he hei
  obtain ⟨hga,hβga,hgraph⟩ := straighteningChart_graph e hae heq
  let c := chartAt (EuclideanHalfSpace 2) x
  let d := extChartAtPartialDiffeomorph (𝓡 3) ∞ (F x)
  let δ := d.toOpenPartialHomeomorph.trans β
  have hδ : δ ∈ IsManifold.maximalAtlas (𝓡 3) ∞ ThreeSphere := by
    apply δ.mem_maximalAtlas_of_contMDiffOn
    · exact hβ.contMDiffOn.comp (d.contMDiffOn.mono inter_subset_left) (fun _ hy => hy.2)
    · exact d.symm.contMDiffOn.comp (hβi.contMDiffOn.mono inter_subset_left) (fun _ hy => hy.2)
  have ht : Tendsto (extChartAt (𝓡∂ 2) x) (𝓝 x)
      (𝓝[range (𝓡∂ 2)] a) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨(contMDiffAt_extChartAt (I := 𝓡∂ 2) (n := ∞)).continuousAt.tendsto,
      Eventually.of_forall (fun y => mem_range_self (c y))⟩
  have hmatch : ∀ᶠ y in 𝓝 x,
      y ∈ c.source ∧ F y ∈ δ.source ∧ δ (F y) = standardPlaneEquiv (extChartAt (𝓡∂ 2) x y,0) := by
    have hm := ht.eventually hge
    have hg' := ((contMDiffAt_extChartAt (I := 𝓡∂ 2) (n := ∞) (x := x)).continuousAt.tendsto).eventually hgraph
    have hd' := hF.continuous.continuousAt.preimage_mem_nhds
      (d.open_source.mem_nhds (mem_extChartAt_source (F x)))
    filter_upwards [c.open_source.mem_nhds (mem_chart_source _ _),hm,hg',hd'] with y hy hmy hgy hdy
    have hey : (extChartAt (𝓡∂ 2) x).symm (extChartAt (𝓡∂ 2) x y) = y :=
      (extChartAt (𝓡∂ 2) x).left_inv (by simpa only [extChartAt_source,c] using hy)
    change g (extChartAt (𝓡∂ 2) x y) = d (F ((extChartAt (𝓡∂ 2) x).symm (extChartAt (𝓡∂ 2) x y))) at hmy
    rw [hey] at hmy
    refine ⟨hy,⟨hdy,by change d (F y) ∈ β.source; rw [← hmy]; exact hgy.1⟩,?_⟩
    change β (d (F y)) = _
    rw [← hmy]
    exact hgy.2
  obtain ⟨U,hU,hUo,hxU⟩ := mem_nhds_iff.mp hmatch
  let α := c.restrOpen U hUo
  have hα : α ∈ IsManifold.maximalAtlas (𝓡∂ 2) ∞ S := by
    apply α.mem_maximalAtlas_of_contMDiffOn
    · exact (contMDiffOn_chart (I := 𝓡∂ 2) (n := ∞) (x := x)).mono inter_subset_left
    · exact (contMDiffOn_chart_symm (I := 𝓡∂ 2) (n := ∞) (x := x)).mono inter_subset_left
  have hmaps : α.source ⊆ F ⁻¹' δ.source := fun y hy => (hU hy.2).2.1
  have hxα : x ∈ α.source := ⟨mem_chart_source _ _,hxU⟩
  apply IsImmersionAtOfComplement.mk_of_charts standardPlaneEquiv α δ hxα (hmaps hxα) hα hδ hmaps
  intro z hz
  let y := (α.extend (𝓡∂ 2)).symm z
  have hys : y ∈ α.source := by
    have hh := (α.extend (𝓡∂ 2)).map_target hz
    simpa only [OpenPartialHomeomorph.extend_source] using hh
  have heyz : extChartAt (𝓡∂ 2) x y = z := (α.extend (𝓡∂ 2)).right_inv hz
  change δ (F y) = standardPlaneEquiv (z,0)
  rw [(hU hys.2).2.2,heyz]

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3BoundarySphereSliceV480 -/
noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
universe u
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Exact whole-image slice shrinking at a source boundary point, with the
actual planar boundary coordinate retained. -/
theorem actual_boundary_slice_of_complement_v480
    {S : CompactOrientedSurface.{u}} {f : S → ThreeSphere} {x : S}
    (h : Manifold.IsImmersionAtOfComplement ℝ (𝓡∂ 2) (𝓡 3) ∞ f x)
    (hf : IsInducing f) (hxb : (𝓡∂ 2).IsBoundaryPoint x) :
    ∃ Φ : OpenPartialHomeomorph ThreeSphere (E2 × ℝ), f x ∈ Φ.source ∧
      ContMDiffOn (𝓡 3) 𝓘(ℝ,E2 × ℝ) ∞ Φ Φ.source ∧
      ContMDiffOn 𝓘(ℝ,E2 × ℝ) (𝓡 3) ∞ Φ.symm Φ.target ∧
      Φ '' (Φ.source ∩ range f)=Φ.target ∩ (range (𝓡∂ 2) ×ˢ ({0}:Set ℝ)) ∧
      Φ '' (Φ.source ∩ f '' S.boundary) =
        Φ.target ∩ ({z : E2 | z 0 = 0} ×ˢ ({0}:Set ℝ)) ∧
      (Φ (f x)).1 0 = 0 := by
  -- The ambient chart of the immersion, read in the splitting `E2 × ℝ` of the ambient model space.
  let Ψ : OpenPartialHomeomorph ThreeSphere (E2 × ℝ) :=
    h.codChart.transHomeomorph ((𝓡 3).toHomeomorph.trans h.equiv.toHomeomorph.symm)
  have hΨ_apply : ∀ p : ThreeSphere, Ψ p = h.equiv.symm ((h.codChart.extend (𝓡 3)) p) := fun _ => rfl
  have hextend : ∀ y : S, (h.domChart.extend (𝓡∂ 2)) y = (𝓡∂ 2) (h.domChart y) := fun _ => rfl
  have hΨsmooth : ContMDiffOn (𝓡 3) 𝓘(ℝ, E2 × ℝ) ∞ Ψ Ψ.source := by
    change ContMDiffOn (𝓡 3) 𝓘(ℝ, E2 × ℝ) ∞
      (h.equiv.symm ∘ h.codChart.extend (𝓡 3)) h.codChart.source
    exact h.contMDiffOn_equiv_symm_extend_codChart
  have hΨsmooth_inv : ContMDiffOn 𝓘(ℝ, E2 × ℝ) (𝓡 3) ∞ Ψ.symm Ψ.target := by
    change ContMDiffOn 𝓘(ℝ, E2 × ℝ) (𝓡 3) ∞
      ((h.codChart.extend (𝓡 3)).symm ∘ h.equiv) Ψ.target
    refine (contMDiffOn_extend_symm h.codChart_mem_maximalAtlas).comp
      h.equiv.contDiff.contMDiff.contMDiffOn ?_
    intro q hq
    change (𝓡 3).symm (h.equiv q) ∈ h.codChart.target at hq
    exact ⟨(𝓡 3).symm (h.equiv q), hq, (𝓡 3).right_inv (by rw [(𝓡 3).range_eq_univ]; trivial)⟩
  -- In this chart the immersion normal form says that `f` is the standard inclusion.
  have key : ∀ y ∈ h.domChart.source, Ψ (f y) = ((h.domChart.extend (𝓡∂ 2)) y, 0) := by
    intro y hy
    rw [hΨ_apply]
    exact h.equiv_symm_extend_codChart_apply hy
  -- An open ambient set cuts the domain chart out of the image.
  obtain ⟨W, hW, hWf⟩ := hf.isOpen_iff.1 h.domChart.open_source
  have hmemW : ∀ y : S, f y ∈ W ↔ y ∈ h.domChart.source := fun y => by
    rw [← hWf]
    exact Iff.rfl
  -- The part of the ambient model space lying over the target of the domain chart.
  have hU : IsOpen ((𝓡∂ 2).symm ⁻¹' h.domChart.target) :=
    h.domChart.open_target.preimage (𝓡∂ 2).continuous_symm
  let V : Set ThreeSphere :=
    (Ψ.source ∩ Ψ ⁻¹' (((𝓡∂ 2).symm ⁻¹' h.domChart.target) ×ˢ (univ : Set ℝ))) ∩ W
  have hVopen : IsOpen V := (Ψ.isOpen_inter_preimage (hU.prod isOpen_univ)).inter hW
  -- The point `f x` survives both restrictions.
  have hx : x ∈ h.domChart.source := h.mem_domChart_source
  have hfx : f x ∈ Ψ.source := h.mem_codChart_source
  have hfxV : f x ∈ V := by
    refine ⟨⟨hfx, ?_⟩, (hmemW x).2 hx⟩
    rw [mem_preimage, key x hx]
    exact ⟨by rw [mem_preimage, hextend, (𝓡∂ 2).left_inv]; exact h.domChart.map_source hx,
      mem_univ _⟩
  let Φ := Ψ.restrOpen V hVopen
  have hiff : ∀ p ∈ Φ.source, p ∈ range f ↔ Φ p ∈ range (𝓡∂ 2) ×ˢ ({0} : Set ℝ) := by
    intro p hp
    change p ∈ Ψ.source ∩ V at hp
    change p ∈ range f ↔ Ψ p ∈ range (𝓡∂ 2) ×ˢ ({0} : Set ℝ)
    constructor
    · rintro ⟨y, rfl⟩
      have hy : y ∈ h.domChart.source := (hmemW y).1 hp.2.2
      rw [key y hy, hextend]
      exact ⟨mem_range_self _, rfl⟩
    · intro hps
      have hmem : (Ψ p).1 ∈ (h.domChart.extend (𝓡∂ 2)).target := by
        rw [h.domChart.extend_target]
        exact ⟨hp.2.1.2.1, hps.1⟩
      have hys : (h.domChart.extend (𝓡∂ 2)).symm (Ψ p).1 ∈ h.domChart.source := by
        rw [← h.domChart.extend_source (I := 𝓡∂ 2)]
        exact (h.domChart.extend (𝓡∂ 2)).map_target hmem
      have hfy : Ψ (f ((h.domChart.extend (𝓡∂ 2)).symm (Ψ p).1)) = Ψ p := by
        rw [key _ hys, (h.domChart.extend (𝓡∂ 2)).right_inv hmem, ← (hps.2 : (Ψ p).2 = 0)]
      exact ⟨_, Ψ.injOn (h.source_subset_preimage_source hys) hp.1 hfy⟩
  have hboundary_chart (y : S) (hy : y ∈ h.domChart.source) :
      ((h.domChart.extend (𝓡∂ 2)) y) 0 = 0 ↔ y ∈ S.boundary := by
    let z := (h.domChart.extend (𝓡∂ 2)) y
    have hzR : z ∈ range (𝓡∂ 2) := mem_range_self (h.domChart y)
    have hzi : (𝓡∂ 2).IsInteriorPoint y ↔ 0 < z 0 := by
      constructor
      · intro hyi
        have hh := ((𝓡∂ 2).isInteriorPoint_iff_of_mem_maximalAtlas
          (by simp : (∞ : ℕ∞ω) ≠ 0) h.domChart_mem_maximalAtlas hy).mp hyi
        have hhr := h.domChart.interior_extend_target_subset_interior_range hh
        simpa only [interior_range_modelWithCornersEuclideanHalfSpace, Set.mem_setOf_eq] using hhr
      · intro hpos
        apply ((𝓡∂ 2).isInteriorPoint_iff_of_mem_maximalAtlas
          (by simp : (∞ : ℕ∞ω) ≠ 0) h.domChart_mem_maximalAtlas hy).mpr
        have hint : (𝓡∂ 2) (h.domChart y) ∈ interior (range (𝓡∂ 2)) := by
          rw [interior_range_modelWithCornersEuclideanHalfSpace]
          exact hpos
        exact h.domChart.mem_interior_extend_target (I := 𝓡∂ 2)
          (h.domChart.map_source hy) hint
    constructor
    · intro hz0
      have hh : ¬ (𝓡∂ 2).IsInteriorPoint y := by
        intro hi
        have hp := hzi.mp hi
        rw [hz0] at hp
        exact lt_irrefl _ hp
      change (𝓡∂ 2).IsBoundaryPoint y
      apply Classical.byContradiction
      intro hyN
      exact hh (((𝓡∂ 2).isInteriorPoint_iff_not_isBoundaryPoint y).mpr hyN)
    · intro hyb
      have hn : ¬ 0 < z 0 := by
        intro hp
        exact ((𝓡∂ 2).isInteriorPoint_iff_not_isBoundaryPoint y).mp (hzi.mpr hp) hyb
      rw [range_modelWithCornersEuclideanHalfSpace] at hzR
      exact le_antisymm (le_of_not_gt hn) hzR
  have hiffBoundary : ∀ p ∈ Φ.source,
      p ∈ f '' S.boundary ↔ Φ p ∈ {z : E2 | z 0 = 0} ×ˢ ({0}:Set ℝ) := by
    intro p hp
    constructor
    · rintro ⟨y,hyb,rfl⟩
      have hy : y ∈ h.domChart.source := (hmemW y).1 hp.2.2
      change (Ψ (f y)).1 0 = 0 ∧ (Ψ (f y)).2 = 0
      rw [key y hy]
      exact ⟨(hboundary_chart y hy).mpr hyb,rfl⟩
    · intro hpb
      have hr : Φ p ∈ range (𝓡∂ 2) ×ˢ ({0}:Set ℝ) := by
        refine ⟨?_,hpb.2⟩
        rw [range_modelWithCornersEuclideanHalfSpace]
        change 0 ≤ (Φ p).1 0
        rw [hpb.1]
      obtain ⟨y,rfl⟩ := (hiff p hp).mpr hr
      have hy : y ∈ h.domChart.source := (hmemW y).1 hp.2.2
      refine ⟨y,(hboundary_chart y hy).mp ?_,rfl⟩
      have hz := hpb.1
      change (Ψ (f y)).1 0 = 0 at hz
      rwa [key y hy] at hz
  have hbase : (Φ (f x)).1 0 = 0 := by
    change (Ψ (f x)).1 0 = 0
    rw [key x hx]
    let z := (h.domChart.extend (𝓡∂ 2)) x
    have hzR : z ∈ range (𝓡∂ 2) := mem_range_self (h.domChart x)
    have hzN : z ∉ interior (range (𝓡∂ 2)) := by
      intro hint
      have hzI := h.domChart.mem_interior_extend_target (h.domChart.map_source hx) hint
      have hxi := ((𝓡∂ 2).isInteriorPoint_iff_of_mem_maximalAtlas
        (by simp : (∞ : ℕ∞ω) ≠ 0) h.domChart_mem_maximalAtlas hx).mpr hzI
      exact ((𝓡∂ 2).isInteriorPoint_iff_not_isBoundaryPoint x).mp hxi hxb
    rw [range_modelWithCornersEuclideanHalfSpace] at hzR
    rw [interior_range_modelWithCornersEuclideanHalfSpace] at hzN
    change z 0 = 0
    exact le_antisymm (le_of_not_gt hzN) hzR
  refine ⟨Φ, ⟨hfx, hfxV⟩, hΨsmooth.mono inter_subset_left,
    hΨsmooth_inv.mono inter_subset_left, ?_,?_,hbase⟩
  · ext q
    constructor
    · rintro ⟨p, ⟨hps, hpr⟩, rfl⟩
      exact ⟨Φ.map_source hps, (hiff p hps).mp hpr⟩
    · rintro ⟨hqt, hqS⟩
      refine ⟨Φ.symm q, ⟨Φ.map_target hqt, ?_⟩, Φ.right_inv hqt⟩
      apply (hiff _ (Φ.map_target hqt)).mpr
      rwa [Φ.right_inv hqt]

  · ext q
    constructor
    · rintro ⟨p,⟨hps,hpr⟩,rfl⟩
      exact ⟨Φ.map_source hps,(hiffBoundary p hps).mp hpr⟩
    · rintro ⟨hqt,hqS⟩
      refine ⟨Φ.symm q,⟨Φ.map_target hqt,?_⟩,Φ.right_inv hqt⟩
      apply (hiffBoundary _ (Φ.map_target hqt)).mpr
      rwa [Φ.right_inv hqt]


/-- Every actual neat surface has a genuine smooth sphere slice chart at
its boundary points, with the entire local surface image and flat boundary. -/
theorem actual_neat_boundary_sphere_slice_v480
    {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
    {S : CompactOrientedSurface.{0}} (f : NeatEmbedding S E.Carrier)
    (x : S) (hx : x ∈ S.boundary) :
    ∃ Φ : OpenPartialHomeomorph ThreeSphere (E2 × ℝ),
      E.toSphere (f.toFun x) ∈ Φ.source ∧
      ContMDiffOn (𝓡 3) 𝓘(ℝ,E2 × ℝ) ∞ Φ Φ.source ∧
      ContMDiffOn 𝓘(ℝ,E2 × ℝ) (𝓡 3) ∞ Φ.symm Φ.target ∧
      Φ '' (Φ.source ∩ range (E.toSphere ∘ f.toFun)) =
        Φ.target ∩ (range (𝓡∂ 2) ×ˢ ({0}:Set ℝ)) ∧
      Φ '' (Φ.source ∩ (E.toSphere ∘ f.toFun) '' S.boundary) =
        Φ.target ∩ ({z : E2 | z 0 = 0} ×ˢ ({0}:Set ℝ)) ∧
      (Φ (E.toSphere (f.toFun x))).1 0 = 0 := by
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  exact actual_boundary_slice_of_complement_v480 (actual_neat_sphere_immersion_v480 f x)
    ((hinc.isEmbedding.comp f.smoothEmbedding.isEmbedding).isInducing) hx


end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3BoundaryCommonGraphV480 -/
noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
set_option maxHeartbeats 300000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- Actual common graph at a boundary tangent-plane coincidence. Both
whole images, the shared literal boundary and a smooth extension are retained;
no supplied B1 collar or image-agreement germ is assumed. -/
theorem actual_arbitrary_boundary_common_graph_v480
    {S : CompactOrientedSurface.{0}} {B : CompactOrientedSurface.{0}}
    (f : NeatEmbedding S E.Carrier) (g : NeatEmbedding B E.Carrier)
    (x : S) (y : B) (hx : x ∈ S.boundary) (hyb : y ∈ B.boundary)
    (hy : g.toFun y = f.toFun x)
    (hboundary : f.toFun '' S.boundary = g.toFun '' B.boundary)
    (ht : tangentPlaneAt f x (f.toFun x) rfl =
      tangentPlaneAt g y (f.toFun x) hy) :
    ∃ Φ Ψ : OpenPartialHomeomorph ThreeSphere (E2 × ℝ),
    ∃ O : Set E2, ∃ p : E2,
    ∃ e : OpenPartialHomeomorph E2 E2, ∃ u : E2 → ℝ,
      g.toFun y=f.toFun x ∧
      O = {z : E2 | (z,0) ∈ Ψ.target ∧ Ψ.symm (z,0) ∈ Φ.source} ∧ IsOpen O ∧ p ∈ O ∧ p ∈ e.source ∧ e.source ⊆ O ∧
      ContMDiffOn (𝓡 3) 𝓘(ℝ,E2 × ℝ) ∞ Φ Φ.source ∧
      ContMDiffOn 𝓘(ℝ,E2 × ℝ) (𝓡 3) ∞ Φ.symm Φ.target ∧
      ContMDiffOn (𝓡 3) 𝓘(ℝ,E2 × ℝ) ∞ Ψ Ψ.source ∧
      ContMDiffOn 𝓘(ℝ,E2 × ℝ) (𝓡 3) ∞ Ψ.symm Ψ.target ∧
      Φ '' (Φ.source ∩ range (E.toSphere ∘ f.toFun)) =
        Φ.target ∩ (range (𝓡∂ 2) ×ˢ ({0}:Set ℝ)) ∧
      Ψ '' (Ψ.source ∩ range (E.toSphere ∘ g.toFun)) =
        Ψ.target ∩ (range (𝓡∂ 2) ×ˢ ({0}:Set ℝ)) ∧
      Φ '' (Φ.source ∩ (E.toSphere ∘ f.toFun) '' S.boundary) =
        Φ.target ∩ ({z : E2 | z 0 = 0} ×ˢ ({0}:Set ℝ)) ∧
      Ψ '' (Ψ.source ∩ (E.toSphere ∘ g.toFun) '' B.boundary) =
        Ψ.target ∩ ({z : E2 | z 0 = 0} ×ˢ ({0}:Set ℝ)) ∧
      E.toSphere (f.toFun x) ∈ Φ.source ∩ Ψ.source ∧
      Ψ (E.toSphere (g.toFun y))=(p,0) ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      ContDiffOn ℝ ∞ u e.target ∧ u (e p)=0 ∧ fderiv ℝ u (e p)=0 ∧
      (∀ z ∈ e.target, Φ (Ψ.symm (e.symm z,0))=(z,u z)) ∧
      (∀ z ∈ e.source, Φ (Ψ.symm (z,0))=(e z,u (e z))) ∧
      p 0 = 0 ∧ (e p) 0 = 0 ∧
      (∀ z ∈ e.source, z 0 = 0 → (e z) 0 = 0 ∧ u (e z) = 0) := by
  classical
  obtain ⟨Φ,hxΦ,hΦ,hΦi,hA,hAB,hΦbase⟩ :=
    actual_neat_boundary_sphere_slice_v480 f x hx
  obtain ⟨Ψ,hyΨ,hΨ,hΨi,hB,hBB,hΨbase⟩ :=
    actual_neat_boundary_sphere_slice_v480 g y hyb
  have hyΦ : E.toSphere (g.toFun y) ∈ Φ.source := by rwa [hy]
  let O₀ := {z : E2 | (z,0) ∈ Ψ.target ∧ Ψ.symm (z,0) ∈ Φ.source}
  let O := O₀
  let P := fun z : E2 => Φ (Ψ.symm (z,0))
  let p := (Ψ (E.toSphere (g.toFun y))).1
  have hBnormal : (Ψ (E.toSphere (g.toFun y))).2=0 := by
    have hh : Ψ (E.toSphere (g.toFun y)) ∈
        Ψ.target ∩ (range (𝓡∂ 2) ×ˢ ({0}:Set ℝ)) := by
      rw [← hB]
      exact mem_image_of_mem Ψ ⟨hyΨ,⟨y,rfl⟩⟩
    exact hh.2.2
  have hpair : Ψ (E.toSphere (g.toFun y))=(p,0) := Prod.ext rfl hBnormal
  obtain ⟨hO₀,hP,hPi⟩ := native_interior_slice_transition_v475 Φ Ψ hΦ hΦi hΨ hΨi
  have hpO : p ∈ O := by
    refine ⟨?_, ?_⟩
    · rw [← hpair]; exact Ψ.map_source hyΨ
    · rw [← hpair, Ψ.left_inv hyΨ]; exact hyΦ
  have hO : IsOpen O := hO₀
  have hPO : ContDiffOn ℝ ∞ P O := hP
  have hpnormal : fderiv ℝ (fun z => (P z).2) p = 0 := by
    have hn := arbitrary_tangency_slice_normal_derivative_v480 f g x y (f.toFun x)
      rfl hy ht Φ Ψ hΦ hΨ hΨi hxΦ (hy ▸ hyΨ) hA hB hP
    simpa only [p, P, hy] using hn
  have hPpoint : P p=Φ (E.toSphere (g.toFun y)) := by
    change Φ (Ψ.symm (p,0))=Φ (E.toSphere (g.toFun y))
    rw [← hpair,Ψ.left_inv hyΨ]
  have hpzero : (P p).2 = 0 := by
    rw [hPpoint, hy]
    have hh : Φ (E.toSphere (f.toFun x)) ∈
        Φ.target ∩ (range (𝓡∂ 2) ×ˢ ({0}:Set ℝ)) := by
      rw [← hA]
      exact mem_image_of_mem Φ ⟨hxΦ, ⟨x, rfl⟩⟩
    exact hh.2.2
  obtain ⟨e,u,hpe,heO,heS,heI,hu,hgraph,hgraphS,himage⟩ :=
    native_interior_graph_of_projection_v475 O hO P hPO p hpO (hPi p hpO) hpnormal
  have hz : u (e p)=0 := by
    have hh := congrArg Prod.snd (hgraphS p hpe)
    exact hh.symm.trans hpzero
  have hgrad : fderiv ℝ u (e p)=0 := by
    have hUs : e.source ∈ 𝓝 p := e.open_source.mem_nhds hpe
    have hevent : (fun z => (P z).2) =ᶠ[𝓝 p] u ∘ e := by
      filter_upwards [hUs] with z hz
      exact congrArg Prod.snd (hgraphS z hz)
    have hUd : DifferentiableAt ℝ u (e p) :=
      (hu.contDiffAt (e.open_target.mem_nhds (e.map_source hpe))).differentiableAt (by simp)
    have hEd : DifferentiableAt ℝ e p :=
      (heS.contDiffAt (e.open_source.mem_nhds hpe)).differentiableAt (by simp)
    have hId : DifferentiableAt ℝ e.symm (e p) :=
      (heI.contDiffAt (e.open_target.mem_nhds (e.map_source hpe))).differentiableAt (by simp)
    have hev : (fun z : E2 => z) =ᶠ[𝓝 p] e.symm ∘ e := by
      filter_upwards [hUs] with z hz
      exact (e.left_inv hz).symm
    have hInv := (hId.hasFDerivAt.comp p hEd.hasFDerivAt).congr_of_eventuallyEq hev
    have hProd : (fderiv ℝ e.symm (e p)).comp (fderiv ℝ e p)=ContinuousLinearMap.id ℝ E2 :=
      hInv.unique (hasFDerivAt_id p)
    have heInv : (fderiv ℝ e p).IsInvertible := by
      have hi : Function.Injective (fderiv ℝ e p) := by
        intro a b hab
        have hh := congrArg (fun L : E2 →L[ℝ] E2 => L a) hProd
        have hk := congrArg (fun L : E2 →L[ℝ] E2 => L b) hProd
        simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] using
          hh.symm.trans ((congrArg (fderiv ℝ e.symm (e p)) hab).trans hk)
      exact ⟨(LinearEquiv.ofBijective _ ⟨hi,LinearMap.injective_iff_surjective.mp hi⟩).toContinuousLinearEquiv,rfl⟩
    have hcomp : (fderiv ℝ u (e p)).comp (fderiv ℝ e p)=0 := by
      rw [← fderiv_comp p hUd hEd,← hevent.fderiv_eq]
      exact hpnormal
    have hdu : fderiv ℝ u (e p)=0 := by
      ext v
      obtain ⟨w,rfl⟩ := heInv.surjective v
      exact congrArg (fun L : E2 →L[ℝ] ℝ => L w) hcomp
    exact hdu
  have hep0 : (e p) 0 = 0 := by
    have hh := congrArg Prod.fst (hgraphS p hpe)
    rw [hPpoint,hy] at hh
    change (Φ (E.toSphere (f.toFun x))).1 = e p at hh
    rwa [← hh]
  have hSphereBoundary : (E.toSphere ∘ f.toFun) '' S.boundary =
      (E.toSphere ∘ g.toFun) '' B.boundary := by
    calc
      _ = E.toSphere '' (f.toFun '' S.boundary) := (image_image _ _ _).symm
      _ = E.toSphere '' (g.toFun '' B.boundary) := congrArg (fun s => E.toSphere '' s) hboundary
      _ = _ := image_image _ _ _
  have hflat (z : E2) (hz : z ∈ e.source) (hz0 : z 0 = 0) :
      (e z) 0 = 0 ∧ u (e z) = 0 := by
    have hOZ := heO hz
    have hpB : Ψ.symm (z,0) ∈ (E.toSphere ∘ g.toFun) '' B.boundary := by
      have hc : (z,(0:ℝ)) ∈ Ψ '' (Ψ.source ∩ (E.toSphere ∘ g.toFun) '' B.boundary) := by
        rw [hBB]
        exact ⟨hOZ.1,⟨hz0,rfl⟩⟩
      obtain ⟨q,⟨hqS,hqB⟩,heq⟩ := hc
      have hqe : Ψ.symm (z,0) = q := by rw [← heq,Ψ.left_inv hqS]
      rwa [hqe]
    have hpA : Ψ.symm (z,0) ∈ (E.toSphere ∘ f.toFun) '' S.boundary := hSphereBoundary.symm ▸ hpB
    have hc : Φ (Ψ.symm (z,0)) ∈
        Φ '' (Φ.source ∩ (E.toSphere ∘ f.toFun) '' S.boundary) :=
      mem_image_of_mem Φ (And.intro hOZ.2 hpA)
    rw [hAB] at hc
    change P z ∈ _ at hc
    rw [hgraphS z hz] at hc
    exact ⟨hc.2.1,hc.2.2⟩
  refine ⟨Φ,Ψ,O,p,e,u,hy,rfl,hO,hpO,hpe,heO,hΦ,hΦi,hΨ,hΨi,hA,hB,hAB,hBB,
    ⟨hxΦ,?_⟩,hpair,heS,heI,hu,hz,hgrad,hgraph,hgraphS,hΨbase,hep0,hflat⟩
  rwa [← hy] 

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3BoundaryProjectionSignsV480 -/

noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.A7Support
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

/-- A smooth boundary-preserving projection has a nonzero normal row. -/
theorem boundary_projection_normal_row_v480
    (e : OpenPartialHomeomorph E2 E2) (p : E2) (hp : p ∈ e.source)
    (hp0 : p 0 = 0) (he : ContDiffOn ℝ ∞ e e.source)
    (hei : ContDiffOn ℝ ∞ e.symm e.target)
    (hb : ∀ z ∈ e.source, z 0 = 0 → (e z) 0 = 0) :
    ∃ c : ℝ, c ≠ 0 ∧
      fderiv ℝ (fun z : E2 => (e z) 0) p =
        c • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2) := by
  let q : E2 → ℝ := fun z => (e z) 0
  let L := fderiv ℝ e p
  let Q := fderiv ℝ q p
  let v0 : E2 := EuclideanSpace.single 0 1
  let c := Q v0
  have hU : e.source ∈ 𝓝 p := e.open_source.mem_nhds hp
  have hed := (he.contDiffAt hU).differentiableAt (by simp)
  have hqd : DifferentiableAt ℝ q p :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).differentiableAt.comp p hed
  have hpa : boundaryProjection p = p := boundaryProjection_fix hp0
  have hpt : Tendsto boundaryProjection (𝓝 p) (𝓝 p) := by
    simpa only [hpa] using boundaryProjection.continuous.continuousAt (x := p) |>.tendsto
  have hzero : q ∘ boundaryProjection =ᶠ[𝓝 p] fun _ => (0 : ℝ) := by
    filter_upwards [hpt.eventually hU] with z hz
    exact hb _ hz (boundaryProjection_zero z)
  have hcomp : Q.comp boundaryProjection = 0 := by
    have hh := ((hpa.symm ▸ hqd).hasFDerivAt.comp p boundaryProjection.hasFDerivAt)
      |>.congr_of_eventuallyEq hzero.symm
    simpa only [hpa] using hh.unique (hasFDerivAt_const (0 : ℝ) p)
  have hrow : Q = c • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2) := by
    ext v
    have hv : v = boundaryProjection v + v 0 • v0 := by
      rw [← boundaryProjection_difference]
      abel
    have hQv : Q (boundaryProjection v) = 0 :=
      congrArg (fun D : E2 →L[ℝ] ℝ => D v) hcomp
    calc
      Q v = Q (boundaryProjection v) + v 0 * Q v0 := by
        conv_lhs => rw [hv]
        rw [map_add,map_smul,smul_eq_mul]
      _ = (c • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)) v := by
        simp only [hQv,zero_add,ContinuousLinearMap.smul_apply,
          EuclideanSpace.proj,PiLp.proj_apply,smul_eq_mul,c]
        ring
  have hI := (hei.contDiffAt (e.open_target.mem_nhds (e.map_source hp))).differentiableAt (by simp)
  have hId : (fun z : E2 => z) =ᶠ[𝓝 p] e.symm ∘ e := by
    filter_upwards [hU] with z hz
    exact (e.left_inv hz).symm
  have hprod : (fderiv ℝ e.symm (e p)).comp L = ContinuousLinearMap.id ℝ E2 :=
    (hI.hasFDerivAt.comp p hed.hasFDerivAt |>.congr_of_eventuallyEq hId).unique (hasFDerivAt_id p)
  have hLi : Injective L := by
    intro a b hab
    have ha := congrArg (fun D : E2 →L[ℝ] E2 => D a) hprod
    have hb' := congrArg (fun D : E2 →L[ℝ] E2 => D b) hprod
    simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] using
      ha.symm.trans ((congrArg (fderiv ℝ e.symm (e p)) hab).trans hb')
  have hLs : Surjective L := LinearMap.injective_iff_surjective.mp hLi
  have hqrow : (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).comp L = Q := by
    exact ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt.comp p hed.hasFDerivAt).fderiv.symm
  refine ⟨c,?_,hrow⟩
  intro hc
  obtain ⟨v,hv⟩ := hLs v0
  have hz := congrArg (fun D : E2 →L[ℝ] ℝ => D v) hqrow
  rw [hrow,hc,zero_smul] at hz
  simpa [ContinuousLinearMap.comp_apply,hv,v0,EuclideanSpace.single,PiLp.single_apply] using hz

private theorem scalar_sign_of_half_error_v480 {a b : ℝ}
    (h : |a-b| ≤ |b| / 2) :
    (a = 0 ↔ b = 0) ∧ (0 < a ↔ 0 < b) ∧ (0 ≤ a ↔ 0 ≤ b) := by
  have hl := neg_abs_le (a-b)
  have hu := le_abs_self (a-b)
  rcases lt_trichotomy b 0 with hb | hb | hb
  · rw [abs_of_neg hb] at h
    have ha : a < 0 := by linarith
    simp [ha.ne,ha.ne',hb.ne,hb.ne',not_lt_of_ge ha.le,not_lt_of_ge hb.le,
      not_le_of_gt ha,not_le_of_gt hb]
  · subst b
    have ha : a = 0 := by
      simp only [sub_zero,abs_zero,zero_div] at h
      exact abs_eq_zero.mp (le_antisymm h (abs_nonneg a))
    simp [ha]
  · rw [abs_of_pos hb] at h
    have ha : 0 < a := by linarith
    simp [ha.ne',hb.ne',ha,hb,ha.le,hb.le]

/-- Strict differentiability and the actual flat boundary determine all signs,
including a possible reversal of the normal direction. -/
theorem signed_boundary_projection_v480 {q : E2 → ℝ} {p : E2}
    (hp : p 0 = 0) {c : ℝ} (hc : c ≠ 0)
    (hq : HasStrictFDerivAt q (c • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)) p)
    (hb : ∀ᶠ z in 𝓝 p, z 0 = 0 → q z = 0) :
    ∀ᶠ z in 𝓝 p,
      (q z = 0 ↔ z 0 = 0) ∧
      (0 < q z ↔ 0 < c * z 0) ∧ (0 ≤ q z ↔ 0 ≤ c * z 0) := by
  have hpa := boundaryProjection_fix hp
  have hpt : Tendsto boundaryProjection (𝓝 p) (𝓝 p) := by
    simpa only [hpa] using boundaryProjection.continuous.continuousAt (x := p) |>.tendsto
  have ht := tendsto_id.prodMk_nhds hpt
  have hbound := ht.eventually (hq.isLittleO.bound (half_pos (abs_pos.mpr hc)))
  filter_upwards [hbound,hpt.eventually hb] with z hz hzero
  have hqzero := hzero (boundaryProjection_zero z)
  have hnorm : ‖z-boundaryProjection z‖ = |z 0| := by
    rw [boundaryProjection_difference,norm_smul]
    simp [PiLp.norm_single,Real.norm_eq_abs]
  have he : |q z-c*z 0| ≤ |c*z 0| / 2 := by
    have hh : |q z-c*z 0| ≤ |c| / 2 * |z 0| := by
      simpa only [id_eq,hqzero,sub_zero,ContinuousLinearMap.smul_apply,EuclideanSpace.proj,
        PiLp.proj_apply,smul_eq_mul,PiLp.sub_apply,boundaryProjection_zero,hnorm,Real.norm_eq_abs] using hz
    rw [abs_mul]
    nlinarith
  obtain ⟨h0,hp',hn⟩ := scalar_sign_of_half_error_v480 he
  exact ⟨h0.trans (mul_eq_zero_iff_left hc),hp',hn⟩

/-- The common graph projection transports its actual boundary and either
preserves or reverses the two halfspaces, with no assumed sign. -/
theorem boundary_graph_projection_signs_v480
    (e : OpenPartialHomeomorph E2 E2) (p : E2) (hp : p ∈ e.source)
    (hp0 : p 0 = 0) (he : ContDiffOn ℝ ∞ e e.source)
    (hei : ContDiffOn ℝ ∞ e.symm e.target)
    (hb : ∀ z ∈ e.source, z 0 = 0 → (e z) 0 = 0) :
    ∃ c : ℝ, c ≠ 0 ∧
      ∀ᶠ z in 𝓝 p,
      ((e z) 0 = 0 ↔ z 0 = 0) ∧
      (0 < (e z) 0 ↔ 0 < c * z 0) ∧ (0 ≤ (e z) 0 ↔ 0 ≤ c * z 0) := by
  obtain ⟨c,hc,hrow⟩ := boundary_projection_normal_row_v480 e p hp hp0 he hei hb
  have hq : ContDiffAt ℝ ∞ (fun z : E2 => (e z) 0) p :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff.contDiffAt.comp p
      (he.contDiffAt (e.open_source.mem_nhds hp))
  have hqd : HasFDerivAt (fun z : E2 => (e z) 0)
      (c • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)) p := by
    rw [← hrow]
    exact (hq.differentiableAt (by simp)).hasFDerivAt
  exact ⟨c,hc,signed_boundary_projection_v480 hp0 hc
    (hq.hasStrictFDerivAt' hqd (by simp))
    (by filter_upwards [e.open_source.mem_nhds hp] with z hz; exact hb z hz)⟩

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3BoundaryCommonCylinderV480 -/
noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
universe u v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- An actual boundary common graph has a whole sphere cylinder with exact
halfspace membership, signed projection and the same zero boundary height. -/
theorem native_boundary_common_graph_cylinder_v480
    {S : CompactOrientedSurface.{u}} {B : CompactOrientedSurface.{v}}
    (f : NeatEmbedding S E.Carrier) (g : NeatEmbedding B E.Carrier)
    (r : E.Carrier)
    (Φ Ψ : OpenPartialHomeomorph ThreeSphere (E2 × ℝ))
    (hΦ : ContMDiffOn (𝓡 3) 𝓘(ℝ,E2 × ℝ) ∞ Φ Φ.source)
    (hΦi : ContMDiffOn 𝓘(ℝ,E2 × ℝ) (𝓡 3) ∞ Φ.symm Φ.target)
    (hrΦ : E.toSphere r ∈ Φ.source) (hrΨ : E.toSphere r ∈ Ψ.source)
    (hA : Φ '' (Φ.source ∩ range (E.toSphere ∘ f.toFun)) =
      Φ.target ∩ (range (𝓡∂ 2) ×ˢ ({0}:Set ℝ)))
    (hB : Ψ '' (Ψ.source ∩ range (E.toSphere ∘ g.toFun)) =
      Ψ.target ∩ (range (𝓡∂ 2) ×ˢ ({0}:Set ℝ)))
    (p : E2) (e : OpenPartialHomeomorph E2 E2) (u : E2 → ℝ)
    (hp : p ∈ e.source) (hrpair : Ψ (E.toSphere r)=(p,0))
    (heO : e.source ⊆ {z : E2 | (z,0) ∈ Ψ.target ∧ Ψ.symm (z,0) ∈ Φ.source})
    (hu : ContDiffOn ℝ ∞ u e.target) (hup : u (e p)=0)
    (hgraph : ∀ z ∈ e.target, Φ (Ψ.symm (e.symm z,0))=(z,u z))
    (hgraphS : ∀ z ∈ e.source, Φ (Ψ.symm (z,0))=(e z,u (e z)))
    (heS : ContDiffOn ℝ ∞ e e.source)
    (heI : ContDiffOn ℝ ∞ e.symm e.target)
    (hp0 : p 0 = 0) (hebase : (e p) 0 = 0)
    (hflat : ∀ z ∈ e.source, z 0 = 0 → (e z) 0 = 0 ∧ u (e z) = 0) :
    ∃ c : SmoothAmbientChart ThreeSphere, ∃ O : Set E2, ∃ η k : ℝ,
      IsOpen O ∧ e p ∈ O ∧ O ⊆ e.target ∧ 0 < η ∧
      k ≠ 0 ∧ c.chart.source ⊆ Φ.source ∧
      (∀ z ∈ O, ((e.symm z) 0 = 0 ↔ z 0 = 0) ∧
        (0 < z 0 ↔ 0 < k * (e.symm z) 0) ∧
        (0 ≤ z 0 ↔ 0 ≤ k * (e.symm z) 0)) ∧
      (∀ z ∈ O, z 0 = 0 → u z = 0) ∧
      c.chart.target = native_interior_graph_splitting_v475 '' (O ×ˢ Ioo (-η) η) ∧
      (∀ a, c.chart a=native_interior_graph_splitting_v475 (Φ a)) ∧
      (∀ y, c.chart.symm y=Φ.symm (native_interior_graph_splitting_v475.symm y)) ∧
      (∀ z ∈ O, jetPoint (z,0,0) ∈ c.chart.target ∧ jetPoint (z,u z,0) ∈ c.chart.target) ∧
      (∀ z ∈ O, c.chart.symm (jetPoint (z,0,0)) ∈ range (E.toSphere ∘ f.toFun) ↔ 0 ≤ z 0) ∧
      (∀ z ∈ O, c.chart.symm (jetPoint (z,u z,0)) ∈ range (E.toSphere ∘ g.toFun) ↔ 0 ≤ (e.symm z) 0) ∧
      (∀ a : S, E.toSphere (f.toFun a) ∈ c.chart.source →
        (c.chart (E.toSphere (f.toFun a))) 2=0) ∧
      (∀ a : B, E.toSphere (g.toFun a) ∈ c.chart.source →
        (c.chart (E.toSphere (g.toFun a))) 2=
        u (native_collar_base_v475 (c.chart (E.toSphere (g.toFun a))))) := by
  classical
  obtain ⟨k,hk,hsigns⟩ := boundary_graph_projection_signs_v480 e p hp hp0 heS heI
    (fun z hz hz0 => (hflat z hz hz0).1)
  obtain ⟨W,hW,hWo,hpW⟩ := mem_nhds_iff.mp hsigns
  let W0 := e.source ∩ W
  have hW0 : IsOpen W0 := e.open_source.inter hWo
  have hpW0 : p ∈ W0 := ⟨hp,hpW⟩
  let U := Φ.source ∩ (Ψ.source ∩ Ψ ⁻¹' (Prod.fst ⁻¹' W0))
  have hU : IsOpen U := Φ.open_source.inter
    (Ψ.isOpen_inter_preimage (hW0.preimage continuous_fst))
  have hrU : E.toSphere r ∈ U := by
    refine ⟨hrΦ,hrΨ,?_⟩
    change (Ψ (E.toSphere r)).1 ∈ W0
    rwa [hrpair]
  obtain ⟨c₀,hc₀U,hc₀,hc₀i⟩ := native_interior_slice_chart_restriction_v475 Φ hΦ hΦi
    U hU (fun a ha => ha.1)
  have hrΦpair : Φ (E.toSphere r)=(e p,0) := by
    have hh := hgraphS p hp
    rw [← hrpair,Ψ.left_inv hrΨ,hup] at hh
    exact hh
  have hrT : native_interior_graph_splitting_v475 (e p,0) ∈ c₀.chart.target := by
    rw [← hrΦpair,← hc₀]
    exact c₀.chart.map_source (hc₀U ▸ hrU)
  let Z := native_interior_graph_splitting_v475 ⁻¹' c₀.chart.target
  have hZ : IsOpen Z := c₀.chart.open_target.preimage native_interior_graph_splitting_v475.continuous
  obtain ⟨N,I,hN,hpN,hI,h0I,hNI⟩ := mem_nhds_prod_iff'.mp (hZ.mem_nhds hrT)
  obtain ⟨η,hη,hηI⟩ := Metric.mem_nhds_iff.mp (hI.mem_nhds h0I)
  have hinterval : Ioo (-η) η ⊆ I := by
    intro t ht
    apply hηI
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_lt] using (show -η < t ∧ t < η from ht)
  let O := ((N ∩ e.target) ∩ e '' W0) ∩ u ⁻¹' Ioo (-η) η
  have hO' : IsOpen O := by
    have hh : IsOpen (e.target ∩ u ⁻¹' Ioo (-η) η) :=
      hu.continuousOn.isOpen_inter_preimage e.open_target isOpen_Ioo
    simpa [O,inter_assoc,inter_left_comm,inter_comm] using
      ((hN.inter (e.isOpen_image_of_subset_source hW0 inter_subset_left)).inter hh)
  have hpO : e p ∈ O := by
    exact ⟨⟨⟨hpN,e.map_source hp⟩,⟨p,hpW0,rfl⟩⟩,by change -η < u (e p) ∧ u (e p) < η; rw [hup]; exact ⟨by linarith,hη⟩⟩
  let V := native_interior_graph_splitting_v475 '' (O ×ˢ Ioo (-η) η)
  have hV : IsOpen V := native_interior_graph_splitting_v475.toHomeomorph.isOpenMap _
    (hO'.prod isOpen_Ioo)
  have hVc : V ⊆ c₀.chart.target := by
    rintro y ⟨⟨z,t⟩,⟨hz,ht⟩,rfl⟩
    exact hNI ⟨hz.1.1.1,hinterval ht⟩
  obtain ⟨c,hcV,hcc,hc,hci,hcsource⟩ := native_interior_chart_restrict_target_v475 c₀ V hV hVc
  have hcΦ : ∀ a, c.chart a=native_interior_graph_splitting_v475 (Φ a) :=
    fun a => (hc a).trans (hc₀ a)
  have hciΦ : ∀ y, c.chart.symm y=Φ.symm (native_interior_graph_splitting_v475.symm y) :=
    fun y => (hci y).trans (hc₀i y)
  have hcU : c.chart.source ⊆ U := by intro a ha; rw [← hc₀U]; exact hcc ha
  have hpoints (z : E2) (hz : z ∈ O) :
      jetPoint (z,0,0) ∈ c.chart.target ∧ jetPoint (z,u z,0) ∈ c.chart.target := by
    rw [hcV]
    exact ⟨⟨(z,0),⟨hz,by exact ⟨by linarith,hη⟩⟩,rfl⟩,
      ⟨(z,u z),⟨hz,hz.2⟩,rfl⟩⟩
  have hsplit (z : E2) (t : ℝ) : native_interior_graph_splitting_v475.symm (jetPoint (z,t,0))=(z,t) :=
    native_interior_graph_splitting_v475.symm_apply_apply (z,t)
  have hbase (z : E2) (t : ℝ) : native_collar_base_v475 (jetPoint (z,t,0))=z := by
    apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
    funext i
    fin_cases i <;> simp [native_collar_base_v475,jetPoint]
  have hInvW (z : E2) (hz : z ∈ O) : e.symm z ∈ W0 := by
    obtain ⟨w,hw,heq⟩ := hz.1.2
    rw [← heq,e.left_inv hw.1]
    exact hw
  have hOsign (z : E2) (hz : z ∈ O) :
      ((e.symm z) 0 = 0 ↔ z 0 = 0) ∧
      (0 < z 0 ↔ 0 < k * (e.symm z) 0) ∧
      (0 ≤ z 0 ↔ 0 ≤ k * (e.symm z) 0) := by
    have hh := hW (hInvW z hz).2
    change ((e (e.symm z)) 0 = 0 ↔ (e.symm z) 0 = 0) ∧
      (0 < (e (e.symm z)) 0 ↔ 0 < k * (e.symm z) 0) ∧
      (0 ≤ (e (e.symm z)) 0 ↔ 0 ≤ k * (e.symm z) 0) at hh
    rw [e.right_inv hz.1.1.2] at hh
    exact ⟨hh.1.symm,hh.2⟩
  have hOzero (z : E2) (hz : z ∈ O) (hz0 : z 0 = 0) : u z = 0 := by
    have hh := (hflat _ (hInvW z hz).1 ((hOsign z hz).1.mpr hz0)).2
    simpa only [e.right_inv hz.1.1.2] using hh
  refine ⟨c,O,η,k,hO',hpO,(fun z hz => hz.1.1.2),hη,hk,
    (fun a ha => (hcU ha).1),hOsign,hOzero,hcV,
    hcΦ,hciΦ,hpoints,?_,?_,?_,?_⟩
  · intro z hz
    have ht := (hpoints z hz).1
    have hs := (hcU (c.chart.map_target ht)).1
    have hcoord : Φ (c.chart.symm (jetPoint (z,0,0)))=(z,0) := by
      apply native_interior_graph_splitting_v475.injective
      rw [← hcΦ,c.chart.right_inv ht]
      rfl
    constructor
    · intro hrange
      have hh : (z,0) ∈ Φ.target ∩ (range (𝓡∂ 2) ×ˢ ({0}:Set ℝ)) := by
        rw [← hA,← hcoord]
        exact mem_image_of_mem Φ ⟨hs,hrange⟩
      simpa only [range_modelWithCornersEuclideanHalfSpace,mem_setOf_eq] using hh.2.1
    · intro hz0
      have hh : (z,0) ∈ Φ '' (Φ.source ∩ range (E.toSphere ∘ f.toFun)) := by
        rw [hA]
        refine ⟨hcoord ▸ Φ.map_source hs,?_,rfl⟩
        simpa only [range_modelWithCornersEuclideanHalfSpace,mem_setOf_eq] using hz0
      obtain ⟨a,⟨ha,haR⟩,heq⟩ := hh
      rwa [Φ.injOn ha hs (heq.trans hcoord.symm)] at haR
  · intro z hz
    have he := e.map_target hz.1.1.2
    have hh := heO he
    have hparam := hgraph z hz.1.1.2
    have hsym : c.chart.symm (jetPoint (z,u z,0))=Ψ.symm (e.symm z,0) := by
      rw [hciΦ,hsplit,← hparam,Φ.left_inv hh.2]
    rw [hsym]
    constructor
    · intro hrange
      have hs := Ψ.map_target hh.1
      have hcoord := Ψ.right_inv hh.1
      have hmem : (e.symm z,0) ∈ Ψ.target ∩ (range (𝓡∂ 2) ×ˢ ({0}:Set ℝ)) := by
        rw [← hB,← hcoord]
        exact mem_image_of_mem Ψ ⟨hs,hrange⟩
      simpa only [range_modelWithCornersEuclideanHalfSpace,mem_setOf_eq] using hmem.2.1
    · intro hz0
      have hmem : (e.symm z,0) ∈ Ψ '' (Ψ.source ∩ range (E.toSphere ∘ g.toFun)) := by
        rw [hB]
        refine ⟨hh.1,?_,rfl⟩
        simpa only [range_modelWithCornersEuclideanHalfSpace,mem_setOf_eq] using hz0
      obtain ⟨a,⟨ha,haR⟩,heq⟩ := hmem
      rwa [← heq,Ψ.left_inv ha]
  · intro a ha
    have huA := (hcU ha).1
    have hh : Φ (E.toSphere (f.toFun a)) ∈ Φ.target ∩
        (range (𝓡∂ 2) ×ˢ ({0}:Set ℝ)) := by
      rw [← hA]
      exact mem_image_of_mem Φ ⟨huA,⟨a,rfl⟩⟩
    rw [hcΦ]
    simpa [jetPoint] using hh.2.2
  · intro a ha
    have huB := (hcU ha).2
    have hh : Ψ (E.toSphere (g.toFun a)) ∈ Ψ.target ∩
        (range (𝓡∂ 2) ×ˢ ({0}:Set ℝ)) := by
      rw [← hB]
      exact mem_image_of_mem Ψ ⟨huB.1,⟨a,rfl⟩⟩
    let z := (Ψ (E.toSphere (g.toFun a))).1
    have hpair : Ψ (E.toSphere (g.toFun a))=(z,0) := Prod.ext rfl hh.2.2
    have hg := hgraphS z huB.2.1
    rw [← hpair,Ψ.left_inv huB.1] at hg
    rw [hcΦ,hg]
    change u (e z)=u (native_collar_base_v475 (jetPoint (e z,u (e z),0)))
    rw [hbase]

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3ArbitraryCommonSliceGraphV480 -/
noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
set_option maxHeartbeats 300000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- Common smooth graph charts at an arbitrary actual interior tangent
plane coincidence. No image-agreement-germ hypothesis is used. -/
theorem native_actual_arbitrary_common_interior_graph_v480
    {S : CompactOrientedSurface.{0}} {B : CompactOrientedSurface.{0}}
    (f : NeatEmbedding S E.Carrier) (g : NeatEmbedding B E.Carrier)
    (x : (𝓡∂ 2).interior S) (y : (𝓡∂ 2).interior B)
    (hy : g.toFun y = f.toFun x)
    (ht : tangentPlaneAt f x (f.toFun x) rfl =
      tangentPlaneAt g y (f.toFun x) hy) :
    ∃ Φ Ψ : OpenPartialHomeomorph ThreeSphere (E2 × ℝ),
    ∃ O : Set E2, ∃ p : E2,
    ∃ e : OpenPartialHomeomorph E2 E2, ∃ u : E2 → ℝ,
      g.toFun y=f.toFun x ∧
      O = {z : E2 | (z,0) ∈ Ψ.target ∧ Ψ.symm (z,0) ∈ Φ.source} ∩ interior (range (𝓡∂ 2)) ∧ IsOpen O ∧ p ∈ O ∧ p ∈ e.source ∧ e.source ⊆ O ∧
      ContMDiffOn (𝓡 3) 𝓘(ℝ,E2 × ℝ) ∞ Φ Φ.source ∧
      ContMDiffOn 𝓘(ℝ,E2 × ℝ) (𝓡 3) ∞ Φ.symm Φ.target ∧
      ContMDiffOn (𝓡 3) 𝓘(ℝ,E2 × ℝ) ∞ Ψ Ψ.source ∧
      ContMDiffOn 𝓘(ℝ,E2 × ℝ) (𝓡 3) ∞ Ψ.symm Ψ.target ∧
      Φ '' (Φ.source ∩ range (E.toSphere ∘ f.toFun)) =
        Φ.target ∩ (range (𝓡∂ 2) ×ˢ ({0}:Set ℝ)) ∧
      Ψ '' (Ψ.source ∩ range (E.toSphere ∘ g.toFun)) =
        Ψ.target ∩ (range (𝓡∂ 2) ×ˢ ({0}:Set ℝ)) ∧
      E.toSphere (f.toFun x) ∈ Φ.source ∩ Ψ.source ∧
      Ψ (E.toSphere (g.toFun y))=(p,0) ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      ContDiffOn ℝ ∞ u e.target ∧ u (e p)=0 ∧ fderiv ℝ u (e p)=0 ∧
      (∀ z ∈ e.target, Φ (Ψ.symm (e.symm z,0))=(z,u z)) ∧
      (∀ z ∈ e.source, Φ (Ψ.symm (z,0))=(e z,u (e z))) ∧
      (e p) ∈ interior (range (𝓡∂ 2)) := by
  classical
  have hxnb : (x : S) ∉ S.boundary := by
    have hn (a : S) (ha : a ∈ (𝓡∂ 2).interior S) : a ∉ S.boundary := by
      rw [← (𝓡∂ 2).compl_boundary] at ha
      exact ha
    exact hn x x.property
  have hynb : (y : B) ∉ B.boundary := by
    have hn (a : B) (ha : a ∈ (𝓡∂ 2).interior B) : a ∉ B.boundary := by
      rw [← (𝓡∂ 2).compl_boundary] at ha
      exact ha
    exact hn y y.property
  obtain ⟨Φ,hxΦ,hΦ,hΦi,hA,hΦbase⟩ :=
    native_actual_interior_slice_chart_with_base_v475 f x hxnb
  obtain ⟨Ψ,hyΨ,hΨ,hΨi,hB,hΨbase⟩ :=
    native_actual_interior_slice_chart_with_base_v475 g y hynb
  have hyΦ : E.toSphere (g.toFun y) ∈ Φ.source := by rwa [hy]
  let O₀ := {z : E2 | (z,0) ∈ Ψ.target ∧ Ψ.symm (z,0) ∈ Φ.source}
  let O := O₀ ∩ interior (range (𝓡∂ 2))
  let P := fun z : E2 => Φ (Ψ.symm (z,0))
  let p := (Ψ (E.toSphere (g.toFun y))).1
  have hBnormal : (Ψ (E.toSphere (g.toFun y))).2=0 := by
    have hh : Ψ (E.toSphere (g.toFun y)) ∈
        Ψ.target ∩ (range (𝓡∂ 2) ×ˢ ({0}:Set ℝ)) := by
      rw [← hB]
      exact mem_image_of_mem Ψ ⟨hyΨ,⟨y,rfl⟩⟩
    exact hh.2.2
  have hpair : Ψ (E.toSphere (g.toFun y))=(p,0) := Prod.ext rfl hBnormal
  obtain ⟨hO₀,hP,hPi⟩ := native_interior_slice_transition_v475 Φ Ψ hΦ hΦi hΨ hΨi
  have hpO : p ∈ O := by
    refine ⟨⟨?_, ?_⟩, hΨbase⟩
    · rw [← hpair]; exact Ψ.map_source hyΨ
    · rw [← hpair, Ψ.left_inv hyΨ]; exact hyΦ
  have hO : IsOpen O := hO₀.inter isOpen_interior
  have hPO : ContDiffOn ℝ ∞ P O := hP.mono inter_subset_left
  have hpnormal : fderiv ℝ (fun z => (P z).2) p = 0 := by
    have hn := arbitrary_tangency_slice_normal_derivative_v480 f g x y (f.toFun x)
      rfl hy ht Φ Ψ hΦ hΨ hΨi hxΦ (hy ▸ hyΨ) hA hB hP
    simpa only [p, P, hy] using hn
  have hPpoint : P p=Φ (E.toSphere (g.toFun y)) := by
    change Φ (Ψ.symm (p,0))=Φ (E.toSphere (g.toFun y))
    rw [← hpair,Ψ.left_inv hyΨ]
  have hpzero : (P p).2 = 0 := by
    rw [hPpoint, hy]
    have hh : Φ (E.toSphere (f.toFun x)) ∈
        Φ.target ∩ (range (𝓡∂ 2) ×ˢ ({0}:Set ℝ)) := by
      rw [← hA]
      exact mem_image_of_mem Φ ⟨hxΦ, ⟨x, rfl⟩⟩
    exact hh.2.2
  obtain ⟨e,u,hpe,heO,heS,heI,hu,hgraph,hgraphS,himage⟩ :=
    native_interior_graph_of_projection_v475 O hO P hPO p hpO (hPi p hpO.1) hpnormal
  have hz : u (e p)=0 := by
    have hh := congrArg Prod.snd (hgraphS p hpe)
    exact hh.symm.trans hpzero
  have hgrad : fderiv ℝ u (e p)=0 := by
    have hUs : e.source ∈ 𝓝 p := e.open_source.mem_nhds hpe
    have hevent : (fun z => (P z).2) =ᶠ[𝓝 p] u ∘ e := by
      filter_upwards [hUs] with z hz
      exact congrArg Prod.snd (hgraphS z hz)
    have hUd : DifferentiableAt ℝ u (e p) :=
      (hu.contDiffAt (e.open_target.mem_nhds (e.map_source hpe))).differentiableAt (by simp)
    have hEd : DifferentiableAt ℝ e p :=
      (heS.contDiffAt (e.open_source.mem_nhds hpe)).differentiableAt (by simp)
    have hId : DifferentiableAt ℝ e.symm (e p) :=
      (heI.contDiffAt (e.open_target.mem_nhds (e.map_source hpe))).differentiableAt (by simp)
    have hev : (fun z : E2 => z) =ᶠ[𝓝 p] e.symm ∘ e := by
      filter_upwards [hUs] with z hz
      exact (e.left_inv hz).symm
    have hInv := (hId.hasFDerivAt.comp p hEd.hasFDerivAt).congr_of_eventuallyEq hev
    have hProd : (fderiv ℝ e.symm (e p)).comp (fderiv ℝ e p)=ContinuousLinearMap.id ℝ E2 :=
      hInv.unique (hasFDerivAt_id p)
    have heInv : (fderiv ℝ e p).IsInvertible := by
      have hi : Function.Injective (fderiv ℝ e p) := by
        intro a b hab
        have hh := congrArg (fun L : E2 →L[ℝ] E2 => L a) hProd
        have hk := congrArg (fun L : E2 →L[ℝ] E2 => L b) hProd
        simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] using
          hh.symm.trans ((congrArg (fderiv ℝ e.symm (e p)) hab).trans hk)
      exact ⟨(LinearEquiv.ofBijective _ ⟨hi,LinearMap.injective_iff_surjective.mp hi⟩).toContinuousLinearEquiv,rfl⟩
    have hcomp : (fderiv ℝ u (e p)).comp (fderiv ℝ e p)=0 := by
      rw [← fderiv_comp p hUd hEd,← hevent.fderiv_eq]
      exact hpnormal
    have hdu : fderiv ℝ u (e p)=0 := by
      ext v
      obtain ⟨w,rfl⟩ := heInv.surjective v
      exact congrArg (fun L : E2 →L[ℝ] ℝ => L w) hcomp
    exact hdu
  have hebase : e p ∈ interior (range (𝓡∂ 2)) := by
    have hh := congrArg Prod.fst (hgraphS p hpe)
    rw [hPpoint,hy] at hh
    change (Φ (E.toSphere (f.toFun x))).1 = e p at hh
    rwa [← hh]
  refine ⟨Φ,Ψ,O,p,e,u,hy,rfl,hO,hpO,hpe,heO,hΦ,hΦi,hΨ,hΨi,hA,hB,
    ⟨hxΦ,?_⟩,hpair,heS,heI,hu,hz,hgrad,hgraph,hgraphS,hebase⟩
  rwa [← hy] 

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3SphereChartExteriorV480 -/

noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
set_option maxHeartbeats 200000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

theorem sphere_interior_chart_to_exterior_v480
    (C : SmoothAmbientChart ThreeSphere)
    (hsource : C.chart.source ⊆ E.toSphere '' (𝓡∂ 3).interior E.Carrier)
    (p : E.Carrier) :
    ∃ d : OpenPartialHomeomorph E.Carrier E3,
      d.source = E.toSphere ⁻¹' C.chart.source ∧ d.target = C.chart.target ∧
      d.source ⊆ (𝓡∂ 3).interior E.Carrier ∧
      ContMDiffOn (𝓡∂ 3) 𝓘(ℝ, E3) ∞ d d.source ∧
      ContMDiffOn 𝓘(ℝ, E3) (𝓡∂ 3) ∞ d.symm d.target ∧
      (∀ a, d a = C.chart (E.toSphere a)) ∧
      (∀ y ∈ d.target, E.toSphere (d.symm y) = C.chart.symm y) := by
  classical
  letI : Nonempty E.Carrier := ⟨p⟩
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  let inverse : ThreeSphere → E.Carrier := Function.invFun E.toSphere
  have hinv (a : E.Carrier) : inverse (E.toSphere a) = a :=
    Function.leftInverse_invFun hinc.isEmbedding.injective a
  have hright (y : E3) (hy : y ∈ C.chart.target) :
      E.toSphere (inverse (C.chart.symm y)) = C.chart.symm y := by
    obtain ⟨a, ha, heq⟩ := hsource (C.chart.map_target hy)
    rw [← heq, hinv]
  let U := E.toSphere ⁻¹' C.chart.source
  have hU : IsOpen U := C.chart.open_source.preimage hinc.isEmbedding.continuous
  have hInterior : U ⊆ (𝓡∂ 3).interior E.Carrier := by
    intro a ha
    obtain ⟨b, hb, hab⟩ := hsource ha
    exact (hinc.isEmbedding.injective hab) ▸ hb
  have hiCont : ContinuousOn (inverse ∘ C.chart.symm) C.chart.target := by
    apply hinc.isEmbedding.isInducing.continuousOn_iff.mpr
    exact C.chart.continuousOn_symm.congr (fun y hy => hright y hy)
  have hiSmooth : ContMDiffOn 𝓘(ℝ, E3) (𝓡∂ 3) ∞
      (inverse ∘ C.chart.symm) C.chart.target := by
    intro y hy
    have hc : ContinuousAt (inverse ∘ C.chart.symm) y :=
      (hiCont y hy).continuousAt (C.chart.open_target.mem_nhds hy)
    have hcs : ContMDiffAt 𝓘(ℝ, E3) (𝓡 3) ∞
        (E.toSphere ∘ (inverse ∘ C.chart.symm)) y := by
      apply (C.inverse_smooth.contMDiffAt (C.chart.open_target.mem_nhds hy)).congr_of_eventuallyEq
      exact Filter.eventuallyEq_of_mem (C.chart.open_target.mem_nhds hy) (fun z hz => hright z hz)
    exact ((ContMDiffAt.iff_comp_isImmersionAt (I := 𝓘(ℝ, E3))
      (hinc.isImmersion.isImmersionAt ((inverse ∘ C.chart.symm) y))).mpr ⟨hc, hcs⟩).contMDiffWithinAt
  let d : OpenPartialHomeomorph E.Carrier E3 := {
    toFun := C.chart ∘ E.toSphere
    invFun := inverse ∘ C.chart.symm
    source := U
    target := C.chart.target
    map_source' := fun a ha => C.chart.map_source ha
    map_target' := by
      intro y hy
      change E.toSphere (inverse (C.chart.symm y)) ∈ C.chart.source
      rw [hright y hy]
      exact C.chart.map_target hy
    left_inv' := by
      intro a ha
      change inverse (C.chart.symm (C.chart (E.toSphere a))) = a
      rw [C.chart.left_inv ha, hinv]
    right_inv' := by
      intro y hy
      change C.chart (E.toSphere (inverse (C.chart.symm y))) = y
      rw [hright y hy, C.chart.right_inv hy]
    open_source := hU
    open_target := C.chart.open_target
    continuousOn_toFun := C.chart.continuousOn.comp hinc.isEmbedding.continuous.continuousOn (fun a ha => ha)
    continuousOn_invFun := hiCont }
  exact ⟨d, rfl, rfl, hInterior,
    C.smooth.comp hinc.contMDiff.contMDiffOn (fun a ha => ha), hiSmooth,
    fun _ => rfl, hright⟩

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3ArbitraryCommonCylinderV480 -/

noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
set_option maxHeartbeats 200000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- Actual arbitrary tangencies admit a common sphere cylinder excluding
every other sheet of the two original compact embeddings. -/
theorem actual_tangency_common_cylinder_v480
    {S B : CompactOrientedSurface.{0}}
    (f : NeatEmbedding S E.Carrier) (g : NeatEmbedding B E.Carrier)
    {p : E.Carrier} (hp : p ∈ interiorTangencies f g) :
    ∃ C : SmoothAmbientChart ThreeSphere, ∃ O : Set E2, ∃ eta : ℝ,
    ∃ z : E2, ∃ u : E2 → ℝ,
      IsOpen O ∧ z ∈ O ∧ 0 < eta ∧
      ContDiffOn ℝ ∞ u O ∧ u z = 0 ∧ fderiv ℝ u z = 0 ∧
      C.chart.source ⊆ E.toSphere '' (𝓡∂ 3).interior E.Carrier ∧
      C.chart.target = native_interior_graph_splitting_v475 '' (O ×ˢ Ioo (-eta) eta) ∧
      E.toSphere p ∈ C.chart.source ∧ C.chart (E.toSphere p) = graphPoint z 0 ∧
      (∀ x ∈ O, graphPoint x 0 ∈ C.chart.target ∧ graphPoint x (u x) ∈ C.chart.target) ∧
      (∀ x ∈ O, C.chart.symm (graphPoint x 0) ∈ range (E.toSphere ∘ f.toFun)) ∧
      (∀ x ∈ O, C.chart.symm (graphPoint x (u x)) ∈ range (E.toSphere ∘ g.toFun)) ∧
      (∀ a : S, E.toSphere (f.toFun a) ∈ C.chart.source →
        (C.chart (E.toSphere (f.toFun a))) 2 = 0) ∧
      (∀ b : B, E.toSphere (g.toFun b) ∈ C.chart.source →
        (C.chart (E.toSphere (g.toFun b))) 2 =
          u (graphPlaneCoordinates (C.chart (E.toSphere (g.toFun b))))) := by
  classical
  rcases hp with ⟨hpI, a, b, ha, hb, ht⟩
  have haI : a ∈ (𝓡∂ 2).interior S := by
    rw [← (𝓡∂ 2).compl_boundary]
    intro hbad
    change a ∈ S.boundary at hbad
    have hbd : f.toFun a ∈ (𝓡∂ 3).boundary E.Carrier := by
      rwa [← f.boundary_preimage] at hbad
    exact (ModelWithCorners.disjoint_interior_boundary (I := 𝓡∂ 3)
      (M := E.Carrier)).le_bot ⟨hpI, ha ▸ hbd⟩
  have hbI : b ∈ (𝓡∂ 2).interior B := by
    rw [← (𝓡∂ 2).compl_boundary]
    intro hbad
    change b ∈ B.boundary at hbad
    have hbd : g.toFun b ∈ (𝓡∂ 3).boundary E.Carrier := by
      rwa [← g.boundary_preimage] at hbad
    exact (ModelWithCorners.disjoint_interior_boundary (I := 𝓡∂ 3)
      (M := E.Carrier)).le_bot ⟨hpI, hb ▸ hbd⟩
  let x : (𝓡∂ 2).interior S := ⟨a, haI⟩
  let y : (𝓡∂ 2).interior B := ⟨b, hbI⟩
  have hy : g.toFun y = f.toFun x := hb.trans ha.symm
  have ht0 : tangentPlaneAt f x (f.toFun x) rfl =
      tangentPlaneAt g y (f.toFun x) hy := by
    cases ha
    exact ht
  obtain ⟨Φ, Ψ, O0, q, e, u, hy', hO0eq, hO0, hqO0, hqe, heO,
    hΦ, hΦi, hΨ, hΨi, hA, hB, hpSrc, hpair, heS, heI, hu, huz, hdu,
    hgraph, hgraphS, hebase⟩ := native_actual_arbitrary_common_interior_graph_v480 f g x y hy ht0
  have hpΦ : E.toSphere p ∈ Φ.source := by simpa only [x, ha] using hpSrc.1
  have hpΨ : E.toSphere p ∈ Ψ.source := by simpa only [x, ha] using hpSrc.2
  have hppair : Ψ (E.toSphere p) = (q, 0) := by simpa only [y, hb] using hpair
  obtain ⟨C, O, eta, hO, hzO, hOe, heta, hsource, htarget, hC, hCi,
    hpoints, hApoints, hBpoints, hAexact, hBexact⟩ :=
    native_interior_common_graph_cylinder_v475 f g p hpI Φ Ψ hΦ hΦi hpΦ hpΨ hA hB
      q e u hqe hppair (by simpa only [hO0eq] using heO) hu huz hgraph hgraphS hebase
  have hbase : Φ (E.toSphere p) = (e q, 0) := by
    have hh := hgraphS q hqe
    rw [← hppair, Ψ.left_inv hpΨ, huz] at hh
    exact hh
  have hCp : C.chart (E.toSphere p) = graphPoint (e q) 0 := by
    rw [hC, hbase]
    rfl
  have hpC : E.toSphere p ∈ C.chart.source := by
    have htC := (hpoints (e q) hzO).1
    have hsym : C.chart.symm (graphPoint (e q) 0) = E.toSphere p := by
      rw [hCi]
      have hsplit : native_interior_graph_splitting_v475.symm (graphPoint (e q) 0) = (e q, 0) :=
        native_interior_graph_splitting_v475.symm_apply_apply (e q, 0)
      rw [hsplit]
      rw [← hbase, Φ.left_inv hpΦ]
    exact hsym ▸ C.chart.map_target htC
  refine ⟨C, O, eta, e q, u, hO, hzO, heta, hu.mono hOe, huz, hdu,
    hsource, htarget, hpC, hCp, hpoints, hApoints, hBpoints, hAexact, ?_⟩
  intro b hbC
  exact hBexact b hbC

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3ActualInteriorGraphConstructionV480 -/

noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
set_option maxHeartbeats 300000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

private theorem graph_plane_point_v480 (x : E2) (t : ℝ) :
    graphPlaneCoordinates (graphPoint x t) = x := by
  ext i
  fin_cases i <;> simp [graphPlaneCoordinates, graphPoint]

private theorem graph_point_reconstruct_v480 (y : E3) :
    graphPoint (graphPlaneCoordinates y) (y 2) = y := by
  ext i
  fin_cases i <;> simp [graphPlaneCoordinates, graphPoint]

private theorem graph_point_add_v480 (x z : E2) (t : ℝ) :
    graphPoint x t + graphPoint z 0 = graphPoint (x + z) t := by
  ext i
  fin_cases i <;> simp [graphPoint]

private theorem graph_plane_continuous_v480 : Continuous graphPlaneCoordinates := by
  unfold graphPlaneCoordinates
  apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
  fun_prop

/-- Construct the original exterior InteriorGraph at every actual interior
tangency. Both whole original surface images are retained in the common
cylinder; all normalizations, target restrictions and base translations are
constructed from the actual embeddings. -/
theorem actual_tangency_flat_interior_graph_v480
    (A B : IncompressibleSpanningSurface.{0} E)
    {p : E.Carrier} (hp : p ∈ interiorTangencies A.1.embedding B.1.embedding) :
    ∃ c : InteriorGraph A B p, c.upper = fun _ => 0 := by
  classical
  obtain ⟨C, O, eta, z, u, hO, hzO, heta, hu, huz, hdu, hsrc, htar,
    hpC, hCp, hpts, hAs, hBs, hA, hB⟩ :=
    actual_tangency_common_cylinder_v480 A.1.embedding B.1.embedding hp
  obtain ⟨R, hR, hRO⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hzO)
  let center := graphPoint z 0
  let H := Homeomorph.addRight (-center)
  let e := C.chart.transHomeomorph H
  have heS : e.source = C.chart.source := rfl
  have heF (a : ThreeSphere) : e a = C.chart a - center := by
    simp [e, H, sub_eq_add_neg]
  have heI (y : E3) : e.symm y = C.chart.symm (y + center) := by
    change C.chart.symm (y - -center) = C.chart.symm (y + center)
    rw [sub_neg_eq_add]
  have hes : ContMDiffOn (𝓡 3) 𝓘(ℝ, E3) ∞ e e.source := by
    change ContMDiffOn (𝓡 3) 𝓘(ℝ, E3) ∞ (H ∘ C.chart) C.chart.source
    exact (show ContDiff ℝ ∞ H from contDiff_id.add contDiff_const).contMDiff.comp_contMDiffOn C.smooth
  have hei : ContMDiffOn 𝓘(ℝ, E3) (𝓡 3) ∞ e.symm e.target := by
    change ContMDiffOn 𝓘(ℝ, E3) (𝓡 3) ∞ (C.chart.symm ∘ H.symm) e.target
    apply C.inverse_smooth.comp
      (show ContDiff ℝ ∞ H.symm from contDiff_id.sub contDiff_const).contMDiff.contMDiffOn
    intro y hy
    exact hy
  let Ce : SmoothAmbientChart ThreeSphere := ⟨e, hes, hei⟩
  let V : Set E3 := {y | ‖graphPlaneCoordinates y‖ < R ∧ |y 2| < eta}
  have hV : IsOpen V :=
    (isOpen_lt graph_plane_continuous_v480.norm continuous_const).inter
      (isOpen_lt (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous.abs continuous_const)
  have hxO (x : E2) (hx : x ∈ Metric.ball (0 : E2) R) : x + z ∈ O := by
    apply hRO
    simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero] using hx
  have hVC : V ⊆ Ce.chart.target := by
    intro y hy
    change H.symm y ∈ C.chart.target
    have hHy : H.symm y = graphPoint (graphPlaneCoordinates y + z) (y 2) := by
      rw [show H.symm y = y + center by change y - -center = y + center; rw [sub_neg_eq_add], ← graph_point_reconstruct_v480 y]
      exact graph_point_add_v480 _ _ _
    rw [hHy, htar]
    refine ⟨(graphPlaneCoordinates y + z, y 2), ⟨hxO _ (by simpa only [Metric.mem_ball, dist_zero_right] using hy.1), ?_⟩, rfl⟩
    exact abs_lt.mp hy.2
  obtain ⟨Cd, hCdT, hCdS, hCdF, hCdI, hCdmem⟩ :=
    native_interior_chart_restrict_target_v475 Ce V hV hVC
  have hpCe : E.toSphere p ∈ Ce.chart.source := hpC
  have hep : Ce.chart (E.toSphere p) = 0 := by
    rw [heF, hCp]
    exact sub_self _
  have h0V : (0 : E3) ∈ V := by
    have hplane : graphPlaneCoordinates (0 : E3) = (0 : E2) := by
      ext i
      fin_cases i <;> simp [graphPlaneCoordinates]
    simpa only [V, Set.mem_setOf_eq, hplane, norm_zero, PiLp.zero_apply, abs_zero] using And.intro hR heta
  have hpCd : E.toSphere p ∈ Cd.chart.source := hCdmem _ hpCe (hep.symm ▸ h0V)
  have hCdsrc : Cd.chart.source ⊆ E.toSphere '' (𝓡∂ 3).interior E.Carrier := hCdS.trans hsrc
  obtain ⟨d, hdS, hdT, hdInt, hdSmooth, hdiSmooth, hdF, hdI⟩ :=
    sphere_interior_chart_to_exterior_v480 Cd hCdsrc p
  have hdTar : d.target = V := hdT.trans hCdT
  have hdBase : d p = 0 := by rw [hdF, hCdF, hep]
  have hpD : p ∈ d.source := by rw [hdS]; exact hpCd
  have htranslate : ContDiff ℝ ∞ (fun x : E2 => x + z) := contDiff_id.add contDiff_const
  have hlow : ContDiffOn ℝ ∞ (fun x : E2 => u (x + z)) (Metric.ball 0 R) :=
    hu.comp htranslate.contDiffOn hxO
  have hlow0 : u ((0 : E2) + z) = 0 := by simpa only [zero_add] using huz
  have hlowDeriv : fderiv ℝ (fun x : E2 => u (x + z)) 0 = 0 := by
    have hud := (hu.contDiffAt (hO.mem_nhds hzO)).differentiableAt (by simp)
    have hshift := (hasFDerivAt_id (𝕜 := ℝ) (0 : E2)).add_const z
    have huf : HasFDerivAt u (fderiv ℝ u z) (id (0 : E2) + z) := by
      simpa only [id_eq, zero_add] using hud.hasFDerivAt
    have hd := huf.comp 0 hshift
    simpa only [Function.comp_def, id_eq, zero_add, hdu, ContinuousLinearMap.zero_comp] using hd.fderiv
  have hpointV (x : E2) (t : ℝ) (hx : x ∈ Metric.ball (0 : E2) R) (ht : |t| < eta) :
      graphPoint x t ∈ V := by
    change ‖graphPlaneCoordinates (graphPoint x t)‖ < R ∧ |(graphPoint x t) 2| < eta
    rw [graph_plane_point_v480]
    exact ⟨by simpa only [Metric.mem_ball, dist_zero_right] using hx, ht⟩
  have hlowInside (x : E2) (hx : x ∈ Metric.ball (0 : E2) R) : |u (x + z)| < eta := by
    have ht := (hpts (x + z) (hxO x hx)).2
    rw [htar] at ht
    obtain ⟨⟨q, t⟩, ⟨hq, ht⟩, heq⟩ := ht
    have hheight := congrArg (fun y : E3 => y 2) heq
    change t = u (x + z) at hheight
    exact abs_lt.mpr (hheight ▸ ht)
  have hsymPoint (x : E2) (t : ℝ) (hx : x ∈ Metric.ball (0 : E2) R) (ht : |t| < eta) :
      E.toSphere (d.symm (graphPoint x t)) = C.chart.symm (graphPoint (x + z) t) := by
    rw [hdI _ (hdTar.symm ▸ hpointV x t hx ht), hCdI, heI]
    exact congrArg C.chart.symm (graph_point_add_v480 x z t)
  have hsourceC (a : E.Carrier) (ha : a ∈ d.source) : E.toSphere a ∈ C.chart.source :=
    hCdS (by simpa only [hdS, Set.mem_preimage] using ha)
  have hcoord (a : E.Carrier) : d a = C.chart (E.toSphere a) - center := by
    rw [hdF, hCdF, heF]
  have hAgraph : A.1.image ∩ d.source =
      (fun x : E2 => d.symm (graphPoint x 0)) '' Metric.ball 0 R := by
    ext a
    constructor
    · rintro ⟨⟨a0, ha0⟩, haD⟩
      have hzero : (d a) 2 = 0 := by
        rw [hcoord]
        simpa [center, graphPoint, PiLp.sub_apply, sub_zero] using
          (ha0 ▸ hA a0 (ha0.symm ▸ hsourceC a haD))
      let x := graphPlaneCoordinates (d a)
      have hx : x ∈ Metric.ball (0 : E2) R := by
        have hh := d.map_source haD
        rw [hdTar] at hh
        simpa only [Metric.mem_ball, dist_zero_right] using hh.1
      refine ⟨x, hx, ?_⟩
      have heq : graphPoint x 0 = d a := by
        rw [← hzero]
        exact graph_point_reconstruct_v480 (d a)
      dsimp only
      rw [heq, d.left_inv haD]
    · rintro ⟨x, hx, rfl⟩
      have hti : |(0 : ℝ)| < eta := by simpa using heta
      have hsrcD := d.map_target (hdTar.symm ▸ hpointV x 0 hx hti)
      obtain ⟨a, ha⟩ := hAs (x + z) (hxO x hx)
      have heq : A.1.embedding.toFun a = d.symm (graphPoint x 0) := by
        have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
        apply hinc.isEmbedding.injective
        exact ha.trans (hsymPoint x 0 hx hti).symm
      exact ⟨⟨a, heq⟩, hsrcD⟩
  have hBgraph : B.1.image ∩ d.source =
      (fun x : E2 => d.symm (graphPoint x (u (x + z)))) '' Metric.ball 0 R := by
    ext a
    constructor
    · rintro ⟨⟨b0, hb0⟩, haD⟩
      let x := graphPlaneCoordinates (d a)
      have hx : x ∈ Metric.ball (0 : E2) R := by
        have hh := d.map_source haD
        rw [hdTar] at hh
        simpa only [Metric.mem_ball, dist_zero_right] using hh.1
      have hbase : graphPlaneCoordinates (C.chart (E.toSphere a)) = x + z := by
        have hy : C.chart (E.toSphere a) = d a + center := by rw [hcoord]; abel
        rw [hy, ← graph_point_reconstruct_v480 (d a), graph_point_add_v480, graph_plane_point_v480]
      have hheight : (d a) 2 = u (x + z) := by
        rw [hcoord]
        have hh := hB b0 (hb0.symm ▸ hsourceC a haD)
        rw [hb0, hbase] at hh
        simpa [center, graphPoint, PiLp.sub_apply, sub_zero] using hh
      refine ⟨x, hx, ?_⟩
      have heq : graphPoint x (u (x + z)) = d a := by
        rw [← hheight]
        exact graph_point_reconstruct_v480 (d a)
      dsimp only
      rw [heq, d.left_inv haD]
    · rintro ⟨x, hx, rfl⟩
      have hti := hlowInside x hx
      have hsrcD := d.map_target (hdTar.symm ▸ hpointV x (u (x + z)) hx hti)
      obtain ⟨b, hb⟩ := hBs (x + z) (hxO x hx)
      have heq : B.1.embedding.toFun b = d.symm (graphPoint x (u (x + z))) := by
        have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
        apply hinc.isEmbedding.injective
        exact hb.trans (hsymPoint x (u (x + z)) hx hti).symm
      exact ⟨⟨b, heq⟩, hsrcD⟩
  exact ⟨{
    coordinates := d
    source_interior := hdInt
    smooth := hdSmooth
    inverse_smooth := hdiSmooth
    base_mem := hpD
    base_zero := hdBase
    R := R
    R_pos := hR
    eta := eta
    eta_pos := heta
    cylinder_inside := by rw [hdTar]
    lower := fun x => u (x + z)
    upper := fun _ => 0
    lower_smooth := hlow
    upper_smooth := contDiffOn_const
    lower_zero := hlow0
    upper_zero := rfl
    lower_tangent := hlowDeriv
    upper_tangent := by simp
    lower_inside := hlowInside
    upper_inside := fun _ _ => by simpa using heta
    graph_A := hAgraph
    graph_B := hBgraph }, rfl⟩


theorem actual_tangency_interior_graph_v480
    (A B : IncompressibleSpanningSurface.{0} E)
    {p : E.Carrier} (hp : p ∈ interiorTangencies A.1.embedding B.1.embedding) :
    Nonempty (InteriorGraph A B p) := by
  obtain ⟨c, _⟩ := actual_tangency_flat_interior_graph_v480 A B hp
  exact ⟨c⟩

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3ActualGraphAnalyticPackageV480 -/

noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}

/-- The complete graph/PDE/nodal clause of original B3, now with the common
graph constructed at each arbitrary original tangency. -/
theorem original_pair_actual_graph_analytic_conclusion (D : OriginalPair g J) :
    ∀ p ∈ interiorTangencies D.A.1.embedding D.B.1.embedding,
      ∃ c : InteriorGraph D.A D.B p, c.upper = (fun _ => 0) ∧
      ∃ m : ℕ, 1 ≤ m ∧ ∃ c1 c2 R : ℝ,
        0 < c1 ∧ 0 < c2 ∧ 0 < R ∧ R ≤ c.R ∧
        (∀ x : E2, 0 < ‖x‖ → ‖x‖ < R →
          c1 * ‖x‖ ^ m - c2 * ‖x‖ ^ (m + 1) ≤ ‖fderiv ℝ (graphDifference c) x‖ ∧
          0 < c1 * ‖x‖ ^ m - c2 * ‖x‖ ^ (m + 1)) ∧
        (∀ x ∈ Metric.ball (0 : E2) R,
          fderiv ℝ (graphDifference c) x = 0 ↔ x = 0) ∧
        (∀ V : Set E2, V ∈ 𝓝 (0 : E2) →
          (∃ x ∈ V ∩ Metric.ball 0 R, 0 < graphDifference c x) ∧
          (∃ x ∈ V ∩ Metric.ball 0 R, graphDifference c x < 0)) := by
  intro p hp
  obtain ⟨c, hc⟩ := actual_tangency_flat_interior_graph_v480 D.A D.B hp
  exact ⟨c, hc, original_pair_graph_full_analytic_conclusion D c⟩

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3FlatGraphTangencyCriticalV480 -/

noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
set_option maxHeartbeats 300000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

private theorem graph_split_point_v480 (x : E2) (t : ℝ) :
    native_interior_graph_splitting_v475.symm (graphPoint x t) = (x,t) := by
  apply native_interior_graph_splitting_v475.injective
  rw [native_interior_graph_splitting_v475.apply_symm_apply]
  rfl

private theorem graph_plane_point_critical_v480 (x : E2) (t : ℝ) :
    graphPlaneCoordinates (graphPoint x t) = x := by
  ext i
  fin_cases i <;> simp [graphPlaneCoordinates,graphPoint]

private theorem graph_split_base_v480 (y : E3) :
    (native_interior_graph_splitting_v475.symm y).1 = graphPlaneCoordinates y := rfl

/-- Actual tangent coincidences in a flat original graph force the derivative
of the same literal upper-minus-lower graph difference to vanish. -/
theorem flat_interior_graph_tangent_to_critical_v480
    {A B : IncompressibleSpanningSurface.{0} E} {p q : E.Carrier}
    (c : InteriorGraph A B p) (hflat : c.upper = fun _ => 0)
    (hq : q ∈ c.coordinates.source)
    (ht : q ∈ interiorTangencies A.1.embedding B.1.embedding) :
    fderiv ℝ (graphDifference c) (graphPlaneCoordinates (c.coordinates q)) = 0 := by
  classical
  obtain ⟨a,b,ha,hb,hab⟩ := ht.2
  obtain ⟨C,hCS,hCT,hCF,hCI⟩ := interior_graph_sphere_chart c
  let Φ := C.chart.transHomeomorph native_interior_graph_splitting_v475.symm.toHomeomorph
  have hΦs : Φ.source = C.chart.source := rfl
  have hΦ : ContMDiffOn (𝓡 3) 𝓘(ℝ,E2 × ℝ) ∞ Φ Φ.source :=
    native_interior_graph_splitting_v475.symm.contDiff.contMDiff.comp_contMDiffOn C.smooth
  have hΦi : ContMDiffOn 𝓘(ℝ,E2 × ℝ) (𝓡 3) ∞ Φ.symm Φ.target := by
    exact C.inverse_smooth.comp
      native_interior_graph_splitting_v475.contDiff.contMDiff.contMDiffOn
      (fun y hy => hy)
  have hqΦ : E.toSphere q ∈ Φ.source := by rw [hΦs,hCS]; exact ⟨q,hq,rfl⟩
  have hcoord (v : E.Carrier) (hv : v ∈ c.coordinates.source) :
      Φ (E.toSphere v) = native_interior_graph_splitting_v475.symm (c.coordinates v) :=
    congrArg native_interior_graph_splitting_v475.symm (hCF v hv)
  have hAcoord (v : A.1.surface) (hv : A.1.embedding.toFun v ∈ c.coordinates.source) :
      (Φ (E.toSphere (A.1.embedding.toFun v))).2 = 0 := by
    have hh : A.1.embedding.toFun v ∈ A.1.image ∩ c.coordinates.source := ⟨⟨v,rfl⟩,hv⟩
    rw [c.graph_A] at hh
    obtain ⟨x,hx,hxv⟩ := hh
    have htar := c.cylinder_inside (a := graphPoint x (c.upper x))
      ⟨by simpa only [graph_plane_point_critical_v480,Metric.mem_ball,dist_zero_right] using hx,
       by simpa [graphPoint] using c.upper_inside x hx⟩
    rw [hcoord _ hv,← hxv,c.coordinates.right_inv htar,graph_split_point_v480,hflat]
  have hBcoord (v : B.1.surface) (hv : B.1.embedding.toFun v ∈ c.coordinates.source) :
      (Φ (E.toSphere (B.1.embedding.toFun v))).1 ∈ Metric.ball (0 : E2) c.R ∧
      (Φ (E.toSphere (B.1.embedding.toFun v))).2 =
        c.lower ((Φ (E.toSphere (B.1.embedding.toFun v))).1) := by
    have hh : B.1.embedding.toFun v ∈ B.1.image ∩ c.coordinates.source := ⟨⟨v,rfl⟩,hv⟩
    rw [c.graph_B] at hh
    obtain ⟨x,hx,hxv⟩ := hh
    have htar := c.cylinder_inside (a := graphPoint x (c.lower x))
      ⟨by simpa only [graph_plane_point_critical_v480,Metric.mem_ball,dist_zero_right] using hx,
       by simpa [graphPoint] using c.lower_inside x hx⟩
    rw [hcoord _ hv,← hxv,c.coordinates.right_inv htar,graph_split_point_v480]
    exact ⟨hx,rfl⟩
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  let G : B.1.surface → ThreeSphere := E.toSphere ∘ B.1.embedding.toFun
  let Q : B.1.surface → E2 × ℝ := Φ ∘ G
  let H : ThreeSphere → ℝ := fun z => (Φ z).2
  have hsnd : ContMDiff 𝓘(ℝ,E2 × ℝ) 𝓘(ℝ) ∞ (Prod.snd : E2 × ℝ → ℝ) :=
    (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : E2 × ℝ → ℝ)).contMDiff
  have hfst : ContMDiff 𝓘(ℝ,E2 × ℝ) 𝓘(ℝ,E2) ∞ (Prod.fst : E2 × ℝ → E2) :=
    (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : E2 × ℝ → E2)).contMDiff
  have hHz : mfderiv (𝓡∂ 2) 𝓘(ℝ) (H ∘ E.toSphere ∘ A.1.embedding.toFun) a = 0 := by
    have heq : (H ∘ E.toSphere ∘ A.1.embedding.toFun) =ᶠ[𝓝 a] fun _ => (0 : ℝ) := by
      filter_upwards [A.1.embedding.smoothEmbedding.isEmbedding.continuous.continuousAt.preimage_mem_nhds
        (c.coordinates.open_source.mem_nhds (ha.symm ▸ hq))] with v hv
      exact hAcoord v hv
    rw [heq.mfderiv_eq]
    exact mfderiv_const (I := 𝓡∂ 2) (I' := 𝓘(ℝ)) (c := (0 : ℝ)) (x := a)
  have hHd : MDifferentiableAt (𝓡 3) 𝓘(ℝ) H (E.toSphere q) :=
    hsnd.mdifferentiableAt (by simp) |>.comp _
      ((hΦ.contMDiffAt (Φ.open_source.mem_nhds hqΦ)).mdifferentiableAt (by simp))
  have hHg := tangency_scalar_derivative_transfer_v480 A.1.embedding B.1.embedding a b q ha hb hab H hHd hHz
  have hGd := hinc.contMDiff.mdifferentiable (by simp) (B.1.embedding.toFun b) |>.comp b
    (B.1.embedding.smoothEmbedding.contMDiff.mdifferentiable (by simp) b)
  have hbΦ : G b ∈ Φ.source := by simpa only [G,Function.comp_apply,hb] using hqΦ
  have hΦd := (hΦ.contMDiffAt (Φ.open_source.mem_nhds hbΦ)).mdifferentiableAt (by simp)
  have hQd : MDifferentiableAt (𝓡∂ 2) 𝓘(ℝ,E2 × ℝ) Q b := hΦd.comp b hGd
  have hQinj : Injective (mfderiv (𝓡∂ 2) 𝓘(ℝ,E2 × ℝ) Q b) := by
    dsimp only [Q,G]
    rw [mfderiv_comp b hΦd hGd,
      mfderiv_comp b (hinc.contMDiff.mdifferentiable (by simp) (B.1.embedding.toFun b))
        (B.1.embedding.smoothEmbedding.contMDiff.mdifferentiable (by simp) b)]
    exact (smooth_slice_derivative_injective_v480 Φ hΦ hΦi hbΦ).comp
      (((hinc.isImmersion.isImmersionAt _).mfderiv_injective (by simp)).comp
        ((B.1.embedding.smoothEmbedding.isImmersion.isImmersionAt b).mfderiv_injective (by simp)))
  have hQnormal : ∀ v, ((mfderiv (𝓡∂ 2) 𝓘(ℝ,E2 × ℝ) Q b) v).2 = 0 := by
    intro v
    have hd := mfderiv_comp b (hsnd.mdifferentiable (by simp) (Q b)) hQd
    change mfderiv (𝓡∂ 2) 𝓘(ℝ) (H ∘ G) b = _ at hd
    rw [hHg,mfderiv_eq_fderiv,fderiv_snd] at hd
    have hh := congrArg (fun T => T v) hd
    exact hh.symm
  let L : E2 →L[ℝ] (E2 × ℝ) :=
    (tangentSpaceCastModel 𝓘(ℝ,E2 × ℝ) (Q b)).toContinuousLinearMap.comp
      ((mfderiv (𝓡∂ 2) 𝓘(ℝ,E2 × ℝ) Q b).comp
        (tangentSpaceCastModel (𝓡∂ 2) b).symm.toContinuousLinearMap)
  have hLinj : Injective L :=
    (tangentSpaceCastModel 𝓘(ℝ,E2 × ℝ) (Q b)).injective.comp
      (hQinj.comp (tangentSpaceCastModel (𝓡∂ 2) b).symm.injective)
  have hLn : (ContinuousLinearMap.snd ℝ E2 ℝ).comp L = 0 := by
    ext v
    exact hQnormal ((tangentSpaceCastModel (𝓡∂ 2) b).symm v)
  obtain ⟨J,hJ⟩ := native_projected_derivative_invertible_v475 L hLinj hLn
  have hbSrc : B.1.embedding.toFun b ∈ c.coordinates.source := hb.symm ▸ hq
  have hbaseball : (Q b).1 ∈ Metric.ball (0 : E2) c.R := (hBcoord b hbSrc).1
  have hld : DifferentiableAt ℝ c.lower ((Q b).1) :=
    (c.lower_smooth.contDiffAt (Metric.isOpen_ball.mem_nhds hbaseball)).differentiableAt (by simp)
  have heq : c.lower ∘ (fun y => (Q y).1) =ᶠ[𝓝 b] H ∘ G := by
    filter_upwards [B.1.embedding.smoothEmbedding.isEmbedding.continuous.continuousAt.preimage_mem_nhds
      (c.coordinates.open_source.mem_nhds hbSrc)] with y hy
    exact (hBcoord y hy).2.symm
  have hchain := mfderiv_comp b hld.mdifferentiableAt (hfst.mdifferentiableAt (by simp) |>.comp b hQd)
  change mfderiv (𝓡∂ 2) 𝓘(ℝ) (c.lower ∘ (fun y => (Q y).1)) b = _ at hchain
  rw [heq.mfderiv_eq,hHg,mfderiv_eq_fderiv] at hchain
  have hfstval (v : TangentSpace (𝓡∂ 2) b) :
      (mfderiv (𝓡∂ 2) 𝓘(ℝ,E2) (fun y => (Q y).1) b) v =
        ((mfderiv (𝓡∂ 2) 𝓘(ℝ,E2 × ℝ) Q b) v).1 := by
    have hd := mfderiv_comp b (hfst.mdifferentiableAt (by simp)) hQd
    rw [mfderiv_eq_fderiv,fderiv_fst] at hd
    exact congrArg (fun T => T v) hd
  have hzero : fderiv ℝ c.lower ((Q b).1) = 0 := by
    ext v
    obtain ⟨w,hw⟩ := J.surjective v
    have hh := congrArg (fun T => T ((tangentSpaceCastModel (𝓡∂ 2) b).symm w)) hchain
    change 0 = (fderiv ℝ c.lower ((Q b).1))
      ((mfderiv (𝓡∂ 2) 𝓘(ℝ,E2) (fun y => (Q y).1) b)
        ((tangentSpaceCastModel (𝓡∂ 2) b).symm w)) at hh
    rw [hfstval] at hh
    change 0 = (fderiv ℝ c.lower ((Q b).1)) ((L w).1) at hh
    have hJw : J w = (L w).1 := congrArg (fun T : E2 →L[ℝ] E2 => T w) hJ
    rw [← hJw,hw] at hh
    exact hh.symm
  have hbase : (Q b).1 = graphPlaneCoordinates (c.coordinates q) := by
    change (Φ (E.toSphere (B.1.embedding.toFun b))).1 = _
    rw [hb,hcoord q hq,graph_split_base_v480]
  have hdiff : graphDifference c = fun x => -c.lower x := by
    ext x
    simp only [graphDifference,hflat,zero_sub]
  rw [hdiff,← hbase]
  change fderiv ℝ (-c.lower) ((Q b).1) = 0
  rw [fderiv_neg,hzero]
  exact neg_zero

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3ActualInteriorIsolationV480 -/

noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}
set_option maxHeartbeats 300000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

private theorem isolation_graph_plane_v480 (x : E2) (t : ℝ) :
    graphPlaneCoordinates (graphPoint x t) = x := by
  ext i
  fin_cases i <;> simp [graphPlaneCoordinates,graphPoint]
private theorem isolation_graph_zero_v480 : graphPoint (0 : E2) 0 = (0 : E3) := by
  ext i
  fin_cases i <;> simp [graphPoint]
private theorem isolation_graph_plane_zero_v480 : graphPlaneCoordinates (0 : E3) = (0 : E2) := by
  rw [← isolation_graph_zero_v480,isolation_graph_plane_v480]

/-- The exact native graph's isolated critical derivative isolates the actual
ambient tangent coincidences of the two original embeddings. -/
theorem flat_graph_isolates_actual_tangencies_v480
    {A B : IncompressibleSpanningSurface.{0} E} {p : E.Carrier}
    (hp : p ∈ interiorTangencies A.1.embedding B.1.embedding)
    (c : InteriorGraph A B p) (hflat : c.upper = fun _ => 0)
    {R : ℝ} (hR : 0 < R)
    (hcritical : ∀ x ∈ Metric.ball (0 : E2) R,
      fderiv ℝ (graphDifference c) x = 0 ↔ x = 0) :
    ∃ U : Set E.Carrier, IsOpen U ∧ p ∈ U ∧
      U ∩ interiorTangencies A.1.embedding B.1.embedding = {p} := by
  classical
  let V : Set E3 := graphPlaneCoordinates ⁻¹' Metric.ball (0 : E2) R
  let U : Set E.Carrier := c.coordinates.source ∩ c.coordinates ⁻¹' V
  have hbaseContinuous : Continuous graphPlaneCoordinates :=
    native_interior_graph_splitting_v475.symm.continuous.fst
  have hV : IsOpen V := Metric.isOpen_ball.preimage hbaseContinuous
  have hU : IsOpen U :=
    c.coordinates.continuousOn.isOpen_inter_preimage c.coordinates.open_source hV
  have hpU : p ∈ U := by
    refine ⟨c.base_mem,?_⟩
    change graphPlaneCoordinates (c.coordinates p) ∈ Metric.ball (0 : E2) R
    rw [c.base_zero,isolation_graph_plane_zero_v480]
    exact Metric.mem_ball_self hR
  refine ⟨U,hU,hpU,?_⟩
  ext q
  constructor
  · rintro ⟨hqU,hqt⟩
    have hqzero : graphPlaneCoordinates (c.coordinates q) = 0 :=
      (hcritical _ hqU.2).mp (flat_interior_graph_tangent_to_critical_v480 c hflat hqU.1 hqt)
    obtain ⟨a,b,ha,hb,ht⟩ := hqt.2
    have hh : q ∈ A.1.image ∩ c.coordinates.source := ⟨⟨a,ha⟩,hqU.1⟩
    rw [c.graph_A] at hh
    obtain ⟨x,hx,hxq⟩ := hh
    have htar := c.cylinder_inside (a := graphPoint x (c.upper x))
      ⟨by simpa only [isolation_graph_plane_v480,Metric.mem_ball,dist_zero_right] using hx,
       by simpa [graphPoint] using c.upper_inside x hx⟩
    have hcoord : c.coordinates q = graphPoint x (c.upper x) := by
      rw [← hxq,c.coordinates.right_inv htar]
    have hx0 : x = 0 := by
      simpa only [hcoord,isolation_graph_plane_v480] using hqzero
    have hqcoord : c.coordinates q = 0 := by
      rw [hcoord,hflat,hx0,isolation_graph_zero_v480]
    exact Set.mem_singleton_iff.mpr
      (c.coordinates.injOn hqU.1 c.base_mem (hqcoord.trans c.base_zero.symm))
  · intro hq
    have hqp : q = p := Set.mem_singleton_iff.mp hq
    subst q
    exact ⟨hpU,hp⟩

/-- Complete original B3 local conclusion: ambient isolation plus a constructed
same native graph with the full quantitative and sign statements. -/
theorem original_pair_interior_tangency_conclusion_v480 (D : OriginalPair g J) :
    InteriorTangencyConclusion D := by
  intro p hp
  obtain ⟨c,hflat,m,hm,c1,c2,R,hc1,hc2,hR,hRc,hlower,hcritical,hsigns⟩ :=
    original_pair_actual_graph_analytic_conclusion D p hp
  exact ⟨flat_graph_isolates_actual_tangencies_v480 hp c hflat hR hcritical,
    c,m,hm,c1,c2,R,hc1,hc2,hR,hRc,hlower,hcritical,hsigns⟩

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3SphereFlatSheetCriticalV480 -/
noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
set_option maxHeartbeats 300000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- A smooth actual scalar graph over a flat opposite sheet has zero graph
height derivative at every actual tangent-plane equality. -/
theorem sphere_flat_sheet_tangent_graph_critical_v480
    {S B : CompactOrientedSurface.{0}}
    (f : NeatEmbedding S E.Carrier) (g : NeatEmbedding B E.Carrier)
    (a : S) (b : B) (p : E.Carrier) (ha : f.toFun a = p) (hb : g.toFun b = p)
    (ht : tangentPlaneAt f a p ha = tangentPlaneAt g b p hb)
    (Φ : OpenPartialHomeomorph ThreeSphere (E2 × ℝ))
    (hΦ : ContMDiffOn (𝓡 3) 𝓘(ℝ,E2 × ℝ) ∞ Φ Φ.source)
    (hΦi : ContMDiffOn 𝓘(ℝ,E2 × ℝ) (𝓡 3) ∞ Φ.symm Φ.target)
    (hpΦ : E.toSphere p ∈ Φ.source)
    (hfirst : (fun y => (Φ (E.toSphere (f.toFun y))).2) =ᶠ[𝓝 a] fun _ => (0 : ℝ))
    (n : E2 → ℝ)
    (hnd : DifferentiableAt ℝ n (Φ (E.toSphere (g.toFun b))).1)
    (hsecond : (fun y => n ((Φ (E.toSphere (g.toFun y))).1)) =ᶠ[𝓝 b]
      (fun y => (Φ (E.toSphere (g.toFun y))).2)) :
    fderiv ℝ n (Φ (E.toSphere p)).1 = 0 := by
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  let G : B → ThreeSphere := E.toSphere ∘ g.toFun
  let Q : B → E2 × ℝ := Φ ∘ G
  let H : ThreeSphere → ℝ := fun z => (Φ z).2
  have hsnd : ContMDiff 𝓘(ℝ,E2 × ℝ) 𝓘(ℝ) ∞ (Prod.snd : E2 × ℝ → ℝ) :=
    (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : E2 × ℝ → ℝ)).contMDiff
  have hfst : ContMDiff 𝓘(ℝ,E2 × ℝ) 𝓘(ℝ,E2) ∞ (Prod.fst : E2 × ℝ → E2) :=
    (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : E2 × ℝ → E2)).contMDiff
  have hHz : mfderiv (𝓡∂ 2) 𝓘(ℝ) (H ∘ E.toSphere ∘ f.toFun) a = 0 := by
    change mfderiv (𝓡∂ 2) 𝓘(ℝ) (fun y => (Φ (E.toSphere (f.toFun y))).2) a = 0
    rw [hfirst.mfderiv_eq]
    exact mfderiv_const (I := 𝓡∂ 2) (I' := 𝓘(ℝ)) (c := (0 : ℝ)) (x := a)
  have hHd : MDifferentiableAt (𝓡 3) 𝓘(ℝ) H (E.toSphere p) :=
    hsnd.mdifferentiableAt (by simp) |>.comp _
      ((hΦ.contMDiffAt (Φ.open_source.mem_nhds hpΦ)).mdifferentiableAt (by simp))
  have hHg := tangency_scalar_derivative_transfer_v480 f g a b p ha hb ht H hHd hHz
  have hGd := hinc.contMDiff.mdifferentiable (by simp) (g.toFun b) |>.comp b
    (g.smoothEmbedding.contMDiff.mdifferentiable (by simp) b)
  have hbΦ : G b ∈ Φ.source := by simpa only [G,Function.comp_apply,hb] using hpΦ
  have hΦd := (hΦ.contMDiffAt (Φ.open_source.mem_nhds hbΦ)).mdifferentiableAt (by simp)
  have hQd : MDifferentiableAt (𝓡∂ 2) 𝓘(ℝ,E2 × ℝ) Q b := hΦd.comp b hGd
  have hQinj : Injective (mfderiv (𝓡∂ 2) 𝓘(ℝ,E2 × ℝ) Q b) := by
    dsimp only [Q,G]
    rw [mfderiv_comp b hΦd hGd,
      mfderiv_comp b (hinc.contMDiff.mdifferentiable (by simp) (g.toFun b))
        (g.smoothEmbedding.contMDiff.mdifferentiable (by simp) b)]
    exact (smooth_slice_derivative_injective_v480 Φ hΦ hΦi hbΦ).comp
      (((hinc.isImmersion.isImmersionAt _).mfderiv_injective (by simp)).comp
        ((g.smoothEmbedding.isImmersion.isImmersionAt b).mfderiv_injective (by simp)))
  have hQnormal : ∀ v, ((mfderiv (𝓡∂ 2) 𝓘(ℝ,E2 × ℝ) Q b) v).2 = 0 := by
    intro v
    have hd := mfderiv_comp b (hsnd.mdifferentiable (by simp) (Q b)) hQd
    change mfderiv (𝓡∂ 2) 𝓘(ℝ) (H ∘ G) b = _ at hd
    rw [hHg,mfderiv_eq_fderiv,fderiv_snd] at hd
    have hh := congrArg (fun T => T v) hd
    exact hh.symm
  let L : E2 →L[ℝ] (E2 × ℝ) :=
    (tangentSpaceCastModel 𝓘(ℝ,E2 × ℝ) (Q b)).toContinuousLinearMap.comp
      ((mfderiv (𝓡∂ 2) 𝓘(ℝ,E2 × ℝ) Q b).comp
        (tangentSpaceCastModel (𝓡∂ 2) b).symm.toContinuousLinearMap)
  have hLinj : Injective L :=
    (tangentSpaceCastModel 𝓘(ℝ,E2 × ℝ) (Q b)).injective.comp
      (hQinj.comp (tangentSpaceCastModel (𝓡∂ 2) b).symm.injective)
  have hLn : (ContinuousLinearMap.snd ℝ E2 ℝ).comp L = 0 := by
    ext v
    exact hQnormal ((tangentSpaceCastModel (𝓡∂ 2) b).symm v)
  obtain ⟨J,hJ⟩ := native_projected_derivative_invertible_v475 L hLinj hLn
  have heq : n ∘ (fun y => (Q y).1) =ᶠ[𝓝 b] H ∘ G := hsecond
  have hchain := mfderiv_comp b hnd.mdifferentiableAt (hfst.mdifferentiableAt (by simp) |>.comp b hQd)
  change mfderiv (𝓡∂ 2) 𝓘(ℝ) (n ∘ (fun y => (Q y).1)) b = _ at hchain
  rw [heq.mfderiv_eq,hHg,mfderiv_eq_fderiv] at hchain
  have hfstval (v : TangentSpace (𝓡∂ 2) b) :
      (mfderiv (𝓡∂ 2) 𝓘(ℝ,E2) (fun y => (Q y).1) b) v =
        ((mfderiv (𝓡∂ 2) 𝓘(ℝ,E2 × ℝ) Q b) v).1 := by
    have hd := mfderiv_comp b (hfst.mdifferentiableAt (by simp)) hQd
    rw [mfderiv_eq_fderiv,fderiv_fst] at hd
    exact congrArg (fun T => T v) hd
  have hzero : fderiv ℝ n ((Q b).1) = 0 := by
    ext v
    obtain ⟨w,hw⟩ := J.surjective v
    have hh := congrArg (fun T => T ((tangentSpaceCastModel (𝓡∂ 2) b).symm w)) hchain
    change 0 = (fderiv ℝ n ((Q b).1))
      ((mfderiv (𝓡∂ 2) 𝓘(ℝ,E2) (fun y => (Q y).1) b)
        ((tangentSpaceCastModel (𝓡∂ 2) b).symm w)) at hh
    rw [hfstval] at hh
    change 0 = (fderiv ℝ n ((Q b).1)) ((L w).1) at hh
    have hJw : J w = (L w).1 := congrArg (fun T : E2 →L[ℝ] E2 => T w) hJ
    rw [← hJw,hw] at hh
    exact hh.symm
  simpa only [Q,G,Function.comp_apply,hb] using hzero

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3BoundaryPairGraphV480 -/

noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- Constructed actual common boundary graph, retaining entire images and the
actual boundary. The normal orientation is a proved coefficient, not an input. -/
structure ActualBoundaryPairGraphV480 {S B : CompactOrientedSurface.{0}}
    (f : NeatEmbedding S E.Carrier) (g : NeatEmbedding B E.Carrier) (p : E.Carrier) where
  coordinates : SmoothAmbientChart ThreeSphere
  O : Set E2
  open_O : IsOpen O
  z : E2
  base_in_O : z ∈ O
  base_flat : z 0 = 0
  eta : ℝ
  eta_pos : 0 < eta
  base_mem : E.toSphere p ∈ coordinates.chart.source
  base_value : coordinates.chart (E.toSphere p) = graphPoint z 0
  target_exact : coordinates.chart.target =
    native_interior_graph_splitting_v475 '' (O ×ˢ Ioo (-eta) eta)
  height : E2 → ℝ
  height_smooth : ContDiffOn ℝ ∞ height O
  height_zero : height z = 0
  height_tangent : fderiv ℝ height z = 0
  height_boundary : ∀ x ∈ O, x 0 = 0 → height x = 0
  inversePlanar : E2 → E2
  inversePlanar_smooth : ContDiffOn ℝ ∞ inversePlanar O
  coefficient : ℝ
  coefficient_ne : coefficient ≠ 0
  halfspace_sign : ∀ x ∈ O,
    (inversePlanar x 0 = 0 ↔ x 0 = 0) ∧
    (0 < x 0 ↔ 0 < coefficient * inversePlanar x 0) ∧
    (0 ≤ x 0 ↔ 0 ≤ coefficient * inversePlanar x 0)
  points_inside : ∀ x ∈ O, graphPoint x 0 ∈ coordinates.chart.target ∧
    graphPoint x (height x) ∈ coordinates.chart.target
  graph_A : range (E.toSphere ∘ f.toFun) ∩ coordinates.chart.source =
    (fun x => coordinates.chart.symm (graphPoint x 0)) '' {x ∈ O | 0 ≤ x 0}
  graph_B : range (E.toSphere ∘ g.toFun) ∩ coordinates.chart.source =
    (fun x => coordinates.chart.symm (graphPoint x (height x))) ''
      {x ∈ O | 0 ≤ inversePlanar x 0}
  boundary_A : (E.toSphere ∘ f.toFun) '' S.boundary ∩ coordinates.chart.source =
    (fun x => coordinates.chart.symm (graphPoint x 0)) '' {x ∈ O | x 0 = 0}

private theorem boundary_base_point_v480 (x : E2) (t : ℝ) :
    native_collar_base_v475 (graphPoint x t) = x := by
  ext i
  fin_cases i <;> simp [native_collar_base_v475,graphPoint]

private theorem boundary_reconstruct_v480 (y : E3) :
    graphPoint (native_collar_base_v475 y) (y 2) = y := by
  ext i
  fin_cases i <;> simp [native_collar_base_v475,graphPoint]

/-- Full boundary common graph from the actual neat surfaces, without a
supplied collar or an agreement germ. -/
theorem actual_boundary_pair_graph_v480
    {S B : CompactOrientedSurface.{0}}
    (f : NeatEmbedding S E.Carrier) (g : NeatEmbedding B E.Carrier)
    (a : S) (b : B) (ha : a ∈ S.boundary) (hb : b ∈ B.boundary)
    (heq : g.toFun b = f.toFun a)
    (hboundary : f.toFun '' S.boundary = g.toFun '' B.boundary)
    (ht : tangentPlaneAt f a (f.toFun a) rfl = tangentPlaneAt g b (f.toFun a) heq) :
    Nonempty (ActualBoundaryPairGraphV480 f g (f.toFun a)) := by
  classical
  obtain ⟨Φ,Ψ,O0,p,e,u,hy,hO0eq,hO0,hpO0,hpe,heO,hΦ,hΦi,hΨ,hΨi,hA,hB,hAB,hBB,
    hpSrc,hpair,heS,heI,hu,huz,hdu,hgraph,hgraphS,hp0,hep0,hflat⟩ :=
    actual_arbitrary_boundary_common_graph_v480 f g a b ha hb heq hboundary ht
  have hpair' : Ψ (E.toSphere (f.toFun a)) = (p,0) := by rwa [heq] at hpair
  obtain ⟨C,O,eta,k,hO,hzO,hOe,heta,hk,hCΦ,hsign,hzero,htar,hC,hCi,hpoints,hAp,hBp,hAf,hBf⟩ :=
    native_boundary_common_graph_cylinder_v480 f g (f.toFun a) Φ Ψ hΦ hΦi
      hpSrc.1 hpSrc.2 hA hB p e u hpe hpair'
      (by simpa only [hO0eq] using heO) hu huz hgraph hgraphS heS heI hp0 hep0 hflat
  have hsplit (x : E2) (t : ℝ) : native_interior_graph_splitting_v475.symm (graphPoint x t) = (x,t) :=
    native_interior_graph_splitting_v475.symm_apply_apply (x,t)
  have hΦbase : Φ (E.toSphere (f.toFun a)) = (e p,0) := by
    have hh := hgraphS p hpe
    rw [← hpair',Ψ.left_inv hpSrc.2,huz] at hh
    exact hh
  have hCbase : C.chart (E.toSphere (f.toFun a)) = graphPoint (e p) 0 := by
    rw [hC,hΦbase]
    rfl
  have hpC : E.toSphere (f.toFun a) ∈ C.chart.source := by
    have htC := (hpoints (e p) hzO).1
    have hs : C.chart.symm (graphPoint (e p) 0) = E.toSphere (f.toFun a) := by
      rw [hCi,hsplit]
      change Φ.symm (e p,0) = E.toSphere (f.toFun a)
      rw [← hΦbase,Φ.left_inv hpSrc.1]
    exact hs ▸ C.chart.map_target htC
  have hcoordO {q : ThreeSphere} (hq : q ∈ C.chart.source) :
      native_collar_base_v475 (C.chart q) ∈ O := by
    have hh := C.chart.map_source hq
    rw [htar] at hh
    obtain ⟨⟨x,t⟩,⟨hx,ht⟩,heq⟩ := hh
    have hbase := congrArg native_collar_base_v475 heq
    change native_collar_base_v475 (graphPoint x t) = _ at hbase
    rw [boundary_base_point_v480] at hbase
    exact hbase ▸ hx
  have hCA {q : ThreeSphere} (hq : q ∈ C.chart.source)
      (hqr : q ∈ range (E.toSphere ∘ f.toFun)) :
      (C.chart q) 2 = 0 := by
    obtain ⟨x,rfl⟩ := hqr
    exact hAf x hq
  have hCB {q : ThreeSphere} (hq : q ∈ C.chart.source)
      (hqr : q ∈ range (E.toSphere ∘ g.toFun)) :
      (C.chart q) 2 = u (native_collar_base_v475 (C.chart q)) := by
    obtain ⟨x,rfl⟩ := hqr
    exact hBf x hq
  have hAexact : range (E.toSphere ∘ f.toFun) ∩ C.chart.source =
      (fun x => C.chart.symm (graphPoint x 0)) '' {x ∈ O | 0 ≤ x 0} := by
    ext q
    constructor
    · rintro ⟨hqR,hqC⟩
      let x := native_collar_base_v475 (C.chart q)
      have hx := hcoordO hqC
      have hqeq : C.chart.symm (graphPoint x 0) = q := by
        rw [← hCA hqC hqR,boundary_reconstruct_v480,C.chart.left_inv hqC]
      refine ⟨x,⟨hx,?_⟩,hqeq⟩
      exact (hAp x hx).mp (hqeq.symm ▸ hqR)
    · rintro ⟨x,⟨hx,hx0⟩,rfl⟩
      exact ⟨(hAp x hx).mpr hx0,C.chart.map_target (hpoints x hx).1⟩
  have hBexact : range (E.toSphere ∘ g.toFun) ∩ C.chart.source =
      (fun x => C.chart.symm (graphPoint x (u x))) '' {x ∈ O | 0 ≤ (e.symm x) 0} := by
    ext q
    constructor
    · rintro ⟨hqR,hqC⟩
      let x := native_collar_base_v475 (C.chart q)
      have hx := hcoordO hqC
      have hqeq : C.chart.symm (graphPoint x (u x)) = q := by
        rw [← hCB hqC hqR,boundary_reconstruct_v480,C.chart.left_inv hqC]
      refine ⟨x,⟨hx,?_⟩,hqeq⟩
      exact (hBp x hx).mp (hqeq.symm ▸ hqR)
    · rintro ⟨x,⟨hx,hx0⟩,rfl⟩
      exact ⟨(hBp x hx).mpr hx0,C.chart.map_target (hpoints x hx).2⟩
  have hAbexact : (E.toSphere ∘ f.toFun) '' S.boundary ∩ C.chart.source =
      (fun x => C.chart.symm (graphPoint x 0)) '' {x ∈ O | x 0 = 0} := by
    ext q
    constructor
    · rintro ⟨⟨x,hx,rfl⟩,hqC⟩
      have hqR : (E.toSphere ∘ f.toFun) x ∈ range (E.toSphere ∘ f.toFun) := mem_range_self x
      have hqΦ : (E.toSphere ∘ f.toFun) x ∈ Φ.source := hCΦ hqC
      have hc : Φ ((E.toSphere ∘ f.toFun) x) ∈
          Φ.target ∩ ({z : E2 | z 0 = 0} ×ˢ ({0}:Set ℝ)) := by
        rw [← hAB]
        exact mem_image_of_mem Φ ⟨hqΦ,⟨x,hx,rfl⟩⟩
      let z := native_collar_base_v475 (C.chart ((E.toSphere ∘ f.toFun) x))
      have hz := hcoordO hqC
      have hz0 : z 0 = 0 := by
        change native_collar_base_v475 (C.chart ((E.toSphere ∘ f.toFun) x)) 0 = 0
        rw [hC]
        exact hc.2.1
      refine ⟨z,⟨hz,hz0⟩,?_⟩
      change C.chart.symm (graphPoint (native_collar_base_v475 (C.chart ((E.toSphere ∘ f.toFun) x))) 0) = _
      rw [← hCA hqC hqR,boundary_reconstruct_v480,C.chart.left_inv hqC]
    · rintro ⟨z,⟨hz,hz0⟩,rfl⟩
      have hqC := C.chart.map_target (hpoints z hz).1
      have hqΦ : C.chart.symm (graphPoint z 0) ∈ Φ.source := hCΦ hqC
      have hΦcoord : Φ (C.chart.symm (graphPoint z 0)) = (z,0) := by
        have htG : graphPoint z 0 ∈ C.chart.target := (hpoints z hz).1
        apply native_interior_graph_splitting_v475.injective
        rw [← hC,C.chart.right_inv htG]
        rfl
      have hh : (z,0) ∈ Φ '' (Φ.source ∩ (E.toSphere ∘ f.toFun) '' S.boundary) := by
        rw [hAB]
        exact ⟨hΦcoord ▸ Φ.map_source hqΦ,hz0,rfl⟩
      obtain ⟨w,⟨hwΦ,hwB⟩,hw⟩ := hh
      exact ⟨by rwa [Φ.injOn hwΦ hqΦ (hw.trans hΦcoord.symm)] at hwB,hqC⟩
  exact ⟨{
    coordinates := C
    O := O
    open_O := hO
    z := e p
    base_in_O := hzO
    base_flat := hep0
    eta := eta
    eta_pos := heta
    base_mem := hpC
    base_value := hCbase
    target_exact := htar
    height := u
    height_smooth := hu.mono hOe
    height_zero := huz
    height_tangent := hdu
    height_boundary := hzero
    inversePlanar := e.symm
    inversePlanar_smooth := heI.mono hOe
    coefficient := k
    coefficient_ne := hk
    halfspace_sign := hsign
    points_inside := hpoints
    graph_A := hAexact
    graph_B := hBexact
    boundary_A := hAbexact }⟩

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3CollarActualTangencyHeightV480 -/

noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}
set_option maxHeartbeats 500000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- The original collar's actual ambient tangent coincidences force a zero
derivative of its same literal local graph height at every positive radius. -/
theorem collar_actual_tangency_local_height_critical_v480
    (D : B1OriginalData g J) (s : Circle) (r : ℝ) (hr : 0 < r) (hrr : r < D.r0)
    (ht : D.collar (s,r,0) ∈ interiorTangencies D.A.1.embedding D.B.1.embedding) :
    fderiv ℝ (localHeight D s)
      ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![0,r]) = 0 := by
  classical
  obtain ⟨W⟩ := actual_collar_window D s
  let O : Set E3 := {y | |y 0| < 2 * W.R ∧ 0 < y 1 ∧ y 1 < D.r0 ∧ |y 2| < D.eta}
  have hO : IsOpen O :=
    (isOpen_lt (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).continuous.abs continuous_const).inter
      ((isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)).continuous).inter
        ((isOpen_lt (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)).continuous continuous_const).inter
          (isOpen_lt (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous.abs continuous_const)))
  have hOC : O ⊆ collarDomain D W.R := fun y hy => ⟨hy.1,⟨hy.2.1.le,hy.2.2.1.le⟩,hy.2.2.2⟩
  obtain ⟨Ψ,hΨS,hΨT,hΨF⟩ := actual_interior_collar_global_partialDiffeomorph_v475 D s W O hO hOC
  let x : E2 := (EuclideanSpace.equiv (Fin 2) ℝ).symm ![0,r]
  let y0 : E3 := jetPoint (x,0,0)
  let p : E.Carrier := D.collar (s,r,0)
  have hy0 : y0 ∈ Ψ.source := by
    rw [hΨS]
    simpa [O,y0,x,jetPoint] using And.intro (by linarith [W.R_pos] : (0 : ℝ) < 2 * W.R)
      (And.intro hr (And.intro hrr D.eta_pos))
  have hy0F : Ψ y0 = E.toSphere p := by
    rw [hΨF]
    simp [localCollar,localCircle,y0,x,jetPoint,p]
  have hpΨ : E.toSphere p ∈ Ψ.target := hy0F ▸ Ψ.toPartialEquiv.map_source hy0
  let Φ := Ψ.symm.toOpenPartialHomeomorph.transHomeomorph native_interior_graph_splitting_v475.symm.toHomeomorph
  have hΦ : ContMDiffOn (𝓡 3) 𝓘(ℝ,E2 × ℝ) ∞ Φ Φ.source :=
    native_interior_graph_splitting_v475.symm.contDiff.contMDiff.comp_contMDiffOn Ψ.symm.contMDiffOn
  have hΦi : ContMDiffOn 𝓘(ℝ,E2 × ℝ) (𝓡 3) ∞ Φ.symm Φ.target :=
    Ψ.contMDiffOn.comp native_interior_graph_splitting_v475.contDiff.contMDiff.contMDiffOn (fun y hy => hy)
  have hpΦ : E.toSphere p ∈ Φ.source := hpΨ
  have hbase : (Φ (E.toSphere p)).1 = x := by
    change (native_interior_graph_splitting_v475.symm (Ψ.symm (E.toSphere p))).1 = x
    have hleft := Ψ.toPartialEquiv.left_inv hy0
    change Ψ.symm.toPartialEquiv (Ψ.toPartialEquiv y0) = y0 at hleft
    rw [← hy0F,hleft]
    rfl
  have hcoord (v : E.Carrier) (hv : E.toSphere v ∈ Ψ.target) :
      Ψ.symm (E.toSphere v) ∈ collarDomain D W.R ∧
      localCollar D s (Ψ.symm (E.toSphere v)) = v := by
    have hy := Ψ.toPartialEquiv.map_target hv
    refine ⟨hOC (hΨS ▸ hy),?_⟩
    have he := Ψ.toPartialEquiv.right_inv hv
    rw [hΨF] at he
    exact (show Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere from E.inclusion).isEmbedding.injective he
  obtain ⟨a,b,ha,hb,hab⟩ := ht.2
  have haP : D.A.1.embedding.toFun a = p := ha
  have hbP : D.B.1.embedding.toFun b = p := hb
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  have hfirst : (fun v => (Φ (E.toSphere (D.B.1.embedding.toFun v))).2) =ᶠ[𝓝 b] fun _ => (0 : ℝ) := by
    filter_upwards [(hinc.isEmbedding.continuous.comp D.B.1.embedding.smoothEmbedding.isEmbedding.continuous).continuousAt.preimage_mem_nhds
      (Ψ.open_target.mem_nhds (by simpa only [Function.comp_apply,hbP] using hpΨ))] with v hv
    obtain ⟨hy,he⟩ := hcoord _ hv
    exact (actual_collar_graph_height_unique_v475 D s W).2 _ hy (he.symm ▸ ⟨v,rfl⟩)
  have hsecond : (fun v => localHeight D s ((Φ (E.toSphere (D.A.1.embedding.toFun v))).1)) =ᶠ[𝓝 a]
      (fun v => (Φ (E.toSphere (D.A.1.embedding.toFun v))).2) := by
    filter_upwards [(hinc.isEmbedding.continuous.comp D.A.1.embedding.smoothEmbedding.isEmbedding.continuous).continuousAt.preimage_mem_nhds
      (Ψ.open_target.mem_nhds (by simpa only [Function.comp_apply,haP] using hpΨ))] with v hv
    obtain ⟨hy,he⟩ := hcoord _ hv
    exact ((actual_collar_graph_height_unique_v475 D s W).1 _ hy (he.symm ▸ ⟨v,rfl⟩)).symm
  let P : E2 → Circle × ℝ := fun z => (localCircle D s (z 0),z 1)
  have hP : ContMDiff 𝓘(ℝ,E2) ((𝓡 1).prod 𝓘(ℝ)) ∞ P := by
    have ha : ContDiff ℝ ∞ (fun z : E2 => 2 * Real.pi * z 0 / D.leafLength) := by fun_prop
    exact (contMDiff_const.mul (contMDiff_circleExp.comp ha.contMDiff)).prodMk
      (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff.contMDiff
  have hPx : P x ∈ D.extendedDomain := by
    apply D.extendedDomain_contains
    change (P x).2 ∈ Icc (0 : ℝ) D.r0
    simpa [P,x] using And.intro hr.le hrr.le
  have hnd : DifferentiableAt ℝ (localHeight D s) x :=
    (((D.f_smooth.contMDiffAt (D.extendedDomain_open.mem_nhds hPx)).comp x hP.contMDiffAt).contDiffAt).differentiableAt (by simp)
  have hn : DifferentiableAt ℝ (localHeight D s) (Φ (E.toSphere (D.A.1.embedding.toFun a))).1 := by
    simpa only [haP,hbase] using hnd
  have hc := sphere_flat_sheet_tangent_graph_critical_v480 D.B.1.embedding D.A.1.embedding b a p hb ha hab.symm
    Φ hΦ hΦi hpΦ hfirst (localHeight D s) hn hsecond
  simpa only [hbase] using hc

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3CollarParameterDerivativeV480 -/

noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}
set_option maxHeartbeats 500000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

private theorem collar_parameter_smooth_v480 (D : B1OriginalData g J) (s : Circle) :
    ContMDiff 𝓘(ℝ,E2) ((𝓡 1).prod 𝓘(ℝ)) ∞
      (fun x : E2 => (localCircle D s (x 0),x 1)) := by
  have ha : ContDiff ℝ ∞ (fun z : E2 => 2 * Real.pi * z 0 / D.leafLength) := by fun_prop
  exact (contMDiff_const.mul (contMDiff_circleExp.comp ha.contMDiff)).prodMk
    (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff.contMDiff

/-- The literal arclength-scaled circle and radial parameter has full actual
rank, so zero planar graph derivative is equivalent to zero native derivative. -/
theorem collar_parameter_derivative_surjective_v480
    (D : B1OriginalData g J) (s : Circle) (x : E2) :
    Surjective (mfderiv 𝓘(ℝ,E2) ((𝓡 1).prod 𝓘(ℝ))
      (fun y : E2 => (localCircle D s (y 0),y 1)) x) := by
  let P : E2 → Circle × ℝ := fun y => (localCircle D s (y 0),y 1)
  let P0 := EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)
  let P1 := EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)
  let gamma : ℝ → ℂ := fun t => (localCircle D s t : ℂ)
  let c : ℂ := (s : ℂ) *
    (Complex.exp ((2 * Real.pi * (x 0) / D.leafLength : ℝ) * Complex.I) *
      ((2 * Real.pi / D.leafLength : ℝ) * Complex.I))
  have hgam : HasDerivAt gamma c (x 0) := by
    simpa [gamma,c,localCircle,Circle.coe_mul,Circle.coe_exp] using
      (((((hasDerivAt_id (x 0)).const_mul (2 * Real.pi)).div_const D.leafLength
        ).ofReal_comp.mul_const Complex.I).cexp.const_mul (s : ℂ))
  have hc : c ≠ 0 := by
    dsimp [c]
    apply mul_ne_zero (Circle.coe_ne_zero s)
    apply mul_ne_zero (Complex.exp_ne_zero _)
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr
      (div_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) D.leafLength_pos.ne'))
      Complex.I_ne_zero
  let post : Circle × ℝ → ℂ := fun p => (p.1 : ℂ)
  let : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨by simp⟩
  have hpost : ContMDiff ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ,ℂ) ∞ post :=
    (contMDiff_coe_sphere (E := ℂ) (n := 1)).comp contMDiff_fst
  have hP := collar_parameter_smooth_v480 D s
  have hf : HasFDerivAt (post ∘ P)
      (ContinuousLinearMap.toSpanSingleton ℝ c ∘L P0) x :=
    hgam.hasFDerivAt.comp x P0.hasFDerivAt
  have hchain := mfderiv_comp x (hpost.mdifferentiable (by simp) (P x)) (hP.mdifferentiable (by simp) x)
  rw [hf.hasMFDerivAt.mfderiv] at hchain
  have hsnd : ContMDiff ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ) ∞ (Prod.snd : Circle × ℝ → ℝ) := contMDiff_snd
  have hchain1 := mfderiv_comp x (hsnd.mdifferentiable (by simp) (P x)) (hP.mdifferentiable (by simp) x)
  have hmf1 : mfderiv 𝓘(ℝ,E2) 𝓘(ℝ) ((Prod.snd : Circle × ℝ → ℝ) ∘ P) x = P1 :=
    P1.hasFDerivAt.hasMFDerivAt.mfderiv
  rw [hmf1] at hchain1
  have hinj : Injective (mfderiv 𝓘(ℝ,E2) ((𝓡 1).prod 𝓘(ℝ)) P x) := by
    intro u v huv
    change E2 at u v
    have h0 : u 0 = v 0 := by
      have h := congrArg (mfderiv ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ,ℂ) post (P x)) huv
      have hu := congrArg (fun L => L u) hchain
      have hv := congrArg (fun L => L v) hchain
      change (u 0 : ℝ) • c = _ at hu
      change (v 0 : ℝ) • c = _ at hv
      exact (smul_left_injective ℝ hc) (hu.trans (h.trans hv.symm))
    have h1 : u 1 = v 1 := by
      have h := congrArg (mfderiv ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ) Prod.snd (P x)) huv
      exact (congrArg (fun L => L u) hchain1).trans
        (h.trans (congrArg (fun L => L v) hchain1).symm)
    change (u : E2) = (v : E2)
    ext i
    fin_cases i
    · exact h0
    · exact h1
  let L : E2 →L[ℝ] (EuclideanSpace ℝ (Fin 1) × ℝ) :=
    (tangentSpaceCastModel ((𝓡 1).prod 𝓘(ℝ)) (P x)).toContinuousLinearMap.comp
      ((mfderiv 𝓘(ℝ,E2) ((𝓡 1).prod 𝓘(ℝ)) P x).comp
        (tangentSpaceCastModel 𝓘(ℝ,E2) x).symm.toContinuousLinearMap)
  have hL : Injective L := (tangentSpaceCastModel ((𝓡 1).prod 𝓘(ℝ)) (P x)).injective.comp
    (hinj.comp (tangentSpaceCastModel 𝓘(ℝ,E2) x).symm.injective)
  let e := L.toLinearMap.linearEquivOfInjective hL (by simp)
  intro v
  obtain ⟨w,hw⟩ := e.surjective (tangentSpaceCastModel ((𝓡 1).prod 𝓘(ℝ)) (P x) v)
  refine ⟨(tangentSpaceCastModel 𝓘(ℝ,E2) x).symm w,?_⟩
  apply (tangentSpaceCastModel ((𝓡 1).prod 𝓘(ℝ)) (P x)).injective
  exact hw

/-- Transport the zero derivative back to the original circle-radial graph
function, with the exact source metric/foliation/collar data retained. -/
theorem collar_local_height_zero_implies_native_critical_v480
    (D : B1OriginalData g J) (s : Circle) (x : E2)
    (hx : (localCircle D s (x 0),x 1) ∈ radialCylinder D.r0)
    (hz : fderiv ℝ (localHeight D s) x = 0) :
    mfderiv ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ) (fun q : Circle × ℝ => D.f q.1 q.2)
      (localCircle D s (x 0),x 1) = 0 := by
  let P : E2 → Circle × ℝ := fun y => (localCircle D s (y 0),y 1)
  have hfd := (D.f_smooth.contMDiffAt (D.extendedDomain_open.mem_nhds (D.extendedDomain_contains hx))).mdifferentiableAt (by simp)
  have hchain := mfderiv_comp x hfd ((collar_parameter_smooth_v480 D s).mdifferentiable (by simp) x)
  change mfderiv 𝓘(ℝ,E2) 𝓘(ℝ) (localHeight D s) x = _ at hchain
  rw [mfderiv_eq_fderiv,hz] at hchain
  ext v
  obtain ⟨w,hw⟩ := collar_parameter_derivative_surjective_v480 D s x v
  have hh := congrArg (fun L => L w) hchain
  change 0 = (mfderiv ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ) (fun q : Circle × ℝ => D.f q.1 q.2)
    (localCircle D s (x 0),x 1))
      ((mfderiv 𝓘(ℝ,E2) ((𝓡 1).prod 𝓘(ℝ)) P x) w) at hh
  rw [hw] at hh
  exact hh.symm

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3NativeCollarConsequencesV480 -/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}

def originalPairOfB1 (D : B1OriginalData g J) : OriginalPair g J where
  A := D.A
  B := D.B
  A_minimum := D.A_relative_minimum
  B_minimum := D.B_relative_minimum
  distance_two := D.distance_two
  convex := D.boundary_strictly_convex
  analytic := D.foliation_analytic

theorem collar_critical_boundary_values (D : B1OriginalData g J) :
    ∀ s ∈ collarCriticalPoints D, D.f s 0 = 0 := by
  intro s _
  exact D.f_boundary_zero s

theorem interior_tangency_mem_B (D : B1OriginalData g J) {p : E.Carrier}
    (hp : p ∈ interiorTangencies D.A.1.embedding D.B.1.embedding) : p ∈ D.B.1.image := by
  rcases hp.2 with ⟨_,b,_,hb,_⟩
  exact ⟨b,hb⟩

theorem B_collar_coordinate_vertical_zero (D : B1OriginalData g J)
    {q : T2Coordinate} (hq : q ∈ halfCylinder D.r0 D.eta)
    (hB : D.collar q ∈ D.B.1.image) : q.2.2 = 0 := by
  have hmem : D.collar q ∈ D.B.1.image ∩ D.collar '' halfCylinder D.r0 D.eta :=
    ⟨hB,⟨q,hq,rfl⟩⟩
  rw [D.B_graph_exact] at hmem
  rcases hmem with ⟨x,hx,hEq⟩
  have hxfull : (x.1,x.2,0) ∈ halfCylinder D.r0 D.eta :=
    ⟨hx,by simpa using D.eta_pos⟩
  have he : (⟨(x.1,x.2,0),hxfull⟩ : halfCylinder D.r0 D.eta) = ⟨q,hq⟩ :=
    D.collar_embedding.injective hEq
  exact (congrArg (fun z : halfCylinder D.r0 D.eta => z.1.2.2) he).symm

theorem collar_radial_bound_of_avoidance (D : B1OriginalData g J)
    {r0 : ℝ} (_hr0 : 0 < r0) (hrD : r0 ≤ D.r0)
    {p : E.Carrier} (hp : p ∈ interiorTangencies D.A.1.embedding D.B.1.embedding)
    (havoid : p ∉ openCollar D r0) : r0 ≤ extendedRadial D r0 p := by
  classical
  by_cases hpin : p ∈ D.collar '' halfCylinder r0 D.eta
  · obtain ⟨q,hq,hqp⟩ := hpin
    have hqD : q ∈ halfCylinder D.r0 D.eta := ⟨⟨hq.1.1,hq.1.2.trans hrD⟩,hq.2⟩
    have hB : D.collar q ∈ D.B.1.image := hqp.symm ▸ interior_tangency_mem_B D hp
    have hy := B_collar_coordinate_vertical_zero D hqD hB
    have hrne : q.2.1 ≠ 0 := by
      intro hz
      have hboundary := (D.collar_boundary q hqD).2 hz
      exact (ModelWithCorners.disjoint_interior_boundary (I := 𝓡∂ 3)
        (M := E.Carrier)).le_bot ⟨hp.1,hqp ▸ hboundary⟩
    have hrpos : 0 < q.2.1 := lt_of_le_of_ne hq.1.1 (Ne.symm hrne)
    have hrad : r0 ≤ q.2.1 := by
      by_contra! hlt
      apply havoid
      refine ⟨(q.1,q.2.1),⟨hrpos,hlt⟩,?_⟩
      change D.collar (q.1,q.2.1,0) = p
      have hqeq : q = (q.1,(q.2.1,0)) := by
        apply Prod.ext
        · rfl
        · apply Prod.ext
          · rfl
          · exact hy
      rw [← hqeq]
      exact hqp
    change r0 ≤ if p ∈ D.collar '' halfCylinder r0 D.eta then D.radialCoordinate p else r0
    rw [ite_eq_left (show p ∈ D.collar '' halfCylinder r0 D.eta from ⟨q,hq,hqp⟩)]
    rw [←hqp,D.radial_exact q hqD]
    exact hrad
  ·
    change r0 ≤ if p ∈ D.collar '' halfCylinder r0 D.eta then D.radialCoordinate p else r0
    rw [ite_eq_right hpin]

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: AuditB3CollarV480 -/
noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}

/-- The paid B1 tangency globalization gives the complete regular-positive-collar
and finite-boundary-critical clauses of B3, after selecting one radius. -/
theorem b3_collar_paid_prefix (D : B1OriginalData g J) :
    ∃ r0 : ℝ, 0 < r0 ∧ r0 ≤ D.r0 ∧
      (∀ s : Circle, ∀ r : ℝ, 0 < r → r < r0 →
        mfderiv ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ)
          (fun q : Circle × ℝ => D.f q.1 q.2) (s, r) ≠ 0) ∧
      (collarCriticalPoints D).Finite ∧
      (∀ s ∈ collarCriticalPoints D, D.f s 0 = 0) := by
  obtain ⟨rho, hrho, hrhoD, hregular, hfinite⟩ :=
    SeifertSurfaces.OriginalEndpoints.original_prop57_tangencies D
  refine ⟨rho, hrho, hrhoD, ?_, hfinite, ?_⟩
  · intro s r hr hrr
    exact hregular s r ⟨hr, hrr⟩
  · exact collar_critical_boundary_values D

/-- Once an avoidance clause is supplied, the exact radial consequence is
available for every interior tangency.  This isolates the remaining B3 collar
obligation without adding it to the original theorem's hypotheses. -/
theorem b3_collar_radial_conditional (D : B1OriginalData g J)
    {r0 : ℝ} (hr0 : 0 < r0) (hrD : r0 ≤ D.r0)
    (havoid : ∀ p ∈ interiorTangencies D.A.1.embedding D.B.1.embedding,
      p ∉ openCollar D r0) :
    ∀ p ∈ interiorTangencies D.A.1.embedding D.B.1.embedding,
      r0 ≤ extendedRadial D r0 p := by
  intro p hp
  exact collar_radial_bound_of_avoidance D hr0 hrD hp (havoid p hp)

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3CollarTangencyExclusionV480 -/

noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}
set_option maxHeartbeats 500000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- The paid regular positive collar contains no actual interior tangent
coincidences between the two original collar surfaces. -/
theorem collar_regular_excludes_actual_tangencies_v480
    (D : B1OriginalData g J) {r0 : ℝ} (hr0 : 0 < r0) (hrD : r0 ≤ D.r0)
    (hreg : ∀ s : Circle, ∀ r : ℝ, 0 < r → r < r0 →
      mfderiv ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ)
        (fun q : Circle × ℝ => D.f q.1 q.2) (s,r) ≠ 0) :
    ∀ s : Circle, ∀ r : ℝ, 0 < r → r < r0 →
      D.collar (s,r,0) ∉ interiorTangencies D.A.1.embedding D.B.1.embedding := by
  intro s r hr hrr ht
  let x : E2 := (EuclideanSpace.equiv (Fin 2) ℝ).symm ![0,r]
  have hxrad : (localCircle D s (x 0),x 1) ∈ radialCylinder D.r0 := by
    change x 1 ∈ Icc (0 : ℝ) D.r0
    simpa [x] using And.intro hr.le (le_trans hrr.le hrD)
  have hz := collar_actual_tangency_local_height_critical_v480 D s r hr (lt_of_lt_of_le hrr hrD) ht
  have hz0 := collar_local_height_zero_implies_native_critical_v480 D s x hxrad hz
  have hx0 : x 0 = 0 := by simp [x]
  have hx1 : x 1 = r := by simp [x]
  have hpair : (localCircle D s (x 0),x 1) = (s,r) := by
    apply Prod.ext
    · change s * Circle.exp (2 * Real.pi * (x 0) / D.leafLength) = s
      rw [hx0]
      simp
    · exact hx1
  have hz0' : mfderiv ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ)
      (fun q : Circle × ℝ => D.f q.1 q.2) (s,r) = 0 := by
    convert hz0 using 1 <;> congr 1
    all_goals first | exact hpair.symm | congr 1 <;> first | exact hx1.symm | simp [localCircle,hx0]
  exact hreg s r hr hrr hz0'

/-- All original B3 collar clauses except global finiteness are now paid,
including the actual ambient collar avoidance and exact extended radial bound. -/
theorem original_b3_collar_regular_avoidance_radial_v480 (D : B1OriginalData g J) :
    ∃ r0 : ℝ, 0 < r0 ∧ r0 ≤ D.r0 ∧
      (∀ s : Circle, ∀ r : ℝ, 0 < r → r < r0 →
        mfderiv ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ)
          (fun q : Circle × ℝ => D.f q.1 q.2) (s,r) ≠ 0) ∧
      (collarCriticalPoints D).Finite ∧
      (∀ s ∈ collarCriticalPoints D, D.f s 0 = 0) ∧
      (∀ p ∈ interiorTangencies D.A.1.embedding D.B.1.embedding,
        p ∉ openCollar D r0) ∧
      (∀ p ∈ interiorTangencies D.A.1.embedding D.B.1.embedding,
        r0 ≤ extendedRadial D r0 p) := by
  obtain ⟨r0,hr0,hrD,hregular,hfinite,hboundary⟩ := b3_collar_paid_prefix D
  have havoid : ∀ p ∈ interiorTangencies D.A.1.embedding D.B.1.embedding,
      p ∉ openCollar D r0 := by
    intro p hp hpc
    obtain ⟨⟨s,r⟩,⟨hr,hrr⟩,he⟩ := hpc
    have he' : D.collar (s,r,0) = p := he
    rw [← he'] at hp
    exact collar_regular_excludes_actual_tangencies_v480 D hr0 hrD hregular s r hr hrr hp
  exact ⟨r0,hr0,hrD,hregular,hfinite,hboundary,havoid,
    b3_collar_radial_conditional D hr0 hrD havoid⟩

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3CompactDiscreteFiniteV480 -/

noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/-- Compactness plus the already proved isolated-neighborhood conclusion turns
an actual tangency locus into a finite set. -/
theorem compact_isolated_set_finite_v480
    {X : Type*} [TopologicalSpace X] [T1Space X]
    (Γ : Set X) (hcompact : IsCompact Γ)
    (hisolate : ∀ p ∈ Γ, ∃ U : Set X, IsOpen U ∧ U ∩ Γ = {p}) :
    Γ.Finite := by
  apply hcompact.finite
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro p hp
  obtain ⟨U,hU,hUp⟩ := hisolate p hp
  exact ⟨U,hU,by simpa [hUp]⟩

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3ContinuousRangeClosureV480 -/

noncomputable section
open Set Topology Function Filter
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.AppendixACoordinates
set_option maxHeartbeats 500000
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false

/-- Equality of two full-rank actual two-plane parametrizations is closed.
A fixed left inverse at the limit constructs a continuous local projection;
no Grassmannian topology or range-continuity assumption is inserted. -/
theorem full_rank_range_equality_at_closure_v480
    {X : Type*} [TopologicalSpace X]
    (L R : X → E2 →L[ℝ] E3) (S : Set X) (x0 : X)
    (hL : ContinuousAt L x0) (hR : ContinuousAt R x0)
    (hLi : Injective (L x0)) (hRi : Injective (R x0))
    (hx : x0 ∈ closure S)
    (hS : ∀ x ∈ S, LinearMap.range (L x).toLinearMap = LinearMap.range (R x).toLinearMap) :
    LinearMap.range (L x0).toLinearMap = LinearMap.range (R x0).toLinearMap := by
  classical
  letI : CompleteSpace E2 := FiniteDimensional.complete ℝ E2
  letI : CompleteSpace (E2 →L[ℝ] E2) := FiniteDimensional.complete ℝ (E2 →L[ℝ] E2)
  letI : HasSummableGeomSeries (E2 →L[ℝ] E2) := inferInstance
  obtain ⟨H,hH⟩ := ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hLi
  let J : X → E2 →L[ℝ] E2 := fun x => H.comp (L x)
  have hJ : ContinuousAt J x0 := continuousAt_const.clm_comp hL
  have hJ0 : J x0 = 1 := by
    apply ContinuousLinearMap.ext
    intro v
    exact hH v
  have hInv : ContinuousAt (fun x => Ring.inverse (J x)) x0 := by
    exact (show ContinuousAt Ring.inverse (J x0) from
      hJ0.symm ▸ NormedRing.inverse_continuousAt (1 : (E2 →L[ℝ] E2)ˣ)).comp hJ
  let C : Set X := {x | IsUnit (J x)}
  have hC : C ∈ 𝓝 x0 := hJ.preimage_mem_nhds
    (Units.isOpen.mem_nhds (hJ0.symm ▸ isUnit_one))
  have hxSC : x0 ∈ closure (S ∩ C) := by
    rw [mem_closure_iff_nhdsWithin_neBot,nhdsWithin_inter_of_mem' (nhdsWithin_le_nhds hC)]
    exact mem_closure_iff_nhdsWithin_neBot.mp hx
  let P : X → E3 →L[ℝ] E3 := fun x => (L x).comp ((Ring.inverse (J x)).comp H)
  let F : X → E2 →L[ℝ] E3 := fun x => (P x).comp (R x) - R x
  have hP : ContinuousAt P x0 := hL.clm_comp (hInv.clm_comp continuousAt_const)
  have hF : ContinuousAt F x0 := (hP.clm_comp hR).sub hR
  have hzero (x : X) (hxS : x ∈ S ∩ C) : F x = 0 := by
    apply ContinuousLinearMap.ext
    intro v
    have hv : R x v ∈ LinearMap.range (L x).toLinearMap :=
      (hS x hxS.1).symm ▸ LinearMap.mem_range_self (R x).toLinearMap v
    obtain ⟨w,hw⟩ := hv
    change L x w = R x v at hw
    have hcancel := congrArg (fun A : E2 →L[ℝ] E2 => A w) (Ring.inverse_mul_cancel (J x) hxS.2)
    change Ring.inverse (J x) (J x w) = w at hcancel
    change L x (Ring.inverse (J x) (H (R x v))) - R x v = 0
    rw [← hw]
    change L x (Ring.inverse (J x) (J x w)) - L x w = 0
    rw [hcancel,sub_self]
  have hF0 : F x0 = 0 := by
    have hc := hF.continuousWithinAt.mem_closure hxSC
      (show MapsTo F (S ∩ C) ({0} : Set (E2 →L[ℝ] E3)) from fun x hx => hzero x hx)
    simpa only [closure_singleton,Set.mem_singleton_iff] using hc
  have hle : LinearMap.range (R x0).toLinearMap ≤ LinearMap.range (L x0).toLinearMap := by
    rintro v ⟨w,rfl⟩
    refine ⟨Ring.inverse (J x0) (H (R x0 w)),?_⟩
    have hh := congrArg (fun A : E2 →L[ℝ] E3 => A w) hF0
    change L x0 (Ring.inverse (J x0) (H (R x0 w))) - R x0 w = 0 at hh
    exact sub_eq_zero.mp hh
  exact (Submodule.eq_of_le_of_finrank_eq hle
    (by rw [LinearMap.finrank_range_of_inj hRi,LinearMap.finrank_range_of_inj hLi])).symm

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3CoordinatePlaneTransportV480 -/

noncomputable section
open Set Topology Function Filter Bundle
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

/-- Every actual overlap change in the tangent-bundle core is bijective. -/
theorem vector_bundle_core_change_bijective_v480
    {X F ι : Type*} [TopologicalSpace X] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Z : VectorBundleCore ℝ X F ι) (i j : ι) (x : X)
    (hi : x ∈ Z.baseSet i) (hj : x ∈ Z.baseSet j) :
    Bijective (Z.coordChange i j x) := by
  have hleft : LeftInverse (Z.coordChange j i x) (Z.coordChange i j x) := by
    intro v
    exact (Z.coordChange_comp i j i x ⟨⟨hi,hj⟩,hi⟩ v).trans (Z.coordChange_self i x hi v)
  have hright : RightInverse (Z.coordChange j i x) (Z.coordChange i j x) := by
    intro v
    exact (Z.coordChange_comp j i j x ⟨⟨hj,hi⟩,hj⟩ v).trans (Z.coordChange_self j x hj v)
  exact ⟨hleft.injective,hright.surjective⟩

/-- Precomposing with an actual bijective coordinate change preserves range. -/
theorem continuous_linear_range_comp_surjective_v480
    {F G H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (L : G →L[ℝ] H) (A : F →L[ℝ] G) (hA : Surjective A) :
    LinearMap.range (L.comp A).toLinearMap = LinearMap.range L.toLinearMap := by
  ext v
  constructor
  · rintro ⟨w,rfl⟩
    exact ⟨A w,rfl⟩
  · rintro ⟨w,rfl⟩
    obtain ⟨z,rfl⟩ := hA w
    exact ⟨z,rfl⟩

/-- The actual derivative range in fixed tangent coordinates is the image of
its native range by the ambient overlap change. -/
theorem native_derivative_range_in_coordinates_v480
    {S : CompactOrientedSurface.{0}} (f : NeatEmbedding S E.Carrier)
    (a0 a : S)
    (ha : a ∈ (chartAt (EuclideanHalfSpace 2) a0).source)
    (hfa : f.toFun a ∈ (chartAt (EuclideanHalfSpace 3) (f.toFun a0)).source) :
    LinearMap.range
      (inTangentCoordinates (𝓡∂ 2) (𝓡∂ 3) id f.toFun
        (mfderiv (𝓡∂ 2) (𝓡∂ 3) f.toFun) a0 a).toLinearMap =
      Submodule.map
        ((tangentBundleCore (𝓡∂ 3) E.Carrier).coordChange
          (achart (EuclideanHalfSpace 3) (f.toFun a))
          (achart (EuclideanHalfSpace 3) (f.toFun a0)) (f.toFun a)).toLinearMap
        (LinearMap.range (mfderiv (𝓡∂ 2) (𝓡∂ 3) f.toFun a).toLinearMap) := by
  let A := (tangentBundleCore (𝓡∂ 2) S).coordChange
    (achart (EuclideanHalfSpace 2) a0) (achart (EuclideanHalfSpace 2) a) a
  let B := (tangentBundleCore (𝓡∂ 3) E.Carrier).coordChange
    (achart (EuclideanHalfSpace 3) (f.toFun a))
    (achart (EuclideanHalfSpace 3) (f.toFun a0)) (f.toFun a)
  have hAs : Surjective A := (vector_bundle_core_change_bijective_v480
    (tangentBundleCore (𝓡∂ 2) S) (achart (EuclideanHalfSpace 2) a0)
      (achart (EuclideanHalfSpace 2) a) a ha (mem_achart_source _ a)).2
  have heq : inTangentCoordinates (𝓡∂ 2) (𝓡∂ 3) id f.toFun
      (mfderiv (𝓡∂ 2) (𝓡∂ 3) f.toFun) a0 a =
      (B.comp (mfderiv (𝓡∂ 2) (𝓡∂ 3) f.toFun a)).comp A := by
    rw [inTangentCoordinates_eq id f.toFun _ ha hfa]
    rfl
  rw [heq,continuous_linear_range_comp_surjective_v480 _ A hAs]
  exact LinearMap.range_comp _ _

/-- Native immersion rank is retained in every actual overlap coordinate. -/
theorem native_derivative_in_coordinates_injective_v480
    {S : CompactOrientedSurface.{0}} (f : NeatEmbedding S E.Carrier)
    (a0 a : S)
    (ha : a ∈ (chartAt (EuclideanHalfSpace 2) a0).source)
    (hfa : f.toFun a ∈ (chartAt (EuclideanHalfSpace 3) (f.toFun a0)).source) :
    Injective (inTangentCoordinates (𝓡∂ 2) (𝓡∂ 3) id f.toFun
        (mfderiv (𝓡∂ 2) (𝓡∂ 3) f.toFun) a0 a) := by
  rw [inTangentCoordinates_eq id f.toFun _ ha hfa]
  apply Injective.comp
    (vector_bundle_core_change_bijective_v480 (tangentBundleCore (𝓡∂ 3) E.Carrier)
      (achart (EuclideanHalfSpace 3) (f.toFun a)) (achart (EuclideanHalfSpace 3) (f.toFun a0)) (f.toFun a) (mem_achart_source _ _) hfa).1
  exact ((f.smoothEmbedding.isImmersion.isImmersionAt a).mfderiv_injective (by simp)).comp
    (vector_bundle_core_change_bijective_v480 (tangentBundleCore (𝓡∂ 2) S)
      (achart (EuclideanHalfSpace 2) a0) (achart (EuclideanHalfSpace 2) a) a ha (mem_achart_source _ a)).1

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3ActualTangencyPairsCompactV480 -/

noncomputable section
open Set Topology Function Filter Bundle
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
set_option maxHeartbeats 500000
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false

/-- Actual embedding pairs with identical image point and identical native
rank-two derivative ranges; the image equality identifies the tangent fibers. -/
def nativeTangencyPairs_v480 {S B : CompactOrientedSurface.{0}}
    (f : NeatEmbedding S E.Carrier) (g : NeatEmbedding B E.Carrier) : Set (S × B) :=
  {q | f.toFun q.1 = g.toFun q.2 ∧
    LinearMap.range (mfderiv (𝓡∂ 2) (𝓡∂ 3) f.toFun q.1).toLinearMap =
      LinearMap.range (mfderiv (𝓡∂ 2) (𝓡∂ 3) g.toFun q.2).toLinearMap}

theorem native_tangent_range_coordinates_iff_v480
    {S B : CompactOrientedSurface.{0}}
    (f : NeatEmbedding S E.Carrier) (g : NeatEmbedding B E.Carrier)
    (a0 a : S) (b0 b : B) (h0 : f.toFun a0 = g.toFun b0) (h : f.toFun a = g.toFun b)
    (ha : a ∈ (chartAt (EuclideanHalfSpace 2) a0).source)
    (hb : b ∈ (chartAt (EuclideanHalfSpace 2) b0).source)
    (hfa : f.toFun a ∈ (chartAt (EuclideanHalfSpace 3) (f.toFun a0)).source)
    (hgb : g.toFun b ∈ (chartAt (EuclideanHalfSpace 3) (g.toFun b0)).source) :
    LinearMap.range (inTangentCoordinates (𝓡∂ 2) (𝓡∂ 3) id f.toFun
      (mfderiv (𝓡∂ 2) (𝓡∂ 3) f.toFun) a0 a).toLinearMap =
      LinearMap.range (inTangentCoordinates (𝓡∂ 2) (𝓡∂ 3) id g.toFun
        (mfderiv (𝓡∂ 2) (𝓡∂ 3) g.toFun) b0 b).toLinearMap ↔
    LinearMap.range (mfderiv (𝓡∂ 2) (𝓡∂ 3) f.toFun a).toLinearMap =
      LinearMap.range (mfderiv (𝓡∂ 2) (𝓡∂ 3) g.toFun b).toLinearMap := by
  rw [native_derivative_range_in_coordinates_v480 f a0 a ha hfa,
    native_derivative_range_in_coordinates_v480 g b0 b hb hgb]
  have hpost : (tangentBundleCore (𝓡∂ 3) E.Carrier).coordChange
      (achart (EuclideanHalfSpace 3) (f.toFun a)) (achart (EuclideanHalfSpace 3) (f.toFun a0)) (f.toFun a) =
    (tangentBundleCore (𝓡∂ 3) E.Carrier).coordChange
      (achart (EuclideanHalfSpace 3) (g.toFun b)) (achart (EuclideanHalfSpace 3) (g.toFun b0)) (g.toFun b) := by rw [h,h0]
  rw [hpost]
  exact (Submodule.map_injective_of_injective
    (vector_bundle_core_change_bijective_v480 (tangentBundleCore (𝓡∂ 3) E.Carrier)
      (achart (EuclideanHalfSpace 3) (g.toFun b)) (achart (EuclideanHalfSpace 3) (g.toFun b0))
      (g.toFun b) (mem_achart_source _ _) hgb).1).eq_iff

/-- The actual coincidence-and-tangent pair locus is closed, including at
boundary points. Smooth differential coordinates and full rank supply the
closure argument without an added tangency-closedness premise. -/
theorem native_tangency_pairs_closed_v480
    {S B : CompactOrientedSurface.{0}}
    (f : NeatEmbedding S E.Carrier) (g : NeatEmbedding B E.Carrier) :
    IsClosed (nativeTangencyPairs_v480 f g) := by
  apply isClosed_of_closure_subset
  intro q0 hq0
  let a0 := q0.1
  let b0 := q0.2
  have himages : IsClosed {q : S × B | f.toFun q.1 = g.toFun q.2} :=
    isClosed_eq (f.smoothEmbedding.isEmbedding.continuous.comp continuous_fst)
      (g.smoothEmbedding.isEmbedding.continuous.comp continuous_snd)
  have h0 : f.toFun a0 = g.toFun b0 :=
    closure_minimal (fun q hq => hq.1) himages hq0
  let L : S × B → E2 →L[ℝ] E3 := fun q => inTangentCoordinates (𝓡∂ 2) (𝓡∂ 3) id f.toFun
    (mfderiv (𝓡∂ 2) (𝓡∂ 3) f.toFun) a0 q.1
  let R : S × B → E2 →L[ℝ] E3 := fun q => inTangentCoordinates (𝓡∂ 2) (𝓡∂ 3) id g.toFun
    (mfderiv (𝓡∂ 2) (𝓡∂ 3) g.toFun) b0 q.2
  have hL : ContinuousAt L q0 :=
    ((f.smoothEmbedding.contMDiff.contMDiffAt (x := a0)).mfderiv_const
      (m := 0) (by simp)).continuousAt.comp continuousAt_fst
  have hR : ContinuousAt R q0 :=
    ((g.smoothEmbedding.contMDiff.contMDiffAt (x := b0)).mfderiv_const
      (m := 0) (by simp)).continuousAt.comp continuousAt_snd
  let U : Set (S × B) := {q | q.1 ∈ (chartAt (EuclideanHalfSpace 2) a0).source ∧
    q.2 ∈ (chartAt (EuclideanHalfSpace 2) b0).source ∧
    f.toFun q.1 ∈ (chartAt (EuclideanHalfSpace 3) (f.toFun a0)).source ∧
    g.toFun q.2 ∈ (chartAt (EuclideanHalfSpace 3) (g.toFun b0)).source}
  have hU : U ∈ 𝓝 q0 := by
    apply Filter.inter_mem
      (continuousAt_fst.preimage_mem_nhds (chart_source_mem_nhds (H := EuclideanHalfSpace 2) a0))
    apply Filter.inter_mem
      (continuousAt_snd.preimage_mem_nhds (chart_source_mem_nhds (H := EuclideanHalfSpace 2) b0))
    exact Filter.inter_mem
      ((f.smoothEmbedding.isEmbedding.continuous.comp continuous_fst).continuousAt.preimage_mem_nhds
        (chart_source_mem_nhds (H := EuclideanHalfSpace 3) (f.toFun a0)))
      ((g.smoothEmbedding.isEmbedding.continuous.comp continuous_snd).continuousAt.preimage_mem_nhds
        (chart_source_mem_nhds (H := EuclideanHalfSpace 3) (g.toFun b0)))
  have hqU : q0 ∈ closure (nativeTangencyPairs_v480 f g ∩ U) := by
    rw [mem_closure_iff_nhdsWithin_neBot,nhdsWithin_inter_of_mem' (nhdsWithin_le_nhds hU)]
    exact mem_closure_iff_nhdsWithin_neBot.mp hq0
  have hLi : Injective (L q0) := native_derivative_in_coordinates_injective_v480 f a0 a0
    (mem_chart_source _ a0) (mem_chart_source _ _)
  have hRi : Injective (R q0) := native_derivative_in_coordinates_injective_v480 g b0 b0
    (mem_chart_source _ b0) (mem_chart_source _ _)
  have hranges := full_rank_range_equality_at_closure_v480 L R
    (nativeTangencyPairs_v480 f g ∩ U) q0 hL hR hLi hRi hqU
    (fun q hq => (native_tangent_range_coordinates_iff_v480 f g a0 q.1 b0 q.2 h0 hq.1.1
      hq.2.1 hq.2.2.1 hq.2.2.2.1 hq.2.2.2.2).mpr hq.1.2)
  exact ⟨h0,(native_tangent_range_coordinates_iff_v480 f g a0 a0 b0 b0 h0 h0
    (mem_chart_source _ _) (mem_chart_source _ _) (mem_chart_source _ _) (mem_chart_source _ _)).mp hranges⟩

/-- Compact original source surfaces make the whole actual tangent-pair locus
compact before restricting its image to the ambient interior. -/
theorem native_tangency_pairs_compact_v480
    {S B : CompactOrientedSurface.{0}}
    (f : NeatEmbedding S E.Carrier) (g : NeatEmbedding B E.Carrier) :
    IsCompact (nativeTangencyPairs_v480 f g) :=
  (native_tangency_pairs_closed_v480 f g).isCompact

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3TangencyImageCompactV480 -/

noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

/-- The compact native pair image represents exactly the protected original
interior tangent-plane locus after intersecting with the actual interior. -/
theorem interior_tangencies_eq_native_pair_image_v480
    {S B : CompactOrientedSurface.{0}}
    (f : NeatEmbedding S E.Carrier) (h : NeatEmbedding B E.Carrier) :
    interiorTangencies f h =
      ((fun q : S × B => f.toFun q.1) '' nativeTangencyPairs_v480 f h) ∩ (𝓡∂ 3).interior E.Carrier := by
  ext p
  constructor
  · rintro ⟨hp,a,b,ha,hb,ht⟩
    have htf : tangentPlaneAt f a p ha =
        LinearMap.range (mfderiv (𝓡∂ 2) (𝓡∂ 3) f.toFun a).toLinearMap := by cases ha; rfl
    have hth : tangentPlaneAt h b p hb =
        LinearMap.range (mfderiv (𝓡∂ 2) (𝓡∂ 3) h.toFun b).toLinearMap := by cases hb; rfl
    exact ⟨⟨(a,b),⟨ha.trans hb.symm,htf.symm.trans (ht.trans hth)⟩,ha⟩,hp⟩
  · rintro ⟨⟨⟨a,b⟩,⟨hab,ht⟩,ha⟩,hp⟩
    have hb : h.toFun b = p := hab.symm.trans ha
    refine ⟨hp,a,b,ha,hb,?_⟩
    have htf : tangentPlaneAt f a p ha =
        LinearMap.range (mfderiv (𝓡∂ 2) (𝓡∂ 3) f.toFun a).toLinearMap := by cases ha; rfl
    have hth : tangentPlaneAt h b p hb =
        LinearMap.range (mfderiv (𝓡∂ 2) (𝓡∂ 3) h.toFun b).toLinearMap := by cases hb; rfl
    exact htf.trans (ht.trans hth.symm)

/-- The whole native tangent-point image, including any boundary tangencies,
is compact with its actual exterior topology. -/
theorem native_tangent_point_image_compact_v480
    {S B : CompactOrientedSurface.{0}}
    (f : NeatEmbedding S E.Carrier) (h : NeatEmbedding B E.Carrier) :
    IsCompact ((fun q : S × B => f.toFun q.1) '' nativeTangencyPairs_v480 f h) :=
  (native_tangency_pairs_compact_v480 f h).image
    (f.smoothEmbedding.isEmbedding.continuous.comp continuous_fst)

/-- Disjoint actual boundary images put every native tangent point in the
ambient interior, making the original interior tangent locus compact. -/
theorem disjoint_boundary_interior_tangencies_compact_v480
    {S B : CompactOrientedSurface.{0}}
    (f : NeatEmbedding S E.Carrier) (h : NeatEmbedding B E.Carrier)
    (hbound : Disjoint (exteriorBoundary f) (exteriorBoundary h)) :
    IsCompact (interiorTangencies f h) := by
  have hinside : ((fun q : S × B => f.toFun q.1) '' nativeTangencyPairs_v480 f h) ⊆
      (𝓡∂ 3).interior E.Carrier := by
    rintro p ⟨⟨a,b⟩,⟨hab,ht⟩,rfl⟩
    change (𝓡∂ 3).IsInteriorPoint (f.toFun a)
    rw [(𝓡∂ 3).isInteriorPoint_iff_not_isBoundaryPoint]
    intro hp
    have ha : a ∈ S.boundary := by rwa [← f.boundary_preimage]
    have hb : b ∈ B.boundary := by
      rw [← h.boundary_preimage]
      change (𝓡∂ 3).IsBoundaryPoint (h.toFun b)
      rw [← hab]
      exact hp
    exact Set.disjoint_left.mp hbound ⟨a,ha,rfl⟩ ⟨b,hb,hab.symm⟩
  rw [interior_tangencies_eq_native_pair_image_v480 f h,inter_eq_left.mpr hinside]
  exact native_tangent_point_image_compact_v480 f h

/-- Complete original B3, as consumed in configuration T1: the actual local
conclusion and actual global finiteness under its existing disjoint-boundary
configuration hypothesis. No finiteness, PDE or graph witness is assumed. -/
theorem original_pair_disjoint_boundary_full_B3_v480 (D : OriginalPair g J)
    (hbound : Disjoint (exteriorBoundary D.A.1.embedding) (exteriorBoundary D.B.1.embedding)) :
    InteriorTangencyConclusion D ∧ (interiorTangencies D.A.1.embedding D.B.1.embedding).Finite := by
  have hlocal := original_pair_interior_tangency_conclusion_v480 D
  refine ⟨hlocal,compact_isolated_set_finite_v480 _
    (disjoint_boundary_interior_tangencies_compact_v480 D.A.1.embedding D.B.1.embedding hbound) ?_⟩
  intro p hp
  obtain ⟨U,hU,hpU,hUt⟩ := (hlocal p hp).1
  exact ⟨U,hU,hUt⟩

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3DistinctLongitudeBoundaryV480 -/

noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}

theorem distinct_longitude_leaves_disjoint_v480 {a b : Circle} (hab : a ≠ b) :
    Disjoint (J.leaf a) (J.leaf b) := by
  rw [Set.disjoint_left]
  intro p hpa hpb
  obtain ⟨za,hza⟩ := hpa
  obtain ⟨zb,hzb⟩ := hpb
  have htor : (a,za) = (b,zb) :=
    J.smoothEmbedding.isEmbedding.injective (hza.trans hzb.symm)
  exact hab (congrArg Prod.fst htor)

theorem original_pair_distinct_boundary_labels_full_B3_v480 (D : OriginalPair g J)
    (hlabels : ∃ a b : Circle, a ≠ b ∧
      D.A.1.embedding.toFun '' D.A.1.surface.boundary = J.leaf a ∧
      D.B.1.embedding.toFun '' D.B.1.surface.boundary = J.leaf b) :
    InteriorTangencyConclusion D ∧
      (interiorTangencies D.A.1.embedding D.B.1.embedding).Finite := by
  obtain ⟨a,b,hab,ha,hb⟩ := hlabels
  apply original_pair_disjoint_boundary_full_B3_v480 D
  change Disjoint (D.A.1.embedding.toFun '' D.A.1.surface.boundary)
    (D.B.1.embedding.toFun '' D.B.1.surface.boundary)
  rw [ha,hb]
  exact distinct_longitude_leaves_disjoint_v480 hab

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3BoundaryGraphConsequencesV480 -/

noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

private theorem consequence_base_point_v480 (x : E2) (t : ℝ) :
    native_collar_base_v475 (graphPoint x t) = x := by
  ext i
  fin_cases i <;> simp [native_collar_base_v475,graphPoint]

/-- Opposite halfspace orientation excludes every actual interior intersection
throughout the constructed boundary chart. -/
theorem boundary_graph_reversed_excludes_interior_v480
    {S B : CompactOrientedSurface.{0}} (f : NeatEmbedding S E.Carrier)
    (g : NeatEmbedding B E.Carrier) {p : E.Carrier}
    (c : ActualBoundaryPairGraphV480 f g p) (hc : c.coefficient < 0) :
    Disjoint (E.toSphere ⁻¹' c.coordinates.chart.source ∩ (𝓡∂ 3).interior E.Carrier)
      (range f.toFun ∩ range g.toFun) := by
  rw [Set.disjoint_left]
  rintro q ⟨hqC,hqI⟩ ⟨⟨a,ha⟩,⟨b,hb⟩⟩
  have hqA : E.toSphere q ∈ range (E.toSphere ∘ f.toFun) ∩ c.coordinates.chart.source :=
    ⟨⟨a,congrArg E.toSphere ha⟩,hqC⟩
  have hqB : E.toSphere q ∈ range (E.toSphere ∘ g.toFun) ∩ c.coordinates.chart.source :=
    ⟨⟨b,congrArg E.toSphere hb⟩,hqC⟩
  rw [c.graph_A] at hqA
  rw [c.graph_B] at hqB
  obtain ⟨x,⟨hx,hx0⟩,hxq⟩ := hqA
  obtain ⟨y,⟨hy,hy0⟩,hyq⟩ := hqB
  have hxy : graphPoint x 0 = graphPoint y (c.height y) := by
    have hh := congrArg c.coordinates.chart (hxq.trans hyq.symm)
    rwa [c.coordinates.chart.right_inv (c.points_inside x hx).1,
      c.coordinates.chart.right_inv (c.points_inside y hy).2] at hh
  have hxy' : x = y := by
    simpa only [consequence_base_point_v480] using congrArg native_collar_base_v475 hxy
  subst y
  have hx0zero : x 0 = 0 := by
    have hprod := (c.halfspace_sign x hx).2.2.mp hx0
    have hneg := mul_nonpos_of_nonpos_of_nonneg hc.le hy0
    have hpzero : c.coefficient * c.inversePlanar x 0 = 0 := le_antisymm hneg hprod
    have hinvzero := (mul_eq_zero_iff_left c.coefficient_ne).mp hpzero
    exact (c.halfspace_sign x hx).1.mp hinvzero
  have hqBound : E.toSphere q ∈
      (E.toSphere ∘ f.toFun) '' S.boundary ∩ c.coordinates.chart.source := by
    rw [c.boundary_A]
    exact ⟨x,⟨hx,hx0zero⟩,hxq⟩
  obtain ⟨a0,ha0,hqa0⟩ := hqBound.1
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  have hqa : f.toFun a0 = q := hinc.isEmbedding.injective hqa0
  have hqboundary : q ∈ (𝓡∂ 3).boundary E.Carrier := by
    have hh : f.toFun a0 ∈ (𝓡∂ 3).boundary E.Carrier := by
      rwa [← f.boundary_preimage] at ha0
    rwa [hqa] at hh
  exact (ModelWithCorners.disjoint_interior_boundary (I := 𝓡∂ 3)
    (M := E.Carrier)).le_bot ⟨hqI,hqboundary⟩

/-- A shared boundary point forces equality of the two literal longitude
boundaries from the original relative minima. -/
theorem original_pair_common_boundary_exact_v480
    {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}
    (D : OriginalPair g J) {p : E.Carrier}
    (ha : p ∈ D.A.1.embedding.toFun '' D.A.1.surface.boundary)
    (hb : p ∈ D.B.1.embedding.toFun '' D.B.1.surface.boundary) :
    D.A.1.embedding.toFun '' D.A.1.surface.boundary =
      D.B.1.embedding.toFun '' D.B.1.surface.boundary := by
  obtain ⟨a,haJ⟩ := D.A_minimum.1
  obtain ⟨b,hbJ⟩ := D.B_minimum.1
  have hab : a = b := by
    by_contra hn
    exact Set.disjoint_left.mp (distinct_longitude_leaves_disjoint_v480 hn)
      (haJ ▸ ha) (hbJ ▸ hb)
  rw [haJ,hbJ,hab]

/-- Every actual boundary point of the compact native tangency image has the
constructed full shared-boundary graph. No original collar is supplied. -/
theorem original_pair_boundary_tangency_actual_graph_v480
    {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}
    (D : OriginalPair g J) {p : E.Carrier}
    (hp : p ∈ (𝓡∂ 3).boundary E.Carrier)
    (ht : p ∈ (fun q : D.A.1.surface × D.B.1.surface => D.A.1.embedding.toFun q.1) ''
      nativeTangencyPairs_v480 D.A.1.embedding D.B.1.embedding) :
    Nonempty (ActualBoundaryPairGraphV480 D.A.1.embedding D.B.1.embedding p) := by
  obtain ⟨⟨a,b⟩,⟨hab,ht⟩,ha⟩ := ht
  change D.A.1.embedding.toFun a = p at ha
  change D.A.1.embedding.toFun a = D.B.1.embedding.toFun b at hab
  have hb : D.B.1.embedding.toFun b = p := hab.symm.trans ha
  have haB : a ∈ D.A.1.surface.boundary := by
    rw [← D.A.1.embedding.boundary_preimage]
    change D.A.1.embedding.toFun a ∈ (𝓡∂ 3).boundary E.Carrier
    rwa [ha]
  have hbB : b ∈ D.B.1.surface.boundary := by
    rw [← D.B.1.embedding.boundary_preimage]
    change D.B.1.embedding.toFun b ∈ (𝓡∂ 3).boundary E.Carrier
    rwa [hb]
  have hbound := original_pair_common_boundary_exact_v480 D
    (show p ∈ D.A.1.embedding.toFun '' D.A.1.surface.boundary from ⟨a,haB,ha⟩)
    (show p ∈ D.B.1.embedding.toFun '' D.B.1.surface.boundary from ⟨b,hbB,hb⟩)
  have hb0 : D.B.1.embedding.toFun b = D.A.1.embedding.toFun a := hab.symm
  have htan : tangentPlaneAt D.A.1.embedding a (D.A.1.embedding.toFun a) rfl =
      tangentPlaneAt D.B.1.embedding b (D.A.1.embedding.toFun a) hb0 := by
    have hcast : tangentPlaneAt D.B.1.embedding b (D.A.1.embedding.toFun a) hb0 =
        LinearMap.range (mfderiv (𝓡∂ 2) (𝓡∂ 3) D.B.1.embedding.toFun b).toLinearMap := by
      unfold tangentPlaneAt
      exact eq_of_heq (@eqRec_heq E.Carrier
        (fun v : E.Carrier => Submodule ℝ (TangentSpace (𝓡∂ 3) v))
        _ _ hb0 (LinearMap.range (mfderiv (𝓡∂ 2) (𝓡∂ 3) D.B.1.embedding.toFun b).toLinearMap))
    exact ht.trans hcast.symm
  have hc := actual_boundary_pair_graph_v480 D.A.1.embedding D.B.1.embedding a b
    haB hbB hb0 hbound htan
  rwa [ha] at hc

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3BoundaryGraphParametersV480 -/

noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- Actual source parameters are recovered through the proved sphere
immersion, including boundary points; inverse smoothness is constructed. -/
theorem actual_sphere_graph_source_parameter_v480
    {S : CompactOrientedSurface.{0}} (f : NeatEmbedding S E.Carrier) (a : S)
    (O : Set E2) (hO : IsOpen O) (Γ : E2 → ThreeSphere)
    (hΓ : ContMDiffOn 𝓘(ℝ,E2) (𝓡 3) ∞ Γ O)
    (himage : ∀ x ∈ O, Γ x ∈ range (E.toSphere ∘ f.toFun)) :
    ∃ q : E2 → S, ContMDiffOn 𝓘(ℝ,E2) (𝓡∂ 2) ∞ q O ∧
      ∀ x ∈ O, E.toSphere (f.toFun (q x)) = Γ x := by
  classical
  let q : E2 → S := fun x => if hx : x ∈ O then (himage x hx).choose else a
  have heq (x : E2) (hx : x ∈ O) : (E.toSphere ∘ f.toFun) (q x) = Γ x := by
    simp only [q,dif_pos hx]
    exact (himage x hx).choose_spec
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  have hF : IsEmbedding (E.toSphere ∘ f.toFun) :=
    hinc.isEmbedding.comp f.smoothEmbedding.isEmbedding
  have hq : ContinuousOn q O := hF.isInducing.continuousOn_iff.mpr
    (hΓ.continuousOn.congr heq)
  refine ⟨q,?_,heq⟩
  intro x hx
  have hcomp : ContMDiffAt 𝓘(ℝ,E2) (𝓡 3) ∞ ((E.toSphere ∘ f.toFun) ∘ q) x := by
    apply (hΓ.contMDiffAt (hO.mem_nhds hx)).congr_of_eventuallyEq
    exact eventuallyEq_of_mem (hO.mem_nhds hx) (fun y hy => heq y hy)
  exact ((ContMDiffAt.iff_comp_isImmersionAt (I := 𝓘(ℝ,E2))
    (actual_neat_sphere_immersion_v480 f (q x)).isImmersionAt).mpr
      ⟨(hq x hx).continuousAt (hO.mem_nhds hx),hcomp⟩).contMDiffWithinAt

private theorem parameter_base_point_v480 (x : E2) (t : ℝ) :
    native_collar_base_v475 (graphPoint x t) = x := by
  ext i
  fin_cases i <;> simp [native_collar_base_v475,graphPoint]

/-- For the positive orientation the actual two halfspace graphs have genuine
smooth source parameters on their full common open interior, with both source
boundaries excluded. -/
theorem actual_boundary_positive_graph_parameters_v480
    {S B : CompactOrientedSurface.{0}} (f : NeatEmbedding S E.Carrier)
    (g : NeatEmbedding B E.Carrier) (a : S) (b : B) {p : E.Carrier}
    (c : ActualBoundaryPairGraphV480 f g p) (hc : 0 < c.coefficient)
    (hboundary : f.toFun '' S.boundary = g.toFun '' B.boundary) :
    ∃ qA : E2 → S, ∃ qB : E2 → B,
      ContMDiffOn 𝓘(ℝ,E2) (𝓡∂ 2) ∞ qA {x ∈ c.O | 0 < x 0} ∧
      ContMDiffOn 𝓘(ℝ,E2) (𝓡∂ 2) ∞ qB {x ∈ c.O | 0 < x 0} ∧
      (∀ x ∈ {x ∈ c.O | 0 < x 0},
        E.toSphere (f.toFun (qA x)) = c.coordinates.chart.symm (graphPoint x 0) ∧
        qA x ∉ S.boundary) ∧
      (∀ x ∈ {x ∈ c.O | 0 < x 0},
        E.toSphere (g.toFun (qB x)) = c.coordinates.chart.symm (graphPoint x (c.height x)) ∧
        qB x ∉ B.boundary) := by
  let O : Set E2 := {x ∈ c.O | 0 < x 0}
  have hO : IsOpen O := c.open_O.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).continuous)
  have hpointSmooth (u : E2 → ℝ) (hu : ContDiffOn ℝ ∞ u O) :
      ContDiffOn ℝ ∞ (fun x => graphPoint x (u x)) O := by
    change ContDiffOn ℝ ∞ (fun x => native_interior_graph_splitting_v475 (x,u x)) O
    exact native_interior_graph_splitting_v475.contDiff.comp_contDiffOn (contDiffOn_id.prodMk hu)
  have hΓA : ContMDiffOn 𝓘(ℝ,E2) (𝓡 3) ∞
      (fun x => c.coordinates.chart.symm (graphPoint x 0)) O :=
    c.coordinates.inverse_smooth.comp (hpointSmooth (fun _ => 0) contDiffOn_const).contMDiffOn
      (fun x hx => (c.points_inside x hx.1).1)
  have hΓB : ContMDiffOn 𝓘(ℝ,E2) (𝓡 3) ∞
      (fun x => c.coordinates.chart.symm (graphPoint x (c.height x))) O :=
    c.coordinates.inverse_smooth.comp (hpointSmooth c.height
      (c.height_smooth.mono inter_subset_left)).contMDiffOn
      (fun x hx => (c.points_inside x hx.1).2)
  have himageA (x : E2) (hx : x ∈ O) :
      c.coordinates.chart.symm (graphPoint x 0) ∈ range (E.toSphere ∘ f.toFun) := by
    have hh : c.coordinates.chart.symm (graphPoint x 0) ∈
        range (E.toSphere ∘ f.toFun) ∩ c.coordinates.chart.source := by
      rw [c.graph_A]
      exact ⟨x,⟨hx.1,hx.2.le⟩,rfl⟩
    exact hh.1
  have himageB (x : E2) (hx : x ∈ O) :
      c.coordinates.chart.symm (graphPoint x (c.height x)) ∈ range (E.toSphere ∘ g.toFun) := by
    have hprod := (c.halfspace_sign x hx.1).2.1.mp hx.2
    have hinv : 0 ≤ c.inversePlanar x 0 := (pos_of_mul_pos_right hprod hc.le).le
    have hh : c.coordinates.chart.symm (graphPoint x (c.height x)) ∈
        range (E.toSphere ∘ g.toFun) ∩ c.coordinates.chart.source := by
      rw [c.graph_B]
      exact ⟨x,⟨hx.1,hinv⟩,rfl⟩
    exact hh.1
  obtain ⟨qA,hqA,heA⟩ := actual_sphere_graph_source_parameter_v480 f a O hO _ hΓA himageA
  obtain ⟨qB,hqB,heB⟩ := actual_sphere_graph_source_parameter_v480 g b O hO _ hΓB himageB
  have hSphereBoundary : (E.toSphere ∘ f.toFun) '' S.boundary =
      (E.toSphere ∘ g.toFun) '' B.boundary := by
    calc
      _ = E.toSphere '' (f.toFun '' S.boundary) := (image_image _ _ _).symm
      _ = E.toSphere '' (g.toFun '' B.boundary) := congrArg (fun s => E.toSphere '' s) hboundary
      _ = _ := image_image _ _ _
  have hBoundaryExclusion (x : E2) (t : ℝ) (hx : x ∈ O)
      (ht : graphPoint x t ∈ c.coordinates.chart.target) :
      c.coordinates.chart.symm (graphPoint x t) ∉ (E.toSphere ∘ f.toFun) '' S.boundary := by
    intro hbd
    have hh : c.coordinates.chart.symm (graphPoint x t) ∈
        (E.toSphere ∘ f.toFun) '' S.boundary ∩ c.coordinates.chart.source :=
      ⟨hbd,c.coordinates.chart.map_target ht⟩
    rw [c.boundary_A] at hh
    obtain ⟨y,⟨hy,hy0⟩,hyx⟩ := hh
    have heq := congrArg c.coordinates.chart hyx
    rw [c.coordinates.chart.right_inv (c.points_inside y hy).1,
      c.coordinates.chart.right_inv ht] at heq
    have hxy : y = x := by
      simpa only [parameter_base_point_v480] using congrArg native_collar_base_v475 heq
    rw [hxy] at hy0
    exact hx.2.ne' hy0
  refine ⟨qA,qB,hqA,hqB,?_,?_⟩
  · intro x hx
    refine ⟨heA x hx,?_⟩
    intro hb
    apply hBoundaryExclusion x 0 hx (c.points_inside x hx.1).1
    exact ⟨qA x,hb,heA x hx⟩
  · intro x hx
    refine ⟨heB x hx,?_⟩
    intro hb
    apply hBoundaryExclusion x (c.height x) hx (c.points_inside x hx.1).2
    rw [hSphereBoundary]
    exact ⟨qB x,hb,heB x hx⟩

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3BoundaryGraphTangencyCriticalV480 -/

noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

private theorem critical_base_point_v480 (x : E2) (t : ℝ) :
    native_collar_base_v475 (graphPoint x t) = x := by
  ext i
  fin_cases i <;> simp [native_collar_base_v475,graphPoint]

private theorem critical_reconstruct_v480 (v : E3) :
    graphPoint (native_collar_base_v475 v) (v 2) = v := by
  ext i
  fin_cases i <;> simp [native_collar_base_v475,graphPoint]

/-- Every actual interior tangency in the constructed boundary graph forces
a zero derivative of its same literal height. -/
theorem actual_boundary_graph_tangency_critical_v480
    {S B : CompactOrientedSurface.{0}} (f : NeatEmbedding S E.Carrier)
    (g : NeatEmbedding B E.Carrier) {p : E.Carrier}
    (c : ActualBoundaryPairGraphV480 f g p) {q : E.Carrier}
    (hqC : E.toSphere q ∈ c.coordinates.chart.source)
    (hqt : q ∈ interiorTangencies f g) :
    fderiv ℝ c.height (native_collar_base_v475 (c.coordinates.chart (E.toSphere q))) = 0 := by
  let C := c.coordinates
  have hsplit (v : E3) : native_interior_graph_splitting_v475.symm v =
      (native_collar_base_v475 v,v 2) := by
    calc
      _ = native_interior_graph_splitting_v475.symm
          (graphPoint (native_collar_base_v475 v) (v 2)) :=
        congrArg native_interior_graph_splitting_v475.symm (critical_reconstruct_v480 v).symm
      _ = _ := native_interior_graph_splitting_v475.symm_apply_apply (native_collar_base_v475 v,v 2)
  let Φ := C.chart.transHomeomorph native_interior_graph_splitting_v475.symm.toHomeomorph
  have hΦ : ContMDiffOn (𝓡 3) 𝓘(ℝ,E2 × ℝ) ∞ Φ Φ.source :=
    native_interior_graph_splitting_v475.symm.contDiff.contMDiff.comp_contMDiffOn C.smooth
  have hΦi : ContMDiffOn 𝓘(ℝ,E2 × ℝ) (𝓡 3) ∞ Φ.symm Φ.target :=
    C.inverse_smooth.comp native_interior_graph_splitting_v475.contDiff.contMDiff.contMDiffOn
      (fun _ hx => hx)
  have hΦfst (v : ThreeSphere) : (Φ v).1 = native_collar_base_v475 (C.chart v) := by
    change (native_interior_graph_splitting_v475.symm (C.chart v)).1 = _
    rw [hsplit]
  have hΦsnd (v : ThreeSphere) : (Φ v).2 = (C.chart v) 2 := by
    change (native_interior_graph_splitting_v475.symm (C.chart v)).2 = _
    rw [hsplit]
  have hO {v : ThreeSphere} (hv : v ∈ C.chart.source) :
      native_collar_base_v475 (C.chart v) ∈ c.O := by
    have hh := C.chart.map_source hv
    rw [c.target_exact] at hh
    obtain ⟨⟨x,t⟩,⟨hx,ht⟩,hxt⟩ := hh
    have he := congrArg native_collar_base_v475 hxt
    change native_collar_base_v475 (graphPoint x t) = _ at he
    rw [critical_base_point_v480] at he
    exact he ▸ hx
  have hA (a : S) (ha : E.toSphere (f.toFun a) ∈ C.chart.source) :
      (C.chart (E.toSphere (f.toFun a))) 2 = 0 := by
    have hh : E.toSphere (f.toFun a) ∈ range (E.toSphere ∘ f.toFun) ∩ C.chart.source :=
      ⟨⟨a,rfl⟩,ha⟩
    rw [c.graph_A] at hh
    obtain ⟨x,⟨hx,hx0⟩,he⟩ := hh
    have hc := congrArg C.chart he
    rw [C.chart.right_inv (c.points_inside x hx).1] at hc
    have ht := congrArg (fun v : E3 => v 2) hc
    simpa [graphPoint] using ht.symm
  have hB (b : B) (hb : E.toSphere (g.toFun b) ∈ C.chart.source) :
      (C.chart (E.toSphere (g.toFun b))) 2 =
        c.height (native_collar_base_v475 (C.chart (E.toSphere (g.toFun b)))) := by
    have hh : E.toSphere (g.toFun b) ∈ range (E.toSphere ∘ g.toFun) ∩ C.chart.source :=
      ⟨⟨b,rfl⟩,hb⟩
    rw [c.graph_B] at hh
    obtain ⟨x,⟨hx,hx0⟩,he⟩ := hh
    have hc := congrArg C.chart he
    rw [C.chart.right_inv (c.points_inside x hx).2] at hc
    rw [← hc,critical_base_point_v480]
    rfl
  obtain ⟨hqI,a,b,ha,hb,ht⟩ := hqt
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  have hFa := hinc.isEmbedding.continuous.comp f.smoothEmbedding.isEmbedding.continuous
  have hGb := hinc.isEmbedding.continuous.comp g.smoothEmbedding.isEmbedding.continuous
  have hfirst : (fun v => (Φ (E.toSphere (f.toFun v))).2) =ᶠ[𝓝 a] fun _ => (0 : ℝ) := by
    filter_upwards [hFa.continuousAt.preimage_mem_nhds
      (C.chart.open_source.mem_nhds (by simpa only [Function.comp_apply,ha] using hqC))] with v hv
    rw [hΦsnd]
    exact hA v hv
  have hsecond : (fun v => c.height (Φ (E.toSphere (g.toFun v))).1) =ᶠ[𝓝 b]
      (fun v => (Φ (E.toSphere (g.toFun v))).2) := by
    filter_upwards [hGb.continuousAt.preimage_mem_nhds
      (C.chart.open_source.mem_nhds (by simpa only [Function.comp_apply,hb] using hqC))] with v hv
    rw [hΦfst,hΦsnd]
    exact (hB v hv).symm
  have hnd : DifferentiableAt ℝ c.height (Φ (E.toSphere (g.toFun b))).1 := by
    rw [hΦfst,hb]
    exact (c.height_smooth.contDiffAt (c.open_O.mem_nhds (hO hqC))).differentiableAt (by simp)
  have hh := sphere_flat_sheet_tangent_graph_critical_v480 f g a b q ha hb ht
    Φ hΦ hΦi hqC hfirst c.height hnd hsecond
  rwa [hΦfst] at hh

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3BoundaryCoordinateExtensionV480 -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Function Filter
open scoped Manifold ContDiff Topology
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.A7Support

universe u v
variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]
  {N : Type v} [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold 𝓘(ℝ,E3) ∞ N]

/-- An actual local boundary map in dimension three has a full smooth
Euclidean extension retaining its native coordinate differential. -/
theorem actual_boundary_coordinate_extension3_v480 {F : M → N}
    (O : Set M) (hO : IsOpen O)
    (hF : ContMDiffOn (𝓡∂ 3) 𝓘(ℝ,E3) ∞ F O) (x : M) (hx : x ∈ O) :
    ∃ g : E3 → E3, ContDiff ℝ ∞ g ∧
      g =ᶠ[𝓝[range (𝓡∂ 3)] (extChartAt (𝓡∂ 3) x x)]
        (writtenInExtChartAt (𝓡∂ 3) 𝓘(ℝ,E3) x F) ∧
      HasFDerivAt g
        ((tangentSpaceCastModel 𝓘(ℝ,E3) (F x)).toContinuousLinearMap.comp
          ((mfderiv (𝓡∂ 3) 𝓘(ℝ,E3) F x).comp
            (tangentSpaceCastModel (𝓡∂ 3) x).symm.toContinuousLinearMap))
        (extChartAt (𝓡∂ 3) x x) := by
  let I := 𝓡∂ 3
  let c := chartAt (EuclideanHalfSpace 3) x
  let e := extChartAt I x
  let d := extChartAtPartialDiffeomorph 𝓘(ℝ,E3) ∞ (F x)
  let B : Set E3 := I.symm ⁻¹' c.target
  have hB : IsOpen B := c.open_target.preimage I.continuous_symm
  have hcB : ContinuousOn e.symm B := by
    apply c.continuousOn_symm.comp I.continuous_symm.continuousOn
    exact fun _ hz => hz
  let U : Set E3 := (B ∩ e.symm ⁻¹' O) ∩ (F ∘ e.symm) ⁻¹' d.source
  have hBO : IsOpen (B ∩ e.symm ⁻¹' O) := hcB.isOpen_inter_preimage hB hO
  have hFC : ContinuousOn (F ∘ e.symm) (B ∩ e.symm ⁻¹' O) :=
    hF.continuousOn.comp (hcB.mono inter_subset_left) (fun z hz => hz.2)
  have hU : IsOpen U := hFC.isOpen_inter_preimage hBO d.open_source
  have hxU : e x ∈ U := by
    refine ⟨?_,?_⟩
    · refine ⟨?_,?_⟩
      · change I.symm (I (c x)) ∈ c.target
        rw [I.left_inv]
        exact c.map_source (mem_chart_source (EuclideanHalfSpace 3) x)
      · change e.symm (e x) ∈ O
        rwa [e.left_inv (mem_extChartAt_source x)]
    · change F (e.symm (e x)) ∈ d.source
      rw [e.left_inv (mem_extChartAt_source x)]
      exact mem_extChartAt_source (F x)
  have hφ : ContDiffOn ℝ ∞ (writtenInExtChartAt I 𝓘(ℝ,E3) x F)
      (U ∩ range I) := by
    have hes : ContMDiffOn 𝓘(ℝ,E3) I ∞ e.symm (U ∩ range I) := by
      apply (contMDiffOn_extChartAt_symm x).mono
      intro z hz
      rw [extChartAt_target]
      exact ⟨hz.1.1.1,hz.2⟩
    exact (d.contMDiffOn.comp (hF.comp hes (fun _ hz => hz.1.1.2))
      (fun _ hz => hz.1.2)).contDiffOn
  obtain ⟨g,hg,hge⟩ := exists_contDiff_extension_halfspace_local hU hφ hxU
  let D : E3 →L[ℝ] E3 :=
    (tangentSpaceCastModel 𝓘(ℝ,E3) (F x)).toContinuousLinearMap.comp
      ((mfderiv I 𝓘(ℝ,E3) F x).comp
        (tangentSpaceCastModel I x).symm.toContinuousLinearMap)
  have hr : e x ∈ range I := mem_range_self _
  have hφD : HasFDerivWithinAt (writtenInExtChartAt I 𝓘(ℝ,E3) x F) D (range I) (e x) :=
    ((hF.contMDiffAt (hO.mem_nhds hx)).mdifferentiableAt (by simp)).hasMFDerivAt.2
  have hgD : HasFDerivWithinAt g D (range I) (e x) :=
    (hge.hasFDerivWithinAt_iff_of_mem hr).2 hφD
  have hfd : fderiv ℝ g (e x) = D := by
    have hud : UniqueDiffWithinAt ℝ (range I) (e x) := I.uniqueDiffOn _ hr
    rw [← fderivWithin_eq_fderiv hud (hg.differentiable (by simp) _), hgD.fderivWithin hud]
  refine ⟨g,hg,hge,?_⟩
  change HasFDerivAt g D (e x)
  rw [← hfd]
  exact (hg.differentiable (by simp) _).hasFDerivAt

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480


/- PAID OWNED SUPPORT: B3BoundaryMetricTransitionV480 -/

noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- The actual native boundary chart and a whole sphere chart have a smooth
Euclidean transition with smooth inverse across the boundary. The extension
retains the literal native map and its actual full-rank derivative. -/
theorem actual_boundary_sphere_metric_transition_v480
    (C : SmoothAmbientChart ThreeSphere) (p : E.Carrier)
    (hpC : E.toSphere p ∈ C.chart.source) :
    ∃ e : OpenPartialHomeomorph E3 E3,
      extChartAt (𝓡∂ 3) p p ∈ e.source ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      e =ᶠ[𝓝[range (𝓡∂ 3)] (extChartAt (𝓡∂ 3) p p)]
        (C.chart ∘ E.toSphere ∘ (extChartAt (𝓡∂ 3) p).symm) := by
  let O : Set E.Carrier := E.toSphere ⁻¹' C.chart.source
  let F : E.Carrier → E3 := C.chart ∘ E.toSphere
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  have hO : IsOpen O := C.chart.open_source.preimage hinc.isEmbedding.continuous
  have hpO : p ∈ O := hpC
  have hF : ContMDiffOn (𝓡∂ 3) 𝓘(ℝ,E3) ∞ F O :=
    C.smooth.comp hinc.contMDiff.contMDiffOn (fun x hx => hx)
  obtain ⟨g,hg,hge,hgd⟩ := actual_boundary_coordinate_extension3_v480 O hO hF p hpO
  let D : E3 →L[ℝ] E3 :=
    (tangentSpaceCastModel 𝓘(ℝ,E3) (F p)).toContinuousLinearMap.comp
      ((mfderiv (𝓡∂ 3) 𝓘(ℝ,E3) F p).comp
        (tangentSpaceCastModel (𝓡∂ 3) p).symm.toContinuousLinearMap)
  have hCf : C.chart.MDifferentiable (𝓡 3) 𝓘(ℝ,E3) :=
    ⟨C.smooth.mdifferentiableOn (by simp),C.inverse_smooth.mdifferentiableOn (by simp)⟩
  have hFi : Injective (mfderiv (𝓡∂ 3) 𝓘(ℝ,E3) F p) := by
    dsimp only [F]
    rw [mfderiv_comp p
      ((C.smooth.contMDiffAt (C.chart.open_source.mem_nhds hpC)).mdifferentiableAt (by simp))
      (hinc.contMDiff.mdifferentiableAt (by simp))]
    exact (hCf.mfderiv_injective hpC).comp
      ((hinc.isImmersion.isImmersionAt p).mfderiv_injective (by simp))
  have hDi : Injective D := (tangentSpaceCastModel 𝓘(ℝ,E3) (F p)).injective.comp
    (hFi.comp (tangentSpaceCastModel (𝓡∂ 3) p).symm.injective)
  let A : E3 ≃L[ℝ] E3 :=
    (LinearEquiv.ofBijective D.toLinearMap
      ⟨hDi,LinearMap.injective_iff_surjective.mp hDi⟩).toContinuousLinearEquiv
  have hgdA : HasFDerivAt g A.toContinuousLinearMap (extChartAt (𝓡∂ 3) p p) := hgd
  obtain ⟨e,hpe,heU,he,hei,heq⟩ :=
    DifferentialGeometry.Analysis.exists_localInverse_of_hasFDerivAt_equiv
      hg.contDiffOn isOpen_univ (mem_univ _) hgdA
  have hwrite : writtenInExtChartAt (𝓡∂ 3) 𝓘(ℝ,E3) p F =
      C.chart ∘ E.toSphere ∘ (extChartAt (𝓡∂ 3) p).symm := by
    ext z
    rfl
  have heq' : e =ᶠ[𝓝[range (𝓡∂ 3)] (extChartAt (𝓡∂ 3) p p)] g :=
    Eventually.of_forall heq
  exact ⟨e,hpe,he,hei,heq'.trans (hwrite ▸ hge)⟩

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3BoundaryCoordinateMetricPullbackV480 -/

noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.AppendixACoordinates
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def actual_coordinate_pullback_tensor_v480 (G : MetricTensor) (f : E3 → E3) : MetricTensor :=
  fun y i j => coordinateInner G (f y)
    (fderiv ℝ f y (coordinateVector 3 i)) (fderiv ℝ f y (coordinateVector 3 j))

theorem actual_coordinate_pullback_inner_v480 (G : MetricTensor) (f : E3 → E3)
    (y v w : E3) :
    coordinateInner (actual_coordinate_pullback_tensor_v480 G f) y v w =
      coordinateInner G (f y) (fderiv ℝ f y v) (fderiv ℝ f y w) := by
  let B : E3 →L[ℝ] E3 →L[ℝ] ℝ :=
    ∑ i : Fin 3, (EuclideanSpace.proj (𝕜 := ℝ) i).smulRight
      (∑ j : Fin 3, G (f y) i j • EuclideanSpace.proj (𝕜 := ℝ) j)
  have hB (a b : E3) : B a b = coordinateInner G (f y) a b := by
    simp only [B,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smulRight_apply,
      smul_apply,EuclideanSpace.proj,PiLp.proj_apply,smul_eq_mul,coordinateInner,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hexp (v : E3) : v = ∑ i : Fin 3, v i • coordinateVector 3 i := by
    ext i
    fin_cases i <;> simp [Fin.sum_univ_three,coordinateVector,EuclideanSpace.single,PiLp.single_apply,Pi.single_apply]
  rw [← hB]
  conv_rhs => rw [hexp v,hexp w]
  simp only [map_sum,map_smul,ContinuousLinearMap.sum_apply,smul_apply,smul_eq_mul]
  simp only [Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  simp only [coordinateInner,actual_coordinate_pullback_tensor_v480]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hB]
  simp only [coordinateInner]
  ring

/-- Pulling the actual metric extension through the constructed smooth chart
transition preserves smoothness, symmetry and positive definiteness. -/
theorem actual_coordinate_pullback_metric_v480
    {U V : Set E3} (hU : IsOpen U) (G : CoordinateMetric V)
    (f : E3 → E3) (hf : ContDiffOn ℝ ∞ f U) (hm : MapsTo f U V)
    (hi : ∀ y ∈ U, Injective (fderiv ℝ f y)) :
    ∃ H : CoordinateMetric U, H.tensor = actual_coordinate_pullback_tensor_v480 G.tensor f := by
  have hd : ContDiffOn ℝ ∞ (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by simp)
  have hentry (i k : Fin 3) : ContDiffOn ℝ ∞
      (fun y => fderiv ℝ f y (coordinateVector 3 i) k) U :=
    (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.comp_contDiffOn
      (hd.clm_apply contDiffOn_const)
  have hcoeff (i j : Fin 3) : ContDiffOn ℝ ∞
      (fun y => actual_coordinate_pullback_tensor_v480 G.tensor f y i j) U := by
    unfold actual_coordinate_pullback_tensor_v480 coordinateInner
    apply ContDiffOn.sum
    intro k hk
    apply ContDiffOn.sum
    intro l hl
    exact ((G.smooth k l).comp hf hm |>.mul (hentry i k)).mul (hentry j l)
  have hsym (y : E3) (hy : y ∈ U) (v w : E3) :
      coordinateInner G.tensor (f y) v w = coordinateInner G.tensor (f y) w v := by
    unfold coordinateInner
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [G.symmetric (f y) (hm hy) j i]
    ring
  refine ⟨{
    tensor := actual_coordinate_pullback_tensor_v480 G.tensor f
    smooth := hcoeff
    symmetric := fun y hy i j => hsym y hy _ _
    positive := ?_ },rfl⟩
  intro y hy v hv
  rw [actual_coordinate_pullback_inner_v480]
  apply G.positive (f y) (hm hy)
  intro hz
  exact hv ((hi y hy) (hz.trans (map_zero _).symm))

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3ArbitraryBoundaryGeometryPackageV480 -/

noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- Whole actual boundary geometry at every potential accumulation point of
the original pair's interior tangencies. Every graph and source map is
constructed from the original pair. The reversing branch is fully excluded;
the preserving branch carries the actual two smooth interior parameters. -/
theorem original_pair_arbitrary_boundary_geometry_package_v480
    (D : OriginalPair g J) {p : E.Carrier}
    (hp : p ∈ (𝓡∂ 3).boundary E.Carrier)
    (ht : p ∈ (fun q : D.A.1.surface × D.B.1.surface => D.A.1.embedding.toFun q.1) ''
      nativeTangencyPairs_v480 D.A.1.embedding D.B.1.embedding) :
    ∃ c : ActualBoundaryPairGraphV480 D.A.1.embedding D.B.1.embedding p,
      (∀ q : E.Carrier, E.toSphere q ∈ c.coordinates.chart.source →
        q ∈ interiorTangencies D.A.1.embedding D.B.1.embedding →
        fderiv ℝ c.height (B1Tangency.native_collar_base_v475
          (c.coordinates.chart (E.toSphere q))) = 0) ∧
      ((0 < c.coefficient ∧
        ∃ qA : E2 → D.A.1.surface, ∃ qB : E2 → D.B.1.surface,
          ContMDiffOn 𝓘(ℝ,E2) (𝓡∂ 2) ∞ qA {x ∈ c.O | 0 < x 0} ∧
          ContMDiffOn 𝓘(ℝ,E2) (𝓡∂ 2) ∞ qB {x ∈ c.O | 0 < x 0} ∧
          (∀ x ∈ {x ∈ c.O | 0 < x 0},
            E.toSphere (D.A.1.embedding.toFun (qA x)) = c.coordinates.chart.symm (graphPoint x 0) ∧
            qA x ∉ D.A.1.surface.boundary) ∧
          (∀ x ∈ {x ∈ c.O | 0 < x 0},
            E.toSphere (D.B.1.embedding.toFun (qB x)) =
              c.coordinates.chart.symm (graphPoint x (c.height x)) ∧
            qB x ∉ D.B.1.surface.boundary)) ∨
       (c.coefficient < 0 ∧ ∃ U : Set E.Carrier, IsOpen U ∧ p ∈ U ∧
        Disjoint (U ∩ (𝓡∂ 3).interior E.Carrier)
          (D.A.1.image ∩ D.B.1.image))) := by
  classical
  obtain ⟨c⟩ := original_pair_boundary_tangency_actual_graph_v480 D hp ht
  refine ⟨c,?_,?_⟩
  · intro q hqC hqt
    exact actual_boundary_graph_tangency_critical_v480 _ _ c hqC hqt
  · rcases lt_or_gt_of_ne c.coefficient_ne with hc | hc
    · right
      let U : Set E.Carrier := E.toSphere ⁻¹' c.coordinates.chart.source
      have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
      exact ⟨hc,U,c.coordinates.chart.open_source.preimage hinc.isEmbedding.continuous,
        c.base_mem,boundary_graph_reversed_excludes_interior_v480 _ _ c hc⟩
    · left
      obtain ⟨⟨a,b⟩,⟨hab,hplane⟩,ha⟩ := ht
      change D.A.1.embedding.toFun a = p at ha
      have hb : D.B.1.embedding.toFun b = p := hab.symm.trans ha
      have haB : a ∈ D.A.1.surface.boundary := by
        rw [← D.A.1.embedding.boundary_preimage]
        change D.A.1.embedding.toFun a ∈ (𝓡∂ 3).boundary E.Carrier
        rwa [ha]
      have hbB : b ∈ D.B.1.surface.boundary := by
        rw [← D.B.1.embedding.boundary_preimage]
        change D.B.1.embedding.toFun b ∈ (𝓡∂ 3).boundary E.Carrier
        rwa [hb]
      have hbound := original_pair_common_boundary_exact_v480 D
        (show p ∈ D.A.1.embedding.toFun '' D.A.1.surface.boundary from ⟨a,haB,ha⟩)
        (show p ∈ D.B.1.embedding.toFun '' D.B.1.surface.boundary from ⟨b,hbB,hb⟩)
      exact ⟨hc,actual_boundary_positive_graph_parameters_v480 _ _ a b c hc hbound⟩

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3BoundaryLocalPDEV480 -/

noncomputable section
open Set Topology Function Filter MeasureTheory
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

private theorem local_pde_neat_interior_v480
    {S : CompactOrientedSurface.{0}} (f : NeatEmbedding S E.Carrier)
    {a : S} (ha : a ∉ S.boundary) :
    f.toFun a ∈ (𝓡∂ 3).interior E.Carrier := by
  rw [← (𝓡∂ 3).compl_boundary]
  intro hb
  have hb' : a ∈ f.toFun ⁻¹' (𝓡∂ 3).boundary E.Carrier := hb
  rw [f.boundary_preimage] at hb'
  exact ha hb'

private theorem local_pde_base_v480 (x : E2) (t : ℝ) :
    native_collar_base_v475 (graphPoint x t) = x := by
  ext i
  fin_cases i <;> simp [native_collar_base_v475,graphPoint]

/-- The actual graph height of the original pair solves the same metric
minimal graph equation as the flat height on its entire positive halfspace.
The whole boundary chart is restricted to the true exterior interior; no
boundary point is asserted to belong to that open interior chart. -/
theorem actual_boundary_local_two_height_pdes_v480
    (D : OriginalPair g J) (a0 : D.A.1.surface) (b0 : D.B.1.surface) {p : E.Carrier}
    (c : ActualBoundaryPairGraphV480 D.A.1.embedding D.B.1.embedding p)
    (hc : 0 < c.coefficient)
    (hboundary : D.A.1.embedding.toFun '' D.A.1.surface.boundary =
      D.B.1.embedding.toFun '' D.B.1.surface.boundary) :
    ∃ d : SmoothAmbientChart ThreeSphere,
      d.chart.source = c.coordinates.chart.source ∩
        (E.toSphere '' (𝓡∂ 3).interior E.Carrier) ∧
      (∀ s, d.chart s = c.coordinates.chart s) ∧
      (∀ y, d.chart.symm y = c.coordinates.chart.symm y) ∧
      (∀ z ∈ {x ∈ c.O | 0 < x 0},
        jetPoint (z,c.height z,0) ∈ d.chart.target ∧ jetPoint (z,0,0) ∈ d.chart.target) ∧
      ∃ χ : E3 → E.Carrier,
        ContMDiffOn 𝓘(ℝ,E3) (𝓡∂ 3) ∞ χ d.chart.target ∧
        (∀ y ∈ d.chart.target, E.toSphere (χ y) = d.chart.symm y) ∧
        ∃ H : CoordinateMetric d.chart.target,
          H.tensor = native_actual_lift_tensor_v475 g χ ∧
        (∀ z ∈ {x ∈ c.O | 0 < x 0},
          native_interior_graph_residual_v475 H c.height z = 0) ∧
        (∀ z ∈ {x ∈ c.O | 0 < x 0},
          native_interior_graph_residual_v475 H (fun _ => (0 : ℝ)) z = 0) := by
  obtain ⟨qA,qB,hqA,hqB,heA,heB⟩ :=
    actual_boundary_positive_graph_parameters_v480
      D.A.1.embedding D.B.1.embedding a0 b0 c hc hboundary
  let O : Set E2 := {x ∈ c.O | 0 < x 0}
  have hO : IsOpen O := c.open_O.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).continuous)
  let U : Set ThreeSphere := c.coordinates.chart.source ∩
    (E.toSphere '' (𝓡∂ 3).interior E.Carrier)
  have hU : IsOpen U := c.coordinates.chart.open_source.inter
    native_actual_exterior_interior_image_open_v475
  let e := c.coordinates.chart.restrOpen U hU
  have heS : e.source = U := inter_eq_right.mpr inter_subset_left
  have heT : e.target ⊆ c.coordinates.chart.target := inter_subset_left
  have hes : ContMDiffOn (𝓡 3) 𝓘(ℝ,E3) ∞ e e.source :=
    c.coordinates.smooth.mono (by rw [heS]; exact inter_subset_left)
  have hei : ContMDiffOn 𝓘(ℝ,E3) (𝓡 3) ∞ e.symm e.target :=
    c.coordinates.inverse_smooth.mono heT
  let d : SmoothAmbientChart ThreeSphere := ⟨e,hes,hei⟩
  have hdsource : d.chart.source = U := heS
  have hdcoord (s : ThreeSphere) : d.chart s = c.coordinates.chart s := rfl
  have hdinverse (y : E3) : d.chart.symm y = c.coordinates.chart.symm y := rfl
  have hsourceA (z : E2) (hz : z ∈ O) :
      c.coordinates.chart.symm (graphPoint z 0) ∈ U := by
    exact ⟨c.coordinates.chart.map_target (c.points_inside z hz.1).1,
      ⟨D.A.1.embedding.toFun (qA z),
        local_pde_neat_interior_v480 _ (heA z hz).2,(heA z hz).1⟩⟩
  have hsourceB (z : E2) (hz : z ∈ O) :
      c.coordinates.chart.symm (graphPoint z (c.height z)) ∈ U := by
    exact ⟨c.coordinates.chart.map_target (c.points_inside z hz.1).2,
      ⟨D.B.1.embedding.toFun (qB z),
        local_pde_neat_interior_v480 _ (heB z hz).2,(heB z hz).1⟩⟩
  have htargetA (z : E2) (hz : z ∈ O) : jetPoint (z,0,0) ∈ d.chart.target :=
    ⟨(c.points_inside z hz.1).1,hsourceA z hz⟩
  have htargetB (z : E2) (hz : z ∈ O) : jetPoint (z,c.height z,0) ∈ d.chart.target :=
    ⟨(c.points_inside z hz.1).2,hsourceB z hz⟩
  have hcE : d.chart.source ⊆ E.toSphere '' (𝓡∂ 3).interior E.Carrier := by
    rw [hdsource]
    exact inter_subset_right
  have hgraphA (a : D.A.1.surface)
      (ha : E.toSphere (D.A.1.embedding.toFun a) ∈ d.chart.source) :
      (d.chart (E.toSphere (D.A.1.embedding.toFun a))) 2 = (0 : ℝ) := by
    have hC : E.toSphere (D.A.1.embedding.toFun a) ∈ c.coordinates.chart.source :=
      (hdsource ▸ ha).1
    have hh : E.toSphere (D.A.1.embedding.toFun a) ∈
        range (E.toSphere ∘ D.A.1.embedding.toFun) ∩ c.coordinates.chart.source :=
      ⟨⟨a,rfl⟩,hC⟩
    rw [c.graph_A] at hh
    obtain ⟨x,⟨hx,hx0⟩,he⟩ := hh
    have hchart := congrArg c.coordinates.chart he
    rw [c.coordinates.chart.right_inv (c.points_inside x hx).1] at hchart
    rw [hdcoord,← hchart]
    simp [graphPoint]
  have hgraphB (b : D.B.1.surface)
      (hb : E.toSphere (D.B.1.embedding.toFun b) ∈ d.chart.source) :
      (d.chart (E.toSphere (D.B.1.embedding.toFun b))) 2 =
        c.height (native_collar_base_v475
          (d.chart (E.toSphere (D.B.1.embedding.toFun b)))) := by
    have hC : E.toSphere (D.B.1.embedding.toFun b) ∈ c.coordinates.chart.source :=
      (hdsource ▸ hb).1
    have hh : E.toSphere (D.B.1.embedding.toFun b) ∈
        range (E.toSphere ∘ D.B.1.embedding.toFun) ∩ c.coordinates.chart.source :=
      ⟨⟨b,rfl⟩,hC⟩
    rw [c.graph_B] at hh
    obtain ⟨x,⟨hx,hx0⟩,he⟩ := hh
    have hchart := congrArg c.coordinates.chart he
    rw [c.coordinates.chart.right_inv (c.points_inside x hx).2] at hchart
    rw [hdcoord,← hchart,local_pde_base_v480]
    simp [graphPoint]
  obtain ⟨χ,hχ,hχeq,hχI,hχright,hχleft⟩ := native_actual_interior_chart_lift_v475 d p hcE
  obtain ⟨H,hH⟩ := native_actual_lift_coordinate_metric_v475 g d χ hχ hχeq
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  have hqgraphA (z : E2) (hz : z ∈ O) :
      D.A.1.embedding.toFun (qA z) = χ (jetPoint (z,0,0)) := by
    apply hinc.isEmbedding.injective
    rw [hχeq _ (htargetA z hz),hdinverse]
    exact (heA z hz).1
  have hqgraphB (z : E2) (hz : z ∈ O) :
      D.B.1.embedding.toFun (qB z) = χ (jetPoint (z,c.height z,0)) := by
    apply hinc.isEmbedding.injective
    rw [hχeq _ (htargetB z hz),hdinverse]
    exact (heB z hz).1
  obtain ⟨hminA,hminB⟩ := original_pair_actual_flow_minima D
  have hl := native_interior_actual_graph_pde_from_flow_v475 g d hcE χ hχ hχeq H hH
    (ProperSmoothEmbedding.ofNeat D.B.1.embedding) hminB O hO c.height
    (c.height_smooth.mono inter_subset_left) qB hqB hqgraphB htargetB
    (fun z hz => (heB z hz).2) hgraphB
  have hu := native_interior_actual_graph_pde_from_flow_v475 g d hcE χ hχ hχeq H hH
    (ProperSmoothEmbedding.ofNeat D.A.1.embedding) hminA O hO (fun _ => 0)
    contDiffOn_const qA hqA hqgraphA htargetA
    (fun z hz => (heA z hz).2) hgraphA
  exact ⟨d,hdsource,hdcoord,hdinverse,
    fun z hz => ⟨htargetB z hz,htargetA z hz⟩,χ,hχ,hχeq,H,hH,hl,hu⟩

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3BoundaryMetricExtensionV480 -/

noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

private theorem boundary_inverse_derivative_injective_v480
    (e : OpenPartialHomeomorph E3 E3)
    (he : ContDiffOn ℝ ∞ e e.source) (hei : ContDiffOn ℝ ∞ e.symm e.target)
    {y : E3} (hy : y ∈ e.target) : Injective (fderiv ℝ e.symm y) := by
  have heD : DifferentiableAt ℝ e (e.symm y) :=
    (he.contDiffAt (e.open_source.mem_nhds (e.map_target hy))).differentiableAt (by simp)
  have heiD : DifferentiableAt ℝ e.symm y :=
    (hei.contDiffAt (e.open_target.mem_nhds hy)).differentiableAt (by simp)
  have heq : e ∘ e.symm =ᶠ[𝓝 y] id :=
    eventuallyEq_of_mem (e.open_target.mem_nhds hy) (fun z hz => e.right_inv hz)
  have hcomp : (fderiv ℝ e (e.symm y)).comp (fderiv ℝ e.symm y) =
      ContinuousLinearMap.id ℝ E3 := by
    rw [← fderiv_comp y heD heiD,heq.fderiv_eq,fderiv_id]
  intro v w hvw
  have hh := congrArg (fderiv ℝ e (e.symm y)) hvw
  change ((fderiv ℝ e (e.symm y)).comp (fderiv ℝ e.symm y)) v =
    ((fderiv ℝ e (e.symm y)).comp (fderiv ℝ e.symm y)) w at hh
  simpa only [hcomp,ContinuousLinearMap.id_apply] using hh

/-- The constructed extension retains the supplied metric in its native
chart and the exact actual coordinate transition on an exterior neighborhood.
Its common-chart tensor is smooth and positive across the boundary. -/
structure ActualBoundaryMetricExtensionV480
    (g : SmoothMetric E.Carrier) (C : SmoothAmbientChart ThreeSphere) (p : E.Carrier) where
  nativeDomain : Set E3
  native_open : IsOpen nativeDomain
  nativeMetric : CoordinateMetric nativeDomain
  native_base : extChartAt (𝓡∂ 3) p p ∈ nativeDomain
  native_exact : ∀ y ∈ nativeDomain ∩ (extChartAt (𝓡∂ 3) p).target,
    nativeMetric.tensor y = SeifertSurfaces.AppendixC.MetricInChart (𝓡∂ 3) g p y
  transition : OpenPartialHomeomorph E3 E3
  transition_smooth : ContDiffOn ℝ ∞ transition transition.source
  transition_inverse_smooth : ContDiffOn ℝ ∞ transition.symm transition.target
  domain : Set E3
  domain_open : IsOpen domain
  base_mem : C.chart (E.toSphere p) ∈ domain
  domain_chart : domain ⊆ C.chart.target
  domain_transition : domain ⊆ transition.target
  inverse_native : MapsTo transition.symm domain nativeDomain
  metric : CoordinateMetric domain
  tensor_exact : metric.tensor =
    actual_coordinate_pullback_tensor_v480 nativeMetric.tensor transition.symm
  neighborhood : Set E.Carrier
  neighborhood_open : IsOpen neighborhood
  neighborhood_base : p ∈ neighborhood
  neighborhood_native : neighborhood ⊆ (extChartAt (𝓡∂ 3) p).source
  neighborhood_chart : ∀ q ∈ neighborhood, E.toSphere q ∈ C.chart.source
  neighborhood_coordinates : ∀ q ∈ neighborhood,
    C.chart (E.toSphere q) ∈ domain ∧
    extChartAt (𝓡∂ 3) p q ∈ transition.source ∧
    transition (extChartAt (𝓡∂ 3) p q) = C.chart (E.toSphere q) ∧
    nativeMetric.tensor (extChartAt (𝓡∂ 3) p q) =
      SeifertSurfaces.AppendixC.MetricInChart (𝓡∂ 3) g p (extChartAt (𝓡∂ 3) p q)

/-- Strict convexity's existing native metric extension is transported to
any actual boundary sphere chart; no metric extension is assumed anew. -/
theorem actual_boundary_metric_extension_v480
    (hconv : IsStrictlyConvexBoundary g) (C : SmoothAmbientChart ThreeSphere)
    (p : E.Carrier) (hp : p ∈ (𝓡∂ 3).boundary E.Carrier)
    (hpC : E.toSphere p ∈ C.chart.source) :
    Nonempty (ActualBoundaryMetricExtensionV480 g C p) := by
  obtain ⟨V,hV,G,hpV,hG,hHess⟩ := hconv p hp
  obtain ⟨e,hpe,he,hei,heq⟩ := actual_boundary_sphere_metric_transition_v480 C p hpC
  have hprange : extChartAt (𝓡∂ 3) p p ∈ range (𝓡∂ 3) :=
    extChartAt_target_subset_range p (mem_extChartAt_target p)
  have hbase : e (extChartAt (𝓡∂ 3) p p) = C.chart (E.toSphere p) := by
    have hh := heq.eq_of_nhdsWithin hprange
    simpa only [Function.comp_apply,extChartAt_to_inv] using hh
  obtain ⟨R,hR,hpR,hReq⟩ := mem_nhdsWithin.mp heq
  let U : Set E3 := (e.target ∩ e.symm ⁻¹' V) ∩ C.chart.target
  have hU : IsOpen U :=
    (hei.continuousOn.isOpen_inter_preimage e.open_target hV).inter C.chart.open_target
  have hpU : C.chart (E.toSphere p) ∈ U := by
    refine ⟨⟨hbase ▸ e.map_source hpe, ?_⟩, C.chart.map_source hpC⟩
    change e.symm (C.chart (E.toSphere p)) ∈ V
    rw [← hbase,e.left_inv hpe]
    exact hpV
  have hUm : MapsTo e.symm U V := fun _ hy => hy.1.2
  obtain ⟨H,hH⟩ := actual_coordinate_pullback_metric_v480 hU G e.symm
    (hei.mono inter_subset_left |>.mono inter_subset_left) hUm
    (fun y hy => boundary_inverse_derivative_injective_v480 e he hei hy.1.1)
  let N0 : Set E.Carrier := (extChartAt (𝓡∂ 3) p).source ∩
    (extChartAt (𝓡∂ 3) p) ⁻¹' (R ∩ e.source)
  have hN0 : IsOpen N0 := (continuousOn_extChartAt p).isOpen_inter_preimage
    (isOpen_extChartAt_source p) (hR.inter e.open_source)
  let NC : Set E.Carrier := E.toSphere ⁻¹' C.chart.source
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  have hNC : IsOpen NC := C.chart.open_source.preimage hinc.isEmbedding.continuous
  have hCC : ContinuousOn (C.chart ∘ E.toSphere) NC :=
    C.smooth.continuousOn.comp hinc.isEmbedding.continuous.continuousOn (fun _ hx => hx)
  let N : Set E.Carrier := N0 ∩ (NC ∩ (C.chart ∘ E.toSphere) ⁻¹' U)
  have hN : IsOpen N := hN0.inter (hCC.isOpen_inter_preimage hNC hU)
  have hpN : p ∈ N := ⟨⟨mem_extChartAt_source p,hpR,hpe⟩,hpC,hpU⟩
  refine ⟨{
    nativeDomain := V
    native_open := hV
    nativeMetric := G
    native_base := hpV
    native_exact := hG
    transition := e
    transition_smooth := he
    transition_inverse_smooth := hei
    domain := U
    domain_open := hU
    base_mem := hpU
    domain_chart := inter_subset_right
    domain_transition := fun _ hy => hy.1.1
    inverse_native := hUm
    metric := H
    tensor_exact := hH
    neighborhood := N
    neighborhood_open := hN
    neighborhood_base := hpN
    neighborhood_native := fun _ hq => hq.1.1
    neighborhood_chart := fun _ hq => hq.2.1
    neighborhood_coordinates := ?_ }⟩
  intro q hq
  have hqr : extChartAt (𝓡∂ 3) p q ∈ range (𝓡∂ 3) :=
    extChartAt_target_subset_range p ((extChartAt (𝓡∂ 3) p).map_source hq.1.1)
  have hcoord : e (extChartAt (𝓡∂ 3) p q) = C.chart (E.toSphere q) := by
    have hh := hReq ⟨hq.1.2.1,hqr⟩
    change e (extChartAt (𝓡∂ 3) p q) =
      C.chart (E.toSphere ((extChartAt (𝓡∂ 3) p).symm (extChartAt (𝓡∂ 3) p q))) at hh
    rwa [(extChartAt (𝓡∂ 3) p).left_inv hq.1.1] at hh
  have hqV : extChartAt (𝓡∂ 3) p q ∈ V := by
    have hh := hUm hq.2.2
    change e.symm (C.chart (E.toSphere q)) ∈ V at hh
    rw [← hcoord,e.left_inv hq.1.2.2] at hh
    exact hh
  exact ⟨hq.2.2,hq.1.2.2,hcoord,
    hG _ ⟨hqV,(extChartAt (𝓡∂ 3) p).map_source hq.1.1⟩⟩

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3BoundaryMetricAgreementV480 -/

noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

private theorem native_metric_chart_inner_v480
    (g : SmoothMetric E.Carrier) (p : E.Carrier) (y v w : E3) :
    coordinateInner (SeifertSurfaces.AppendixC.MetricInChart (𝓡∂ 3) g p) y v w =
      g.inner ((extChartAt (𝓡∂ 3) p).symm y)
        (mfderivWithin 𝓘(ℝ,E3) (𝓡∂ 3) (extChartAt (𝓡∂ 3) p).symm
          (range (𝓡∂ 3)) y v)
        (mfderivWithin 𝓘(ℝ,E3) (𝓡∂ 3) (extChartAt (𝓡∂ 3) p).symm
          (range (𝓡∂ 3)) y w) := by
  let d := mfderivWithin 𝓘(ℝ,E3) (𝓡∂ 3) (extChartAt (𝓡∂ 3) p).symm
    (range (𝓡∂ 3)) y
  have hexp (v : E3) : v = ∑ i : Fin 3, v i • coordinateVector 3 i := by
    ext i
    fin_cases i <;> simp [Fin.sum_univ_three,coordinateVector,EuclideanSpace.single]
  change coordinateInner (SeifertSurfaces.AppendixC.MetricInChart (𝓡∂ 3) g p) y v w =
    g.inner ((extChartAt (𝓡∂ 3) p).symm y) (d v) (d w)
  conv_rhs => rw [hexp v,hexp w]
  simp only [map_sum,map_smul,ContinuousLinearMap.sum_apply,smul_apply,smul_eq_mul,
    coordinateInner,SeifertSurfaces.AppendixC.MetricInChart]
  simp only [Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  dsimp only [d,coordinateVector]
  ring

/-- On its actual interior chart lift, the transported boundary metric is
the literal pullback of the supplied exterior metric, coefficient for
coefficient. -/
theorem actual_boundary_metric_agrees_lift_v480
    (g : SmoothMetric E.Carrier) (C : SmoothAmbientChart ThreeSphere) (p : E.Carrier)
    (X : ActualBoundaryMetricExtensionV480 g C p)
    (d : SmoothAmbientChart ThreeSphere)
    (hd : ∀ s, d.chart s = C.chart s)
    (χ : E3 → E.Carrier)
    (hχ : ContMDiffOn 𝓘(ℝ,E3) (𝓡∂ 3) ∞ χ d.chart.target)
    (hχeq : ∀ y ∈ d.chart.target, E.toSphere (χ y) = d.chart.symm y) :
    ∃ W : Set E3, IsOpen W ∧ W = d.chart.target ∩ χ ⁻¹' X.neighborhood ∧
      W ⊆ X.domain ∧
      ∀ y ∈ W, X.metric.tensor y = native_actual_lift_tensor_v475 g χ y := by
  let W : Set E3 := d.chart.target ∩ χ ⁻¹' X.neighborhood
  have hW : IsOpen W := hχ.continuousOn.isOpen_inter_preimage
    d.chart.open_target X.neighborhood_open
  have hcoord (y : E3) (hy : y ∈ W) :
      C.chart (E.toSphere (χ y)) = y := by
    rw [← hd,hχeq y hy.1,d.chart.right_inv hy.1]
  have hWdomain : W ⊆ X.domain := by
    intro y hy
    exact (hcoord y hy) ▸ (X.neighborhood_coordinates (χ y) hy.2).1
  have hinverse (y : E3) (hy : y ∈ W) :
      X.transition.symm y = extChartAt (𝓡∂ 3) p (χ y) := by
    have hcoords := X.neighborhood_coordinates (χ y) hy.2
    have heq := hcoords.2.2.1.trans (hcoord y hy)
    exact (congrArg X.transition.symm heq).symm.trans
      (X.transition.left_inv hcoords.2.1)
  have hlift (y : E3) (hy : y ∈ W) :
      (extChartAt (𝓡∂ 3) p).symm (X.transition.symm y) = χ y := by
    rw [hinverse y hy]
    exact (extChartAt (𝓡∂ 3) p).left_inv (X.neighborhood_native hy.2)
  refine ⟨W,hW,rfl,hWdomain,?_⟩
  intro y hy
  have hevent : (extChartAt (𝓡∂ 3) p).symm ∘ X.transition.symm =ᶠ[𝓝 y] χ :=
    eventuallyEq_of_mem (hW.mem_nhds hy) (fun z hz => hlift z hz)
  have hmaps : X.transition.symm ⁻¹' range (𝓡∂ 3) ∈ 𝓝 y := by
    apply Filter.mem_of_superset (hW.mem_nhds hy)
    intro z hz
    rw [mem_preimage,hinverse z hz]
    exact extChartAt_target_subset_range p
      ((extChartAt (𝓡∂ 3) p).map_source (X.neighborhood_native hz.2))
  have hnative : X.transition.symm y ∈ (extChartAt (𝓡∂ 3) p).target := by
    rw [hinverse y hy]
    exact (extChartAt (𝓡∂ 3) p).map_source (X.neighborhood_native hy.2)
  have hTD : DifferentiableAt ℝ X.transition.symm y :=
    (X.transition_inverse_smooth.contDiffAt
      (X.transition.open_target.mem_nhds (X.domain_transition (hWdomain hy)))).differentiableAt (by simp)
  have hchain : mfderiv 𝓘(ℝ,E3) (𝓡∂ 3) χ y =
      (mfderivWithin 𝓘(ℝ,E3) (𝓡∂ 3) (extChartAt (𝓡∂ 3) p).symm
        (range (𝓡∂ 3)) (X.transition.symm y)).comp
        (mfderiv 𝓘(ℝ,E3) 𝓘(ℝ,E3) X.transition.symm y) := by
    have hh := mfderivWithin_comp_of_preimage_mem_nhdsWithin
      (I := 𝓘(ℝ,E3)) (I' := 𝓘(ℝ,E3)) (I'' := 𝓡∂ 3)
      (s := univ) y (mdifferentiableWithinAt_extChartAt_symm hnative)
      hTD.mdifferentiableAt.mdifferentiableWithinAt
      (by simpa only [nhdsWithin_univ] using hmaps)
      (uniqueMDiffWithinAt_univ 𝓘(ℝ,E3))
    rw [mfderivWithin_univ,mfderivWithin_univ,hevent.mfderiv_eq] at hh
    exact hh
  have hnativeMetric : X.nativeMetric.tensor (X.transition.symm y) =
      SeifertSurfaces.AppendixC.MetricInChart (𝓡∂ 3) g p (X.transition.symm y) :=
    X.native_exact _ ⟨X.inverse_native (hWdomain hy),hnative⟩
  have hnativeInner (v w : E3) :
      coordinateInner X.nativeMetric.tensor (X.transition.symm y) v w =
        coordinateInner (SeifertSurfaces.AppendixC.MetricInChart (𝓡∂ 3) g p)
          (X.transition.symm y) v w := by
    unfold coordinateInner
    simp only [hnativeMetric]
  ext i j
  rw [X.tensor_exact]
  change coordinateInner X.nativeMetric.tensor (X.transition.symm y)
    (fderiv ℝ X.transition.symm y (coordinateVector 3 i))
    (fderiv ℝ X.transition.symm y (coordinateVector 3 j)) = _
  rw [hnativeInner]
  rw [native_metric_chart_inner_v480,hlift y hy]
  unfold native_actual_lift_tensor_v475
  rw [hchain,mfderiv_eq_fderiv]
  rfl

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3GraphMetricGermCongruenceV480 -/

noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

private theorem graph_density_metric_eq_v480
    {V W : Set E3} (G : CoordinateMetric V) (H : CoordinateMetric W)
    (j : Jet) (h : G.tensor (jetPoint j) = H.tensor (jetPoint j)) :
    native_interior_graph_density_v475 G j = native_interior_graph_density_v475 H j := by
  unfold native_interior_graph_density_v475 native_interior_graph_gram_v475 coordinateInner
  simp only [h]

private theorem graph_flux_metric_eq_v480
    {V W : Set E3} (G : CoordinateMetric V) (H : CoordinateMetric W)
    (j : Jet) (h : G.tensor (jetPoint j) = H.tensor (jetPoint j)) :
    native_interior_graph_flux_v475 G j = native_interior_graph_flux_v475 H j := by
  have hfun : (fun p : E2 => native_interior_graph_density_v475 G (j.1,j.2.1,p)) =
      (fun p : E2 => native_interior_graph_density_v475 H (j.1,j.2.1,p)) := by
    funext p
    apply graph_density_metric_eq_v480
    exact h
  unfold native_interior_graph_flux_v475
  rw [hfun]

/-- The literal graph Euler-Lagrange residual depends only on the ambient
metric germ at its physical graph point. -/
theorem graph_residual_metric_germ_congr_v480
    {V W : Set E3} (G : CoordinateMetric V) (H : CoordinateMetric W)
    (u : E2 → ℝ) (x : E2) (hu : ContinuousAt u x)
    (h : G.tensor =ᶠ[𝓝 (graphPoint x (u x))] H.tensor) :
    native_interior_graph_residual_v475 G u x =
      native_interior_graph_residual_v475 H u x := by
  have hΓ : ContinuousAt (fun y : E2 => graphPoint y (u y)) x := by
    change ContinuousAt (fun y : E2 => native_interior_graph_splitting_v475 (y,u y)) x
    exact native_interior_graph_splitting_v475.continuous.continuousAt.comp
      (continuousAt_id.prodMk hu)
  have hΓeq : ∀ᶠ y in 𝓝 x,
      G.tensor (graphPoint y (u y)) = H.tensor (graphPoint y (u y)) :=
    hΓ.eventually h
  have hflux (i : Fin 2) :
      (fun y => native_interior_graph_flux_v475 G (y,u y,planarGradient u y) i) =ᶠ[𝓝 x]
        (fun y => native_interior_graph_flux_v475 H (y,u y,planarGradient u y) i) := by
    filter_upwards [hΓeq] with y hy
    exact congrArg (fun v : E2 => v i)
      (graph_flux_metric_eq_v480 G H (y,u y,planarGradient u y) hy)
  have hz : ContinuousAt (fun z : ℝ => graphPoint x z) (u x) := by
    change ContinuousAt (fun z : ℝ => native_interior_graph_splitting_v475 (x,z)) (u x)
    exact native_interior_graph_splitting_v475.continuous.continuousAt.comp
      (continuousAt_const.prodMk continuousAt_id)
  have hzeq : ∀ᶠ z in 𝓝 (u x), G.tensor (graphPoint x z) = H.tensor (graphPoint x z) :=
    hz.eventually h
  have hden : (fun z => native_interior_graph_density_v475 G (x,z,planarGradient u x)) =ᶠ[𝓝 (u x)]
      (fun z => native_interior_graph_density_v475 H (x,z,planarGradient u x)) := by
    filter_upwards [hzeq] with z hz
    exact graph_density_metric_eq_v480 G H (x,z,planarGradient u x) hz
  unfold native_interior_graph_residual_v475 native_interior_graph_lower_v475
  rw [hden.deriv_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [(hflux i).fderiv_eq]

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3ActualBoundaryPDEPackageV480 -/

noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- Both actual heights solve one metric graph equation with coefficients
smooth across the boundary.  The neighborhood, metric and exact native
agreement are constructed from the original pair. -/
theorem original_pair_actual_boundary_pde_package_v480
    (D : OriginalPair g J) (a0 : D.A.1.surface) (b0 : D.B.1.surface) {p : E.Carrier}
    (hp : p ∈ (𝓡∂ 3).boundary E.Carrier)
    (c : ActualBoundaryPairGraphV480 D.A.1.embedding D.B.1.embedding p)
    (hc : 0 < c.coefficient)
    (hboundary : D.A.1.embedding.toFun '' D.A.1.surface.boundary =
      D.B.1.embedding.toFun '' D.B.1.surface.boundary) :
    ∃ X : ActualBoundaryMetricExtensionV480 g c.coordinates p,
    ∃ Q : Set E2, IsOpen Q ∧ c.z ∈ Q ∧ Q ⊆ c.O ∧
      (∀ x ∈ Q, graphPoint x 0 ∈ X.domain ∧ graphPoint x (c.height x) ∈ X.domain) ∧
      (∀ x ∈ Q, 0 < x 0 →
        native_interior_graph_residual_v475 X.metric c.height x = 0 ∧
        native_interior_graph_residual_v475 X.metric (fun _ => (0 : ℝ)) x = 0) := by
  obtain ⟨d,hdsource,hdcoord,hdinverse,hpoints,χ,hχ,hχeq,H,hH,hPDEheight,hPDEzero⟩ :=
    actual_boundary_local_two_height_pdes_v480 D a0 b0 c hc hboundary
  obtain ⟨X⟩ := actual_boundary_metric_extension_v480 D.convex c.coordinates p hp c.base_mem
  obtain ⟨W,hW,hWdef,hWX,hagree⟩ :=
    actual_boundary_metric_agrees_lift_v480 g c.coordinates p X d hdcoord χ hχ hχeq
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  obtain ⟨Z,hZ,hZN⟩ := hinc.isEmbedding.isInducing.isOpen_iff.mp X.neighborhood_open
  let ΓA : E2 → ThreeSphere := fun x => c.coordinates.chart.symm (graphPoint x 0)
  let ΓB : E2 → ThreeSphere := fun x => c.coordinates.chart.symm (graphPoint x (c.height x))
  have hGA : ContDiffOn ℝ ∞ (fun x : E2 => graphPoint x 0) c.O := by
    change ContDiffOn ℝ ∞ (fun x : E2 => native_interior_graph_splitting_v475 (x,0)) c.O
    exact native_interior_graph_splitting_v475.contDiff.comp_contDiffOn
      (contDiffOn_id.prodMk contDiffOn_const)
  have hGB : ContDiffOn ℝ ∞ (fun x : E2 => graphPoint x (c.height x)) c.O := by
    change ContDiffOn ℝ ∞ (fun x : E2 => native_interior_graph_splitting_v475 (x,c.height x)) c.O
    exact native_interior_graph_splitting_v475.contDiff.comp_contDiffOn
      (contDiffOn_id.prodMk c.height_smooth)
  have hΓA : ContinuousOn ΓA c.O :=
    (c.coordinates.inverse_smooth.comp hGA.contMDiffOn
      (fun x hx => (c.points_inside x hx).1)).continuousOn
  have hΓB : ContinuousOn ΓB c.O :=
    (c.coordinates.inverse_smooth.comp hGB.contMDiffOn
      (fun x hx => (c.points_inside x hx).2)).continuousOn
  let Q : Set E2 := ((c.O ∩ ΓA ⁻¹' Z) ∩ (c.O ∩ ΓB ⁻¹' Z)) ∩
    ((c.O ∩ (fun x => graphPoint x 0) ⁻¹' X.domain) ∩
      (c.O ∩ (fun x => graphPoint x (c.height x)) ⁻¹' X.domain))
  have hQ : IsOpen Q :=
    ((hΓA.isOpen_inter_preimage c.open_O hZ).inter
      (hΓB.isOpen_inter_preimage c.open_O hZ)).inter
      ((hGA.continuousOn.isOpen_inter_preimage c.open_O X.domain_open).inter
        (hGB.continuousOn.isOpen_inter_preimage c.open_O X.domain_open))
  have hbaseΓA : ΓA c.z = E.toSphere p := by
    change c.coordinates.chart.symm (graphPoint c.z 0) = _
    rw [← c.base_value,c.coordinates.chart.left_inv c.base_mem]
  have hbaseΓB : ΓB c.z = E.toSphere p := by
    change c.coordinates.chart.symm (graphPoint c.z (c.height c.z)) = _
    rw [c.height_zero,← c.base_value,c.coordinates.chart.left_inv c.base_mem]
  have hpZ : E.toSphere p ∈ Z := by
    have hh : p ∈ E.toSphere ⁻¹' Z := hZN.symm ▸ X.neighborhood_base
    exact hh
  have hzQ : c.z ∈ Q := by
    refine ⟨⟨⟨c.base_in_O,?_⟩,⟨c.base_in_O,?_⟩⟩,
      ⟨⟨c.base_in_O,?_⟩,⟨c.base_in_O,?_⟩⟩⟩
    · change ΓA c.z ∈ Z
      rwa [hbaseΓA]
    · change ΓB c.z ∈ Z
      rwa [hbaseΓB]
    · change graphPoint c.z 0 ∈ X.domain
      exact c.base_value ▸ X.base_mem
    · change graphPoint c.z (c.height c.z) ∈ X.domain
      rw [c.height_zero]
      exact c.base_value ▸ X.base_mem
  have hQO : Q ⊆ c.O := fun _ hx => hx.1.1.1
  have hgraphLift (x : E2) (t : ℝ) (hx : x ∈ c.O)
      (ht : graphPoint x t ∈ d.chart.target) :
      E.toSphere (χ (graphPoint x t)) = c.coordinates.chart.symm (graphPoint x t) := by
    rw [hχeq _ ht,hdinverse]
  have hWA (x : E2) (hx : x ∈ Q) (hx0 : 0 < x 0) : graphPoint x 0 ∈ W := by
    rw [hWdef]
    refine ⟨(hpoints x ⟨hQO hx,hx0⟩).2,?_⟩
    rw [← hZN]
    change E.toSphere (χ (graphPoint x 0)) ∈ Z
    rw [hgraphLift x 0 (hQO hx) (hpoints x ⟨hQO hx,hx0⟩).2]
    exact hx.1.1.2
  have hWB (x : E2) (hx : x ∈ Q) (hx0 : 0 < x 0) : graphPoint x (c.height x) ∈ W := by
    rw [hWdef]
    refine ⟨(hpoints x ⟨hQO hx,hx0⟩).1,?_⟩
    rw [← hZN]
    change E.toSphere (χ (graphPoint x (c.height x))) ∈ Z
    rw [hgraphLift x (c.height x) (hQO hx) (hpoints x ⟨hQO hx,hx0⟩).1]
    exact hx.1.2.2
  have hmetric (y : E3) (hy : y ∈ W) : X.metric.tensor =ᶠ[𝓝 y] H.tensor := by
    filter_upwards [hW.mem_nhds hy] with z hz
    rw [hH]
    exact hagree z hz
  refine ⟨X,Q,hQ,hzQ,hQO,fun x hx => ⟨hx.2.1.2,hx.2.2.2⟩,?_⟩
  intro x hx hx0
  refine ⟨?_,?_⟩
  · rw [graph_residual_metric_germ_congr_v480 X.metric H c.height x
      (c.height_smooth.contDiffAt (c.open_O.mem_nhds (hQO hx))).continuousAt
      (hmetric _ (hWB x hx hx0))]
    exact hPDEheight x ⟨hQO hx,hx0⟩
  · rw [graph_residual_metric_germ_congr_v480 X.metric H (fun _ => (0 : ℝ)) x
      continuousAt_const (hmetric _ (hWA x hx hx0))]
    exact hPDEzero x ⟨hQO hx,hx0⟩

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3ActualBoundaryLinearEquationV480 -/

noncomputable section
open Set Topology Function Filter MeasureTheory
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}
set_option maxHeartbeats 600000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

private theorem boundary_compact_affine_height_tube_v480
    (O : Set E2) (hO : IsOpen O) (p : E2) (hp : p ∈ O)
    (u : E2 → ℝ) (hu : ContDiffOn ℝ ∞ u O) (hu0 : u p = 0)
    (V : Set E3) (hV : IsOpen V) (hpV : graphPoint p 0 ∈ V) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall p r ⊆ O ∧
      ∀ x ∈ Metric.closedBall p r, ∀ t ∈ Icc (0 : ℝ) 1,
        jetPoint (x,t*u x,t • planarGradient u x) ∈ V := by
  let F : ℝ × E2 → E3 := fun q => graphPoint q.2 (q.1*u q.2)
  have hF : ContDiffOn ℝ ∞ F (univ ×ˢ O) := by
    change ContDiffOn ℝ ∞
      (fun q : ℝ × E2 => native_interior_graph_splitting_v475 (q.2,q.1*u q.2)) _
    exact native_interior_graph_splitting_v475.contDiff.comp_contDiffOn
      (contDiffOn_snd.prodMk (contDiffOn_fst.mul
        (hu.comp contDiffOn_snd (fun _ hx => hx.2))))
  let P : Set (ℝ × E2) := (univ ×ˢ O) ∩ F ⁻¹' V
  have hP : IsOpen P := hF.continuousOn.isOpen_inter_preimage (isOpen_univ.prod hO) hV
  have hCP : Icc (0 : ℝ) 1 ×ˢ ({p} : Set E2) ⊆ P := by
    intro q hq
    have hqp : q.2 = p := mem_singleton_iff.mp hq.2
    refine ⟨⟨mem_univ _,hqp ▸ hp⟩,?_⟩
    simpa [F,hqp,hu0] using hpV
  obtain ⟨Q,N,hQ,hN,hCQ,hpN,hQNP⟩ :=
    generalized_tube_lemma isCompact_Icc isCompact_singleton hP hCP
  have hpN' : p ∈ N := hpN (mem_singleton p)
  obtain ⟨r,hr,hBr⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hN.mem_nhds hpN')
  have hN0 (x : E2) (hx : x ∈ N) : x ∈ O :=
    (hQNP (show (0,x) ∈ Q ×ˢ N from
      ⟨hCQ (show (0 : ℝ) ∈ Icc 0 1 by norm_num),hx⟩)).1.2
  refine ⟨r,hr,hBr.trans hN0,?_⟩
  intro x hx t ht
  exact (hQNP (show (t,x) ∈ Q ×ˢ N from ⟨hCQ ht,hBr hx⟩)).2

/-- Actual arbitrary-pair boundary graph coefficients are smooth and
uniformly elliptic on a full ball across the boundary. Its literal height
solves the linear equation on the positive half of that same ball. -/
theorem original_pair_actual_boundary_linear_equation_v480
    (D : OriginalPair g J) (a0 : D.A.1.surface) (b0 : D.B.1.surface) {p : E.Carrier}
    (hp : p ∈ (𝓡∂ 3).boundary E.Carrier)
    (c : ActualBoundaryPairGraphV480 D.A.1.embedding D.B.1.embedding p)
    (hc : 0 < c.coefficient)
    (hboundary : D.A.1.embedding.toFun '' D.A.1.surface.boundary =
      D.B.1.embedding.toFun '' D.B.1.surface.boundary) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall c.z r ⊆ c.O ∧
      ∃ a : E2 → Mat2, ∃ b : E2 → E2, ∃ c0 : E2 → ℝ,
        SmoothEllipticOn a b c0 (Metric.ball c.z r) ∧
        (∀ x ∈ Metric.ball c.z r, 0 < x 0 → classicalL a b c0 c.height x = 0) ∧
        (∀ x ∈ Metric.ball c.z r, x 0 = 0 → c.height x = 0) := by
  obtain ⟨X,Q,hQ,hzQ,hQO,hpoints,hPDE⟩ :=
    original_pair_actual_boundary_pde_package_v480 D a0 b0 hp c hc hboundary
  obtain ⟨r,hr,hclosed,hsegments⟩ := boundary_compact_affine_height_tube_v480
    Q hQ c.z hzQ c.height (c.height_smooth.mono hQO) c.height_zero
    X.domain X.domain_open (c.base_value ▸ X.base_mem)
  let W : TwoHeightGraphWindow := {
    U := Q
    U_open := hQ
    V := X.domain
    V_open := X.domain_open
    metric := X.metric
    lowerHeightFunction := fun _ => 0
    upperHeightFunction := c.height
    lower_smooth := contDiffOn_const
    upper_smooth := c.height_smooth.mono hQO
    compactBase := Metric.closedBall c.z r
    compactBase_compact := isCompact_closedBall c.z r
    U_contains := hclosed
    jets_inside := by
      intro x hx t ht
      have hgrad0 : planarGradient (fun _ : E2 => (0 : ℝ)) x = 0 := by
        unfold planarGradient
        simp
      have hgrad : planarGradient (fun x => c.height x - (0 : ℝ)) x = planarGradient c.height x := by
        simp only [sub_zero]
      simpa only [zero_add,sub_zero,hgrad0,hgrad] using hsegments x hx t ht }
  obtain ⟨N,hN,hKN,hNQ,hs,hheight,hgrad,ha,hq,hlg,hlh,hb,hcc⟩ :=
    two_height_coefficient_open_tube W
  obtain ⟨hformula,hsym,ell,A,hell,hA,hbounds⟩ :=
    two_height_slope_hessian_uniform_bounds W
  have hballK : Metric.ball c.z r ⊆ W.compactBase := Metric.ball_subset_closedBall
  have hballN : Metric.ball c.z r ⊆ N := hballK.trans hKN
  have hEll : SmoothEllipticOn W.a W.b W.c (Metric.ball c.z r) :=
    ⟨fun i j => (ha i j).mono hballN,hb.mono hballN,hcc.mono hballN,
      fun x hx i j => hsym x (hballK hx) i j,ell,A,hell,hA,
      fun x hx v => hbounds x (hballK hx) v⟩
  refine ⟨r,hr,hclosed.trans hQO,W.a,W.b,W.c,hEll,?_,?_⟩
  · intro x hx hx0
    have hh := two_height_residual_mean_value W N hN hNQ hs hq x (hballN hx)
    have heq := hPDE x (hclosed (hballK hx)) hx0
    change native_interior_graph_residual_v475 X.metric c.height x -
      native_interior_graph_residual_v475 X.metric (fun _ => (0 : ℝ)) x =
        classicalL W.a W.b W.c (fun y => c.height y - 0) x at hh
    rw [heq.1,heq.2,sub_self] at hh
    simpa only [sub_zero] using hh.symm
  · intro x hx hx0
    exact c.height_boundary x (hQO (hclosed (hballK hx))) hx0

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3BoundaryGraphNoncoincidenceV480 -/

noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}
set_option maxHeartbeats 600000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

private theorem noncoincidence_base_v480 (x : E2) (t : ℝ) :
    native_collar_base_v475 (graphPoint x t) = x := by
  ext i
  fin_cases i <;> simp [native_collar_base_v475,graphPoint]

/-- The actual boundary graph height cannot vanish throughout any open
positive part of its original plane domain. Its nonzero germ is derived
from the original distance-two pair and actual image equality. -/
theorem original_pair_boundary_graph_no_positive_zero_germ_v480
    (D : OriginalPair g J) {p : E.Carrier}
    (c : ActualBoundaryPairGraphV480 D.A.1.embedding D.B.1.embedding p)
    (hc : 0 < c.coefficient)
    (V : Set E2) (hV : IsOpen V) (hVO : V ⊆ c.O)
    (x : E2) (hx : x ∈ V) (hx0 : 0 < x 0) :
    ¬ EqOn c.height (fun _ => (0 : ℝ)) {y ∈ V | 0 < y 0} := by
  intro hzero
  let VP : Set E2 := {y ∈ V | 0 < y 0}
  have hVP : IsOpen VP := hV.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).continuous)
  have hxO := hVO hx
  have hhA : c.coordinates.chart.symm (graphPoint x 0) ∈
      range (E.toSphere ∘ D.A.1.embedding.toFun) ∩ c.coordinates.chart.source := by
    rw [c.graph_A]
    exact ⟨x,⟨hxO,hx0.le⟩,rfl⟩
  obtain ⟨a,ha⟩ := hhA.1
  let q : E.Carrier := D.A.1.embedding.toFun a
  have haq : E.toSphere q = c.coordinates.chart.symm (graphPoint x 0) := ha
  have hqC : E.toSphere q ∈ c.coordinates.chart.source := haq.symm ▸ hhA.2
  have hqcoord : c.coordinates.chart (E.toSphere q) = graphPoint x 0 := by
    rw [haq,c.coordinates.chart.right_inv (c.points_inside x hxO).1]
  have hqaB : a ∉ D.A.1.surface.boundary := by
    intro haB
    have hh : E.toSphere q ∈ (E.toSphere ∘ D.A.1.embedding.toFun) ''
        D.A.1.surface.boundary ∩ c.coordinates.chart.source := ⟨⟨a,haB,rfl⟩,hqC⟩
    rw [c.boundary_A] at hh
    obtain ⟨y,⟨hy,hy0⟩,he⟩ := hh
    have heq := congrArg c.coordinates.chart he
    rw [c.coordinates.chart.right_inv (c.points_inside y hy).1,hqcoord] at heq
    have hyx : y = x := by
      simpa only [noncoincidence_base_v480] using congrArg native_collar_base_v475 heq
    exact hx0.ne' (hyx ▸ hy0)
  have hqI : q ∈ (𝓡∂ 3).interior E.Carrier := by
    rw [← (𝓡∂ 3).compl_boundary]
    intro hb
    have hb' : a ∈ D.A.1.embedding.toFun ⁻¹' (𝓡∂ 3).boundary E.Carrier := hb
    rw [D.A.1.embedding.boundary_preimage] at hb'
    exact hqaB hb'
  have hbaseCont : Continuous native_collar_base_v475 := by
    unfold native_collar_base_v475
    fun_prop
  let U : Set ThreeSphere := c.coordinates.chart.source ∩
    c.coordinates.chart ⁻¹' (native_collar_base_v475 ⁻¹' VP)
  have hU : IsOpen U := c.coordinates.chart.isOpen_inter_preimage (hVP.preimage hbaseCont)
  let N : Set E.Carrier := E.toSphere ⁻¹' U
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  have hN : IsOpen N := hU.preimage hinc.isEmbedding.continuous
  have hqN : q ∈ N := by
    refine ⟨hqC,?_⟩
    change native_collar_base_v475 (c.coordinates.chart (E.toSphere q)) ∈ VP
    rw [hqcoord,noncoincidence_base_v480]
    exact ⟨hx,hx0⟩
  have hmembership (r : E.Carrier) (s : E2) (t : ℝ) (hr : r ∈ N)
      (hs : s ∈ c.O) (ht : graphPoint s t ∈ c.coordinates.chart.target)
      (he : c.coordinates.chart.symm (graphPoint s t) = E.toSphere r) : s ∈ VP := by
    have hh := congrArg c.coordinates.chart he
    rw [c.coordinates.chart.right_inv ht] at hh
    have hbase := hr.2
    change native_collar_base_v475 (c.coordinates.chart (E.toSphere r)) ∈ VP at hbase
    rw [← hh,noncoincidence_base_v480] at hbase
    exact hbase
  have hImages : D.A.1.image ∩ N = D.B.1.image ∩ N := by
    ext r
    constructor
    · rintro ⟨hrA,hrN⟩
      obtain ⟨aa,haa⟩ := hrA
      have hh : E.toSphere r ∈ range (E.toSphere ∘ D.A.1.embedding.toFun) ∩
          c.coordinates.chart.source := ⟨⟨aa,congrArg E.toSphere haa⟩,hrN.1⟩
      rw [c.graph_A] at hh
      obtain ⟨y,⟨hy,hy0⟩,he⟩ := hh
      have hyVP := hmembership r y 0 hrN hy (c.points_inside y hy).1 he
      have hyzero := hzero hyVP
      have hinv : 0 ≤ c.inversePlanar y 0 :=
        (pos_of_mul_pos_right ((c.halfspace_sign y hy).2.1.mp hyVP.2) hc.le).le
      have hhB : E.toSphere r ∈ range (E.toSphere ∘ D.B.1.embedding.toFun) ∩
          c.coordinates.chart.source := by
        rw [c.graph_B]
        refine ⟨y,⟨hy,hinv⟩,?_⟩
        change c.coordinates.chart.symm (graphPoint y (c.height y)) = E.toSphere r
        change c.coordinates.chart.symm (graphPoint y 0) = E.toSphere r at he
        rwa [hyzero]
      obtain ⟨bb,hbb⟩ := hhB.1
      exact ⟨⟨bb,hinc.isEmbedding.injective hbb⟩,hrN⟩
    · rintro ⟨hrB,hrN⟩
      obtain ⟨bb,hbb⟩ := hrB
      have hh : E.toSphere r ∈ range (E.toSphere ∘ D.B.1.embedding.toFun) ∩
          c.coordinates.chart.source := ⟨⟨bb,congrArg E.toSphere hbb⟩,hrN.1⟩
      rw [c.graph_B] at hh
      obtain ⟨y,⟨hy,hy0⟩,he⟩ := hh
      have hyVP := hmembership r y (c.height y) hrN hy (c.points_inside y hy).2 he
      have hyzero := hzero hyVP
      have hhA : E.toSphere r ∈ range (E.toSphere ∘ D.A.1.embedding.toFun) ∩
          c.coordinates.chart.source := by
        rw [c.graph_A]
        refine ⟨y,⟨hy,hyVP.2.le⟩,?_⟩
        change c.coordinates.chart.symm (graphPoint y (c.height y)) = E.toSphere r at he
        rwa [hyzero] at he
      obtain ⟨aa,haa⟩ := hhA.1
      exact ⟨⟨aa,hinc.isEmbedding.injective haa⟩,hrN⟩
  have hqA : q ∈ D.A.1.image := ⟨a,rfl⟩
  have hqB : q ∈ D.B.1.image := (hImages ▸ (show q ∈ D.A.1.image ∩ N from ⟨hqA,hqN⟩)).1
  exact original_pair_no_interior_agreement_germ D hqI hqA hqB ⟨N,hN,hqN,hImages⟩

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3ActualBoundaryNormalizationV480 -/

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal Manifold
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
set_option maxHeartbeats 600000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- Actual boundary normalization: the height equation is asserted only on
its positive half. The auxiliary positive solution solves on the whole open set. -/
structure BoundaryNormalizationDataV480 where
  O : Set E2
  isOpen_O : IsOpen O
  a : E2 → Mat2
  b : E2 → E2
  c : E2 → ℝ
  u : E2 → ℝ
  h : E2 → ℝ
  elliptic : SmoothEllipticOn a b c O
  smooth_u : ContDiffOn ℝ ∞ u O
  smooth_h : ContDiffOn ℝ ∞ h O
  h_positive : ∀ x ∈ O, 0 < h x
  u_classical : ∀ x ∈ O, 0 < x 0 → classicalL a b c u x = 0
  h_classical : ∀ x ∈ O, classicalL a b c h x = 0

namespace BoundaryNormalizationDataV480
/-- A truthful coefficient-only wrapper with both solutions equal to h.
Its quotient is not the actual graph height quotient. -/
def coefficientData (N : BoundaryNormalizationDataV480) : InteriorNormalizationData_v475 :=
  { O := N.O, isOpen_O := N.isOpen_O, a := N.a, b := N.b, c := N.c,
    u := N.h, h := N.h, elliptic := N.elliptic,
    smooth_u := N.smooth_h, smooth_h := N.smooth_h,
    h_positive := N.h_positive, u_classical := N.h_classical, h_classical := N.h_classical }
def v (N : BoundaryNormalizationDataV480) (x : E2) : ℝ := N.u x/N.h x
def leading (N : BoundaryNormalizationDataV480) := N.coefficientData.leading
def drift (N : BoundaryNormalizationDataV480) := N.coefficientData.drift
def factor (N : BoundaryNormalizationDataV480) := N.coefficientData.factor
def normalizedA (N : BoundaryNormalizationDataV480) := N.coefficientData.normalizedA
def normalizedB (N : BoundaryNormalizationDataV480) := N.coefficientData.normalizedB
end BoundaryNormalizationDataV480

theorem boundary_divide_positive_classical_v480
    (N : BoundaryNormalizationDataV480) :
    ∀ x ∈ N.O, 0 < x 0 → classicalL N.leading N.drift (fun _ => 0) N.v x = 0 := by
  let U := N.O
  let f := N.u
  let Xf : E2 → E2 := fun x => matrixAction (N.a x) (planarGradient f x)
  let Xh : E2 → E2 := fun x => matrixAction (N.a x) (planarGradient N.h x)
  let X : E2 → E2 := fun x => matrixAction (N.leading x) (planarGradient N.v x)
  have hU : IsOpen U := N.isOpen_O
  have hfAt (x : E2) (hx : x ∈ U) : ContDiffAt ℝ ∞ f x :=
    (N.smooth_u x hx).contDiffAt (hU.mem_nhds hx)
  have hhAt (x : E2) (hx : x ∈ U) : ContDiffAt ℝ ∞ N.h x :=
    (N.smooth_h x hx).contDiffAt (hU.mem_nhds hx)
  have hhne (x : E2) (hx : x ∈ U) : N.h x ≠ 0 := (N.h_positive x hx).ne'
  have hvAt (x : E2) (hx : x ∈ U) : ContDiffAt ℝ ∞ N.v x :=
    (hfAt x hx).div (hhAt x hx) (hhne x hx)
  have haAt (x : E2) (hx : x ∈ U) (i j : Fin 2) :
      ContDiffAt ℝ ∞ (fun y => N.a y i j) x :=
    (N.elliptic.1 i j x hx).contDiffAt (hU.mem_nhds hx)
  have hgradAt (v : E2 → ℝ) (x : E2) (hv : ContDiffAt ℝ ∞ v x) :
      ContDiffAt ℝ ∞ (planarGradient v) x := by
    delta planarGradient
    apply ContDiffAt.sum
    intro i hi
    exact ((hv.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).smul contDiffAt_const
  have hactionAt (v : E2 → E2) (x : E2) (hx : x ∈ U)
      (hv : ContDiffAt ℝ ∞ v x) : ContDiffAt ℝ ∞ (fun y => matrixAction (N.a y) (v y)) x := by
    apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.contDiff.contDiffAt.comp
    apply contDiffAt_pi.mpr
    intro i
    apply ContDiffAt.sum
    intro j hj
    exact (haAt x hx i j).mul
      ((EuclideanSpace.proj (𝕜 := ℝ) (j : Fin 2)).contDiff.contDiffAt.comp x hv)
  have hXfAt (x : E2) (hx : x ∈ U) : ContDiffAt ℝ ∞ Xf x :=
    hactionAt _ x hx (hgradAt f x (hfAt x hx))
  have hXhAt (x : E2) (hx : x ∈ U) : ContDiffAt ℝ ∞ Xh x :=
    hactionAt _ x hx (hgradAt N.h x (hhAt x hx))
  have hqgrad (x : E2) (hx : x ∈ U) :
      N.h x • planarGradient N.v x = planarGradient f x - N.v x • planarGradient N.h x := by
    have hf := (hfAt x hx).differentiableAt (by simp)
    have hh := (hhAt x hx).differentiableAt (by simp)
    have hinv := (hasDerivAt_inv (hhne x hx)).comp_hasFDerivAt x hh.hasFDerivAt
    have hfd := hf.hasFDerivAt.mul hinv
    delta BoundaryNormalizationDataV480.v planarGradient
    simp only [div_eq_mul_inv]
    dsimp only [Pi.mul_def,Function.comp_def] at hfd
    rw [hfd.fderiv]
    simp only [add_apply,smul_apply,smul_eq_mul]
    rw [Finset.smul_sum,Finset.smul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [smul_smul]
    rw [← sub_smul]
    congr 1
    dsimp only [f]
    field_simp [hhne x hx]
    ring
  have hXeq (x : E2) (hx : x ∈ U) : X x = Xf x - N.v x • Xh x := by
    have hg := hqgrad x hx
    have hma : matrixAction (N.leading x) (planarGradient N.v x) =
        matrixAction (N.a x) (N.h x • planarGradient N.v x) := by
      ext i
      change (∑ j, (N.h x * N.a x i j) * planarGradient N.v x j) =
        ∑ j, N.a x i j * (N.h x * planarGradient N.v x j)
      apply Finset.sum_congr rfl
      intro j hj
      ring
    dsimp only [X,Xf,Xh]
    rw [hma,hg]
    ext i
    change (∑ j, N.a x i j * (planarGradient f x j - N.v x * planarGradient N.h x j)) =
      (∑ j, N.a x i j * planarGradient f x j) - N.v x * ∑ j, N.a x i j * planarGradient N.h x j
    simp only [Fin.sum_univ_two]
    ring
  have hXAt (x : E2) (hx : x ∈ U) : ContDiffAt ℝ ∞ X x := by
    apply ((hXfAt x hx).sub ((hvAt x hx).smul (hXhAt x hx))).congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hXeq y hy
  have hgcoord (v : E2 → ℝ) (x : E2) (i : Fin 2) :
      planarGradient v x i = fderiv ℝ v x (coordinateVector 2 i) := by
    fin_cases i <;> simp [planarGradient,coordinateVector,Fin.sum_univ_two]
  have hclassical (x : E2) (hx : x ∈ U) (hx0 : 0 < x 0) :
      (∑ i : Fin 2, fderiv ℝ (fun y => X y i) x (coordinateVector 2 i)) +
        inner ℝ (N.drift x) (planarGradient N.v x) = 0 := by
    have hdx (i : Fin 2) : fderiv ℝ (fun y => X y i) x =
        fderiv ℝ (fun y => Xf y i) x -
          (N.v x • fderiv ℝ (fun y => Xh y i) x + Xh x i • fderiv ℝ N.v x) := by
      have hevent : (fun y => X y i) =ᶠ[nhds x]
          (fun y => Xf y i - N.v y * Xh y i) := by
        filter_upwards [hU.mem_nhds hx] with y hy
        exact congrArg (fun v : E2 => v i) (hXeq y hy)
      rw [hevent.fderiv_eq]
      exact (((EuclideanSpace.proj (𝕜 := ℝ) (i : Fin 2)).differentiableAt.comp x
        ((hXfAt x hx).differentiableAt (by simp))).hasFDerivAt.sub
        (((hvAt x hx).differentiableAt (by simp)).hasFDerivAt.mul
          (((EuclideanSpace.proj (𝕜 := ℝ) (i : Fin 2)).differentiableAt.comp x
            ((hXhAt x hx).differentiableAt (by simp))).hasFDerivAt))).fderiv
    have hf := N.u_classical x hx hx0
    have hh := N.h_classical x hx
    have hvh : f x = N.v x * N.h x := by
      change f x = (f x / N.h x) * N.h x
      rw [div_mul_cancel₀ _ (hhne x hx)]
    have hg0 := congrArg (fun v : E2 => v 0) (hqgrad x hx)
    have hg1 := congrArg (fun v : E2 => v 1) (hqgrad x hx)
    simp only [PiLp.smul_apply,PiLp.sub_apply,smul_eq_mul] at hg0 hg1
    simp only [Fin.sum_univ_two,hdx,sub_apply,add_apply,smul_apply,smul_eq_mul]
    simp only [classicalL,Fin.sum_univ_two] at hf hh
    change fderiv ℝ (fun y => Xf y 0) x (coordinateVector 2 0) +
      fderiv ℝ (fun y => Xf y 1) x (coordinateVector 2 1) +
      inner ℝ (N.b x) (planarGradient f x) + N.c x * f x = 0 at hf
    change fderiv ℝ (fun y => Xh y 0) x (coordinateVector 2 0) +
      fderiv ℝ (fun y => Xh y 1) x (coordinateVector 2 1) +
      inner ℝ (N.b x) (planarGradient N.h x) + N.c x * N.h x = 0 at hh
    simp only [BoundaryNormalizationDataV480.drift, BoundaryNormalizationDataV480.coefficientData, InteriorNormalizationData_v475.drift]
    change _ + inner ℝ (Xh x + N.h x • N.b x) (planarGradient N.v x) = 0
    simp only [EuclideanSpace.inner_eq_star_dotProduct,Fin.sum_univ_two,
      dotProduct,star_trivial,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul] at hf hh ⊢
    simp only [← hgcoord] at hf hh ⊢
    rw [hvh] at hf
    linear_combination hf - N.v x * hh + N.b x 0 * hg0 + N.b x 1 * hg1
  intro x hx hx0
  simpa only [classicalL,zero_mul,add_zero] using hclassical x hx hx0


theorem boundary_normalized_classical_v480 (N : BoundaryNormalizationDataV480) :
    ∀ x ∈ N.O, 0 < x 0 → classicalL N.normalizedA N.normalizedB (fun _ => 0) N.v x = 0 := by
  intro x hx hx0
  have hO := N.isOpen_O
  have hhAt : ContDiffAt ℝ ∞ N.h x := (N.smooth_h x hx).contDiffAt (hO.mem_nhds hx)
  have huAt : ContDiffAt ℝ ∞ N.u x := (N.smooth_u x hx).contDiffAt (hO.mem_nhds hx)
  have hvAt : ContDiffAt ℝ ∞ N.v x := huAt.div hhAt (N.h_positive x hx).ne'
  have haAt (i j : Fin 2) : ContDiffAt ℝ ∞ (fun y => N.a y i j) x :=
    (N.elliptic.1 i j x hx).contDiffAt (hO.mem_nhds hx)
  have hleadAt (i j : Fin 2) : ContDiffAt ℝ ∞ (fun y => N.leading y i j) x :=
    hhAt.mul (haAt i j)
  have hgrad : ContDiffAt ℝ ∞ (planarGradient N.v) x := by
    unfold planarGradient
    apply ContDiffAt.sum
    intro i hi
    exact ((hvAt.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).smul contDiffAt_const
  have hP (i : Fin 2) : DifferentiableAt ℝ
      (fun y => matrixAction (N.leading y) (planarGradient N.v y) i) x := by
    change DifferentiableAt ℝ (fun y => ∑ j : Fin 2,
      N.leading y i j * planarGradient N.v y j) x
    apply DifferentiableAt.fun_sum
    intro j hj
    exact ((hleadAt i j).differentiableAt (by simp)).mul
      ((EuclideanSpace.proj (𝕜 := ℝ) j).differentiableAt.comp x (hgrad.differentiableAt (by simp)))
  have hfactor : ContDiffAt ℝ ∞ N.factor x :=
    (native_interior_normalized_coefficients_v475 N.coefficientData {x} isCompact_singleton
      (convex_singleton x) (singleton_nonempty x) (singleton_subset_iff.mpr hx)).2.2.2.2
      x (mem_singleton x)
  have hsym (i j : Fin 2) : N.leading x i j = N.leading x j i := by
    change N.h x*N.a x i j = N.h x*N.a x j i
    rw [N.elliptic.2.2.2.1 x hx i j]
  have hh := native_scalar_normalized_classical_v475 N.leading N.drift N.v N.factor x
    hsym (hfactor.differentiableAt (by simp)) hP
  change classicalL N.normalizedA N.normalizedB (fun _ => 0) N.v x = _ at hh
  rw [boundary_divide_positive_classical_v480 N x hx hx0,mul_zero] at hh
  exact hh


variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}

/-- The positive solution and determinant normalization are constructed
for the same arbitrary original-pair boundary height and its actual PDE. -/
theorem original_pair_actual_boundary_normalization_v480
    (D : OriginalPair g J) (a0 : D.A.1.surface) (b0 : D.B.1.surface) {p : E.Carrier}
    (hp : p ∈ (𝓡∂ 3).boundary E.Carrier)
    (c : ActualBoundaryPairGraphV480 D.A.1.embedding D.B.1.embedding p)
    (hc : 0 < c.coefficient)
    (hboundary : D.A.1.embedding.toFun '' D.A.1.surface.boundary =
      D.B.1.embedding.toFun '' D.B.1.surface.boundary) :
    ∃ N : BoundaryNormalizationDataV480, c.z ∈ N.O ∧ N.O ⊆ c.O ∧ N.u = c.height ∧
      (∀ x ∈ N.O, x 0 = 0 → N.v x = 0) ∧
      (∀ x ∈ N.O, 0 < x 0 → classicalL N.normalizedA N.normalizedB
        (fun _ => 0) N.v x = 0) := by
  obtain ⟨r,hr,hclosed,a,b,c0,hEll,hu,hflat⟩ :=
    original_pair_actual_boundary_linear_equation_v480 D a0 b0 hp c hc hboundary
  have hz : c.z ∈ Metric.ball c.z r := Metric.mem_ball_self hr
  obtain ⟨V,hV,hzV,hVr,h,hh,hpos,hLh⟩ := native_local_positive_classical_v475
    (Metric.ball c.z r) Metric.isOpen_ball c.z hz a b c0 hEll
  have hVO : V ⊆ c.O := hVr.trans (Metric.ball_subset_closedBall.trans hclosed)
  let N : BoundaryNormalizationDataV480 := {
    O := V, isOpen_O := hV, a := a, b := b, c := c0,
    u := c.height, h := h,
    elliptic := ⟨fun i j => (hEll.1 i j).mono hVr,
      hEll.2.1.mono hVr,hEll.2.2.1.mono hVr,
      fun x hx i j => hEll.2.2.2.1 x (hVr hx) i j,
      let ⟨ell,A,hell,hA,hbounds⟩ := hEll.2.2.2.2
      ⟨ell,A,hell,hA,fun x hx v => hbounds x (hVr hx) v⟩⟩,
    smooth_u := c.height_smooth.mono hVO, smooth_h := hh,
    h_positive := fun x hx => lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/2) (hpos x hx),
    u_classical := fun x hx => hu x (hVr hx), h_classical := hLh }
  refine ⟨N,hzV,hVO,rfl,?_,boundary_normalized_classical_v480 N⟩
  intro x hx hx0
  change c.height x / h x = 0
  rw [hflat x (hVr hx) hx0,zero_div]

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3BoundaryOperatorSwapV480 -/

noncomputable section
open Set Topology Function Filter MeasureTheory
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
set_option maxHeartbeats 600000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

private def swapIndexV480 : Fin 2 ≃ Fin 2 := Equiv.swap 0 1

def boundarySwapLeadingV480 (a : E2 → Mat2) (y : E2) : Mat2 :=
  fun i j => a (coordinateSwap y) (swapIndexV480 i) (swapIndexV480 j)
def boundarySwapDriftV480 (b : E2 → E2) (y : E2) : E2 :=
  coordinateSwap (b (coordinateSwap y))

private theorem boundary_swap_coordinateVector_v480 (i : Fin 2) :
    coordinateSwap (coordinateVector 2 i) = coordinateVector 2 (swapIndexV480 i) := by
  ext j
  fin_cases i <;> fin_cases j <;> simp [coordinateSwap,coordinateVector,swapIndexV480]

private theorem boundary_gradient_coordinate_v480 (u : E2 → ℝ) (x : E2) (i : Fin 2) :
    planarGradient u x i = fderiv ℝ u x (coordinateVector 2 i) := by
  fin_cases i <;> simp [planarGradient,coordinateVector,Fin.sum_univ_two]

private theorem boundary_swap_fderiv_v480 (x : E2) :
    fderiv ℝ (coordinateSwap : E2 → E2) x =
      coordinateSwap.toContinuousLinearEquiv.toContinuousLinearMap :=
  coordinateSwap.toContinuousLinearEquiv.hasFDerivAt.fderiv

/-- The actual pointwise gradient under the normal/tangent permutation. -/
theorem boundary_gradient_swap_v480 (u : E2 → ℝ) (x : E2)
    (hu : DifferentiableAt ℝ u (coordinateSwap x)) :
    planarGradient (fun y => u (coordinateSwap y)) x =
      coordinateSwap (planarGradient u (coordinateSwap x)) := by
  ext i
  rw [boundary_gradient_coordinate_v480]
  change fderiv ℝ (u ∘ coordinateSwap) x (coordinateVector 2 i) = _
  rw [fderiv_comp x hu coordinateSwap.toContinuousLinearEquiv.differentiableAt,
    ContinuousLinearMap.comp_apply,
    boundary_swap_fderiv_v480]
  change fderiv ℝ u (coordinateSwap x) (coordinateSwap (coordinateVector 2 i)) = _
  rw [boundary_swap_coordinateVector_v480]
  fin_cases i <;> simp [coordinateSwap,swapIndexV480,boundary_gradient_coordinate_v480]

private theorem boundary_swap_action_v480 (a : E2 → Mat2) (y v : E2) :
    matrixAction (boundarySwapLeadingV480 a y) (coordinateSwap v) =
      coordinateSwap (matrixAction (a (coordinateSwap y)) v) := by
  ext i
  fin_cases i <;> simp [matrixAction,boundarySwapLeadingV480,swapIndexV480,
    coordinateSwap,Fin.sum_univ_two] <;> ring

/-- Exact orthogonal transport of the divergence operator, including drift
and zeroth-order coefficient. -/
theorem boundary_classical_swap_v480 (O : Set E2) (hO : IsOpen O)
    (a : E2 → Mat2) (b : E2 → E2) (c u : E2 → ℝ)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) O)
    (hu : ContDiffOn ℝ ∞ u O) (x : E2) (hx : coordinateSwap x ∈ O) :
    classicalL (boundarySwapLeadingV480 a) (boundarySwapDriftV480 b)
      (fun y => c (coordinateSwap y)) (fun y => u (coordinateSwap y)) x =
      classicalL a b c u (coordinateSwap x) := by
  let v := fun y => u (coordinateSwap y)
  let F := fun y => matrixAction (a y) (planarGradient u y)
  have hd (y : E2) (hy : y ∈ O) : DifferentiableAt ℝ u y :=
    ((hu y hy).contDiffAt (hO.mem_nhds hy)).differentiableAt (by simp)
  have hg : ContDiffOn ℝ ∞ (planarGradient u) O := by
    unfold planarGradient
    apply ContDiffOn.sum
    intro i hi
    exact ((hu.fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const).smul_const _
  have hF (i : Fin 2) : DifferentiableAt ℝ (fun y => F y i) (coordinateSwap x) := by
    change DifferentiableAt ℝ (fun y => ∑ j : Fin 2, a y i j * planarGradient u y j) _
    apply DifferentiableAt.fun_sum
    intro j hj
    exact (((ha i j _ hx).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)).mul
      ((EuclideanSpace.proj (𝕜 := ℝ) j).differentiableAt.comp _
        (((hg _ hx).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)))
  have he (i : Fin 2) :
      (fun y => matrixAction (boundarySwapLeadingV480 a y) (planarGradient v y) i) =ᶠ[𝓝 x]
        (fun y => F (coordinateSwap y) (swapIndexV480 i)) := by
    filter_upwards [coordinateSwap.continuous.continuousAt.preimage_mem_nhds
      (hO.mem_nhds hx)] with y hy
    rw [boundary_gradient_swap_v480 u y (hd _ hy),boundary_swap_action_v480]
    fin_cases i <;> simp [coordinateSwap,swapIndexV480,F]
  have hf (i : Fin 2) : fderiv ℝ
      (fun y => matrixAction (boundarySwapLeadingV480 a y) (planarGradient v y) i) x
        (coordinateVector 2 i) =
      fderiv ℝ (fun y => F y (swapIndexV480 i)) (coordinateSwap x)
        (coordinateVector 2 (swapIndexV480 i)) := by
    rw [(he i).fderiv_eq]
    change fderiv ℝ ((fun y => F y (swapIndexV480 i)) ∘ coordinateSwap) x _ = _
    rw [fderiv_comp x (hF _) coordinateSwap.toContinuousLinearEquiv.differentiableAt,
      boundary_swap_fderiv_v480,ContinuousLinearMap.comp_apply]
    change fderiv ℝ (fun y => F y (swapIndexV480 i)) (coordinateSwap x)
      (coordinateSwap (coordinateVector 2 i)) = _
    rw [boundary_swap_coordinateVector_v480]
  unfold classicalL
  change (∑ i : Fin 2, fderiv ℝ
    (fun y => matrixAction (boundarySwapLeadingV480 a y) (planarGradient v y) i) x
    (coordinateVector 2 i)) + _ + _ = _
  simp_rw [hf]
  rw [boundary_gradient_swap_v480 u x (hd _ hx)]
  have hin : inner ℝ (boundarySwapDriftV480 b x)
      (coordinateSwap (planarGradient u (coordinateSwap x))) =
      inner ℝ (b (coordinateSwap x)) (planarGradient u (coordinateSwap x)) :=
    coordinateSwap.inner_map_map _ _
  rw [hin]
  simp [Fin.sum_univ_two,swapIndexV480,F,add_comm]

/-- Full smooth uniform ellipticity is preserved by the actual isometry. -/
theorem boundary_smooth_elliptic_swap_v480 (O : Set E2)
    (a : E2 → Mat2) (b : E2 → E2) (c : E2 → ℝ)
    (hEll : SmoothEllipticOn a b c O) :
    SmoothEllipticOn (boundarySwapLeadingV480 a) (boundarySwapDriftV480 b)
      (fun y => c (coordinateSwap y)) (coordinateSwap ⁻¹' O) := by
  obtain ⟨ha,hb,hc,hsym,ell,A,hell,hA,hbounds⟩ := hEll
  refine ⟨fun i j => (ha (swapIndexV480 i) (swapIndexV480 j)).comp
    coordinateSwap.contDiff.contDiffOn (fun _ hx => hx),
    coordinateSwap.contDiff.comp_contDiffOn
      (hb.comp coordinateSwap.contDiff.contDiffOn (fun _ hx => hx)),
    hc.comp coordinateSwap.contDiff.contDiffOn (fun _ hx => hx),
    fun y hy i j => hsym _ hy _ _,ell,A,hell,hA,?_⟩
  intro y hy v
  have heq : inner ℝ v (matrixAction (boundarySwapLeadingV480 a y) v) =
      inner ℝ (coordinateSwap v)
        (matrixAction (a (coordinateSwap y)) (coordinateSwap v)) := by
    rw [← coordinateSwap_involutive v,boundary_swap_action_v480,
      coordinateSwap.inner_map_map]
    rw [coordinateSwap_involutive]
  rw [heq]
  simpa only [coordinateSwap.norm_map] using hbounds _ hy (coordinateSwap v)

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3BoundaryIsothermalPatchV480 -/

noncomputable section
open Set Topology Function MeasureTheory
open scoped Manifold ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider
set_option maxHeartbeats 600000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

structure BoundaryIsothermalPatchV480 (R : ℝ) (A : E2 → Mat2) where
  sourceR : ℝ
  sourceR_pos : 0 < sourceR
  sourceR_inside : sourceR < R
  targetR : ℝ
  targetR_pos : 0 < targetR
  chart : PartialHomeomorph E2 E2
  source_contains : SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc sourceR ⊆ chart.source
  target_contains : SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc targetR ⊆ chart.target
  base : chart 0 = 0
  forward_C1 : ContDiffOn ℝ 1 chart chart.source
  inverse_C1 : ContDiffOn ℝ 1 chart.symm chart.target
  forward_det : ∀ x ∈ chart.source, Matrix.det (jacobian chart x) ≠ 0
  inverse_det : ∀ z ∈ chart.target, Matrix.det (jacobian chart.symm z) ≠ 0
  alpha : ℝ≥0
  alpha_pos : 0 < alpha
  alpha_lt_one : alpha < 1
  forward_holder : ∀ i j, ∃ C : ℝ≥0,
    HolderOnWith C alpha (fun x => jacobian chart x i j) (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc sourceR)
  inverse_holder : ∀ i j, ∃ C : ℝ≥0,
    HolderOnWith C alpha (fun z => jacobian chart.symm z i j) (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc targetR)
  forward_boundary : ∀ x ∈ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc sourceR, (chart x) 1 = 0 ↔ x 1 = 0
  forward_interior : ∀ x ∈ halfDisc sourceR, 0 < (chart x) 1
  inverse_half_disc : ∀ z ∈ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc targetR, chart.symm z ∈ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc sourceR
  inverse_interior : ∀ z ∈ halfDisc targetR, chart.symm z ∈ halfDisc sourceR
  inverse_flat : ∀ z ∈ flatArc targetR, chart.symm z ∈ flatArc sourceR
  biLipschitz : ∃ lo hi : ℝ, 0 < lo ∧ 0 < hi ∧
    ∀ x ∈ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc sourceR, ∀ y ∈ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc sourceR,
      lo * dist x y ≤ dist (chart x) (chart y) ∧ dist (chart x) (chart y) ≤ hi * dist x y
  conformalInverseMetric : ∀ x ∈ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc sourceR, ∃ lambda : ℝ,
    0 < lambda ∧ (A x)⁻¹ =
      lambda • ((jacobian chart x).transpose * jacobian chart x)

theorem boundary_isothermal_patch_from_metric_provider_v480 (R : ℝ) (A : E2 → Mat2)
    (G : InverseMetricData (R) A)
    (Ω : SmoothFlatJordanDomain (R))
    (P : MetricDiscParametrization G Ω) (X : MetricParametrizationExtensions P) :
    ∃ F : BoundaryIsothermalPatchV480 R A,
      F.sourceR < Ω.localR ∧
      (∀ x ∈ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc F.sourceR, F.chart x = boundaryMobius P.base (P.tau.symm x)) ∧
      (∀ x ∈ F.chart.source, F.chart x = boundaryMobius P.base (X.inverse x)) ∧
      (∀ x ∈ flatArc F.sourceR, P.tau.symm x ≠ -P.base) :=  by 
  have pole_denominator (a z : E2) : (-complexCoordinate a) - complexCoordinate z = 0 ↔ z = -a := by
    constructor
    · intro h
      ext i
      fin_cases i
      · have hr := congrArg Complex.re h
        dsimp [complexCoordinate] at hr
        simp at hr
        change z 0 = -a 0
        linarith
      · have hi := congrArg Complex.im h
        dsimp [complexCoordinate] at hi
        simp at hi
        change z 1 = -a 1
        linarith
    · intro h
      subst z
      dsimp [complexCoordinate]
      simp
      ring
  have mobius_base (a : E2) : boundaryMobius a a = 0 := by
    change realCoordinate (Complex.I * ((-complexCoordinate a) + complexCoordinate a) /
      ((-complexCoordinate a) - complexCoordinate a)) = 0
    rw [neg_add_cancel, mul_zero, zero_div]
    change (EuclideanSpace.equiv (Fin 2) ℝ).symm ![(0 : ℂ).re, (0 : ℂ).im] = 0
    ext i
    fin_cases i <;> rfl
  have complex_smooth : ContDiff ℝ ∞ complexCoordinate := by
    unfold complexCoordinate
    apply ContDiff.add
    · exact Complex.ofRealCLM.contDiff.comp (by fun_prop)
    · apply contDiff_const.mul
      exact Complex.ofRealCLM.contDiff.comp (by fun_prop)
  have real_smooth : ContDiff ℝ ∞ realCoordinate := by
    unfold realCoordinate
    apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearMap.contDiff.comp
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact Complex.reCLM.contDiff
    · exact Complex.imCLM.contDiff
  have mobius_smooth (a : E2) : ContDiffOn ℝ ∞ (boundaryMobius a) {z | z ≠ -a} := by
    have hc : ContDiff ℝ ∞ complexCoordinate := by
      unfold complexCoordinate
      apply ContDiff.add
      · exact Complex.ofRealCLM.contDiff.comp (by fun_prop)
      · apply contDiff_const.mul
        exact Complex.ofRealCLM.contDiff.comp (by fun_prop)
    have hr : ContDiff ℝ ∞ realCoordinate := by
      unfold realCoordinate
      apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearMap.contDiff.comp
      apply contDiff_pi.mpr
      intro i
      fin_cases i
      · exact Complex.reCLM.contDiff
      · exact Complex.imCLM.contDiff
    intro z hz
    have hd : (-complexCoordinate a) - complexCoordinate z ≠ 0 := by
      intro h
      apply hz
      ext i
      fin_cases i
      · have he := congrArg Complex.re h
        dsimp [complexCoordinate] at he
        simp at he
        change z 0 = -a 0
        linarith
      · have he := congrArg Complex.im h
        dsimp [complexCoordinate] at he
        simp at he
        change z 1 = -a 1
        linarith
    change ContDiffWithinAt ℝ ∞
      (fun y => realCoordinate (Complex.I * ((-complexCoordinate a) + complexCoordinate y) /
        ((-complexCoordinate a) - complexCoordinate y))) _ z
    apply ContDiffAt.contDiffWithinAt
    apply hr.contDiffAt.comp z
    simp only [div_eq_mul_inv]
    exact (contDiffAt_const.mul (contDiffAt_const.add hc.contDiffAt)).mul
      ((contDiffAt_const.sub hc.contDiffAt).inv hd)
  have mobius_boundary (a z : E2) (ha : ‖a‖ = 1) (hz : ‖z‖ = 1) (hza : z ≠ -a) :
      (boundaryMobius a z) 1 = 0 := by
    have hd : (-complexCoordinate a) - complexCoordinate z ≠ 0 := by
      intro h
      apply hza
      ext i
      fin_cases i
      · have he := congrArg Complex.re h
        dsimp [complexCoordinate] at he
        simp at he
        change z 0 = -a 0
        linarith
      · have he := congrArg Complex.im h
        dsimp [complexCoordinate] at he
        simp at he
        change z 1 = -a 1
        linarith
    change (Complex.I * ((-complexCoordinate a) + complexCoordinate z) /
      ((-complexCoordinate a) - complexCoordinate z)).im = 0
    rw [Complex.div_im]
    have hnorm : Complex.normSq ((-complexCoordinate a) - complexCoordinate z) ≠ 0 :=
      (Complex.normSq_pos.mpr hd).ne'
    field_simp [hnorm]
    have ha2 := EuclideanSpace.norm_sq_eq a
    have hz2 := EuclideanSpace.norm_sq_eq z
    simp only [ha, hz, one_pow, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs] at ha2 hz2
    dsimp only [complexCoordinate]
    simp only [Complex.neg_re, Complex.neg_im, Complex.add_re,
      Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    nlinarith
  have mobius_interior (a z : E2) (ha : ‖a‖ = 1) (hz : ‖z‖ < 1) (hza : z ≠ -a) :
      0 < (boundaryMobius a z) 1 := by
    have hd : (-complexCoordinate a) - complexCoordinate z ≠ 0 := by
      intro h
      apply hza
      ext i
      fin_cases i
      · have he := congrArg Complex.re h
        dsimp [complexCoordinate] at he
        simp at he
        change z 0 = -a 0
        linarith
      · have he := congrArg Complex.im h
        dsimp [complexCoordinate] at he
        simp at he
        change z 1 = -a 1
        linarith
    change 0 < (Complex.I * ((-complexCoordinate a) + complexCoordinate z) /
      ((-complexCoordinate a) - complexCoordinate z)).im
    rw [Complex.div_im]
    have hnorm : Complex.normSq ((-complexCoordinate a) - complexCoordinate z) ≠ 0 :=
      (Complex.normSq_pos.mpr hd).ne'
    rw [← sub_div, div_pos_iff]
    left
    refine ⟨?_, Complex.normSq_pos.mpr hd⟩
    have ha2 := EuclideanSpace.norm_sq_eq a
    have hz2 := EuclideanSpace.norm_sq_eq z
    simp only [ha, one_pow, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs] at ha2 hz2
    dsimp only [complexCoordinate]
    simp only [Complex.neg_re, Complex.neg_im, Complex.add_re,
      Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    nlinarith [norm_nonneg z]
  have safe_radius :
      ∃ r : ℝ, 0 < r ∧ r < Ω.localR ∧
        closedDisc r ⊆ X.inverse_neighborhood ∧
        (∀ x ∈ closedDisc r, X.inverse x ≠ -P.base) ∧
        (∀ x ∈ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc r, P.tau.symm x ≠ -P.base) := by
    have hzero : (0 : E2) ∈ closure Ω.domain := frontier_subset_closure Ω.base_boundary
    have hbase : X.inverse 0 = P.base := (X.inverse_agrees 0 hzero).trans P.inverse_base
    have hnorm : ‖P.base‖ = 1 := by
      have hh := P.base_on_circle
      rw [Metric.mem_sphere, dist_zero_right] at hh
      exact hh
    have hne : P.base ≠ -P.base := by
      intro hh
      have hz : P.base = 0 := by
        ext i
        have hi := congrArg (fun x : E2 => x i) hh
        change P.base i = -P.base i at hi
        change P.base i = 0
        linarith
      rw [hz, norm_zero] at hnorm
      norm_num at hnorm
    have hcontinuous : ContinuousAt X.inverse 0 :=
      (X.inverse_C1 0 (X.inverse_contains hzero)).contDiffAt
        (X.inverse_open.mem_nhds (X.inverse_contains hzero)) |>.continuousAt
    have hpole := hcontinuous.eventually_ne (show X.inverse 0 ≠ -P.base by rw [hbase]; exact hne)
    obtain ⟨e, he, hball⟩ := Metric.mem_nhds_iff.mp
      (Filter.inter_mem hpole (X.inverse_open.mem_nhds (X.inverse_contains hzero)))
    refine ⟨min e Ω.localR / 2, div_pos (lt_min he Ω.localR_pos) (by norm_num), ?_, ?_, ?_, ?_⟩
    · have := min_le_right e Ω.localR
      linarith [Ω.localR_pos]
    · intro x hx
      exact (hball ((Metric.closedBall_subset_ball (by linarith [min_le_left e Ω.localR, he])) hx)).2
    · intro x hx
      exact (hball ((Metric.closedBall_subset_ball (by linarith [min_le_left e Ω.localR, he])) hx)).1
    · intro x hx
      have hcl : x ∈ closure Ω.domain := Ω.contains_closed_half_disc
        ⟨Metric.closedBall_subset_closedBall (by linarith [min_le_right e Ω.localR, Ω.localR_pos]) hx.1, hx.2⟩
      rw [← X.inverse_agrees x hcl]
      exact (hball ((Metric.closedBall_subset_ball (by linarith [min_le_left e Ω.localR, he])) hx.1)).1
  obtain ⟨r, hr, hr_local, hr_neighborhood, hr_pole, hr_tau_pole⟩ := safe_radius
  have hr_inside : r < R := hr_local.trans Ω.localR_inside
  have map_regular : ∀ x ∈ closedDisc r,
      ContDiffAt ℝ 1 (fun y => boundaryMobius P.base (X.inverse y)) x := by
    intro x hx
    have hc := (X.inverse_C1 x (hr_neighborhood hx)).contDiffAt
      (X.inverse_open.mem_nhds (hr_neighborhood hx))
    have hm : ContDiffAt ℝ ∞ (boundaryMobius P.base) (X.inverse x) :=
      (mobius_smooth P.base (X.inverse x) (hr_pole x hx)).contDiffAt
        (isOpen_compl_singleton.mem_nhds (hr_pole x hx))
    exact (hm.of_le (by simp)).comp x hc
  have actual_inverse_agrees : ∀ x ∈ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc r,
      X.inverse x = P.tau.symm x := by
    intro x hx
    apply X.inverse_agrees
    apply Ω.contains_closed_half_disc
    exact ⟨Metric.closedBall_subset_closedBall hr_local.le hx.1, hx.2⟩
  have map_base : boundaryMobius P.base (X.inverse 0) = 0 := by
    rw [X.inverse_agrees 0 (frontier_subset_closure Ω.base_boundary), P.inverse_base]
    exact mobius_base P.base
  have base_norm : ‖P.base‖ = 1 := by
    have h := P.base_on_circle
    rwa [Metric.mem_sphere, dist_zero_right] at h
  have map_boundary : ∀ x ∈ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc r, x 1 = 0 →
      (boundaryMobius P.base (X.inverse x)) 1 = 0 := by
    intro x hx hxzero
    have hflat : x ∈ flatArc Ω.localR :=
      ⟨Metric.closedBall_subset_ball hr_local hx.1, hxzero⟩
    have hfront : x ∈ frontier Ω.domain := by
      rw [← Ω.flat_subarc] at hflat
      exact hflat.1
    have hunit : P.tau.symm x ∈ Metric.sphere (0 : E2) 1 := by
      rw [← P.inverse_boundary_image]
      exact ⟨x, hfront, rfl⟩
    rw [actual_inverse_agrees x hx]
    apply mobius_boundary P.base (P.tau.symm x) base_norm
    · rwa [Metric.mem_sphere, dist_zero_right] at hunit
    · exact hr_tau_pole x hx
  have map_interior : ∀ x ∈ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc r, 0 < x 1 →
      0 < (boundaryMobius P.base (X.inverse x)) 1 := by
    intro x hx hxpos
    have hhalf : x ∈ halfDisc Ω.localR :=
      ⟨Metric.closedBall_subset_ball hr_local hx.1, hxpos⟩
    have hdom : x ∈ Ω.domain := by
      rw [← Ω.inward_side] at hhalf
      exact hhalf.1
    have hunit : P.tau.symm x ∈ disc 1 := by
      rw [← P.inverse_interior_image]
      exact ⟨x, hdom, rfl⟩
    rw [actual_inverse_agrees x hx]
    apply mobius_interior P.base (P.tau.symm x) base_norm
    · change dist (P.tau.symm x) 0 < 1 at hunit
      rwa [dist_zero_right] at hunit
    · exact hr_tau_pole x hx
  have map_boundary_iff : ∀ x ∈ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc r,
      (boundaryMobius P.base (X.inverse x)) 1 = 0 ↔ x 1 = 0 := by
    intro x hx
    constructor
    · intro he
      by_contra hn
      have hp := map_interior x hx (lt_of_le_of_ne hx.2 (Ne.symm hn))
      rw [he] at hp
      exact (lt_irrefl _ hp)
    · exact map_boundary x hx
  have inverse_metric_algebra (A T : Mat2) (lam : ℝ) (hT : Matrix.det T ≠ 0)
      (h : T.transpose * A * T = lam • (1 : Mat2)) :
      A = lam • (T⁻¹.transpose * T⁻¹) := by
    have hu : IsUnit (Matrix.det T) := isUnit_iff_ne_zero.mpr hT
    have hut : IsUnit (Matrix.det T.transpose) := by simpa using hu
    have he := congrArg (fun M : Mat2 => T.transpose⁻¹ * M * T⁻¹) h
    rw [Matrix.mul_assoc (Matrix.transpose T) A T, Matrix.nonsing_inv_mul_cancel_left, Matrix.mul_nonsing_inv_cancel_right] at he
    · rw [← Matrix.transpose_nonsing_inv] at he
      simpa only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one] using he
    · exact hu
    · exact hut
  have actual_metric_inverse : ∀ x ∈ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc r,
      inverseMetric A x = P.lambda (P.tau.symm x) •
        ((jacobianWithin P.tau (closedDisc 1) (P.tau.symm x))⁻¹.transpose *
          (jacobianWithin P.tau (closedDisc 1) (P.tau.symm x))⁻¹) := by
    intro x hx
    have htarget : x ∈ P.tau.target := by
      rw [P.target_eq]
      apply Ω.contains_closed_half_disc
      exact ⟨Metric.closedBall_subset_closedBall hr_local.le hx.1, hx.2⟩
    have hsource : P.tau.symm x ∈ closedDisc 1 := by
      rw [← P.source_eq]
      exact P.tau.map_target htarget
    have hm := P.conformal (P.tau.symm x) hsource
    rw [P.tau.right_inv htarget] at hm
    exact inverse_metric_algebra _ _ _ (P.forward_det _ hsource) hm
  have inverse_mobius (a : E2) (ha : ‖a‖ = 1) :
      ∃ inv : E2 → E2,
        (∀ z, z ≠ -a → inv (boundaryMobius a z) = z) ∧
        (∀ w, 0 ≤ w 1 → boundaryMobius a (inv w) = w) ∧
        (∀ w, 0 ≤ w 1 → inv w ∈ closedDisc 1) ∧
        (∀ w, 0 < w 1 → inv w ∈ disc 1) ∧
        (∀ w, w 1 = 0 → inv w ∈ Metric.sphere (0 : E2) 1) ∧
        inv 0 = a ∧
        (∀ w, 0 ≤ w 1 → ContDiffAt ℝ ∞ inv w) ∧
        (∀ w, 0 ≤ w 1 → inv w ≠ -a) := by
    have cr (z : ℂ) : complexCoordinate (realCoordinate z) = z := by
      dsimp only [complexCoordinate, realCoordinate]
      change (z.re : ℂ) + Complex.I * (z.im : ℂ) = z
      rw [mul_comm]
      exact Complex.re_add_im z
    have rc (x : E2) : realCoordinate (complexCoordinate x) = x := by
      ext i
      fin_cases i <;> dsimp only [realCoordinate, complexCoordinate] <;>
        simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
          Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero,
          Complex.add_im, Complex.mul_im, one_mul, zero_add] <;> rfl
    have cnorm (x : E2) : ‖complexCoordinate x‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, EuclideanSpace.real_norm_sq_eq]
      dsimp only [complexCoordinate]
      simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, zero_mul, one_mul, sub_zero, add_zero, zero_add, Fin.sum_univ_two]
      ring
    have an : complexCoordinate a ≠ 0 := by
      intro hh
      have hn := cnorm a
      rw [hh, norm_zero, ha] at hn
      norm_num at hn
    let inv (w : E2) : E2 := realCoordinate
      (complexCoordinate a * (Complex.I - complexCoordinate w) / (Complex.I + complexCoordinate w))
    have den (w : E2) (hw : 0 ≤ w 1) : Complex.I + complexCoordinate w ≠ 0 := by
      intro h
      have hh := congrArg Complex.im h
      dsimp only [complexCoordinate] at hh
      simp only [Complex.add_im, Complex.I_im, Complex.mul_im, Complex.I_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, add_zero, zero_add,
        Complex.zero_im] at hh
      linarith
    have inv_complex (w : E2) : complexCoordinate (inv w) =
        complexCoordinate a * (Complex.I - complexCoordinate w) / (Complex.I + complexCoordinate w) := cr _
    have inv_norm (w : E2) (hw : 0 ≤ w 1) :
        ‖inv w‖ ^ 2 = ‖Complex.I - complexCoordinate w‖ ^ 2 /
          ‖Complex.I + complexCoordinate w‖ ^ 2 := by
      rw [← cnorm, inv_complex, norm_div, norm_mul, div_pow, mul_pow, cnorm, ha, one_pow, one_mul]
    have diff_norm (w : E2) :
        ‖Complex.I + complexCoordinate w‖ ^ 2 - ‖Complex.I - complexCoordinate w‖ ^ 2 = 4 * w 1 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
      dsimp only [complexCoordinate]
      simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
        Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, zero_mul, mul_zero, one_mul, sub_zero, add_zero, zero_add]
      ring
    refine ⟨inv, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro z hz
      have hd : (-complexCoordinate a) - complexCoordinate z ≠ 0 := by
        intro hh
        apply hz
        apply (Function.LeftInverse.injective rc)
        have hzneg : complexCoordinate (-a) = -complexCoordinate a := by
          dsimp only [complexCoordinate]
          simp only [PiLp.neg_apply, Complex.ofReal_neg]
          ring
        rw [hzneg]
        linear_combination -hh
      apply (Function.LeftInverse.injective rc)
      rw [inv_complex]
      change complexCoordinate a *
        (Complex.I - complexCoordinate (realCoordinate (Complex.I * ((-complexCoordinate a) + complexCoordinate z) / ((-complexCoordinate a) - complexCoordinate z)))) /
        (Complex.I + complexCoordinate (realCoordinate (Complex.I * ((-complexCoordinate a) + complexCoordinate z) / ((-complexCoordinate a) - complexCoordinate z)))) = _
      rw [cr]
      field_simp (disch := first | assumption | exact Complex.I_ne_zero | positivity | norm_num)
      <;> ring_nf
      <;> field_simp (disch := first | assumption | exact Complex.I_ne_zero | positivity | norm_num)
    · intro w hw
      apply (Function.LeftInverse.injective rc)
      change complexCoordinate (realCoordinate (Complex.I * ((-complexCoordinate a) + complexCoordinate (inv w)) / ((-complexCoordinate a) - complexCoordinate (inv w)))) = complexCoordinate w
      rw [cr, inv_complex]
      have hdw := den w hw
      field_simp (disch := first | assumption | exact Complex.I_ne_zero | positivity | norm_num)
      <;> ring_nf
      <;> field_simp (disch := first | assumption | exact Complex.I_ne_zero | positivity | norm_num)
    · intro w hw
      change dist (inv w) 0 ≤ 1
      rw [dist_zero_right]
      have hdpos : 0 < ‖Complex.I + complexCoordinate w‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (den w hw))
      have hn : ‖inv w‖ ^ 2 ≤ 1 := by
        rw [inv_norm w hw, div_le_one hdpos]
        linarith [diff_norm w]
      nlinarith [norm_nonneg (inv w)]
    · intro w hw
      change dist (inv w) 0 < 1
      rw [dist_zero_right]
      have hdpos : 0 < ‖Complex.I + complexCoordinate w‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (den w hw.le))
      have hn : ‖inv w‖ ^ 2 < 1 := by
        rw [inv_norm w hw.le, div_lt_one hdpos]
        linarith [diff_norm w]
      nlinarith [norm_nonneg (inv w)]
    · intro w hw
      rw [Metric.mem_sphere, dist_zero_right]
      have hdpos : 0 < ‖Complex.I + complexCoordinate w‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (den w (by linarith)))
      have hn : ‖inv w‖ ^ 2 = 1 := by
        rw [inv_norm w (by linarith), div_eq_one_iff_eq hdpos.ne']
        linarith [diff_norm w]
      nlinarith [norm_nonneg (inv w)]
    · change realCoordinate (complexCoordinate a * (Complex.I - complexCoordinate 0) / (Complex.I + complexCoordinate 0)) = a
      have hc0 : complexCoordinate 0 = 0 := by
        dsimp only [complexCoordinate]
        change (0 : ℂ) + Complex.I * 0 = 0
        ring
      rw [hc0, sub_zero, add_zero, mul_div_cancel_right₀ _ Complex.I_ne_zero, rc]
    · intro w hw
      have hc : ContDiff ℝ ∞ complexCoordinate := by
        unfold complexCoordinate
        exact Complex.ofRealCLM.contDiff.comp (by fun_prop) |>.add
          (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (by fun_prop)))
      have hr : ContDiff ℝ ∞ realCoordinate := by
        unfold realCoordinate
        apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearMap.contDiff.comp
        apply contDiff_pi.mpr
        intro i
        fin_cases i
        · exact Complex.reCLM.contDiff
        · exact Complex.imCLM.contDiff
      change ContDiffAt ℝ ∞ (fun y => realCoordinate (complexCoordinate a * (Complex.I - complexCoordinate y) / (Complex.I + complexCoordinate y))) w
      apply hr.contDiffAt.comp w
      simp only [div_eq_mul_inv]
      exact (contDiffAt_const.mul (contDiffAt_const.sub hc.contDiffAt)).mul
        ((contDiffAt_const.add hc.contDiffAt).inv (den w hw))
    · intro w hw hh
      have hc := congrArg complexCoordinate hh
      rw [inv_complex] at hc
      have hneg : complexCoordinate (-a) = -complexCoordinate a := by
        dsimp only [complexCoordinate]
        simp only [PiLp.neg_apply, Complex.ofReal_neg]
        ring
      rw [hneg] at hc
      have he : Complex.I * 2 = 0 := by
        have hdw := den w hw
        field_simp (disch := first | assumption | exact Complex.I_ne_zero | positivity | norm_num) at hc
        linear_combination hc
      have hn : Complex.I * 2 ≠ 0 := mul_ne_zero Complex.I_ne_zero (by norm_num)
      exact hn he
  have unique_half (r : ℝ) (hr : 0 < r) : UniqueDiffOn ℝ (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc r) := by
    have hlin : IsLinearMap ℝ (fun x : E2 => x 1) := by
      constructor
      · intro x y; rfl
      · intro c x; rfl
    have hc : Convex ℝ (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc r) := (convex_closedBall (0 : E2) r).inter (convex_halfSpace_ge hlin 0)
    apply uniqueDiffOn_convex hc
    have ho : IsOpen (halfDisc r) := Metric.isOpen_ball.inter (isOpen_lt continuous_const (show Continuous (fun x : E2 => x 1) by fun_prop))
    have hsub : halfDisc r ⊆ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc r := fun x hx => ⟨Metric.ball_subset_closedBall hx.1, hx.2.le⟩
    let p : E2 := (r / 2) • coordinateVector 2 1
    have hp1 : p 1 = r / 2 := by
      dsimp only [p, coordinateVector]
      simp
    have hp : ‖p‖ = r / 2 := by
      dsimp only [p, coordinateVector]
      rw [norm_smul, EuclideanSpace.norm_single]
      simp [abs_of_pos hr]
    refine ⟨p, interior_maximal hsub ho ?_⟩
    constructor
    · change dist p 0 < r
      rw [dist_zero_right, hp]
      linarith
    · rw [hp1]
      exact half_pos hr
  have jacobian_facts :
      (∀ (f g : E2 → E2) (x : E2), DifferentiableAt ℝ f x → DifferentiableAt ℝ g (f x) →
        jacobian (fun y => g (f y)) x = jacobian g (f x) * jacobian f x) ∧
      (∀ (a z : E2), ‖a‖ = 1 → z ≠ -a → ∃ c : ℂ,
        c ≠ 0 ∧ jacobian (boundaryMobius a) z = !![c.re, -c.im; c.im, c.re]) := by
    have decomp (p : E2) : p = ∑ j : Fin 2, p j • coordinateVector 2 j := by
      ext i
      fin_cases i <;> simp only [Fin.sum_univ_two, PiLp.add_apply, PiLp.smul_apply]
      all_goals dsimp only [coordinateVector]
      all_goals norm_num
    constructor
    · intro f g x hf hg
      ext i j
      change (fderiv ℝ (fun y => g (f y)) x (coordinateVector 2 j)) i =
        ∑ k : Fin 2, (fderiv ℝ g (f x) (coordinateVector 2 k)) i * (fderiv ℝ f x (coordinateVector 2 j)) k
      rw [fderiv_fun_comp x hg hf]
      change (fderiv ℝ g (f x) (fderiv ℝ f x (coordinateVector 2 j))) i = _
      nth_rw 1 [decomp (fderiv ℝ f x (coordinateVector 2 j))]
      rw [map_sum]
      simp only [Fin.sum_univ_two, PiLp.add_apply, map_smul, PiLp.smul_apply, smul_eq_mul]
      ring
    · intro a z ha hz
      let e : E2 ≃L[ℝ] ℂ := ((EuclideanSpace.equiv (Fin 2) ℝ).trans
        (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)).trans Complex.equivRealProdCLM.symm
      have he (x : E2) : e x = complexCoordinate x := by
        apply Complex.ext <;> dsimp only [complexCoordinate]
        all_goals simp [e]
      have hei (w : ℂ) : e.symm w = realCoordinate w := by
        ext i
        fin_cases i <;> rfl
      have hd : (-e a) - e z ≠ 0 := by
        intro h
        have hz' : e z = e (-a) := by rw [map_neg]; linear_combination -h
        exact hz (e.injective hz')
      have ha0 : e a ≠ 0 := by
        intro h
        have : a = 0 := e.injective (by rw [h, map_zero])
        rw [this, norm_zero] at ha
        norm_num at ha
      let C : ℂ := (Complex.I * 1 * ((-e a) - e z) - (Complex.I * ((-e a) + e z)) * (-1)) /
        ((-e a) - e z) ^ 2
      have hC : C ≠ 0 := by
        dsimp only [C]
        apply div_ne_zero _ (pow_ne_zero 2 hd)
        have hh : Complex.I * 1 * ((-e a) - e z) - (Complex.I * ((-e a) + e z)) * (-1) = -2 * Complex.I * e a := by ring
        rw [hh]
        exact mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) ha0
      have hder := (((hasDerivAt_id (e z)).const_add (-e a)).const_mul Complex.I).div
          ((hasDerivAt_id (e z)).const_sub (-e a)) hd
      have hdreal := hder.hasFDerivAt.restrictScalars ℝ
      have hf := e.symm.hasFDerivAt.comp z (hdreal.comp z e.hasFDerivAt)
      have hfun : (fun x : E2 => e.symm (Complex.I * ((-e a) + e x) / ((-e a) - e x))) = boundaryMobius a := by
        funext x
        rw [hei, he a, he x]
        rfl
      change HasFDerivAt (fun x : E2 => e.symm (Complex.I * ((-e a) + e x) / ((-e a) - e x))) _ z at hf
      rw [hfun] at hf
      refine ⟨C, hC, ?_⟩
      ext i j
      change (fderiv ℝ (boundaryMobius a) z (coordinateVector 2 j)) i = _
      rw [hf.fderiv]
      fin_cases i <;> fin_cases j
      all_goals
        change (e.symm (e (coordinateVector 2 _) * C)) _ = _
        rw [hei, he]
        dsimp only [realCoordinate, complexCoordinate, coordinateVector]
        norm_num [Complex.mul_re, Complex.mul_im]
  have holder_facts (S : Set E2) (hs : IsCompact S) (α : ℝ≥0) (hα : 0 < α) :
      (∀ (f : E2 → ℝ) (C : ℝ≥0), (∀ x ∈ S, ∀ y ∈ S,
        dist (f x) (f y) ≤ C * dist x y ^ (α : ℝ)) → HolderOnWith C α f S) ∧
      (∀ (f g : E2 → ℝ), (∃ C, HolderOnWith C α f S) →
        (∃ C, HolderOnWith C α g S) → ∃ C, HolderOnWith C α (fun x => f x + g x) S) ∧
      (∀ (f g : E2 → ℝ), (∃ C, HolderOnWith C α f S) →
        (∃ C, HolderOnWith C α g S) → ∃ C, HolderOnWith C α (fun x => f x * g x) S) := by
    have ofdist (f : E2 → ℝ) (C : ℝ≥0) (h : ∀ x ∈ S, ∀ y ∈ S,
        dist (f x) (f y) ≤ C * dist x y ^ (α : ℝ)) : HolderOnWith C α f S := by
      intro x hx y hy
      rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,
        ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul C.coe_nonneg]
      exact ENNReal.ofReal_le_ofReal (h x hx y hy)
    refine ⟨ofdist, ?_, ?_⟩
    · intro f g hf hg
      obtain ⟨Cf, hf⟩ := hf
      obtain ⟨Cg, hg⟩ := hg
      refine ⟨Cf + Cg, ofdist _ _ ?_⟩
      intro x hx y hy
      have hsum := dist_add_add_le (f x) (g x) (f y) (g y)
      have hff := hf.dist_le hx hy
      have hgg := hg.dist_le hx hy
      change dist (f x + g x) (f y + g y) ≤ ((Cf : ℝ) + Cg) * dist x y ^ (α : ℝ)
      linarith
    · intro f g hf hg
      obtain ⟨Cf, hf⟩ := hf
      obtain ⟨Cg, hg⟩ := hg
      obtain ⟨Bf, hBf⟩ := hs.exists_bound_of_continuousOn (hf.continuousOn (by positivity))
      obtain ⟨Bg, hBg⟩ := hs.exists_bound_of_continuousOn (hg.continuousOn (by positivity))
      let bf : ℝ≥0 := ⟨max Bf 0, le_max_right _ _⟩
      let bg : ℝ≥0 := ⟨max Bg 0, le_max_right _ _⟩
      refine ⟨bf * Cg + bg * Cf, ofdist _ _ ?_⟩
      intro x hx y hy
      have h1 : |f x| ≤ (bf : ℝ) := by dsimp [bf]; exact (hBf x hx).trans (le_max_left _ _)
      have h2 : |g y| ≤ (bg : ℝ) := by dsimp [bg]; exact (hBg y hy).trans (le_max_left _ _)
      have hff := hf.dist_le hx hy
      have hgg := hg.dist_le hx hy
      have he : f x * g x - f y * g y = f x * (g x - g y) + g y * (f x - f y) := by ring
      rw [Real.dist_eq, he]
      calc
        |f x * (g x - g y) + g y * (f x - f y)| ≤ |f x * (g x - g y)| + |g y * (f x - f y)| := abs_add_le _ _
        _ = |f x| * dist (g x) (g y) + |g y| * dist (f x) (f y) := by rw [abs_mul, abs_mul, Real.dist_eq, Real.dist_eq]
        _ ≤ (bf : ℝ) * ((Cg : ℝ) * dist x y ^ (α : ℝ)) + (bg : ℝ) * ((Cf : ℝ) * dist x y ^ (α : ℝ)) := add_le_add
          (mul_le_mul h1 hgg dist_nonneg bf.coe_nonneg) (mul_le_mul h2 hff dist_nonneg bg.coe_nonneg)
        _ = ↑(bf * Cg + bg * Cf) * dist x y ^ (α : ℝ) := by push_cast; ring
  obtain ⟨jac_comp, mobius_jac⟩ := jacobian_facts
  obtain ⟨invM, hMleft, hMright, hMclosed, hMopen, hMflat, hMzero, hMsmooth, hMnopole⟩ :=
    inverse_mobius P.base base_norm
  let f (x : E2) : E2 := boundaryMobius P.base (X.inverse x)
  let h (z : E2) : E2 := X.forward (invM z)
  have hzero : h 0 = 0 := by
    change X.forward (invM 0) = 0
    rw [hMzero, X.forward_agrees P.base (Metric.sphere_subset_closedBall P.base_on_circle), P.base_image]
  have hclosure (z : E2) (hz : 0 ≤ z 1) : h z ∈ closure Ω.domain := by
    change X.forward (invM z) ∈ _
    rw [X.forward_agrees _ (hMclosed z hz), ← P.target_eq]
    exact P.tau.map_source (by rw [P.source_eq]; exact hMclosed z hz)
  have hsmooth (z : E2) (hz : 0 ≤ z 1) : ContDiffAt ℝ 1 h z := by
    have hf := (X.forward_C1 _ (X.forward_contains (hMclosed z hz))).contDiffAt
      (X.forward_open.mem_nhds (X.forward_contains (hMclosed z hz)))
    exact hf.comp z ((hMsmooth z hz).of_le (by simp))
  have fpos (x : E2) (hx : x ∈ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc r) : 0 ≤ (f x) 1 := by
    rcases eq_or_lt_of_le hx.2 with he | hp
    · exact le_of_eq (map_boundary x hx he.symm).symm
    · exact (map_interior x hx hp).le
  have hfleft (x : E2) (hx : x ∈ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc r) : h (f x) = x := by
    change X.forward (invM (boundaryMobius P.base (X.inverse x))) = x
    rw [actual_inverse_agrees x hx, hMleft _ (hr_tau_pole x hx)]
    have ht : x ∈ P.tau.target := by
      rw [P.target_eq]
      exact Ω.contains_closed_half_disc ⟨Metric.closedBall_subset_closedBall hr_local.le hx.1, hx.2⟩
    rw [X.forward_agrees _ (by rw [← P.source_eq]; exact P.tau.map_target ht), P.tau.right_inv ht]
  have hfright (z : E2) (hz : 0 ≤ z 1) : f (h z) = z := by
    change boundaryMobius P.base (X.inverse (h z)) = z
    rw [X.inverse_agrees _ (hclosure z hz)]
    change boundaryMobius P.base (P.tau.symm (X.forward (invM z))) = z
    rw [X.forward_agrees _ (hMclosed z hz), P.tau.left_inv (by rw [P.source_eq]; exact hMclosed z hz)]
    exact hMright z hz
  have hsmall : ∃ t : ℝ, 0 < t ∧ ∀ z ∈ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc t, h z ∈ disc r := by
    have hn := (hsmooth 0 (by simp)).continuousAt.preimage_mem_nhds
      (show disc r ∈ nhds (h 0) by rw [hzero]; exact Metric.ball_mem_nhds _ hr)
    obtain ⟨e, he, hemap⟩ := Metric.mem_nhds_iff.mp hn
    refine ⟨e / 2, half_pos he, ?_⟩
    intro z hz
    exact hemap (Metric.closedBall_subset_ball (by linarith) hz.1)
  obtain ⟨t, ht, htmap⟩ := hsmall
  have hhalf (z : E2) (hz : z ∈ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc t) : h z ∈ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc r :=
    ⟨Metric.ball_subset_closedBall (htmap z hz), (Ω.closure_inside (hclosure z hz.2)).2⟩
  have hinner (z : E2) (hz : z ∈ halfDisc t) : h z ∈ halfDisc r := by
    have hcl : z ∈ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc t := ⟨Metric.ball_subset_closedBall hz.1, hz.2.le⟩
    have hdom : h z ∈ Ω.domain := by
      change X.forward (invM z) ∈ _
      rw [X.forward_agrees _ (hMclosed z hz.2.le), ← P.interior_image]
      exact ⟨invM z, hMopen z hz.2, rfl⟩
    have hlocal : h z ∈ disc Ω.localR := Metric.ball_subset_ball hr_local.le (htmap z hcl)
    have hm : h z ∈ halfDisc Ω.localR := by rw [← Ω.inward_side]; exact ⟨hdom, hlocal⟩
    exact ⟨htmap z hcl, hm.2⟩
  have hflat (z : E2) (hz : z ∈ flatArc t) : h z ∈ flatArc r := by
    have hcl : z ∈ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc t := ⟨Metric.ball_subset_closedBall hz.1, le_of_eq hz.2.symm⟩
    have hfront : h z ∈ frontier Ω.domain := by
      change X.forward (invM z) ∈ _
      rw [X.forward_agrees _ (hMclosed z hcl.2), ← P.boundary_image]
      exact ⟨invM z, hMflat z hz.2, rfl⟩
    have hlocal : h z ∈ disc Ω.localR := Metric.ball_subset_ball hr_local.le (htmap z hcl)
    have hm : h z ∈ flatArc Ω.localR := by rw [← Ω.flat_subarc]; exact ⟨hfront, hlocal⟩
    exact ⟨htmap z hcl, hm.2⟩
  let chart : PartialHomeomorph E2 E2 := {
    toFun := f
    invFun := h
    source := SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc r
    target := f '' SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc r
    map_source' := fun x hx => ⟨x, hx, rfl⟩
    map_target' := by
      rintro z ⟨x, hx, rfl⟩
      rw [hfleft x hx]
      exact hx
    left_inv' := hfleft
    right_inv' := by
      rintro z ⟨x, hx, rfl⟩
      rw [hfleft x hx]
    continuousOn_toFun := fun x hx => (map_regular x hx.1).continuousAt.continuousWithinAt
    continuousOn_invFun := by
      rintro z ⟨x, hx, rfl⟩
      exact (hsmooth (f x) (fpos x hx)).continuousAt.continuousWithinAt }
  have htarget_contains : SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc t ⊆ chart.target := by
    intro z hz
    exact ⟨h z, hhalf z hz, hfright z hz.2⟩
  have hsource_compact : IsCompact (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc r) := by
    change IsCompact (Metric.closedBall (0 : E2) r ∩ {x : E2 | 0 ≤ x 1})
    exact (isCompact_closedBall (0 : E2) r).inter_right (isClosed_le continuous_const (show Continuous (fun x : E2 => x 1) by fun_prop))
  have hflip : ∃ C : ℝ≥0, LipschitzOnWith C f (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc r) := by
    apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hsource_compact
    intro x hx
    obtain ⟨C, U, hU, hLip⟩ := (map_regular x hx.1).exists_lipschitzOnWith
    exact ⟨C, U, mem_nhdsWithin_of_mem_nhds hU, hLip⟩
  have hhlip : ∃ C : ℝ≥0, LipschitzOnWith C h chart.target := by
    apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
      (hsource_compact.image_of_continuousOn chart.continuousOn)
    rintro z ⟨x, hx, rfl⟩
    obtain ⟨C, U, hU, hLip⟩ := (hsmooth (f x) (fpos x hx)).exists_lipschitzOnWith
    exact ⟨C, U, mem_nhdsWithin_of_mem_nhds hU, hLip⟩
  have hbilip : ∃ lo hi : ℝ, 0 < lo ∧ 0 < hi ∧
      ∀ x ∈ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc r, ∀ y ∈ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc r,
        lo * dist x y ≤ dist (chart x) (chart y) ∧ dist (chart x) (chart y) ≤ hi * dist x y := by
    obtain ⟨Cf, hfLip⟩ := hflip
    obtain ⟨Ch, hhLip⟩ := hhlip
    refine ⟨((Ch : ℝ) + 1)⁻¹, (Cf : ℝ) + 1, inv_pos.mpr (by positivity), by positivity, ?_⟩
    intro x hx y hy
    have hup := hfLip.dist_le_mul x hx y hy
    have hlo := hhLip.dist_le_mul (f x) (chart.map_source hx) (f y) (chart.map_source hy)
    rw [hfleft x hx, hfleft y hy] at hlo
    constructor
    · change ((Ch : ℝ) + 1)⁻¹ * dist x y ≤ dist (f x) (f y)
      rw [← div_eq_inv_mul, div_le_iff₀ (by positivity)]
      nlinarith [show 0 ≤ dist (f x) (f y) from dist_nonneg]
    · change dist (f x) (f y) ≤ ((Cf : ℝ) + 1) * dist x y
      nlinarith [show 0 ≤ dist x y from dist_nonneg]
  have jacobian_id_from_eqOn (u : E2 → E2) (R : ℝ) (hR : 0 < R)
      (heq : ∀ x ∈ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc R, u x = x) (x : E2)
      (hx : x ∈ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc R) (hd : DifferentiableAt ℝ u x) : jacobian u x = 1 := by
    have hu := (unique_half R hR) x hx
    have hid : HasFDerivWithinAt (id : E2 → E2) (fderiv ℝ u x) (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc R) x :=
      hd.hasFDerivAt.hasFDerivWithinAt.congr' (fun y hy => (heq y hy).symm) hx
    have hder : fderiv ℝ u x = ContinuousLinearMap.id ℝ E2 :=
      hu.eq hid (hasFDerivWithinAt_id x (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc R))
    ext i j
    change (fderiv ℝ u x (coordinateVector 2 j)) i = (1 : Mat2) i j
    rw [hder]
    fin_cases i <;> fin_cases j <;> norm_num [coordinateVector]
  have invM_det (z : E2) (hz : 0 ≤ z 1) : Matrix.det (jacobian invM z) ≠ 0 := by
    have hp := hMnopole z hz
    have hc := (mobius_smooth P.base (invM z) hp).contDiffAt
      (isOpen_compl_singleton.mem_nhds hp)
    have hi := (hMsmooth z hz).differentiableAt (by simp)
    have hd := hc.differentiableAt (by simp)
    have hh := jacobian_id_from_eqOn (fun w => boundaryMobius P.base (invM w))
      (‖z‖ + 1) (by positivity) (fun w hw => hMright w hw.2) z
      (by constructor; change dist z 0 ≤ ‖z‖ + 1; rw [dist_zero_right]; linarith; exact hz)
      (hd.comp z hi)
    rw [jac_comp invM (boundaryMobius P.base) z hi hd] at hh
    have hdet := congrArg Matrix.det hh
    rw [Matrix.det_mul, Matrix.det_one] at hdet
    intro hn
    rw [hn, mul_zero] at hdet
    norm_num at hdet
  have fdet (x : E2) (hx : x ∈ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc r) : Matrix.det (jacobian f x) ≠ 0 := by
    have hp := hr_pole x hx.1
    have hm := (mobius_smooth P.base (X.inverse x) hp).contDiffAt
      (isOpen_compl_singleton.mem_nhds hp)
    have hi := (X.inverse_C1 x (hr_neighborhood hx.1)).contDiffAt
      (X.inverse_open.mem_nhds (hr_neighborhood hx.1))
    change Matrix.det (jacobian (fun y => boundaryMobius P.base (X.inverse y)) x) ≠ 0
    rw [jac_comp X.inverse (boundaryMobius P.base) x (hi.differentiableAt (by norm_num))
      (hm.differentiableAt (by simp)), Matrix.det_mul]
    apply mul_ne_zero _ (X.inverse_det x (hr_neighborhood hx.1))
    obtain ⟨c, hc, he⟩ := mobius_jac P.base (X.inverse x) base_norm hp
    rw [he, Matrix.det_fin_two]
    change c.re * c.re - (-c.im) * c.im ≠ 0
    have hp := Complex.normSq_pos.mpr hc
    rw [Complex.normSq_apply] at hp
    nlinarith
  have hdet (z : E2) (hz : 0 ≤ z 1) : Matrix.det (jacobian h z) ≠ 0 := by
    have hi := (hMsmooth z hz).differentiableAt (by simp)
    have hf := (X.forward_C1 _ (X.forward_contains (hMclosed z hz))).contDiffAt
      (X.forward_open.mem_nhds (X.forward_contains (hMclosed z hz)))
    change Matrix.det (jacobian (fun w => X.forward (invM w)) z) ≠ 0
    rw [jac_comp invM X.forward z hi (hf.differentiableAt (by norm_num)), Matrix.det_mul]
    exact mul_ne_zero (X.forward_det _ (X.forward_contains (hMclosed z hz))) (invM_det z hz)
  have jets_inverse (x : E2) (hx : x ∈ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc r) :
      jacobian X.inverse x = (jacobianWithin P.tau (closedDisc 1) (P.tau.symm x))⁻¹ := by
    have hcl : x ∈ closure Ω.domain := Ω.contains_closed_half_disc
      ⟨Metric.closedBall_subset_closedBall hr_local.le hx.1, hx.2⟩
    have ht : x ∈ P.tau.target := by rw [P.target_eq]; exact hcl
    have hs : P.tau.symm x ∈ closedDisc 1 := by rw [← P.source_eq]; exact P.tau.map_target ht
    have hi := (X.inverse_C1 x (hr_neighborhood hx.1)).contDiffAt
      (X.inverse_open.mem_nhds (hr_neighborhood hx.1))
    have hf := (X.forward_C1 (X.inverse x) (by rw [actual_inverse_agrees x hx]; exact X.forward_contains hs)).contDiffAt
      (X.forward_open.mem_nhds (by rw [actual_inverse_agrees x hx]; exact X.forward_contains hs))
    have heq : ∀ y ∈ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc r, X.forward (X.inverse y) = y := by
      intro y hy
      have hyt : y ∈ P.tau.target := by
        rw [P.target_eq]
        exact Ω.contains_closed_half_disc ⟨Metric.closedBall_subset_closedBall hr_local.le hy.1, hy.2⟩
      rw [actual_inverse_agrees y hy, X.forward_agrees _ (by rw [← P.source_eq]; exact P.tau.map_target hyt), P.tau.right_inv hyt]
    have hm := jacobian_id_from_eqOn (fun y => X.forward (X.inverse y)) r hr heq x hx
      ((hf.differentiableAt (by norm_num)).comp x (hi.differentiableAt (by norm_num)))
    rw [jac_comp X.inverse X.forward x (hi.differentiableAt (by norm_num)) (hf.differentiableAt (by norm_num)),
      actual_inverse_agrees x hx, X.forward_jet _ hs] at hm
    have he := congrArg (fun M : Mat2 => (jacobianWithin P.tau (closedDisc 1) (P.tau.symm x))⁻¹ * M) hm
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (P.forward_det _ hs)), Matrix.one_mul, Matrix.mul_one] at he
    exact he
  have fmetric (x : E2) (hx : x ∈ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc r) : ∃ lam : ℝ,
      0 < lam ∧ (A x)⁻¹ = lam • ((jacobian f x).transpose * jacobian f x) := by
    have hp := hr_pole x hx.1
    have hm := (mobius_smooth P.base (X.inverse x) hp).contDiffAt
      (isOpen_compl_singleton.mem_nhds hp)
    have hi := (X.inverse_C1 x (hr_neighborhood hx.1)).contDiffAt
      (X.inverse_open.mem_nhds (hr_neighborhood hx.1))
    obtain ⟨c, hc, hj⟩ := mobius_jac P.base (X.inverse x) base_norm hp
    have hjf : jacobian f x = !![c.re, -c.im; c.im, c.re] * jacobian X.inverse x := by
      rw [jac_comp X.inverse (boundaryMobius P.base) x (hi.differentiableAt (by norm_num)) (hm.differentiableAt (by simp)), hj]
    have hgram : (!![c.re, -c.im; c.im, c.re] : Mat2).transpose * !![c.re, -c.im; c.im, c.re] = Complex.normSq c • (1 : Mat2) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.normSq_apply] <;> ring
    have hz : P.tau.symm x ∈ closedDisc 1 := by
      rw [← P.source_eq]
      apply P.tau.map_target
      rw [P.target_eq]
      exact Ω.contains_closed_half_disc ⟨Metric.closedBall_subset_closedBall hr_local.le hx.1, hx.2⟩
    refine ⟨P.lambda (P.tau.symm x) / Complex.normSq c,
      div_pos (P.lambda_pos _ hz) (Complex.normSq_pos.mpr hc), ?_⟩
    change inverseMetric A x = _
    rw [actual_metric_inverse x hx, ← jets_inverse x hx, hjf, Matrix.transpose_mul]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (!![c.re, -c.im; c.im, c.re] : Mat2).transpose, hgram]
    simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, smul_smul]
    rw [div_mul_cancel₀ _ (Complex.normSq_pos.mpr hc).ne']
  have compact_lipschitz {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (S : Set E2) (hS : IsCompact S) (u : E2 → V)
      (hu : ∀ x ∈ S, ContDiffAt ℝ 1 u x) : ∃ C : ℝ≥0, LipschitzOnWith C u S := by
    apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hS
    intro x hx
    obtain ⟨C, U, hU, hLip⟩ := (hu x hx).exists_lipschitzOnWith
    exact ⟨C, U, mem_nhdsWithin_of_mem_nhds hU, hLip⟩
  have half_compact (q : ℝ) : IsCompact (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc q) := by
    change IsCompact (Metric.closedBall (0 : E2) q ∩ {x : E2 | 0 ≤ x 1})
    exact (isCompact_closedBall (0 : E2) q).inter_right
      (isClosed_le continuous_const (show Continuous (fun x : E2 => x 1) by fun_prop))
  have smooth_jac (u : E2 → E2) (x : E2) (hu : ContDiffAt ℝ ∞ u x) (i j : Fin 2) :
      ContDiffAt ℝ 1 (fun y => jacobian u y i j) x := by
    have hd : ContDiffAt ℝ 1 (fun y => fderiv ℝ u y (coordinateVector 2 j)) x :=
      (hu.fderiv_right (by simp)).clm_apply contDiffAt_const
    exact (show ContDiff ℝ 1 (fun p : E2 => p i) by fun_prop).contDiffAt.comp x hd
  have lip_holder (q : ℝ) (hq : 0 < q) (u : E2 → ℝ)
      (hL : ∃ C, LipschitzOnWith C u (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc q)) :
      ∃ C, HolderOnWith C G.alpha u (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc q) := by
    obtain ⟨C, hC⟩ := hL
    let diam : ℝ≥0 := ⟨2 * q, by positivity⟩
    have hdiam : ∀ x ∈ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc q, ∀ y ∈ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc q, edist x y ≤ (diam : ℝ≥0∞) := by
      intro x hx y hy
      rw [edist_dist, ENNReal.ofReal_le_coe]
      change dist x y ≤ 2 * q
      have hx' : dist x 0 ≤ q := hx.1
      have hy' : dist y 0 ≤ q := hy.1
      have htri := dist_triangle_right x y (0 : E2)
      linarith
    exact ⟨_, HolderOnWith.of_le hdiam hC.holderOnWith G.alpha_lt_one.le⟩
  have inv_coeff_holder (i j : Fin 2) : ∃ C,
      HolderOnWith C G.alpha (fun x => jacobian X.inverse x i j) (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc r) := by
    obtain ⟨C, hC⟩ := P.inverse_holder i j
    refine ⟨C, ?_⟩
    intro x hx y hy
    have hxc := Ω.contains_closed_half_disc ⟨Metric.closedBall_subset_closedBall hr_local.le hx.1, hx.2⟩
    have hyc := Ω.contains_closed_half_disc ⟨Metric.closedBall_subset_closedBall hr_local.le hy.1, hy.2⟩
    change edist (jacobian X.inverse x i j) (jacobian X.inverse y i j) ≤ _
    rw [X.inverse_jet x hxc, X.inverse_jet y hyc]
    exact hC x hxc y hyc
  have mobius_coeff_holder (i j : Fin 2) : ∃ C,
      HolderOnWith C G.alpha (fun x => jacobian (boundaryMobius P.base) (X.inverse x) i j) (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc r) := by
    apply lip_holder r hr
    apply compact_lipschitz _ hsource_compact
    intro x hx
    have hp := hr_pole x hx.1
    have hm := (mobius_smooth P.base (X.inverse x) hp).contDiffAt
      (isOpen_compl_singleton.mem_nhds hp)
    have hi := (X.inverse_C1 x (hr_neighborhood hx.1)).contDiffAt
      (X.inverse_open.mem_nhds (hr_neighborhood hx.1))
    exact (smooth_jac _ _ hm i j).comp x hi
  have fjac (x : E2) (hx : x ∈ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc r) :
      jacobian f x = jacobian (boundaryMobius P.base) (X.inverse x) * jacobian X.inverse x := by
    have hp := hr_pole x hx.1
    have hm := (mobius_smooth P.base (X.inverse x) hp).contDiffAt
      (isOpen_compl_singleton.mem_nhds hp)
    have hi := (X.inverse_C1 x (hr_neighborhood hx.1)).contDiffAt
      (X.inverse_open.mem_nhds (hr_neighborhood hx.1))
    exact jac_comp _ _ _ (hi.differentiableAt (by norm_num)) (hm.differentiableAt (by simp))
  have fholder (i j : Fin 2) : ∃ C, HolderOnWith C G.alpha
      (fun x => jacobian f x i j) (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc r) := by
    obtain ⟨hofdist, hadd, hmul⟩ := holder_facts (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc r) hsource_compact G.alpha G.alpha_pos
    have h0 := hmul (fun x => jacobian (boundaryMobius P.base) (X.inverse x) i 0)
      (fun x => jacobian X.inverse x 0 j) (mobius_coeff_holder i 0) (inv_coeff_holder 0 j)
    have h1 := hmul (fun x => jacobian (boundaryMobius P.base) (X.inverse x) i 1)
      (fun x => jacobian X.inverse x 1 j) (mobius_coeff_holder i 1) (inv_coeff_holder 1 j)
    obtain ⟨C, hC⟩ := hadd _ _ h0 h1
    refine ⟨C, ?_⟩
    intro x hx y hy
    change edist (jacobian f x i j) (jacobian f y i j) ≤ _
    rw [fjac x hx, fjac y hy]
    simpa only [Matrix.mul_apply, Fin.sum_univ_two] using hC x hx y hy
  have invMlip : ∃ C : ℝ≥0, LipschitzOnWith C invM (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc t) :=
    compact_lipschitz _ (half_compact t) invM (fun x hx => (hMsmooth x hx.2).of_le (by simp))
  have forward_coeff_holder (i j : Fin 2) : ∃ C,
      HolderOnWith C G.alpha (fun z => jacobian X.forward (invM z) i j) (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc t) := by
    obtain ⟨C, hC⟩ := P.forward_holder i j
    obtain ⟨L, hL⟩ := invMlip
    have hcomp := hC.comp hL.holderOnWith (show MapsTo invM (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc t) (closedDisc 1) from fun z hz => hMclosed z hz.2)
    rw [mul_one] at hcomp
    refine ⟨C * L ^ (G.alpha : ℝ), ?_⟩
    intro x hx y hy
    change edist (jacobian X.forward (invM x) i j) (jacobian X.forward (invM y) i j) ≤ _
    rw [X.forward_jet _ (hMclosed x hx.2), X.forward_jet _ (hMclosed y hy.2)]
    exact hcomp x hx y hy
  have invM_coeff_holder (i j : Fin 2) : ∃ C,
      HolderOnWith C G.alpha (fun z => jacobian invM z i j) (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc t) := by
    apply lip_holder t ht
    exact compact_lipschitz _ (half_compact t) _ (fun z hz => smooth_jac invM z (hMsmooth z hz.2) i j)
  have hjac (z : E2) (hz : 0 ≤ z 1) :
      jacobian h z = jacobian X.forward (invM z) * jacobian invM z := by
    have hi := (hMsmooth z hz).differentiableAt (by simp)
    have hf := (X.forward_C1 _ (X.forward_contains (hMclosed z hz))).contDiffAt
      (X.forward_open.mem_nhds (X.forward_contains (hMclosed z hz)))
    exact jac_comp _ _ _ hi (hf.differentiableAt (by norm_num))
  have hholder (i j : Fin 2) : ∃ C, HolderOnWith C G.alpha
      (fun z => jacobian h z i j) (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc t) := by
    obtain ⟨hofdist, hadd, hmul⟩ := holder_facts (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc t) (half_compact t) G.alpha G.alpha_pos
    have h0 := hmul (fun z => jacobian X.forward (invM z) i 0)
      (fun z => jacobian invM z 0 j) (forward_coeff_holder i 0) (invM_coeff_holder 0 j)
    have h1 := hmul (fun z => jacobian X.forward (invM z) i 1)
      (fun z => jacobian invM z 1 j) (forward_coeff_holder i 1) (invM_coeff_holder 1 j)
    obtain ⟨C, hC⟩ := hadd _ _ h0 h1
    refine ⟨C, ?_⟩
    intro x hx y hy
    change edist (jacobian h x i j) (jacobian h y i j) ≤ _
    rw [hjac x hx.2, hjac y hy.2]
    simpa only [Matrix.mul_apply, Fin.sum_univ_two] using hC x hx y hy
  have chart_construction : ∃ F : BoundaryIsothermalPatchV480 R A,
      F.sourceR ≤ r ∧
      (∀ x ∈ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc F.sourceR, F.chart x = boundaryMobius P.base (P.tau.symm x)) ∧
      (∀ x ∈ F.chart.source, F.chart x = boundaryMobius P.base (X.inverse x)) := by
    let F : BoundaryIsothermalPatchV480 R A := {
      sourceR := r
      sourceR_pos := hr
      sourceR_inside := hr_inside
      targetR := t
      targetR_pos := ht
      chart := chart
      source_contains := Subset.rfl
      target_contains := htarget_contains
      base := map_base
      forward_C1 := fun x hx => (map_regular x hx.1).contDiffWithinAt
      inverse_C1 := by
        rintro z ⟨x, hx, rfl⟩
        exact (hsmooth (f x) (fpos x hx)).contDiffWithinAt
      forward_det := fdet
      inverse_det := by
        rintro z ⟨x, hx, rfl⟩
        exact hdet (f x) (fpos x hx)
      alpha := G.alpha
      alpha_pos := G.alpha_pos
      alpha_lt_one := G.alpha_lt_one
      forward_holder := fholder
      inverse_holder := hholder
      forward_boundary := map_boundary_iff
      forward_interior := fun x hx => map_interior x ⟨Metric.ball_subset_closedBall hx.1, hx.2.le⟩ hx.2
      inverse_half_disc := hhalf
      inverse_interior := hinner
      inverse_flat := hflat
      biLipschitz := hbilip
      conformalInverseMetric := fmetric }
    refine ⟨F, le_rfl, ?_, ?_⟩
    · intro x hx
      change boundaryMobius P.base (X.inverse x) = boundaryMobius P.base (P.tau.symm x)
      rw [actual_inverse_agrees x hx]
    · intro x hx
      rfl
  obtain ⟨F, hFr, hFactual, hFextension⟩ := chart_construction
  refine ⟨F, hFr.trans_lt hr_local, hFactual, hFextension, ?_⟩
  intro x hx
  apply hr_tau_pole x
  exact ⟨Metric.closedBall_subset_closedBall hFr (Metric.ball_subset_closedBall hx.1),
    le_of_eq hx.2.symm⟩


end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3BoundaryNormalizedWindowV480 -/

noncomputable section
open Set Topology Function Filter MeasureTheory
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
set_option maxHeartbeats 600000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- Coefficients and actual quotient in centered boundary coordinates.
The normal coordinate is 1. Smoothness holds across the flat edge; the
classical and weak equations hold on the positive half-disc. -/
structure BoundaryNormalizedWindowV480 where
  R : ℝ
  R_pos : 0 < R
  O : Set E2
  O_open : IsOpen O
  contains : SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc R ⊆ O
  A : E2 → Mat2
  B : E2 → E2
  v : E2 → ℝ
  smooth_v : ContDiffOn ℝ ∞ v O
  elliptic : SmoothEllipticOn A B (fun _ => 0) O
  det_one : ∀ x ∈ O, Matrix.det (A x) = 1
  lipschitz : ∀ i j, LipschitzBoundOn (fun x => A x i j)
    (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc R)
  B_bounded : BoundedOn B (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc R)
  classical : ∀ x ∈ halfDisc R, classicalL A B (fun _ => 0) v x = 0
  flat : ∀ x ∈ flatArc R, v x = 0

/-- Exact centering and normal/tangent swap of the constructed actual
boundary normalization; the returned function is the SAME height quotient. -/
theorem boundary_normalized_window_v480 (N : BoundaryNormalizationDataV480)
    (z : E2) (hz : z ∈ N.O) (hz0 : z 0 = 0)
    (hflat : ∀ x ∈ N.O, x 0 = 0 → N.v x = 0) :
    ∃ W : BoundaryNormalizedWindowV480,
      W.v = (fun y => N.v (coordinateSwap y+z)) ∧
      W.O ⊆ (fun y => coordinateSwap y+z) ⁻¹' N.O := by
  obtain ⟨ε,hε,hK⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (N.isOpen_O.mem_nhds hz)
  let K : Set E2 := Metric.closedBall z ε
  obtain ⟨hEll,hLip,hB,hDet,hfactor⟩ := native_interior_normalized_coefficients_v475
    N.coefficientData K (isCompact_closedBall z ε) (convex_closedBall z ε)
    ⟨z,Metric.mem_closedBall_self hε.le⟩ hK
  let V : Set E2 := Metric.ball z ε
  have hVK : V ⊆ K := Metric.ball_subset_closedBall
  have hVO : V ⊆ N.O := hVK.trans hK
  have hv : ContDiffOn ℝ ∞ N.v V :=
    (N.smooth_u.mono hVO).div (N.smooth_h.mono hVO)
      (fun x hx => (N.h_positive x (hVO hx)).ne')
  let τ : E2 → E2 := fun y => y+z
  let Vτ : Set E2 := τ ⁻¹' V
  have hτ : ContDiff ℝ ∞ τ := contDiff_id.add contDiff_const
  let aτ : E2 → Mat2 := fun y => N.normalizedA (τ y)
  let bτ : E2 → E2 := fun y => N.normalizedB (τ y)
  let vτ : E2 → ℝ := fun y => N.v (τ y)
  have hEllτ : SmoothEllipticOn aτ bτ (fun _ => 0) Vτ := by
    obtain ⟨ha,hb,hc,hsym,ell,A,hell,hA,hbounds⟩ := hEll
    exact ⟨fun i j => ((ha i j).mono hVK).comp hτ.contDiffOn (fun _ hy => hy),
      (hb.mono hVK).comp hτ.contDiffOn (fun _ hy => hy),contDiffOn_const,
      fun y hy i j => hsym _ (hVK hy) i j,ell,A,hell,hA,
      fun y hy p => hbounds _ (hVK hy) p⟩
  let O : Set E2 := coordinateSwap ⁻¹' Vτ
  let R : ℝ := ε/2
  have hR : 0 < R := half_pos hε
  have hcontains : SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc R ⊆ O := by
    intro y hy
    change coordinateSwap y+z ∈ Metric.ball z ε
    rw [Metric.mem_ball,dist_eq_norm,add_sub_cancel_right,coordinateSwap.norm_map]
    have hh : ‖y‖ ≤ R := by simpa only [closedDisc,Metric.mem_closedBall,dist_zero_right] using hy.1
    exact lt_of_le_of_lt hh (by dsimp [R]; linarith)
  let A : E2 → Mat2 := boundarySwapLeadingV480 aτ
  let B : E2 → E2 := boundarySwapDriftV480 bτ
  let v : E2 → ℝ := fun y => vτ (coordinateSwap y)
  have hEllS : SmoothEllipticOn A B (fun _ => 0) O :=
    boundary_smooth_elliptic_swap_v480 Vτ aτ bτ (fun _ => 0) hEllτ
  have hO : IsOpen O := (Metric.isOpen_ball.preimage hτ.continuous).preimage coordinateSwap.continuous
  have hvS : ContDiffOn ℝ ∞ v O :=
    (hv.comp hτ.contDiffOn (fun _ hx => hx)).comp coordinateSwap.contDiff.contDiffOn (fun _ hx => hx)
  have hDetS (y : E2) (hy : y ∈ O) : Matrix.det (A y) = 1 := by
    have hh := hDet (coordinateSwap y+z) (hVK hy)
    change Matrix.det (N.normalizedA (coordinateSwap y+z)) = 1 at hh
    change Matrix.det (fun i j => N.normalizedA (coordinateSwap y+z)
      (Equiv.swap (0 : Fin 2) 1 i) (Equiv.swap (0 : Fin 2) 1 j)) = 1
    simp only [Matrix.det_fin_two,Equiv.swap_apply_left,Equiv.swap_apply_right]
    simpa only [Matrix.det_fin_two,mul_comm] using hh
  have hcompact : IsCompact (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc R) :=
    (isCompact_closedBall _ _).inter_right
      (isClosed_le continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous)
  have hconvex : Convex ℝ (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc R) :=
    (convex_closedBall (0 : E2) R).inter
      (convex_halfSpace_ge (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).toLinearMap.isLinear (0 : ℝ))
  have hLipS : ∀ i j, LipschitzBoundOn (fun y => A y i j)
      (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc R) := by
    intro i j
    obtain ⟨L,hL⟩ := ((hEllS.1 i j).mono hcontains).exists_lipschitzOnWith
      (by simp) hconvex hcompact
    exact ⟨L,L.coe_nonneg,fun x hx y hy => hL.dist_le_mul x hx y hy⟩
  obtain ⟨CB,hCB⟩ := hcompact.exists_bound_of_continuousOn
    (hEllS.2.1.continuousOn.mono hcontains)
  have hclass (y : E2) (hy : y ∈ halfDisc R) : classicalL A B (fun _ => 0) v y = 0 := by
    have hyO := hcontains ⟨Metric.ball_subset_closedBall hy.1,hy.2.le⟩
    have hs := boundary_classical_swap_v480 Vτ (Metric.isOpen_ball.preimage hτ.continuous)
      aτ bτ (fun _ => 0) vτ hEllτ.1
      (hv.comp hτ.contDiffOn (fun _ hx => hx)) y hyO
    have ht := native_classical_translate_v475 V Metric.isOpen_ball N.normalizedA
      N.normalizedB (fun _ => 0) N.v (fun i j => (hEll.1 i j).mono hVK) hv z
      (coordinateSwap y) hyO
    change classicalL A B (fun _ => 0) v y = _ at hs
    rw [hs,ht]
    exact boundary_normalized_classical_v480 N _ (hVO hyO)
      (by simpa only [PiLp.add_apply,coordinateSwap_zero,hz0,add_zero] using hy.2)
  refine ⟨{
    R := R,R_pos := hR,O := O,O_open := hO,contains := hcontains,
    A := A,B := B,v := v,smooth_v := hvS,elliptic := hEllS,det_one := hDetS,
    lipschitz := hLipS,
    B_bounded := ⟨max CB 0,le_max_right _ _,fun y hy => (hCB y hy).trans (le_max_left _ _)⟩,
    classical := hclass,
    flat := by
      intro y hy
      exact hflat _ (hVO (hcontains ⟨Metric.ball_subset_closedBall hy.1,hy.2.ge⟩))
        (by change (coordinateSwap y+z) 0 = 0
            simp only [PiLp.add_apply,coordinateSwap_zero,hz0,hy.2,add_zero]) },rfl,?_⟩
  exact fun y hy => hVO hy

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3BoundaryDensityTransportV480 -/

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.OriginalEndpoints.B1Tangency.WeakTransport
set_option maxHeartbeats 600000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def boundaryTransportSourceV480 {R : ℝ} {A : E2 → Mat2}
    (F : BoundaryIsothermalPatchV480 R A) : Set E2 :=
  {x ∈ halfDisc F.sourceR | x ∈ F.chart.source ∧ F.chart x ∈ halfDisc F.targetR}
def boundaryPullbackTestV480 {R : ℝ} {A : E2 → Mat2}
    (F : BoundaryIsothermalPatchV480 R A) (φ : E2 → ℝ) (x : E2) : ℝ :=
  @ite ℝ (x ∈ boundaryTransportSourceV480 F) (Classical.propDecidable _) (φ (F.chart x)) 0
def boundaryVhatV480 {R : ℝ} {A : E2 → Mat2}
    (F : BoundaryIsothermalPatchV480 R A) (v : E2 → ℝ) (z : E2) : ℝ := v (F.chart.symm z)
def boundaryBhatV480 {R : ℝ} {A : E2 → Mat2}
    (F : BoundaryIsothermalPatchV480 R A) (b : E2 → E2) (z : E2) : E2 :=
  densityDrift b F.chart (F.chart.symm z)

theorem boundary_chart_first_jets_H1_v480 (W : BoundaryNormalizedWindowV480)
    (F : BoundaryIsothermalPatchV480 W.R W.A) :
    (∃ U : Set E2, IsOpen U ∧ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc F.sourceR ⊆ U ∧
      ContDiffOn ℝ ∞ W.v U) ∧
    BoundedOn W.v (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc F.sourceR) ∧
    BoundedOn (planarGradient W.v) (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc F.sourceR) ∧
    (∀ x ∈ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc F.sourceR, DifferentiableAt ℝ F.chart x) ∧
    (∀ z ∈ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc F.targetR, DifferentiableAt ℝ F.chart.symm z) ∧
    (∀ z ∈ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc F.targetR, DifferentiableAt ℝ (boundaryVhatV480 F W.v) z) ∧
    (∀ z ∈ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc F.targetR,
      planarGradient (boundaryVhatV480 F W.v) z = matrixAction (jacobian F.chart.symm z).transpose
        (planarGradient W.v (F.chart.symm z))) ∧
    ContinuousOn (boundaryVhatV480 F W.v) (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc F.targetR) ∧
    ContinuousOn (planarGradient (boundaryVhatV480 F W.v)) (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc F.targetR) ∧
    BoundedOn (boundaryVhatV480 F W.v) (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc F.targetR) ∧
    BoundedOn (planarGradient (boundaryVhatV480 F W.v)) (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc F.targetR) ∧
    H1On (halfDisc F.targetR) (boundaryVhatV480 F W.v) (planarGradient (boundaryVhatV480 F W.v)) := by
  classical
  have hsub (a b : ℝ) (hab : a ≤ b) : SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc a ⊆ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc b := by
    intro x hx
    exact ⟨Metric.closedBall_subset_closedBall hab hx.1, hx.2⟩
  have hhalf (r : ℝ) : halfDisc r ⊆ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc r := by
    intro x hx
    exact ⟨Metric.ball_subset_closedBall hx.1, hx.2.le⟩
  have hcompact (r : ℝ) : IsCompact (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc r) := by
    change IsCompact (Metric.closedBall (0 : E2) r ∩ {x : E2 | 0 ≤ x 1})
    exact (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const (by fun_prop))
  have hsource : SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc F.sourceR ⊆ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc W.R :=
    hsub _ _ F.sourceR_inside.le
  let U : Set E2 := W.O
  have hU : IsOpen U := W.O_open
  have hcontains : SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc F.sourceR ⊆ U := hsource.trans W.contains
  have hv : ContDiffOn ℝ ∞ W.v U := W.smooth_v
  have hvdiff (x : E2) (hx : x ∈ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc F.sourceR) : DifferentiableAt ℝ W.v x :=
    ((hv x (hcontains hx)).contDiffAt (hU.mem_nhds (hcontains hx))).differentiableAt (by simp)
  have hvc : ContinuousOn W.v (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc F.sourceR) := hv.continuousOn.mono hcontains
  have hgradU : ContinuousOn (planarGradient W.v) U := by
    have hdu := hv.continuousOn_fderiv_of_isOpen hU (by simp)
    unfold planarGradient
    apply continuousOn_finsetSum
    intro i hi
    exact (hdu.clm_apply continuousOn_const).smul continuousOn_const
  have hgrad : ContinuousOn (planarGradient W.v) (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc F.sourceR) :=
    hgradU.mono hcontains
  have hbound {V : Type} [NormedAddCommGroup V] (u : E2 → V) (r : ℝ)
      (hc : ContinuousOn u (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc r)) : BoundedOn u (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc r) := by
    obtain ⟨C, hC⟩ := (hcompact r).exists_bound_of_continuousOn hc
    exact ⟨max C 0, le_max_right _ _, fun x hx => (hC x hx).trans (le_max_left _ _)⟩
  have hdifferentiable (f : E2 → E2) (x : E2) (hdet : Matrix.det (jacobian f x) ≠ 0) :
      DifferentiableAt ℝ f x := by
    by_contra hh
    have hz : fderiv ℝ f x = 0 := fderiv_zero_of_not_differentiableAt hh
    apply hdet
    change Matrix.det (fun i j : Fin 2 => (fderiv ℝ f x (coordinateVector 2 j)) i) = 0
    rw [hz]
    change Matrix.det (0 : Mat2) = 0
    exact Matrix.det_zero
  have hforward (x : E2) (hx : x ∈ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc F.sourceR) :
      DifferentiableAt ℝ F.chart x :=
    hdifferentiable F.chart x (F.forward_det x (F.source_contains hx))
  have hinverse (z : E2) (hz : z ∈ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc F.targetR) :
      DifferentiableAt ℝ F.chart.symm z :=
    hdifferentiable F.chart.symm z (F.inverse_det z (F.target_contains hz))
  have hvhat (z : E2) (hz : z ∈ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc F.targetR) :
      DifferentiableAt ℝ (boundaryVhatV480 F W.v) z :=
    (hvdiff _ (F.inverse_half_disc z hz)).comp z (hinverse z hz)
  have hgradcoord (u : E2 → ℝ) (x : E2) (i : Fin 2) :
      planarGradient u x i = fderiv ℝ u x (coordinateVector 2 i) := by
    fin_cases i <;> simp [planarGradient, coordinateVector, Fin.sum_univ_two]
  have hgradchain (z : E2) (hz : z ∈ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc F.targetR) :
      planarGradient (boundaryVhatV480 F W.v) z = matrixAction (jacobian F.chart.symm z).transpose
        (planarGradient W.v (F.chart.symm z)) := by
    ext i
    rw [hgradcoord]
    change fderiv ℝ (W.v ∘ F.chart.symm) z (coordinateVector 2 i) = _
    rw [fderiv_comp z (hvdiff _ (F.inverse_half_disc z hz)) (hinverse z hz)]
    change fderiv ℝ W.v (F.chart.symm z) (fderiv ℝ F.chart.symm z (coordinateVector 2 i)) = _
    have hexp (w : E2) : w = ∑ j : Fin 2, w j • coordinateVector 2 j := by
      ext j
      fin_cases j <;> simp [coordinateVector, Fin.sum_univ_two]
    rw [hexp (fderiv ℝ F.chart.symm z (coordinateVector 2 i)), map_sum]
    simp only [map_smul, smul_eq_mul]
    change (∑ j : Fin 2, (fderiv ℝ F.chart.symm z (coordinateVector 2 i)) j *
      fderiv ℝ W.v (F.chart.symm z) (coordinateVector 2 j)) =
      ∑ j : Fin 2, (fderiv ℝ F.chart.symm z (coordinateVector 2 i)) j *
        planarGradient W.v (F.chart.symm z) j
    simp only [hgradcoord]
  have hinc : ContinuousOn F.chart.symm (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc F.targetR) :=
    F.inverse_C1.continuousOn.mono F.target_contains
  have hvhatc : ContinuousOn (boundaryVhatV480 F W.v) (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc F.targetR) :=
    hvc.comp hinc F.inverse_half_disc
  have hgradcomp : ContinuousOn (fun z => planarGradient W.v (F.chart.symm z))
      (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc F.targetR) := hgrad.comp hinc F.inverse_half_disc
  have hjac (i j : Fin 2) : ContinuousOn (fun z => jacobian F.chart.symm z i j)
      (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc F.targetR) := by
    obtain ⟨C, hC⟩ := F.inverse_holder i j
    exact hC.continuousOn F.alpha_pos
  have hgradchat : ContinuousOn (planarGradient (boundaryVhatV480 F W.v)) (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc F.targetR) := by
    have hm : ContinuousOn (fun z => matrixAction (jacobian F.chart.symm z).transpose
        (planarGradient W.v (F.chart.symm z))) (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc F.targetR) := by
      change ContinuousOn (fun z => (EuclideanSpace.equiv (Fin 2) ℝ).symm
        (fun i => ∑ j, (jacobian F.chart.symm z).transpose i j *
          planarGradient W.v (F.chart.symm z) j)) _
      apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp_continuousOn
      apply continuousOn_pi.mpr
      intro i
      apply continuousOn_finsetSum
      intro j hj
      exact (hjac j i).mul ((show Continuous (fun x : E2 => x j) from by fun_prop).comp_continuousOn hgradcomp)
    exact hm.congr (fun z hz => hgradchain z hz)
  refine ⟨⟨U, hU, hcontains, hv⟩, hbound _ _ hvc, hbound _ _ hgrad,
    hforward, hinverse, hvhat, hgradchain, hvhatc, hgradchat,
    hbound _ _ hvhatc, hbound _ _ hgradchat, ?_⟩
  have hopen : IsOpen (halfDisc F.targetR) := by
    change IsOpen (Metric.ball (0 : E2) F.targetR ∩ {x : E2 | 0 < x 1})
    exact Metric.isOpen_ball.inter (isOpen_lt continuous_const (by fun_prop))
  have huc := hvhatc.mono (hhalf F.targetR)
  have hgc := hgradchat.mono (hhalf F.targetR)
  have hweak : WeakGradientOn (halfDisc F.targetR) (boundaryVhatV480 F W.v) (planarGradient (boundaryVhatV480 F W.v)) := by
    refine ⟨huc.locallyIntegrableOn hopen.measurableSet,
      hgc.locallyIntegrableOn hopen.measurableSet, ?_⟩
    intro φ hφ hc hs i
    have hpartial : ContinuousOn (fun x => fderiv ℝ (boundaryVhatV480 F W.v) x (coordinateVector 2 i))
        (halfDisc F.targetR) := by
      exact ((show Continuous (fun x : E2 => x i) from by fun_prop).comp_continuousOn hgc).congr
        (fun x hx => (hgradcoord (boundaryVhatV480 F W.v) x i).symm)
    have integral_product (f ψ : E2 → ℝ) (hf : ContinuousOn f (halfDisc F.targetR))
        (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
        (hψs : tsupport ψ ⊆ halfDisc F.targetR) : Integrable (fun x => f x * ψ x) := by
      apply (integrableOn_iff_integrable_of_support_subset ?_).mp
        (((hf.mono hψs).mul hψ.continuousOn).integrableOn_compact hψc)
      intro x hx
      exact subset_tsupport ψ ((mul_ne_zero_iff.mp hx).2)
    have hi1 : Integrable (fun x => fderiv ℝ (boundaryVhatV480 F W.v) x (coordinateVector 2 i) * φ x) :=
      integral_product _ _ hpartial hφ.continuous hc hs
    have hi2 : Integrable (fun x => (boundaryVhatV480 F W.v) x * fderiv ℝ φ x (coordinateVector 2 i)) :=
      integral_product _ _ huc ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
        (hc.fderiv_apply ℝ _) ((tsupport_fderiv_apply_subset ℝ _).trans hs)
    have hi3 : Integrable (fun x => (boundaryVhatV480 F W.v) x * φ x) :=
      integral_product _ _ huc hφ.continuous hc hs
    have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hi1 hi2 hi3
      (fun x hx => hvhat x (hhalf _ (hs hx)))
      (fun x _ => hφ.differentiable (by simp) x)
    simp_rw [hgradcoord]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero,
      setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact hibp
    · intro x hx
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), mul_zero]
    · intro x hx
      rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (hs h))]
      simp
  have hfinite : volume (halfDisc F.targetR) < ⊤ :=
    lt_of_le_of_lt (measure_mono (hhalf _)) (hcompact F.targetR).measure_lt_top
  letI : IsFiniteMeasure (volume.restrict (halfDisc F.targetR)) :=
    isFiniteMeasure_restrict.mpr hfinite.ne
  refine ⟨hweak, ?_, ?_⟩
  · obtain ⟨C, hC, hboundC⟩ := hbound _ _ hvhatc
    exact MemLp.of_bound (huc.aestronglyMeasurable hopen.measurableSet) C
      ((ae_restrict_mem hopen.measurableSet).mono (fun x hx => hboundC x (hhalf _ hx)))
  · obtain ⟨C, hC, hboundC⟩ := hbound _ _ hgradchat
    exact MemLp.of_bound (hgc.aestronglyMeasurable hopen.measurableSet) C
      ((ae_restrict_mem hopen.measurableSet).mono (fun x hx => hboundC x (hhalf _ hx)))



theorem boundary_density_test_transport_v480 (W : BoundaryNormalizedWindowV480)
    (F : BoundaryIsothermalPatchV480 W.R W.A)
    (heq : WeakLinearEquationOn (halfDisc (W.R)) W.A W.B
      (fun _ => 0) W.v (planarGradient W.v))
    (helliptic : SmoothEllipticOn W.A W.B (fun _ => 0)
      (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc (W.R)))
    (hb : BoundedOn W.B (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc (W.R)))
    (hdet : ∀ x ∈ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc (W.R), Matrix.det (W.A x) = 1)
    (htrace : ∀ x ∈ flatArc (W.R), W.v x = 0) :
    MeasurableSet (boundaryTransportSourceV480 F) ∧
    F.chart '' boundaryTransportSourceV480 F = halfDisc F.targetR ∧
    (∀ z ∈ halfDisc F.targetR,
      jacobian F.chart (F.chart.symm z) * jacobian F.chart.symm z = 1 ∧
      jacobian F.chart.symm z * jacobian F.chart (F.chart.symm z) = 1 ∧
      planarGradient W.v (F.chart.symm z) =
        matrixAction (jacobian F.chart (F.chart.symm z)).transpose (planarGradient (boundaryVhatV480 F W.v) z)) ∧
    (∀ x ∈ boundaryTransportSourceV480 F,
      (fderiv ℝ F.chart x).toLinearMap.det = Matrix.det (jacobian F.chart x)) ∧
    (∀ φ : E2 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ halfDisc F.targetR →
      ContDiff ℝ 1 (boundaryPullbackTestV480 F φ) ∧ HasCompactSupport (boundaryPullbackTestV480 F φ) ∧
      tsupport (boundaryPullbackTestV480 F φ) ⊆ halfDisc F.sourceR ∧
      (∀ x ∈ boundaryTransportSourceV480 F,
        planarGradient (boundaryPullbackTestV480 F φ) x =
          matrixAction (jacobian F.chart x).transpose (planarGradient φ (F.chart x))) ∧
      IntegrableOn (weakIntegrand W.A W.B (fun _ => 0) W.v
        (planarGradient W.v) (boundaryPullbackTestV480 F φ)) (halfDisc (W.R)) ∧
      IntegrableOn (weakIntegrand
        (fun z => densityLeading W.A F.chart (F.chart.symm z)) (boundaryBhatV480 F W.B)
        (fun _ => 0) (boundaryVhatV480 F W.v) (planarGradient (boundaryVhatV480 F W.v)) φ) (halfDisc F.targetR) ∧
      (∫ x in halfDisc (W.R), weakIntegrand W.A W.B
        (fun _ => 0) W.v (planarGradient W.v) (boundaryPullbackTestV480 F φ) x) =
      (∫ z in halfDisc F.targetR, weakIntegrand
        (fun z => densityLeading W.A F.chart (F.chart.symm z)) (boundaryBhatV480 F W.B)
        (fun _ => 0) (boundaryVhatV480 F W.v) (planarGradient (boundaryVhatV480 F W.v)) φ z)) ∧
    (∀ z ∈ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc F.targetR,
      densityLeading W.A F.chart (F.chart.symm z) = 1) ∧
    ContinuousOn (boundaryBhatV480 F W.B) (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc F.targetR) ∧
    BoundedOn (boundaryBhatV480 F W.B) (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc F.targetR) ∧
    MemLp (boundaryBhatV480 F W.B) ⊤ (volume.restrict (halfDisc F.targetR)) ∧
    (∀ z ∈ flatArc F.targetR, (boundaryVhatV480 F W.v) z = 0) ∧
    WeakLinearEquationOn (halfDisc F.targetR) (fun _ => 1) (boundaryBhatV480 F W.B) (fun _ => 0)
      (boundaryVhatV480 F W.v) (planarGradient (boundaryVhatV480 F W.v)) := by
  classical
  have hhc (r : ℝ) : halfDisc r ⊆ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc r := by
    intro x hx
    exact ⟨Metric.mem_closedBall.mpr (Metric.mem_ball.mp hx.1).le, hx.2.le⟩
  have hop (r : ℝ) : IsOpen (halfDisc r) :=
    Metric.isOpen_ball.inter (isOpen_lt continuous_const (EuclideanSpace.proj (1 : Fin 2)).continuous)
  have hsrc : halfDisc F.sourceR ⊆ F.chart.source :=
    (hhc F.sourceR).trans F.source_contains
  have htgt : halfDisc F.targetR ⊆ F.chart.target :=
    (hhc F.targetR).trans F.target_contains
  have heqsrc : boundaryTransportSourceV480 F = halfDisc F.sourceR ∩ F.chart ⁻¹' halfDisc F.targetR := by
    ext x
    exact ⟨fun hx => ⟨hx.1, hx.2.2⟩, fun hx => ⟨hx.1, hsrc hx.1, hx.2⟩⟩
  have hopen : IsOpen (boundaryTransportSourceV480 F) := by
    rw [heqsrc]
    exact (F.chart.continuousOn.mono hsrc).isOpen_inter_preimage (hop _) (hop _)
  have himg : F.chart '' boundaryTransportSourceV480 F = halfDisc F.targetR := by
    apply Set.Subset.antisymm
    · rintro z ⟨x, hx, rfl⟩
      exact hx.2.2
    · intro z hz
      refine ⟨F.chart.symm z, ⟨F.inverse_interior z hz, F.chart.map_target (htgt hz), ?_⟩,
        F.chart.right_inv (htgt hz)⟩
      simpa only [F.chart.right_inv (htgt hz)] using hz
  have hjac (f : E2 → E2) (x : E2) :
      LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis (fderiv ℝ f x).toLinearMap = jacobian f x := by
    ext i j
    simp [LinearMap.toMatrix_apply, jacobian, coordinateVector, EuclideanSpace.basisFun_apply]
  have hdetbridge (x : E2) :
      (fderiv ℝ F.chart x).toLinearMap.det = Matrix.det (jacobian F.chart x) := by
    rw [← hjac]
    exact (LinearMap.det_toMatrix _ _).symm
  have hfd (x : E2) (hx : x ∈ halfDisc F.sourceR) : DifferentiableAt ℝ F.chart x :=
    ((F.forward_C1.differentiableOn (by simp)).mono hsrc x hx).differentiableAt ((hop _).mem_nhds hx)
  have hid (z : E2) (hz : z ∈ halfDisc F.targetR) : DifferentiableAt ℝ F.chart.symm z :=
    ((F.inverse_C1.differentiableOn (by simp)).mono htgt z hz).differentiableAt ((hop _).mem_nhds hz)
  have hmat (z : E2) (hz : z ∈ halfDisc F.targetR) :
      jacobian F.chart (F.chart.symm z) * jacobian F.chart.symm z = 1 := by
    have hcomp := (hfd _ (F.inverse_interior z hz)).hasFDerivAt.comp z (hid z hz).hasFDerivAt
    have hevent : (fun x : E2 => x) =ᶠ[𝓝 z] F.chart ∘ F.chart.symm := by
      filter_upwards [(hop _).mem_nhds hz] with y hy
      exact (F.chart.right_inv (htgt hy)).symm
    have hidder := hcomp.congr_of_eventuallyEq hevent
    have heqder := hidder.unique (hasFDerivAt_id z)
    have heqlin := congrArg ContinuousLinearMap.toLinearMap heqder
    have hmatrix := congrArg (LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis) heqlin
    change LinearMap.toMatrix _ _ ((fderiv ℝ F.chart (F.chart.symm z)).toLinearMap.comp
      (fderiv ℝ F.chart.symm z).toLinearMap) = LinearMap.toMatrix _ _ LinearMap.id at hmatrix
    rw [LinearMap.toMatrix_comp _ (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis _, hjac, hjac,
      LinearMap.toMatrix_id] at hmatrix
    exact hmatrix
  have hvdiff (x : E2) (hx : x ∈ halfDisc F.sourceR) : DifferentiableAt ℝ W.v x :=
    ((W.smooth_v x (W.contains
      ⟨Metric.closedBall_subset_closedBall F.sourceR_inside.le (Metric.ball_subset_closedBall hx.1),hx.2.le⟩)).contDiffAt
      (W.O_open.mem_nhds (W.contains
        ⟨Metric.closedBall_subset_closedBall F.sourceR_inside.le (Metric.ball_subset_closedBall hx.1),hx.2.le⟩))).differentiableAt (by simp)
  have hvhatdiff (z : E2) (hz : z ∈ halfDisc F.targetR) : DifferentiableAt ℝ (boundaryVhatV480 F W.v) z :=
    (hvdiff _ (F.inverse_interior z hz)).comp z (hid z hz)
  have hgradcoord (u : E2 → ℝ) (x : E2) (i : Fin 2) :
      planarGradient u x i = fderiv ℝ u x (coordinateVector 2 i) := by
    fin_cases i <;> simp [planarGradient, coordinateVector, Fin.sum_univ_two]
  have hchain (u : E2 → ℝ) (f : E2 → E2) (x : E2)
      (hu : DifferentiableAt ℝ u (f x)) (hf : DifferentiableAt ℝ f x) :
      planarGradient (u ∘ f) x = matrixAction (jacobian f x).transpose (planarGradient u (f x)) := by
    ext i
    rw [hgradcoord, fderiv_comp x hu hf]
    have he (w : E2) : w = ∑ j : Fin 2, w j • coordinateVector 2 j := by
      ext j
      fin_cases j <;> simp [coordinateVector, Fin.sum_univ_two]
    change fderiv ℝ u (f x) (fderiv ℝ f x (coordinateVector 2 i)) = _
    rw [he (fderiv ℝ f x (coordinateVector 2 i)), map_sum]
    simp only [map_smul, smul_eq_mul, matrixAction, Matrix.transpose_apply, jacobian, hgradcoord]
    rfl
  have hgradient (z : E2) (hz : z ∈ halfDisc F.targetR) :
      planarGradient W.v (F.chart.symm z) =
        matrixAction (jacobian F.chart (F.chart.symm z)).transpose (planarGradient (boundaryVhatV480 F W.v) z) := by
    have hx := F.inverse_interior z hz
    have hevent : W.v =ᶠ[𝓝 (F.chart.symm z)] (boundaryVhatV480 F W.v) ∘ F.chart := by
      filter_upwards [(hop _).mem_nhds hx] with x hx'
      exact congrArg W.v (F.chart.left_inv (hsrc hx')).symm
    have hg : planarGradient W.v (F.chart.symm z) =
        planarGradient ((boundaryVhatV480 F W.v) ∘ F.chart) (F.chart.symm z) := by
      unfold planarGradient
      rw [hevent.fderiv_eq]
    rw [hg, hchain (boundaryVhatV480 F W.v) F.chart _ (by simpa only [F.chart.right_inv (htgt hz)] using hvhatdiff z hz)
      (hfd _ hx), F.chart.right_inv (htgt hz)]
  have hsmall : SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc F.sourceR ⊆ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc (W.R) := by
    intro x hx
    exact ⟨Metric.closedBall_subset_closedBall F.sourceR_inside.le hx.1, hx.2⟩
  have hdensity (z : E2) (hz : z ∈ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc F.targetR) :
      densityLeading W.A F.chart (F.chart.symm z) = 1 := by
    let x := F.chart.symm z
    let A := W.A x
    let M := jacobian F.chart x
    have hx : x ∈ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc F.sourceR := F.inverse_half_disc z hz
    have ha : A.det = 1 := hdet x (hsmall hx)
    have hau : IsUnit A.det := by rw [ha]; exact isUnit_one
    have hm : M.det ≠ 0 := F.forward_det x (F.source_contains hx)
    have hmu : IsUnit M.det := isUnit_iff_ne_zero.mpr hm
    obtain ⟨lam, hlam, hi⟩ := F.conformalInverseMetric x hx
    change A⁻¹ = lam • (M.transpose * M) at hi
    have he : lam • (M * A * M.transpose) = 1 := by
      calc
        _ = M * (A * A⁻¹) * M⁻¹ := by
          rw [hi]
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc,
            Matrix.mul_nonsing_inv M hmu, Matrix.mul_one]
        _ = 1 := by rw [Matrix.mul_nonsing_inv A hau, Matrix.mul_one, Matrix.mul_nonsing_inv M hmu]
    have hdetinv : A⁻¹.det = 1 := by
      simpa only [ha, mul_one] using Matrix.det_nonsing_inv_mul_det A hau
    have hh := congrArg Matrix.det hi
    rw [hdetinv, Matrix.det_smul, Matrix.det_mul, Matrix.det_transpose] at hh
    have hprod : lam * |M.det| = 1 := by
      have hn : 0 ≤ lam * |M.det| := mul_nonneg hlam.le (abs_nonneg _)
      have hsq : (lam * |M.det|) ^ 2 = 1 := by
        simpa only [Fintype.card_fin, mul_pow, sq_abs, ← pow_two] using hh.symm
      nlinarith
    have hlam_eq : lam = |M.det|⁻¹ := by
      simpa only [one_div] using (eq_div_iff (abs_ne_zero.mpr hm)).mpr hprod
    change |M.det|⁻¹ • (M * A * M.transpose) = 1
    rw [← hlam_eq]
    exact he
  have hcompact (r : ℝ) : IsCompact (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc r) :=
    (isCompact_closedBall _ _).inter_right
      (isClosed_le continuous_const (EuclideanSpace.proj (1 : Fin 2)).continuous)
  have hbcont : ContinuousOn (boundaryBhatV480 F W.B) (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc F.targetR) := by
    have hj (i j : Fin 2) : ContinuousOn (fun x => jacobian F.chart x i j)
        (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc F.sourceR) := by
      obtain ⟨C, hC⟩ := F.forward_holder i j
      exact hC.continuousOn F.alpha_pos
    have hjdet : ContinuousOn (fun x => Matrix.det (jacobian F.chart x))
        (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc F.sourceR) := by
      simp only [Matrix.det_fin_two]
      exact ((hj 0 0).mul (hj 1 1)).sub ((hj 0 1).mul (hj 1 0))
    have hfactor : ContinuousOn (fun x => |Matrix.det (jacobian F.chart x)|⁻¹)
        (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc F.sourceR) :=
      hjdet.abs.inv₀ (fun x hx => abs_ne_zero.mpr (F.forward_det x (F.source_contains hx)))
    have hbc := helliptic.2.1.continuousOn.mono hsmall
    have haction : ContinuousOn (fun x => matrixAction (jacobian F.chart x) (W.B x))
        (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc F.sourceR) := by
      unfold matrixAction
      apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp_continuousOn
      apply continuousOn_pi.mpr
      intro i
      apply continuousOn_finsetSum
      intro j hj'
      exact (hj i j).mul ((EuclideanSpace.proj j).continuous.comp_continuousOn hbc)
    exact (hfactor.smul haction).comp
      (F.chart.symm.continuousOn.mono F.target_contains) F.inverse_half_disc
  have hbbound : BoundedOn (boundaryBhatV480 F W.B) (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc F.targetR) := by
    obtain ⟨C, hC⟩ := (hcompact _).exists_bound_of_continuousOn hbcont
    exact ⟨max C 0, le_max_right _ _, fun x hx => (hC x hx).trans (le_max_left _ _)⟩
  have hbLp : MemLp (boundaryBhatV480 F W.B) ⊤ (volume.restrict (halfDisc F.targetR)) := by
    letI : IsFiniteMeasure (volume.restrict (halfDisc F.targetR)) :=
      isFiniteMeasure_restrict.mpr ((measure_mono (hhc _)).trans_lt (hcompact _).measure_lt_top).ne
    obtain ⟨C, hC, hbC⟩ := hbbound
    exact MemLp.of_bound ((hbcont.mono (hhc _)).aestronglyMeasurable (hop _).measurableSet) C
      ((ae_restrict_mem (hop _).measurableSet).mono (fun x hx => hbC x (hhc _ hx)))
  have hNv : ContDiffOn ℝ ∞ W.v (halfDisc W.R) :=
    W.smooth_v.mono ((hhc W.R).trans W.contains)
  have hgradcontinuous (u : E2 → ℝ) (U : Set E2) (ho : IsOpen U) (hu : ContDiffOn ℝ 1 u U) :
      ContinuousOn (planarGradient u) U := by
    have hd := hu.continuousOn_fderiv_of_isOpen ho (by simp)
    unfold planarGradient
    apply continuousOn_finsetSum
    intro i hi
    exact (hd.clm_apply continuousOn_const).smul continuousOn_const
  have hNg := hgradcontinuous W.v _ (hop _) (hNv.of_le (by simp))
  have hflux : ContinuousOn (fun x => matrixAction (W.A x) (planarGradient W.v x))
      (halfDisc (W.R)) := by
    unfold matrixAction
    apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp_continuousOn
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_finsetSum
    intro j hj
    exact ((helliptic.1 i j).continuousOn.mono (hhc _)).mul
      ((EuclideanSpace.proj j).continuous.comp_continuousOn hNg)
  have hlower : ContinuousOn (fun x => inner ℝ (W.B x) (planarGradient W.v x))
      (halfDisc (W.R)) :=
    (helliptic.2.1.continuousOn.mono (hhc _)).inner hNg
  have hvg : ContinuousOn (planarGradient (boundaryVhatV480 F W.v)) (halfDisc F.targetR) := by
    apply hgradcontinuous _ _ (hop _)
    exact (hNv.of_le (by simp)).comp (F.inverse_C1.mono htgt) (fun z hz =>
      ⟨Metric.ball_subset_ball F.sourceR_inside.le (F.inverse_interior z hz).1,
        (F.inverse_interior z hz).2⟩)
  have hint (U : Set E2) (q : E2 → E2) (r ψ : E2 → ℝ)
      (hq : ContinuousOn q U) (hr : ContinuousOn r U) (hψ : ContDiff ℝ 1 ψ)
      (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ U) :
      Integrable (fun x => inner ℝ (q x) (planarGradient ψ x) - r x * ψ x) := by
    have hgc : Continuous (planarGradient ψ) := by
      rw [← continuousOn_univ]
      exact hgradcontinuous ψ Set.univ isOpen_univ hψ.contDiffOn
    apply (integrableOn_iff_integrable_of_support_subset ?_).mp
      ((((hq.mono hs).inner hgc.continuousOn).sub
        ((hr.mono hs).mul hψ.continuous.continuousOn)).integrableOn_compact hc)
    intro x hx
    by_contra hn
    have hz := image_eq_zero_of_notMem_tsupport hn
    have hdz := fderiv_of_notMem_tsupport ℝ hn
    apply hx
    simp [planarGradient, hz, hdz]
  have htests : (∀ φ : E2 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ halfDisc F.targetR →
      ContDiff ℝ 1 (boundaryPullbackTestV480 F φ) ∧ HasCompactSupport (boundaryPullbackTestV480 F φ) ∧
      tsupport (boundaryPullbackTestV480 F φ) ⊆ halfDisc F.sourceR ∧
      (∀ x ∈ boundaryTransportSourceV480 F,
        planarGradient (boundaryPullbackTestV480 F φ) x =
          matrixAction (jacobian F.chart x).transpose (planarGradient φ (F.chart x))) ∧
      IntegrableOn (weakIntegrand W.A W.B (fun _ => 0) W.v
        (planarGradient W.v) (boundaryPullbackTestV480 F φ)) (halfDisc (W.R)) ∧
      IntegrableOn (weakIntegrand
        (fun z => densityLeading W.A F.chart (F.chart.symm z)) (boundaryBhatV480 F W.B)
        (fun _ => 0) (boundaryVhatV480 F W.v) (planarGradient (boundaryVhatV480 F W.v)) φ) (halfDisc F.targetR) ∧
      (∫ x in halfDisc (W.R), weakIntegrand W.A W.B
        (fun _ => 0) W.v (planarGradient W.v) (boundaryPullbackTestV480 F φ) x) =
      (∫ z in halfDisc F.targetR, weakIntegrand
        (fun z => densityLeading W.A F.chart (F.chart.symm z)) (boundaryBhatV480 F W.B)
        (fun _ => 0) (boundaryVhatV480 F W.v) (planarGradient (boundaryVhatV480 F W.v)) φ z)) := by
    intro φ hφ hc hs
    let C : Set E2 := F.chart.symm '' tsupport φ
    have hC : IsCompact C := hc.image_of_continuousOn
      (F.chart.symm.continuousOn.mono (hs.trans htgt))
    have hCsrc : C ⊆ boundaryTransportSourceV480 F := by
      rintro x ⟨z, hz, rfl⟩
      exact ⟨F.inverse_interior z (hs hz), F.chart.map_target (htgt (hs hz)),
        by simpa only [F.chart.right_inv (htgt (hs hz))] using hs hz⟩
    have hsupp : Function.support (boundaryPullbackTestV480 F φ) ⊆ C := by
      intro x hx
      change boundaryPullbackTestV480 F φ x ≠ 0 at hx
      by_cases hxS : x ∈ boundaryTransportSourceV480 F
      · have hn : φ (F.chart x) ≠ 0 := by simpa only [boundaryPullbackTestV480, if_pos hxS] using hx
        exact ⟨F.chart x, subset_tsupport φ hn, F.chart.left_inv hxS.2.1⟩
      · exact False.elim (hx (by simp only [boundaryPullbackTestV480, if_neg hxS]))
    have htsupp : tsupport (boundaryPullbackTestV480 F φ) ⊆ C := closure_minimal hsupp hC.isClosed
    have htsrc : tsupport (boundaryPullbackTestV480 F φ) ⊆ boundaryTransportSourceV480 F := htsupp.trans hCsrc
    have hlocal (x : E2) (hx : x ∈ boundaryTransportSourceV480 F) :
        boundaryPullbackTestV480 F φ =ᶠ[𝓝 x] φ ∘ F.chart := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      simp only [boundaryPullbackTestV480, if_pos hy, Function.comp_apply]
    have hC1 : ContDiff ℝ 1 (boundaryPullbackTestV480 F φ) := by
      apply contDiff_iff_contDiffAt.mpr
      intro x
      by_cases hx : x ∈ boundaryTransportSourceV480 F
      · apply (((hφ.of_le (by norm_num : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω))).contDiffAt).comp x
          ((F.forward_C1 x hx.2.1).contDiffAt
            (Filter.mem_of_superset ((hop _).mem_nhds hx.1) hsrc))).congr_of_eventuallyEq
        exact hlocal x hx
      · exact contDiffAt_const.congr_of_eventuallyEq
          (notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (htsrc h)))
    have hgrad (x : E2) (hx : x ∈ boundaryTransportSourceV480 F) :
        planarGradient (boundaryPullbackTestV480 F φ) x =
          matrixAction (jacobian F.chart x).transpose (planarGradient φ (F.chart x)) := by
      have he : planarGradient (boundaryPullbackTestV480 F φ) x = planarGradient (φ ∘ F.chart) x := by
        unfold planarGradient
        rw [(hlocal x hx).fderiv_eq]
      rw [he]
      exact hchain φ F.chart x (hφ.differentiable (by simp) _) (hfd x hx.1)
    have hψsrc : tsupport (boundaryPullbackTestV480 F φ) ⊆ halfDisc (W.R) := by
      intro x hx
      have h := (htsrc hx).1
      exact ⟨Metric.ball_subset_ball F.sourceR_inside.le h.1, h.2⟩
    have hiSource : IntegrableOn (weakIntegrand W.A W.B (fun _ => 0) W.v
        (planarGradient W.v) (boundaryPullbackTestV480 F φ)) (halfDisc (W.R)) := by
      unfold weakIntegrand
      simp only [zero_mul, add_zero]
      exact (hint _ _ _ _ hflux hlower hC1 (hC.of_isClosed_subset isClosed_closure htsupp) hψsrc).integrableOn
    have hone (p : E2) : matrixAction (1 : Mat2) p = p := by
      ext i
      simp [matrixAction, Matrix.one_apply]
    have hiTarget : IntegrableOn (weakIntegrand
        (fun z => densityLeading W.A F.chart (F.chart.symm z)) (boundaryBhatV480 F W.B)
        (fun _ => 0) (boundaryVhatV480 F W.v) (planarGradient (boundaryVhatV480 F W.v)) φ) (halfDisc F.targetR) := by
      apply ((hint _ _ _ φ hvg ((hbcont.mono (hhc _)).inner hvg)
        (hφ.of_le (by simp)) hc hs).integrableOn).congr
      filter_upwards [ae_restrict_mem (hop F.targetR).measurableSet] with z hz
      simp only [weakIntegrand, hdensity z (hhc _ hz), hone, zero_mul, add_zero]
    have hpoint (x : E2) (hx : x ∈ boundaryTransportSourceV480 F) :
        weakIntegrand W.A W.B (fun _ => 0) W.v
          (planarGradient W.v) (boundaryPullbackTestV480 F φ) x =
        |(fderiv ℝ F.chart x).toLinearMap.det| • weakIntegrand
          (fun z => densityLeading W.A F.chart (F.chart.symm z)) (boundaryBhatV480 F W.B)
          (fun _ => 0) (boundaryVhatV480 F W.v) (planarGradient (boundaryVhatV480 F W.v)) φ (F.chart x) := by
      have hg := hgradient (F.chart x) hx.2.2
      rw [F.chart.left_inv hx.2.1] at hg
      have hnonzero : |Matrix.det (jacobian F.chart x)| ≠ 0 :=
        abs_ne_zero.mpr (F.forward_det x hx.2.1)
      simp only [weakIntegrand, zero_mul, add_zero, hgrad x hx, hg, boundaryPullbackTestV480,
        if_pos hx, hdetbridge, boundaryBhatV480, densityDrift, densityLeading,
        F.chart.left_inv hx.2.1, smul_eq_mul]
      simp [PiLp.inner_apply, matrixAction, Matrix.mul_apply, Matrix.transpose_apply,
        Fin.sum_univ_two]
      field_simp
      <;> ring
    have hzero (x : E2) (hx : x ∉ boundaryTransportSourceV480 F) :
        weakIntegrand W.A W.B (fun _ => 0) W.v
          (planarGradient W.v) (boundaryPullbackTestV480 F φ) x = 0 := by
      have hnot : x ∉ tsupport (boundaryPullbackTestV480 F φ) := fun h => hx (htsrc h)
      simp [weakIntegrand, planarGradient, fderiv_of_notMem_tsupport ℝ hnot,
        image_eq_zero_of_notMem_tsupport hnot]
    have hsubstitution := integral_image_eq_integral_abs_det_fderiv_smul volume hopen.measurableSet
      (fun x hx => (hfd x hx.1).hasFDerivAt.hasFDerivWithinAt)
      (F.chart.injOn.mono (fun x hx => hx.2.1))
      (weakIntegrand (fun z => densityLeading W.A F.chart (F.chart.symm z)) (boundaryBhatV480 F W.B)
        (fun _ => 0) (boundaryVhatV480 F W.v) (planarGradient (boundaryVhatV480 F W.v)) φ)
    rw [himg] at hsubstitution
    have htransport :
        (∫ x in halfDisc (W.R), weakIntegrand W.A W.B
          (fun _ => 0) W.v (planarGradient W.v) (boundaryPullbackTestV480 F φ) x) =
        (∫ z in halfDisc F.targetR, weakIntegrand
          (fun z => densityLeading W.A F.chart (F.chart.symm z)) (boundaryBhatV480 F W.B)
          (fun _ => 0) (boundaryVhatV480 F W.v) (planarGradient (boundaryVhatV480 F W.v)) φ z) := by
      rw [hsubstitution, ← setIntegral_congr_fun hopen.measurableSet hpoint]
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
        setIntegral_eq_integral_of_forall_compl_eq_zero]
      intro x hx
      apply hzero x
      intro hxS
      exact hx ⟨Metric.ball_subset_ball F.sourceR_inside.le hxS.1.1, hxS.1.2⟩
    exact ⟨hC1, hC.of_isClosed_subset isClosed_closure htsupp,
      htsrc.trans (fun x hx => hx.1), hgrad, hiSource, hiTarget, htransport⟩
  refine ⟨hopen.measurableSet, himg, ?_, fun x _ => hdetbridge x, htests,
    hdensity, hbcont, hbbound, hbLp, ?_, ?_⟩
  · intro z hz
    exact ⟨hmat z hz, (mul_eq_one_comm.mp (hmat z hz)), hgradient z hz⟩
  · intro z hz
    change W.v (F.chart.symm z) = 0
    apply htrace
    have hflat := F.inverse_flat z hz
    exact ⟨Metric.ball_subset_ball F.sourceR_inside.le hflat.1, hflat.2⟩
  · have hvcont : ContinuousOn (boundaryVhatV480 F W.v) (halfDisc F.targetR) :=
      (show DifferentiableOn ℝ (boundaryVhatV480 F W.v) (halfDisc F.targetR) from
        fun z hz => (hvhatdiff z hz).differentiableWithinAt).continuousOn
    have hweak : WeakGradientOn (halfDisc F.targetR) (boundaryVhatV480 F W.v) (planarGradient (boundaryVhatV480 F W.v)) := by
      refine ⟨hvcont.locallyIntegrableOn (hop _).measurableSet,
        hvg.locallyIntegrableOn (hop _).measurableSet, ?_⟩
      intro φ hφ hc hs i
      have hp (f ψ : E2 → ℝ) (hf : ContinuousOn f (halfDisc F.targetR))
          (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ ⊆ halfDisc F.targetR) :
          Integrable (fun x => f x * ψ x) := by
        apply (integrableOn_iff_integrable_of_support_subset ?_).mp
          (((hf.mono hsψ).mul hψ.continuousOn).integrableOn_compact hcψ)
        intro x hx
        exact subset_tsupport ψ ((mul_ne_zero_iff.mp hx).2)
      have hpartial : ContinuousOn (fun z => fderiv ℝ (boundaryVhatV480 F W.v) z (coordinateVector 2 i))
          (halfDisc F.targetR) :=
        ((EuclideanSpace.proj i).continuous.comp_continuousOn hvg).congr
          (fun z hz => (hgradcoord (boundaryVhatV480 F W.v) z i).symm)
      have hi := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        (hp _ _ hpartial hφ.continuous hc hs)
        (hp _ _ hvcont ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
          (hc.fderiv_apply ℝ _) ((tsupport_fderiv_apply_subset ℝ _).trans hs))
        (hp _ _ hvcont hφ.continuous hc hs)
        (fun z hz => hvhatdiff z (hs hz)) (fun z hz => hφ.differentiable (by simp) z)
      simp_rw [hgradcoord]
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero,
        setIntegral_eq_integral_of_forall_compl_eq_zero]
      · exact hi
      · intro z hz
        rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hs h)), mul_zero]
      · intro z hz
        rw [fderiv_of_notMem_tsupport ℝ (fun h => hz (hs h))]
        simp
    refine ⟨hweak, ?_⟩
    intro φ hφ hc hs
    obtain ⟨hψC1, hψcompact, hψsupport, hψgrad, hiSource, hiTarget, htransport⟩ := htests φ hφ hc hs
    have hone (p : E2) : matrixAction (1 : Mat2) p = p := by
      ext i
      simp [matrixAction, Matrix.one_apply]
    have htargeteq : Set.EqOn
        (weakIntegrand (fun z => densityLeading W.A F.chart (F.chart.symm z)) (boundaryBhatV480 F W.B)
          (fun _ => 0) (boundaryVhatV480 F W.v) (planarGradient (boundaryVhatV480 F W.v)) φ)
        (weakIntegrand (fun _ => 1) (boundaryBhatV480 F W.B) (fun _ => 0) (boundaryVhatV480 F W.v) (planarGradient (boundaryVhatV480 F W.v)) φ)
        (halfDisc F.targetR) := by
      intro z hz
      simp only [weakIntegrand, hdensity z (hhc _ hz)]
    change IntegrableOn (weakIntegrand (fun _ => 1) (boundaryBhatV480 F W.B) (fun _ => 0) (boundaryVhatV480 F W.v)
      (planarGradient (boundaryVhatV480 F W.v)) φ) (halfDisc F.targetR) ∧ _
    refine ⟨hiTarget.congr ((ae_restrict_mem (hop _).measurableSet).mono (fun z hz => htargeteq hz)), ?_⟩
    change (∫ z in halfDisc F.targetR, weakIntegrand (fun _ => 1) (boundaryBhatV480 F W.B) (fun _ => 0) (boundaryVhatV480 F W.v)
      (planarGradient (boundaryVhatV480 F W.v)) φ z) = 0
    rw [← setIntegral_congr_fun (hop _).measurableSet htargeteq, ← htransport]
    have hψsource : tsupport (boundaryPullbackTestV480 F φ) ⊆ halfDisc (W.R) := by
      intro x hx
      exact ⟨Metric.ball_subset_ball F.sourceR_inside.le (hψsupport hx).1, (hψsupport hx).2⟩
    exact (compact_C1_test_extension (halfDisc (W.R)) (hop _) W.A W.B
      (fun _ => 0) W.v (planarGradient W.v) heq
      (hflux.locallyIntegrableOn (hop _).measurableSet)
      (by simpa only [zero_mul, add_zero] using hlower.locallyIntegrableOn (hop _).measurableSet)
      (boundaryPullbackTestV480 F φ) hψC1 hψcompact hψsource).2.2



end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3BoundaryIsothermalExistsV480 -/

noncomputable section
open Set Topology Function MeasureTheory
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider
set_option maxHeartbeats 600000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

theorem boundary_actual_isothermal_patch_exists_v480 (W : BoundaryNormalizedWindowV480) :
    Nonempty (BoundaryIsothermalPatchV480 W.R W.A) := by
  obtain ⟨ha,hb,hc,hsym,ell,A,hell,hA,hbounds⟩ := W.elliptic
  obtain ⟨G⟩ := inverse_det_one_metric_data W.R W.R_pos W.A
    (fun x hx i j => hsym x (W.contains hx) i j)
    ⟨ell,A,hell,hA,fun x hx p => hbounds x (W.contains hx) p⟩ W.lipschitz
    (fun x hx => W.det_one x (W.contains hx))
  obtain ⟨Ω⟩ := smooth_flat_jordan_domain W.R W.R_pos
  obtain ⟨P⟩ := boundary_metric_conformal_provider W.R W.A G Ω
  obtain ⟨X⟩ := metric_parametrization_ambient_extensions P
  obtain ⟨F,hF⟩ := boundary_isothermal_patch_from_metric_provider_v480 W.R W.A G Ω P X
  exact ⟨F⟩

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3ActualBoundaryReflectionV480 -/

noncomputable section
open Set Topology Function MeasureTheory
open scoped Manifold ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.OriginalEndpoints.B1Tangency.WeakTransport
set_option maxHeartbeats 600000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def boundaryReflectedV480 {R : ℝ} {A : E2 → Mat2}
    (F : BoundaryIsothermalPatchV480 R A) (v : E2 → ℝ) : E2 → ℝ :=
  oddReflect (boundaryVhatV480 F v)
def boundaryReflectedB480 {R : ℝ} {A : E2 → Mat2}
    (F : BoundaryIsothermalPatchV480 R A) (b : E2 → E2) : E2 → E2 :=
  driftReflect (boundaryBhatV480 F b)
def boundaryReflectedGradientV480 {R : ℝ} {A : E2 → Mat2}
    (F : BoundaryIsothermalPatchV480 R A) (v : E2 → ℝ) : ℂ → ℂ :=
  complexGradient (boundaryReflectedV480 F v)

private theorem boundary_window_density_inputs_v480 (W : BoundaryNormalizedWindowV480) :
    WeakLinearEquationOn (halfDisc W.R) W.A W.B (fun _ => 0) W.v (planarGradient W.v) ∧
    SmoothEllipticOn W.A W.B (fun _ => 0) (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc W.R) ∧
    BoundedOn W.B (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc W.R) ∧
    (∀ x ∈ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc W.R, Matrix.det (W.A x) = 1) ∧
    (∀ x ∈ flatArc W.R, W.v x = 0) := by
  have hhalf : halfDisc W.R ⊆ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc W.R :=
    fun x hx => ⟨Metric.ball_subset_closedBall hx.1,hx.2.le⟩
  have hsub := hhalf.trans W.contains
  have hhalfopen : IsOpen (halfDisc W.R) := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous)
  obtain ⟨ha,hb,hc,hsym,ell,A,hell,hA,hbounds⟩ := W.elliptic
  exact ⟨native_local_classical_linear_weak_v475 (halfDisc W.R) hhalfopen
    W.A W.B (fun _ => 0) W.v (fun i j => (ha i j).mono hsub)
    (hb.mono hsub) contDiffOn_const (W.smooth_v.mono hsub) W.classical,
    ⟨fun i j => (ha i j).mono W.contains,hb.mono W.contains,contDiffOn_const,
      fun x hx i j => hsym x (W.contains hx) i j,ell,A,hell,hA,
      fun x hx p => hbounds x (W.contains hx) p⟩,
    W.B_bounded,fun x hx => W.det_one x (W.contains hx),W.flat⟩

theorem boundary_actual_density_equation_v480 (W : BoundaryNormalizedWindowV480)
    (F : BoundaryIsothermalPatchV480 W.R W.A) :
    (∀ z ∈ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc F.targetR,
      densityLeading W.A F.chart (F.chart.symm z) = 1) ∧
    BoundedOn (boundaryBhatV480 F W.B) (halfDisc F.targetR) ∧
    MemLp (boundaryBhatV480 F W.B) ⊤ (volume.restrict (halfDisc F.targetR)) ∧
    (∀ z ∈ flatArc F.targetR, (boundaryVhatV480 F W.v) z = 0) ∧
    H1On (halfDisc F.targetR) (boundaryVhatV480 F W.v) (planarGradient (boundaryVhatV480 F W.v)) ∧
    WeakLinearEquationOn (halfDisc F.targetR) (fun _ => 1) (boundaryBhatV480 F W.B) (fun _ => 0)
      (boundaryVhatV480 F W.v) (planarGradient (boundaryVhatV480 F W.v)) := by
  obtain ⟨heq,hell,hb,hdet,htrace⟩ := boundary_window_density_inputs_v480 W
  obtain ⟨hU,himage,hjets,hdetF,htests,hleading,hbc,hbb,hblp,hflat,hweak⟩ :=
    boundary_density_test_transport_v480 W F heq hell hb hdet htrace
  have hjet := boundary_chart_first_jets_H1_v480 W F
  refine ⟨hleading, ?_, hblp, hflat, hjet.2.2.2.2.2.2.2.2.2.2.2, hweak⟩
  exact ⟨hbb.choose,hbb.choose_spec.1,fun x hx => hbb.choose_spec.2 x
    ⟨Metric.ball_subset_closedBall hx.1,hx.2.le⟩⟩

theorem boundary_actual_odd_reflected_weak_equation_v480 (W : BoundaryNormalizedWindowV480)
    (F : BoundaryIsothermalPatchV480 W.R W.A) :
    ContDiffOn ℝ 1 (boundaryReflectedV480 F W.v) (disc F.targetR) ∧
    H1On (disc F.targetR) (boundaryReflectedV480 F W.v) (planarGradient (boundaryReflectedV480 F W.v)) ∧
    BoundedOn (boundaryReflectedB480 F W.B) (disc F.targetR) ∧
    MemLp (boundaryReflectedB480 F W.B) ⊤ (volume.restrict (disc F.targetR)) ∧
    WeakLinearEquationOn (disc F.targetR) (fun _ => 1) (boundaryReflectedB480 F W.B) (fun _ => 0)
      (boundaryReflectedV480 F W.v) (planarGradient (boundaryReflectedV480 F W.v)) := by
  obtain ⟨heq,hell,hb,hdet,htrace⟩ := boundary_window_density_inputs_v480 W
  obtain ⟨hU,himage,hjets,hdetF,htests,hleading,hbc,hbb,hblp,hflat,hweak⟩ :=
    boundary_density_test_transport_v480 W F heq hell hb hdet htrace
  obtain ⟨hNv,hNvb,hNdb,hFd,hFi,hvd,hvg,hvc,hgc,hvb,hgb,hH1⟩ :=
    boundary_chart_first_jets_H1_v480 W F
  have hmeas : MeasurableSet (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc F.targetR) := by
    change MeasurableSet (Metric.closedBall (0 : E2) F.targetR ∩ {x : E2 | 0 ≤ x 1})
    exact (Metric.isClosed_closedBall.inter
      (isClosed_le continuous_const (EuclideanSpace.proj (1 : Fin 2)).continuous)).measurableSet
  have hm : AEStronglyMeasurable (boundaryBhatV480 F W.B) (volume.restrict (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc F.targetR)) :=
    hbc.aestronglyMeasurable hmeas
  obtain ⟨hflatjet,hoddjet,hC1,hoddH1,hob,hod,hdb,hdLp⟩ :=
    odd_first_jet_paste_H1 F.targetR F.targetR_pos (boundaryVhatV480 F W.v) (boundaryBhatV480 F W.B) hvc hgc hvd
      hflat hvb hgb hbb hm
  have hhalf : halfDisc F.targetR ⊆ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc F.targetR :=
    fun x hx => ⟨Metric.ball_subset_closedBall hx.1,hx.2.le⟩
  have hlocal : ∀ K' : Set E2, IsCompact K' → K' ⊆ disc F.targetR →
      BoundedOn (planarGradient (boundaryVhatV480 F W.v)) (K' ∩ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc F.targetR) ∧
      BoundedOn (boundaryBhatV480 F W.B) (K' ∩ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc F.targetR) := by
    intro K' hK hKsub
    exact ⟨⟨hgb.choose,hgb.choose_spec.1,fun x hx => hgb.choose_spec.2 x hx.2⟩,
      ⟨hbb.choose,hbb.choose_spec.1,fun x hx => hbb.choose_spec.2 x hx.2⟩⟩
  have href := (reflected_weak_test_assembly F.targetR F.targetR_pos (boundaryVhatV480 F W.v) (boundaryBhatV480 F W.B)
    hweak hoddH1 hoddjet (hm.mono_measure (Measure.restrict_mono hhalf le_rfl)) hlocal).2
  exact ⟨hC1,hoddH1,hdb,hdLp,href⟩


/-- Distributional ∂bar w=A*w+B*conj(w), w=∂1v-i∂2v, using the actual
reflected drift, including all Lp preconditions for every finite p>2. -/
theorem boundary_actual_reflected_gradient_vekua_v480 (W : BoundaryNormalizedWindowV480)
    (F : BoundaryIsothermalPatchV480 W.R W.A) :
    ContinuousOn (boundaryReflectedGradientV480 F W.v) (Metric.ball (0 : ℂ) F.targetR) ∧
    WeakVekuaOn (Metric.ball (0 : ℂ) F.targetR) (boundaryReflectedGradientV480 F W.v)
      (vekuaA (boundaryReflectedB480 F W.B)) (vekuaB (boundaryReflectedB480 F W.B)) ∧
    ∀ p : ℝ, 2 < p →
      MemLp (vekuaA (boundaryReflectedB480 F W.B)) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : ℂ) F.targetR)) ∧
      MemLp (vekuaB (boundaryReflectedB480 F W.B)) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : ℂ) F.targetR)) := by
  obtain ⟨hu,hH1,hb,hbLp,heq⟩ := boundary_actual_odd_reflected_weak_equation_v480 W F
  obtain ⟨hw,hvekua,hid,hlp⟩ := C1_real_weak_to_vekua F.targetR F.targetR_pos
    (boundaryReflectedV480 F W.v) (boundaryReflectedB480 F W.B) hu heq hb hbLp
  exact ⟨hw,hvekua,hlp⟩



/-- The reflected first jet at the flat origin is the same transported
actual quotient jet. -/
theorem boundary_actual_reflected_gradient_zero_v480 (W : BoundaryNormalizedWindowV480)
    (F : BoundaryIsothermalPatchV480 W.R W.A) (hdv0 : fderiv ℝ W.v 0 = 0) :
    boundaryReflectedGradientV480 F W.v 0 = 0 := by
  obtain ⟨heq,hell,hb,hdet,htrace⟩ := boundary_window_density_inputs_v480 W
  obtain ⟨hU,himage,hjets,hdetF,htests,hleading,hbc,hbb,hblp,hflat,hweak⟩ :=
    boundary_density_test_transport_v480 W F heq hell hb hdet htrace
  obtain ⟨hNv,hNvb,hNdb,hFd,hFi,hvd,hvg,hvc,hgc,hvb,hgb,hH1⟩ :=
    boundary_chart_first_jets_H1_v480 W F
  have hmeas : MeasurableSet (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc F.targetR) := by
    change MeasurableSet (Metric.closedBall (0 : E2) F.targetR ∩ {x : E2 | 0 ≤ x 1})
    exact (Metric.isClosed_closedBall.inter
      (isClosed_le continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous)).measurableSet
  obtain ⟨hflatjet,hoddjet,hC1,hoddH1,hob,hod,hdb,hdLp⟩ :=
    odd_first_jet_paste_H1 F.targetR F.targetR_pos (boundaryVhatV480 F W.v)
      (boundaryBhatV480 F W.B) hvc hgc hvd hflat hvb hgb hbb (hbc.aestronglyMeasurable hmeas)
  have h0S : (0 : E2) ∈ F.chart.source := F.source_contains
    ⟨Metric.mem_closedBall_self F.sourceR_pos.le,by simp⟩
  have h0T : (0 : E2) ∈ F.chart.target := F.base ▸ F.chart.map_source h0S
  have hsym0 : F.chart.symm (0 : E2) = 0 := by simpa only [F.base] using F.chart.left_inv h0S
  have hg0 : planarGradient (boundaryVhatV480 F W.v) 0 = 0 := by
    rw [hvg 0 ⟨Metric.mem_closedBall_self F.targetR_pos.le,by simp⟩,hsym0]
    ext i
    simp [planarGradient,hdv0,matrixAction]
  have hro0 : planarGradient (boundaryReflectedV480 F W.v) 0 = 0 := by
    change planarGradient (oddReflect (boundaryVhatV480 F W.v)) 0 = 0
    have h := hoddjet 0 (Metric.mem_ball_self F.targetR_pos)
    simpa only [PiLp.zero_apply,le_refl,ite_true,hg0] using h
  have hpoint0 : complexPoint (0 : ℂ) = (0 : E2) := by ext i; fin_cases i <;> simp [complexPoint]
  simp [boundaryReflectedGradientV480,complexGradient,hpoint0,hro0]

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3BoundaryReflectedNonzeroV480 -/

noncomputable section
open Set Topology Function Filter MeasureTheory
open scoped ContDiff NNReal ENNReal Manifold
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
set_option maxHeartbeats 600000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}

theorem original_pair_boundary_window_no_zero_v480
    (D : OriginalPair g J) {p : E.Carrier}
    (c : ActualBoundaryPairGraphV480 D.A.1.embedding D.B.1.embedding p)
    (hc : 0 < c.coefficient) (N : BoundaryNormalizationDataV480)
    (hNu : N.u = c.height) (hNO : N.O ⊆ c.O)
    (W : BoundaryNormalizedWindowV480)
    (hWv : W.v = fun y => N.v (coordinateSwap y+c.z))
    (hWO : W.O ⊆ (fun y => coordinateSwap y+c.z) ⁻¹' N.O)
    (F : BoundaryIsothermalPatchV480 W.R W.A) :
    ¬ EqOn W.v (fun _ => 0) (boundaryTransportSourceV480 F) := by
  intro hzero
  have hop (r : ℝ) : IsOpen (halfDisc r) := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous)
  have hhalf (r : ℝ) : halfDisc r ⊆ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc r :=
    fun x hx => ⟨Metric.ball_subset_closedBall hx.1,hx.2.le⟩
  have hsrc := (hhalf F.sourceR).trans F.source_contains
  have heq : boundaryTransportSourceV480 F = halfDisc F.sourceR ∩
      F.chart ⁻¹' halfDisc F.targetR := by
    ext x
    exact ⟨fun hx => ⟨hx.1,hx.2.2⟩,fun hx => ⟨hx.1,hsrc hx.1,hx.2⟩⟩
  have hU : IsOpen (boundaryTransportSourceV480 F) := by
    rw [heq]
    exact (F.chart.continuousOn.mono hsrc).isOpen_inter_preimage (hop _) (hop _)
  let V : Set E2 := (fun x => coordinateSwap (x-c.z)) ⁻¹' boundaryTransportSourceV480 F
  have hV : IsOpen V := hU.preimage (coordinateSwap.continuous.comp
    (continuous_id.sub continuous_const))
  have hVNO (x : E2) (hx : x ∈ V) : x ∈ N.O := by
    have ht : coordinateSwap (x-c.z) ∈ W.O := W.contains
      ⟨Metric.closedBall_subset_closedBall F.sourceR_inside.le
        (Metric.ball_subset_closedBall hx.1.1),hx.1.2.le⟩
    have hh := hWO ht
    change coordinateSwap (coordinateSwap (x-c.z))+c.z ∈ N.O at hh
    simpa only [coordinateSwap_involutive,sub_add_cancel] using hh
  have hVO : V ⊆ c.O := fun x hx => hNO (hVNO x hx)
  let y : E2 := (F.targetR/2) • coordinateVector 2 1
  have hy : y ∈ halfDisc F.targetR := by
    constructor
    · rw [disc,Metric.mem_ball,dist_zero_right]
      simp only [y,norm_smul,Real.norm_eq_abs,abs_of_pos (half_pos F.targetR_pos)]
      simpa [coordinateVector] using (half_lt_self F.targetR_pos)
    · simp [y,coordinateVector,PiLp.single_apply,half_pos F.targetR_pos]
  let t := F.chart.symm y
  have ht : t ∈ boundaryTransportSourceV480 F :=
    ⟨F.inverse_interior y hy,F.chart.map_target (F.target_contains (hhalf _ hy)),
      by simpa only [t,F.chart.right_inv (F.target_contains (hhalf _ hy))] using hy⟩
  let x := coordinateSwap t+c.z
  have hx : x ∈ V := by
    change coordinateSwap (coordinateSwap t+c.z-c.z) ∈ boundaryTransportSourceV480 F
    simpa only [add_sub_cancel_right,coordinateSwap_involutive] using ht
  have hx0 : 0 < x 0 := by
    simpa only [x,PiLp.add_apply,coordinateSwap_zero,c.base_flat,add_zero] using ht.1.2
  apply original_pair_boundary_graph_no_positive_zero_germ_v480 D c hc V hV hVO x hx hx0
  intro q hq
  have hz := hzero hq.1
  rw [hWv] at hz
  change N.u (coordinateSwap (coordinateSwap (q-c.z))+c.z) /
    N.h (coordinateSwap (coordinateSwap (q-c.z))+c.z) = 0 at hz
  simp only [coordinateSwap_involutive,sub_add_cancel] at hz
  have hh : N.u q = 0 := (div_eq_zero_iff.mp hz).resolve_right
    (N.h_positive q (hVNO q hq.1)).ne'
  rwa [hNu] at hh

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3BoundaryReflectedFiniteOrderV480 -/

noncomputable section
open Set Topology Function Filter MeasureTheory
open scoped ContDiff NNReal ENNReal Manifold
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
set_option maxHeartbeats 600000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- Finite integer order for the same reflected gradient. The zero branch
is excluded by an actual nonzero positive graph germ. -/
theorem boundary_reflected_finite_order_v480 (W : BoundaryNormalizedWindowV480)
    (F : BoundaryIsothermalPatchV480 W.R W.A) (hdv0 : fderiv ℝ W.v 0 = 0)
    (hnot : ¬ EqOn W.v (fun _ => 0) (boundaryTransportSourceV480 F)) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ delta c1 c2 : ℝ,
      0 < delta ∧ delta < F.targetR ∧ 0 < c1 ∧ 0 < c2 ∧
      (∀ z ∈ Metric.ball (0 : ℂ) delta,
        c1 * ‖z‖ ^ m ≤ ‖boundaryReflectedGradientV480 F W.v z‖ ∧
        ‖boundaryReflectedGradientV480 F W.v z‖ ≤ c2 * ‖z‖ ^ m) := by
  obtain ⟨hw,hveq,hLp⟩ := boundary_actual_reflected_gradient_vekua_v480 W F
  obtain ⟨S⟩ := weak_vekua_similarity F.targetR F.targetR_pos
    (boundaryReflectedGradientV480 F W.v) (vekuaA (boundaryReflectedB480 F W.B))
    (vekuaB (boundaryReflectedB480 F W.B)) hw hveq 3 (by norm_num)
    (hLp 3 (by norm_num)).1 (hLp 3 (by norm_num)).2
  have hw0 := boundary_actual_reflected_gradient_zero_v480 W F hdv0
  obtain hzero | horder := similarity_finite_integer_order F.targetR F.targetR_pos
    (boundaryReflectedGradientV480 F W.v) S hw0
  · have h0S : (0 : E2) ∈ F.chart.source := F.source_contains
      ⟨Metric.mem_closedBall_self F.sourceR_pos.le,by simp⟩
    have hsym0 : F.chart.symm (0 : E2) = 0 := by simpa only [F.base] using F.chart.left_inv h0S
    have hv0 : boundaryReflectedV480 F W.v 0 = 0 := by
      have hh := W.flat 0 ⟨Metric.mem_ball_self W.R_pos,by simp⟩
      simp [boundaryReflectedV480,oddReflect,boundaryVhatV480,hsym0,hh]
    obtain ⟨hu,hH1,hb,hbLp,heq⟩ := boundary_actual_odd_reflected_weak_equation_v480 W F
    let e : ℂ ≃ₗᵢ[ℝ] E2 := Complex.orthonormalBasisOneI.repr
    have he (z : ℂ) : e z = complexPoint z := rfl
    have hball (z : ℂ) : complexPoint z ∈ disc F.targetR ↔ z ∈ Metric.ball (0 : ℂ) F.targetR := by
      change e z ∈ Metric.ball 0 F.targetR ↔ _
      simpa only [Metric.mem_ball,dist_zero_right,map_zero] using
        (show ‖e z‖ < F.targetR ↔ ‖z‖ < F.targetR by rw [e.norm_map])
    have hdAll (x : E2) (hx : x ∈ disc F.targetR) :
        fderiv ℝ (boundaryReflectedV480 F W.v) x = 0 := by
      let z := e.symm x
      have hzpoint : complexPoint z = x := by change e (e.symm x) = x; exact e.apply_symm_apply x
      have hwz := hzero z ((hball z).mp (hzpoint ▸ hx))
      have hgrad : planarGradient (boundaryReflectedV480 F W.v) x = 0 := by
        have hr := congrArg Complex.re hwz
        have hi := congrArg Complex.im hwz
        ext i
        fin_cases i
        · simpa [boundaryReflectedGradientV480,complexGradient,hzpoint] using hr
        · simpa [boundaryReflectedGradientV480,complexGradient,hzpoint] using hi
      ext v
      have hv : v = ∑ i : Fin 2, v i • coordinateVector 2 i := by
        ext i
        fin_cases i <;> simp [Fin.sum_univ_two,coordinateVector,PiLp.single_apply]
      rw [hv,map_sum]
      apply Finset.sum_eq_zero
      intro i _
      have hcoord : planarGradient (boundaryReflectedV480 F W.v) x i =
          fderiv ℝ (boundaryReflectedV480 F W.v) x (coordinateVector 2 i) := by
        fin_cases i <;> simp [planarGradient,coordinateVector,Fin.sum_univ_two]
      rw [map_smul,← hcoord,hgrad]
      simp
    have hvAll : EqOn (boundaryReflectedV480 F W.v) (fun _ => 0) (disc F.targetR) := by
      intro x hx
      have hh := (convex_ball (0 : E2) F.targetR).is_const_of_fderivWithin_eq_zero
        (hu.differentiableOn (by norm_num))
        (fun y hy => (fderivWithin_of_isOpen Metric.isOpen_ball hy).trans (hdAll y hy))
        hx (Metric.mem_ball_self F.targetR_pos)
      exact hh.trans hv0
    apply False.elim
    apply hnot
    intro x hx
    have hh := hvAll hx.2.2.1
    have hz0 : 0 ≤ (F.chart x) 1 := hx.2.2.2.le
    change boundaryReflectedV480 F W.v (F.chart x) = 0 at hh
    simpa only [boundaryReflectedV480,oddReflect,if_pos hz0,
      boundaryVhatV480,F.chart.left_inv hx.2.1] using hh
  · exact horder

variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}

/-- Actual arbitrary original-pair boundary finite order, retaining the
same height, positive solution, centered coordinate change and reflected gradient. -/
theorem original_pair_actual_boundary_reflected_finite_order_v480
    (D : OriginalPair g J) (a0 : D.A.1.surface) (b0 : D.B.1.surface) {p : E.Carrier}
    (hp : p ∈ (𝓡∂ 3).boundary E.Carrier)
    (c : ActualBoundaryPairGraphV480 D.A.1.embedding D.B.1.embedding p)
    (hc : 0 < c.coefficient)
    (hboundary : D.A.1.embedding.toFun '' D.A.1.surface.boundary =
      D.B.1.embedding.toFun '' D.B.1.surface.boundary) :
    ∃ N : BoundaryNormalizationDataV480, ∃ W : BoundaryNormalizedWindowV480,
    ∃ F : BoundaryIsothermalPatchV480 W.R W.A,
      c.z ∈ N.O ∧ N.O ⊆ c.O ∧ N.u = c.height ∧
      W.v = (fun y => N.v (coordinateSwap y+c.z)) ∧
      W.O ⊆ (fun y => coordinateSwap y+c.z) ⁻¹' N.O ∧
      ∃ m : ℕ, 1 ≤ m ∧ ∃ delta c1 c2 : ℝ,
        0 < delta ∧ delta < F.targetR ∧ 0 < c1 ∧ 0 < c2 ∧
        (∀ z ∈ Metric.ball (0 : ℂ) delta,
          c1 * ‖z‖ ^ m ≤ ‖boundaryReflectedGradientV480 F W.v z‖ ∧
          ‖boundaryReflectedGradientV480 F W.v z‖ ≤ c2 * ‖z‖ ^ m) := by
  obtain ⟨N,hzN,hNO,hNu,hflat,hclass⟩ :=
    original_pair_actual_boundary_normalization_v480 D a0 b0 hp c hc hboundary
  obtain ⟨W,hWv,hWO⟩ := boundary_normalized_window_v480 N c.z hzN c.base_flat hflat
  obtain ⟨F⟩ := boundary_actual_isothermal_patch_exists_v480 W
  have hnot := original_pair_boundary_window_no_zero_v480 D c hc N hNu hNO W hWv hWO F
  have hu0 : N.u c.z = 0 := hNu ▸ c.height_zero
  have hdu0 : fderiv ℝ N.u c.z = 0 := hNu ▸ c.height_tangent
  have hdNv : fderiv ℝ N.v c.z = 0 := by
    have hud := (N.smooth_u.contDiffAt (N.isOpen_O.mem_nhds hzN)).differentiableAt (by simp)
    have hhd := (N.smooth_h.contDiffAt (N.isOpen_O.mem_nhds hzN)).differentiableAt (by simp)
    change fderiv ℝ (fun x => N.u x/N.h x) c.z = 0
    simp only [div_eq_mul_inv]
    simpa only [Pi.inv_apply,hdu0,hu0,zero_smul,smul_zero,add_zero] using
      fderiv_fun_mul hud (hhd.inv (N.h_positive c.z hzN).ne')
  have hdW0 : fderiv ℝ W.v 0 = 0 := by
    rw [hWv]
    change fderiv ℝ (N.v ∘ (fun y => coordinateSwap y+c.z)) 0 = 0
    have hvd : DifferentiableAt ℝ N.v c.z := by
      change DifferentiableAt ℝ (fun x => N.u x/N.h x) c.z
      exact ((N.smooth_u.div N.smooth_h (fun x hx => (N.h_positive x hx).ne')).contDiffAt
        (N.isOpen_O.mem_nhds hzN)).differentiableAt (by simp)
    have hψ : DifferentiableAt ℝ (fun y : E2 => coordinateSwap y+c.z) 0 :=
      coordinateSwap.toContinuousLinearEquiv.differentiableAt.add_const c.z
    rw [fderiv_comp 0 (by simpa only [map_zero,zero_add] using hvd) hψ,
      map_zero,zero_add,hdNv,ContinuousLinearMap.zero_comp]
  exact ⟨N,W,F,hzN,hNO,hNu,hWv,hWO,boundary_reflected_finite_order_v480 W F hdW0 hnot⟩

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3BoundaryCommonPointV480 -/

noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
set_option maxHeartbeats 600000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

private theorem common_point_base_v480 (x : E2) (t : ℝ) :
    native_collar_base_v475 (graphPoint x t) = x := by
  ext i
  fin_cases i <;> simp [native_collar_base_v475,graphPoint]

/-- Every actual interior common point in the boundary graph lies over a
positive planar point and is a zero of the same literal graph height. -/
theorem actual_boundary_graph_interior_common_point_v480
    {S B : CompactOrientedSurface.{0}}
    (f : NeatEmbedding S E.Carrier) (gb : NeatEmbedding B E.Carrier) {p q : E.Carrier}
    (c : ActualBoundaryPairGraphV480 f gb p)
    (hqC : E.toSphere q ∈ c.coordinates.chart.source)
    (hqI : q ∈ (𝓡∂ 3).interior E.Carrier)
    (hqA : q ∈ range f.toFun) (hqB : q ∈ range gb.toFun) :
    let x := native_collar_base_v475 (c.coordinates.chart (E.toSphere q))
    x ∈ c.O ∧ 0 < x 0 ∧ c.height x = 0 ∧
      c.coordinates.chart (E.toSphere q) = graphPoint x 0 := by
  obtain ⟨a,ha⟩ := hqA
  obtain ⟨b,hb⟩ := hqB
  have hhA : E.toSphere q ∈ range (E.toSphere ∘ f.toFun) ∩ c.coordinates.chart.source :=
    ⟨⟨a,congrArg E.toSphere ha⟩,hqC⟩
  have hhB : E.toSphere q ∈ range (E.toSphere ∘ gb.toFun) ∩ c.coordinates.chart.source :=
    ⟨⟨b,congrArg E.toSphere hb⟩,hqC⟩
  rw [c.graph_A] at hhA
  rw [c.graph_B] at hhB
  obtain ⟨x,⟨hx,hx0⟩,heA⟩ := hhA
  obtain ⟨y,⟨hy,hy0⟩,heB⟩ := hhB
  have hcoord : c.coordinates.chart (E.toSphere q) = graphPoint x 0 := by
    rw [← heA]
    exact c.coordinates.chart.right_inv (c.points_inside x hx).1
  have hxy : graphPoint x 0 = graphPoint y (c.height y) := by
    have hh := congrArg c.coordinates.chart (heA.trans heB.symm)
    rwa [c.coordinates.chart.right_inv (c.points_inside x hx).1,
      c.coordinates.chart.right_inv (c.points_inside y hy).2] at hh
  have hxy' : x = y := by
    simpa only [common_point_base_v480] using congrArg native_collar_base_v475 hxy
  subst y
  have hheight : c.height x = 0 := by
    have hh := congrArg (fun v : E3 => v 2) hxy
    change 0 = c.height x at hh
    exact hh.symm
  have hxpos : 0 < x 0 := by
    apply lt_of_le_of_ne hx0
    intro hxzero
    have hqBound : E.toSphere q ∈ (E.toSphere ∘ f.toFun) '' S.boundary ∩ c.coordinates.chart.source := by
      rw [c.boundary_A]
      exact ⟨x,⟨hx,hxzero.symm⟩,heA⟩
    obtain ⟨a0,ha0,he0⟩ := hqBound.1
    have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
    have hqa : f.toFun a0 = q := hinc.isEmbedding.injective he0
    have hqb : q ∈ (𝓡∂ 3).boundary E.Carrier := by
      have hh : f.toFun a0 ∈ (𝓡∂ 3).boundary E.Carrier := by rwa [← f.boundary_preimage] at ha0
      rwa [hqa] at hh
    exact (ModelWithCorners.disjoint_interior_boundary (I := 𝓡∂ 3) (M := E.Carrier)).le_bot ⟨hqI,hqb⟩
  dsimp only
  rw [hcoord,common_point_base_v480]
  exact ⟨hx,hxpos,hheight,rfl⟩

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3ActualBoundaryTangencyExclusionV480 -/

noncomputable section
open Set Topology Function Filter MeasureTheory
open scoped ContDiff NNReal ENNReal Manifold
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
set_option maxHeartbeats 600000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}

private theorem exclusion_base_v480 (x : E2) (t : ℝ) :
    native_collar_base_v475 (graphPoint x t) = x := by
  ext i
  fin_cases i <;> simp [native_collar_base_v475,graphPoint]

/-- The actual arbitrary shared-boundary graph has an ambient neighborhood
of its boundary base point containing no interior tangency. -/
theorem actual_boundary_positive_graph_excludes_tangencies_v480
    (D : OriginalPair g J) (a0 : D.A.1.surface) (b0 : D.B.1.surface) {p : E.Carrier}
    (hp : p ∈ (𝓡∂ 3).boundary E.Carrier)
    (c : ActualBoundaryPairGraphV480 D.A.1.embedding D.B.1.embedding p)
    (hc : 0 < c.coefficient)
    (hboundary : D.A.1.embedding.toFun '' D.A.1.surface.boundary =
      D.B.1.embedding.toFun '' D.B.1.surface.boundary) :
    ∃ U : Set E.Carrier, IsOpen U ∧ p ∈ U ∧
      Disjoint U (interiorTangencies D.A.1.embedding D.B.1.embedding) := by
  obtain ⟨N,W,F,hzN,hNO,hNu,hWv,hWO,m,hm,delta,c1,c2,hd,hdR,hc1,hc2,hbounds⟩ :=
    original_pair_actual_boundary_reflected_finite_order_v480 D a0 b0 hp c hc hboundary
  obtain ⟨hNv,hNvb,hNdb,hFd,hFi,hvd,hvg,hvc,hgc,hvb,hgb,hH1⟩ :=
    boundary_chart_first_jets_H1_v480 W F
  have h0S : (0 : E2) ∈ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc F.sourceR :=
    ⟨Metric.mem_closedBall_self F.sourceR_pos.le,by simp⟩
  have h0W : (0 : E2) ∈ W.O := W.contains ⟨Metric.mem_closedBall_self W.R_pos.le,by simp⟩
  have hn : ∀ᶠ y in 𝓝 (0 : E2), y ∈ W.O ∧ y ∈ disc F.sourceR ∧
      F.chart y ∈ disc delta := by
    filter_upwards [W.O_open.mem_nhds h0W,
      Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self F.sourceR_pos),
      (hFd 0 h0S).continuousAt.preimage_mem_nhds
        (by rw [F.base]; exact Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hd))]
      with y hyW hyS hyT
    exact ⟨hyW,hyS,hyT⟩
  obtain ⟨s,hs,hnear⟩ := Metric.eventually_nhds_iff.mp hn
  let ψ : E2 → E2 := fun x => coordinateSwap (x-c.z)
  let P : Set E2 := ψ ⁻¹' Metric.ball 0 s
  have hP : IsOpen P := Metric.isOpen_ball.preimage
    (coordinateSwap.continuous.comp (continuous_id.sub continuous_const))
  have hbaseCont : Continuous native_collar_base_v475 := by unfold native_collar_base_v475;fun_prop
  let Z : Set ThreeSphere := c.coordinates.chart.source ∩
    c.coordinates.chart ⁻¹' (native_collar_base_v475 ⁻¹' P)
  have hZ : IsOpen Z := c.coordinates.chart.isOpen_inter_preimage (hP.preimage hbaseCont)
  let U : Set E.Carrier := E.toSphere ⁻¹' Z
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  have hU : IsOpen U := hZ.preimage hinc.isEmbedding.continuous
  have hpU : p ∈ U := by
    refine ⟨c.base_mem,?_⟩
    change ψ (native_collar_base_v475 (c.coordinates.chart (E.toSphere p))) ∈ Metric.ball 0 s
    rw [c.base_value,exclusion_base_v480]
    simpa only [ψ,sub_self,map_zero] using Metric.mem_ball_self hs
  refine ⟨U,hU,hpU,?_⟩
  rw [Set.disjoint_left]
  intro q hqU hqt
  have hqC := hqU.1
  obtain ⟨hqI,aq,bq,haq,hbq,htq⟩ := hqt
  have hqt' : q ∈ interiorTangencies D.A.1.embedding D.B.1.embedding :=
    ⟨hqI,aq,bq,haq,hbq,htq⟩
  let x := native_collar_base_v475 (c.coordinates.chart (E.toSphere q))
  obtain ⟨hxO,hxpos,hxzero,hcoord⟩ := actual_boundary_graph_interior_common_point_v480
    _ _ c hqC hqI ⟨aq,haq⟩ ⟨bq,hbq⟩
  have hdheight : fderiv ℝ c.height x = 0 :=
    actual_boundary_graph_tangency_critical_v480 _ _ c hqC hqt'
  let y := ψ x
  have hyball : y ∈ Metric.ball 0 s := hqU.2
  obtain ⟨hyW,hyS,hyT⟩ := hnear (Metric.mem_ball.mp hyball)
  have hypos : 0 < y 1 := by
    simpa only [y,ψ,coordinateSwap_one,PiLp.sub_apply,c.base_flat,sub_zero] using hxpos
  have hyhalf : y ∈ halfDisc F.sourceR := ⟨hyS,hypos⟩
  have hySrc : y ∈ F.chart.source := F.source_contains
    ⟨Metric.ball_subset_closedBall hyS,hypos.le⟩
  let w : E2 := F.chart y
  have hwpos : 0 < w 1 := F.forward_interior y hyhalf
  have hwT : w ∈ halfDisc F.targetR := ⟨Metric.ball_subset_ball hdR.le hyT,hwpos⟩
  have hψeq : coordinateSwap y+c.z = x := by simp only [y,ψ,coordinateSwap_involutive,sub_add_cancel]
  have hxN : x ∈ N.O := by
    have hh := hWO hyW
    change coordinateSwap y+c.z ∈ N.O at hh
    rwa [hψeq] at hh
  have hu0 : N.u x = 0 := hNu ▸ hxzero
  have hdu0 : fderiv ℝ N.u x = 0 := hNu ▸ hdheight
  have hvNx : DifferentiableAt ℝ N.v x := by
    change DifferentiableAt ℝ (fun t => N.u t/N.h t) x
    exact ((N.smooth_u.div N.smooth_h (fun t ht => (N.h_positive t ht).ne')).contDiffAt
      (N.isOpen_O.mem_nhds hxN)).differentiableAt (by simp)
  have hdNv : fderiv ℝ N.v x = 0 := by
    have hud := (N.smooth_u.contDiffAt (N.isOpen_O.mem_nhds hxN)).differentiableAt (by simp)
    have hhd := (N.smooth_h.contDiffAt (N.isOpen_O.mem_nhds hxN)).differentiableAt (by simp)
    change fderiv ℝ (fun t => N.u t/N.h t) x = 0
    simp only [div_eq_mul_inv]
    simpa only [Pi.inv_apply,hdu0,hu0,zero_smul,smul_zero,add_zero] using
      fderiv_fun_mul hud (hhd.inv (N.h_positive x hxN).ne')
  have hdW : fderiv ℝ W.v y = 0 := by
    rw [hWv]
    change fderiv ℝ (N.v ∘ (fun t => coordinateSwap t+c.z)) y = 0
    have hψd : DifferentiableAt ℝ (fun t : E2 => coordinateSwap t+c.z) y :=
      coordinateSwap.toContinuousLinearEquiv.differentiableAt.add_const c.z
    rw [fderiv_comp y (hψeq.symm ▸ hvNx) hψd,
      hψeq,hdNv,ContinuousLinearMap.zero_comp]
  have hVhat : fderiv ℝ (boundaryVhatV480 F W.v) w = 0 := by
    have hWd := (W.smooth_v.contDiffAt (W.O_open.mem_nhds hyW)).differentiableAt (by simp)
    have hwi : w ∈ SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc F.targetR :=
      ⟨Metric.ball_subset_closedBall hwT.1,hwT.2.le⟩
    have hi := hFi w hwi
    have hsym : F.chart.symm w = y := F.chart.left_inv hySrc
    change fderiv ℝ (W.v ∘ F.chart.symm) w = 0
    rw [fderiv_comp w (hsym.symm ▸ hWd) hi,hsym,hdW,ContinuousLinearMap.zero_comp]
  have hReflected : fderiv ℝ (boundaryReflectedV480 F W.v) w = 0 := by
    have hevent : boundaryReflectedV480 F W.v =ᶠ[𝓝 w] boundaryVhatV480 F W.v := by
      have hposN := (isOpen_lt continuous_const
        (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous).mem_nhds hwpos
      filter_upwards [hposN] with t ht
      have ht' : 0 < t 1 := ht
      change (if 0 ≤ t 1 then boundaryVhatV480 F W.v t else
        -boundaryVhatV480 F W.v (reflectPoint t)) = boundaryVhatV480 F W.v t
      rw [if_pos ht'.le]
    rw [hevent.fderiv_eq,hVhat]
  let z : ℂ := ⟨w 0,w 1⟩
  have hpoint : complexPoint z = w := by ext i;fin_cases i <;> simp [complexPoint,z]
  have hnorm : ‖z‖ = ‖w‖ := by
    let e : ℂ ≃ₗᵢ[ℝ] E2 := Complex.orthonormalBasisOneI.repr
    have hh : e z = w := hpoint
    exact hh ▸ (e.norm_map z).symm
  have hzball : z ∈ Metric.ball 0 delta := by
    rw [Metric.mem_ball,dist_zero_right,hnorm]
    simpa only [disc,Metric.mem_ball,dist_zero_right] using hyT
  have hz0 : z ≠ 0 := by
    intro hh
    have hi := congrArg Complex.im hh
    change w 1 = 0 at hi
    exact hwpos.ne' hi
  have hwzero : boundaryReflectedGradientV480 F W.v z = 0 := by
    simp [boundaryReflectedGradientV480,complexGradient,hpoint,planarGradient,hReflected]
  have hbound := (hbounds z hzball).1
  rw [hwzero,norm_zero] at hbound
  exact (mul_pos hc1 (pow_pos (norm_pos_iff.mpr hz0) m)).not_ge hbound

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- PAID OWNED SUPPORT: B3OriginalArbitraryPairGlobalV480 -/

noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}
set_option maxHeartbeats 600000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- Every actual native boundary tangent point of an arbitrary original
pair has an ambient neighborhood free of interior tangencies. Both signs of
the actual halfspace normal projection are handled. -/
theorem original_pair_actual_boundary_tangencies_excluded_v480 (D : OriginalPair g J)
    {p : E.Carrier} (hp : p ∈ (𝓡∂ 3).boundary E.Carrier)
    (ht : p ∈ (fun q : D.A.1.surface × D.B.1.surface => D.A.1.embedding.toFun q.1) ''
      nativeTangencyPairs_v480 D.A.1.embedding D.B.1.embedding) :
    ∃ U : Set E.Carrier, IsOpen U ∧ p ∈ U ∧
      Disjoint U (interiorTangencies D.A.1.embedding D.B.1.embedding) := by
  obtain ⟨c⟩ := original_pair_boundary_tangency_actual_graph_v480 D hp ht
  rcases lt_or_gt_of_ne c.coefficient_ne with hc | hc
  · let U : Set E.Carrier := E.toSphere ⁻¹' c.coordinates.chart.source
    have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
    refine ⟨U,c.coordinates.chart.open_source.preimage hinc.isEmbedding.continuous,
      c.base_mem,?_⟩
    rw [Set.disjoint_left]
    intro q hqU hqt
    obtain ⟨hqI,a,b,ha,hb,htq⟩ := hqt
    exact Set.disjoint_left.mp (boundary_graph_reversed_excludes_interior_v480 _ _ c hc)
      ⟨hqU,hqI⟩ ⟨⟨a,ha⟩,⟨b,hb⟩⟩
  · obtain ⟨⟨a,b⟩,⟨hab,hplane⟩,ha⟩ := ht
    change D.A.1.embedding.toFun a = p at ha
    have hb : D.B.1.embedding.toFun b = p := hab.symm.trans ha
    have haB : a ∈ D.A.1.surface.boundary := by
      rw [← D.A.1.embedding.boundary_preimage]
      change D.A.1.embedding.toFun a ∈ (𝓡∂ 3).boundary E.Carrier
      rwa [ha]
    have hbB : b ∈ D.B.1.surface.boundary := by
      rw [← D.B.1.embedding.boundary_preimage]
      change D.B.1.embedding.toFun b ∈ (𝓡∂ 3).boundary E.Carrier
      rwa [hb]
    have hbound := original_pair_common_boundary_exact_v480 D
      (show p ∈ D.A.1.embedding.toFun '' D.A.1.surface.boundary from ⟨a,haB,ha⟩)
      (show p ∈ D.B.1.embedding.toFun '' D.B.1.surface.boundary from ⟨b,hbB,hb⟩)
    exact actual_boundary_positive_graph_excludes_tangencies_v480 D a b hp c hc hbound

/-- Actual boundary exclusion makes the original interior tangency locus
closed inside the compact native tangent-pair image. -/
theorem original_pair_interior_tangencies_compact_v480 (D : OriginalPair g J) :
    IsCompact (interiorTangencies D.A.1.embedding D.B.1.embedding) := by
  let P : Set E.Carrier :=
    (fun q : D.A.1.surface × D.B.1.surface => D.A.1.embedding.toFun q.1) ''
      nativeTangencyPairs_v480 D.A.1.embedding D.B.1.embedding
  let Γ := interiorTangencies D.A.1.embedding D.B.1.embedding
  have hP : IsCompact P := native_tangent_point_image_compact_v480 _ _
  have hΓ : Γ = P ∩ (𝓡∂ 3).interior E.Carrier :=
    interior_tangencies_eq_native_pair_image_v480 _ _
  have hΓP : Γ ⊆ P := hΓ ▸ inter_subset_left
  have hopen : IsOpen Γᶜ := by
    apply isOpen_iff_mem_nhds.mpr
    intro p hpΓ
    by_cases hpP : p ∈ P
    · have hpB : p ∈ (𝓡∂ 3).boundary E.Carrier := by
        rw [← (𝓡∂ 3).compl_interior]
        intro hpI
        exact hpΓ (hΓ ▸ (show p ∈ P ∩ (𝓡∂ 3).interior E.Carrier from ⟨hpP,hpI⟩))
      obtain ⟨U,hU,hpU,hd⟩ := original_pair_actual_boundary_tangencies_excluded_v480 D hpB hpP
      exact mem_of_superset (hU.mem_nhds hpU) (fun q hq => Set.disjoint_left.mp hd hq)
    · exact mem_of_superset (hP.isClosed.isOpen_compl.mem_nhds hpP)
        (fun q hq hqΓ => hq (hΓP hqΓ))
  have hclosed : IsClosed Γ := isOpen_compl_iff.mp hopen
  have hc := hP.inter_right hclosed
  rwa [inter_eq_right.mpr hΓP] at hc

/-- Full original B3 for arbitrary original inputs: actual normal graph,
literal PDE, integer derivative bounds, isolated critical point, both signs,
and global finiteness, with no boundary configuration supplied. -/
theorem original_pair_full_B3_all_clauses_v480 (D : OriginalPair g J) :
    InteriorTangencyConclusion D ∧
      (interiorTangencies D.A.1.embedding D.B.1.embedding).Finite := by
  have hlocal := original_pair_interior_tangency_conclusion_v480 D
  refine ⟨hlocal,compact_isolated_set_finite_v480 _
    (original_pair_interior_tangencies_compact_v480 D) ?_⟩
  intro p hp
  obtain ⟨U,hU,hpU,hUt⟩ := (hlocal p hp).1
  exact ⟨U,hU,hUt⟩

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480


noncomputable section
open Set Topology Function MeasureTheory Bundle
open scoped Manifold ContDiff BigOperators ENNReal
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
/-- Appendix B.3, Proposition 5.7(1),(3); (2) is the exact inherited B1 graph below. -/
theorem B3_original_interior {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}
    (D : OriginalPair g J) :
    InteriorTangencyConclusion D ∧ (interiorTangencies D.A.1.embedding D.B.1.embedding).Finite := by
  exact original_pair_full_B3_all_clauses_v480 D

#print axioms B3_original_interior
end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

end

section
/- Exact paid support from B3HalfSpaceBoundaryOpenV480.lean; imports and diagnostic axiom prints removed only. -/

noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.AppendixACoordinates
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

private def reflectFirst_v480 (x : E3) : E3 :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm ![-x 0,x 1,x 2]
private def foldFirst_v480 (x : E3) : EuclideanHalfSpace 3 :=
  ⟨(EuclideanSpace.equiv (Fin 3) ℝ).symm ![|x 0|,x 1,x 2],by simp⟩
private theorem reflect_first_continuous_v480 : Continuous reflectFirst_v480 := by
  apply (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous.comp
  apply continuous_pi
  intro i
  fin_cases i <;> first | exact (PiLp.continuous_apply 2 _ 0).neg | exact PiLp.continuous_apply 2 _ 1 | exact PiLp.continuous_apply 2 _ 2
private theorem fold_first_continuous_v480 : Continuous foldFirst_v480 := by
  apply Continuous.subtype_mk
  apply (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous.comp
  apply continuous_pi
  intro i
  fin_cases i <;> first | exact (PiLp.continuous_apply 2 _ 0).abs | exact PiLp.continuous_apply 2 _ 1 | exact PiLp.continuous_apply 2 _ 2
private theorem reflect_first_involutive_v480 : Involutive reflectFirst_v480 := by
  intro x
  ext i
  fin_cases i <;> simp [reflectFirst_v480]
private theorem reflect_first_eq_self_v480 {x : E3} (h : x 0 = 0) : reflectFirst_v480 x = x := by
  ext i
  fin_cases i <;> simp [reflectFirst_v480,h]
private theorem fold_first_val_v480 {x : E3} (h : 0 ≤ x 0) : (foldFirst_v480 x).val = x := by
  ext i
  fin_cases i <;> simp [foldFirst_v480,abs_of_nonneg h]
private theorem fold_first_val_negative_v480 {x : E3} (h : x 0 ≤ 0) :
    (foldFirst_v480 x).val = reflectFirst_v480 x := by
  ext i
  fin_cases i <;> simp [foldFirst_v480,reflectFirst_v480,abs_of_nonpos h]

/-- Doubling across the flat boundary proves relative openness for a literal
boundary-preserving half-space embedding. -/
theorem halfspace_boundary_preserving_open_image_v480
    (f : EuclideanHalfSpace 3 → EuclideanHalfSpace 3) {U : Set (EuclideanHalfSpace 3)}
    (hU : IsOpen U) (hf : ContinuousOn f U) (hinj : InjOn f U)
    (hboundary : ∀ x ∈ U, (f x).val 0 = 0 ↔ x.val 0 = 0) :
    IsOpen (f '' U) := by
  let V : Set E3 := foldFirst_v480 ⁻¹' U
  have hV : IsOpen V := hU.preimage fold_first_continuous_v480
  let G : E3 → E3 := fun x =>
    if 0 ≤ x 0 then (f (foldFirst_v480 x)).val
      else reflectFirst_v480 (f (foldFirst_v480 x)).val
  have hGc : ContinuousOn G V := by
    rw [continuousOn_iff_continuous_restrict]
    have hfc : Continuous (fun x : V => (f (foldFirst_v480 x.val)).val) :=
      continuous_subtype_val.comp (hf.comp_continuous
        (fold_first_continuous_v480.comp continuous_subtype_val) (fun x => x.property))
    exact continuous_if_le continuous_const
      ((PiLp.continuous_apply 2 _ 0).comp continuous_subtype_val)
      hfc.continuousOn (reflect_first_continuous_v480.comp hfc).continuousOn
      (fun x hx => (reflect_first_eq_self_v480
        ((hboundary (foldFirst_v480 x.val) x.property).mpr
          (by simp [foldFirst_v480,← hx]))).symm)
  have hGi : InjOn G V := by
    intro x hx y hy hxy
    have hfx := (f (foldFirst_v480 x)).property
    have hfy := (f (foldFirst_v480 y)).property
    by_cases hxpos : 0 ≤ x 0 <;> by_cases hypos : 0 ≤ y 0
    · have he : f (foldFirst_v480 x) = f (foldFirst_v480 y) :=
        Subtype.ext (by simpa [G,hxpos,hypos] using hxy)
      have he' := congrArg Subtype.val (hinj hx hy he)
      simpa only [fold_first_val_v480 hxpos,fold_first_val_v480 hypos] using he'
    · have he0 := congrArg (fun z : E3 => z 0) hxy
      have hzero : (f (foldFirst_v480 y)).val 0 = 0 := by
        have hz : (f (foldFirst_v480 x)).val 0 = -(f (foldFirst_v480 y)).val 0 := by
          simpa [G,hxpos,hypos,reflectFirst_v480] using he0
        linarith
      have hy0 := (hboundary _ hy).mp hzero
      have : y 0 = 0 := by simpa [foldFirst_v480] using hy0
      exact False.elim (hypos this.ge)
    · have he0 := congrArg (fun z : E3 => z 0) hxy
      have hzero : (f (foldFirst_v480 x)).val 0 = 0 := by
        have hz : -(f (foldFirst_v480 x)).val 0 = (f (foldFirst_v480 y)).val 0 := by
          simpa [G,hxpos,hypos,reflectFirst_v480] using he0
        linarith
      have hx0 := (hboundary _ hx).mp hzero
      have : x 0 = 0 := by simpa [foldFirst_v480] using hx0
      exact False.elim (hxpos this.ge)
    · have he : f (foldFirst_v480 x) = f (foldFirst_v480 y) :=
        Subtype.ext (reflect_first_involutive_v480.injective
          (by simpa [G,hxpos,hypos] using hxy))
      have he' := congrArg Subtype.val (hinj hx hy he)
      have he'' : reflectFirst_v480 x = reflectFirst_v480 y := by
        simpa only [fold_first_val_negative_v480 (le_of_not_ge hxpos),
          fold_first_val_negative_v480 (le_of_not_ge hypos)] using he'
      exact reflect_first_involutive_v480.injective he''
  have hopen : IsOpen (G '' V) := DifferentialGeometry.Topology.invariance_of_domain_isOpen_image hV hGc hGi
  have heq : f '' U = (Subtype.val : EuclideanHalfSpace 3 → E3) ⁻¹' (G '' V) := by
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      have hfold : foldFirst_v480 x.val = x := Subtype.ext (fold_first_val_v480 x.property)
      exact ⟨x.val,by simpa [V,hfold] using hx,by simp [G,x.property,hfold]⟩
    · rintro ⟨x,hx,hxz⟩
      by_cases hxpos : 0 ≤ x 0
      · exact ⟨foldFirst_v480 x,hx,Subtype.ext (by simpa [G,hxpos] using hxz)⟩
      · have he0 := congrArg (fun w : E3 => w 0) hxz
        have hzero : (f (foldFirst_v480 x)).val 0 = 0 := by
          have hz : -(f (foldFirst_v480 x)).val 0 = z.val 0 := by
            simpa [G,hxpos,reflectFirst_v480] using he0
          linarith [(f (foldFirst_v480 x)).property,z.property]
        have hx0 := (hboundary _ hx).mp hzero
        have : x 0 = 0 := by simpa [foldFirst_v480] using hx0
        exact False.elim (hxpos this.ge)
  rw [heq]
  exact hopen.preimage continuous_subtype_val

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480



/- Exact paid support from B3HalfSpaceManifoldOpenV480.lean; imports and diagnostic axiom prints removed only. -/

noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.AppendixACoordinates
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

/-- The half-space doubling argument applied in actual target charts. -/
theorem halfspace_manifold_boundary_preserving_open_image_v480
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    (f : EuclideanHalfSpace 3 → M) {U : Set (EuclideanHalfSpace 3)}
    (hU : IsOpen U) (hf : ContinuousOn f U) (hinj : InjOn f U)
    (hboundary : ∀ x ∈ U, (𝓡∂ 3).IsBoundaryPoint (f x) ↔ x.val 0 = 0) :
    IsOpen (f '' U) := by
  rw [isOpen_iff_forall_mem_open]
  rintro p ⟨x,hx,rfl⟩
  let c := chartAt (EuclideanHalfSpace 3) (f x)
  let W := U ∩ f ⁻¹' c.source
  have hW : IsOpen W := hf.isOpen_inter_preimage hU c.open_source
  let F : EuclideanHalfSpace 3 → EuclideanHalfSpace 3 := c ∘ f
  have hFc : ContinuousOn F W :=
    c.continuousOn.comp (hf.mono inter_subset_left) (fun y hy => hy.2)
  have hFi : InjOn F W := by
    intro y hy z hz hyz
    exact hinj hy.1 hz.1 (c.injOn hy.2 hz.2 hyz)
  have hFb : ∀ y ∈ W, (F y).val 0 = 0 ↔ y.val 0 = 0 := by
    intro y hy
    have hchart := DifferentialGeometry.Topology.isBoundaryPoint_iff_any_chart_real
      (𝓡∂ 3) hy.2
    have hchart' : (𝓡∂ 3).IsBoundaryPoint (f y) ↔ (F y).val 0 = 0 := by
      change (𝓡∂ 3).IsBoundaryPoint (f y) ↔ (c (f y)).val 0 = 0
      simpa only [frontier_range_modelWithCornersEuclideanHalfSpace,mem_setOf_eq,
        modelWithCornersEuclideanHalfSpace_apply,eq_comm] using hchart
    exact hchart'.symm.trans (hboundary y hy.1)
  have hFo : IsOpen (F '' W) :=
    halfspace_boundary_preserving_open_image_v480 F hW hFc hFi hFb
  have hFtarget : F '' W ⊆ c.target := by
    rintro _ ⟨y,hy,rfl⟩
    exact c.map_source hy.2
  have hopen : IsOpen (f '' W) := by
    have heq : f '' W = c.symm '' (F '' W) := by
      ext p
      constructor
      · rintro ⟨y,hy,rfl⟩
        exact ⟨F y,mem_image_of_mem _ hy,c.left_inv hy.2⟩
      · rintro ⟨q,⟨y,hy,rfl⟩,rfl⟩
        exact ⟨y,hy,(c.left_inv hy.2).symm⟩
    rw [heq]
    exact c.isOpen_image_symm_of_subset_target hFo hFtarget
  exact ⟨f '' W,image_mono inter_subset_left,hopen,
    ⟨x,⟨hx,mem_chart_source _ _⟩,rfl⟩⟩

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480



/- Exact paid support from B3ActualCollarBoundaryNeighborhoodV480.lean; imports and diagnostic axiom prints removed only. -/

noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

/-- Every literal boundary leaf point has an actual open exterior neighborhood
inside any smaller positive half-cylinder. The boundary coverage is derived,
using the original collar embedding and exact boundary-stratum equation. -/
theorem actual_collar_boundary_neighborhood_v480
    (D : B1OriginalData g J) (s : Circle) {r : ℝ} (hr : 0 < r) (hrD : r ≤ D.r0) :
    ∃ O : Set E.Carrier, IsOpen O ∧ D.leafParameter s ∈ O ∧
      O ⊆ D.collar '' halfCylinder r D.eta := by
  obtain ⟨W⟩ := actual_collar_window D s
  let pre : EuclideanHalfSpace 3 → T2Coordinate := fun z =>
    (localCircle D s (z.val 1),z.val 0,z.val 2)
  let U : Set (EuclideanHalfSpace 3) :=
    {z | |z.val 1| < 2 * W.R ∧ z.val 0 < r ∧ |z.val 2| < D.eta}
  let F : EuclideanHalfSpace 3 → E.Carrier := D.collar ∘ pre
  have hU : IsOpen U :=
    (isOpen_lt ((PiLp.continuous_apply 2 _ 1).comp continuous_subtype_val).abs continuous_const).inter
      ((isOpen_lt ((PiLp.continuous_apply 2 _ 0).comp continuous_subtype_val) continuous_const).inter
        (isOpen_lt ((PiLp.continuous_apply 2 _ 2).comp continuous_subtype_val).abs continuous_const))
  have hpre : Continuous pre := by
    have hlocal : Continuous (localCircle D s) := by
      unfold localCircle
      exact continuous_const.mul ((contMDiff_circleExp (m := ∞)).continuous.comp (by fun_prop))
    exact (hlocal.comp ((PiLp.continuous_apply 2 _ 1).comp continuous_subtype_val)).prodMk
      (((PiLp.continuous_apply 2 _ 0).comp continuous_subtype_val).prodMk
        ((PiLp.continuous_apply 2 _ 2).comp continuous_subtype_val))
  have hC : MapsTo pre U (halfCylinder D.r0 D.eta) :=
    fun z hz => ⟨⟨z.property,hz.2.1.le.trans hrD⟩,hz.2.2⟩
  have hFc : ContinuousOn F U := D.collar_smooth.continuousOn.comp hpre.continuousOn hC
  have hFi : InjOn F U := by
    intro z hz w hw he
    have hepre : pre z = pre w := congrArg Subtype.val
      (D.collar_embedding.injective (a₁ := ⟨pre z,hC hz⟩) (a₂ := ⟨pre w,hC hw⟩) he)
    have h1 : z.val 1 = w.val 1 := actual_localCircle_injective_v475 D s W hz.1 hw.1
      (congrArg Prod.fst hepre)
    have h0 : z.val 0 = w.val 0 := congrArg (fun p : T2Coordinate => p.2.1) hepre
    have h2 : z.val 2 = w.val 2 := congrArg (fun p : T2Coordinate => p.2.2) hepre
    apply Subtype.ext
    ext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  have hFb : ∀ z ∈ U, (𝓡∂ 3).IsBoundaryPoint (F z) ↔ z.val 0 = 0 := by
    intro z hz
    exact D.collar_boundary (pre z) (hC hz)
  have hopen : IsOpen (F '' U) :=
    halfspace_manifold_boundary_preserving_open_image_v480 F hU hFc hFi hFb
  have hzero : (0 : EuclideanHalfSpace 3) ∈ U := by
    change |(0 : E3) 1| < 2 * W.R ∧ (0 : E3) 0 < r ∧ |(0 : E3) 2| < D.eta
    simpa only [PiLp.zero_apply,abs_zero] using And.intro (by linarith [W.R_pos] : (0 : ℝ) < 2 * W.R)
      (And.intro hr D.eta_pos)
  have hFzero : F 0 = D.leafParameter s := by
    change D.collar (localCircle D s 0,0,0) = D.leafParameter s
    simpa [localCircle] using D.collar_leaf s
  refine ⟨F '' U,hopen,⟨0,hzero,hFzero⟩,?_⟩
  rintro p ⟨z,hz,rfl⟩
  exact ⟨pre z,⟨⟨z.property,hz.2.1.le⟩,hz.2.2⟩,rfl⟩

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480



/- Exact paid support from B3OriginalCollarFiniteV480.lean; imports and diagnostic axiom prints removed only. -/

noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

/-- The literal radial lower bound excludes actual tangencies from the
smaller half-cylinder, including its boundary face. -/
theorem collar_radial_bound_excludes_smaller_halfCylinder_v480
    (D : B1OriginalData g J) {r : ℝ} (hr : 0 < r) (hrD : r ≤ D.r0)
    (hbound : ∀ p ∈ interiorTangencies D.A.1.embedding D.B.1.embedding,
      r ≤ extendedRadial D r p) :
    Disjoint (D.collar '' halfCylinder (r / 2) D.eta)
      (interiorTangencies D.A.1.embedding D.B.1.embedding) := by
  rw [Set.disjoint_left]
  rintro p ⟨q,hq,hqp⟩ hp
  have hqbig : q ∈ halfCylinder r D.eta :=
    ⟨⟨hq.1.1,hq.1.2.trans (half_le_self hr.le)⟩,hq.2⟩
  have hqD : q ∈ halfCylinder D.r0 D.eta :=
    ⟨⟨hq.1.1,hqbig.1.2.trans hrD⟩,hq.2⟩
  have hext : extendedRadial D r p = q.2.1 := by
    unfold extendedRadial
    rw [ite_eq_left (show p ∈ D.collar '' halfCylinder r D.eta from ⟨q,hqbig,hqp⟩)]
    rw [← hqp,D.radial_exact q hqD]
  have h := hbound p hp
  rw [hext] at h
  linarith [hq.1.2]

/-- The original B1 collar covers every boundary accumulation point, so the
actual interior tangency locus is closed and compact. -/
theorem b1_collar_interior_tangencies_compact_v480
    (D : B1OriginalData g J) {r : ℝ} (hr : 0 < r) (hrD : r ≤ D.r0)
    (hbound : ∀ p ∈ interiorTangencies D.A.1.embedding D.B.1.embedding,
      r ≤ extendedRadial D r p) :
    IsCompact (interiorTangencies D.A.1.embedding D.B.1.embedding) := by
  let Γ := interiorTangencies D.A.1.embedding D.B.1.embedding
  let C := ((fun q : D.A.1.surface × D.B.1.surface => D.A.1.embedding.toFun q.1) ''
    nativeTangencyPairs_v480 D.A.1.embedding D.B.1.embedding)
  have hC : IsCompact C := native_tangent_point_image_compact_v480 _ _
  have hΓC : Γ ⊆ C := by
    change interiorTangencies D.A.1.embedding D.B.1.embedding ⊆ C
    rw [interior_tangencies_eq_native_pair_image_v480]
    exact inter_subset_left
  have hΓclosed : IsClosed Γ := by
    apply isClosed_of_closure_subset
    intro p hp
    have hpC : p ∈ C := closure_minimal hΓC hC.isClosed hp
    have hpinterior : p ∈ (𝓡∂ 3).interior E.Carrier := by
      change (𝓡∂ 3).IsInteriorPoint p
      rw [(𝓡∂ 3).isInteriorPoint_iff_not_isBoundaryPoint]
      intro hpboundary
      obtain ⟨⟨a,b⟩,⟨hab,ht⟩,ha⟩ := hpC
      have hb : D.B.1.embedding.toFun b = p := hab.symm.trans ha
      have hbB : b ∈ D.B.1.surface.boundary := by
        rw [← D.B.1.embedding.boundary_preimage]
        change (𝓡∂ 3).IsBoundaryPoint (D.B.1.embedding.toFun b)
        rwa [hb]
      have hpLeaf : p ∈ J.leaf D.boundaryLabel :=
        D.B_boundary ▸ (show p ∈ D.B.1.embedding.toFun '' D.B.1.surface.boundary from ⟨b,hbB,hb⟩)
      rw [← D.leafParameter_image] at hpLeaf
      obtain ⟨s,hs⟩ := hpLeaf
      obtain ⟨O,hO,hsO,hsub⟩ := actual_collar_boundary_neighborhood_v480 D s
        (half_pos hr) ((half_le_self hr.le).trans hrD)
      have hpO : p ∈ O := hs ▸ hsO
      have hdisjoint := (collar_radial_bound_excludes_smaller_halfCylinder_v480 D hr hrD hbound).mono_left hsub
      obtain ⟨q,hqO,hqΓ⟩ := (mem_closure_iff_nhds.mp hp) O (hO.mem_nhds hpO)
      exact Set.disjoint_left.mp hdisjoint hqO hqΓ
    change p ∈ interiorTangencies D.A.1.embedding D.B.1.embedding
    rw [interior_tangencies_eq_native_pair_image_v480]
    exact ⟨hpC,hpinterior⟩
  exact hΓclosed.isCompact

/-- Full original B3 collar package: regular positive collar, finite boundary
critical set, exact radial bound, and global finite actual interior tangencies. -/
theorem original_b3_collar_all_clauses_v480 (D : B1OriginalData g J) :
    ∃ r0 : ℝ, 0 < r0 ∧ r0 ≤ D.r0 ∧
      (∀ s : Circle, ∀ r : ℝ, 0 < r → r < r0 →
        mfderiv ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ)
          (fun q : Circle × ℝ => D.f q.1 q.2) (s,r) ≠ 0) ∧
      (collarCriticalPoints D).Finite ∧
      (∀ s ∈ collarCriticalPoints D, D.f s 0 = 0) ∧
      (∀ p ∈ interiorTangencies D.A.1.embedding D.B.1.embedding,
        r0 ≤ extendedRadial D r0 p) ∧
      (interiorTangencies D.A.1.embedding D.B.1.embedding).Finite := by
  obtain ⟨r0,hr0,hrD,hreg,hcrit,hzero,havoid,hbound⟩ :=
    original_b3_collar_regular_avoidance_radial_v480 D
  have hlocal := original_pair_interior_tangency_conclusion_v480 (originalPairOfB1 D)
  have hfinite := compact_isolated_set_finite_v480 _
    (b1_collar_interior_tangencies_compact_v480 D hr0 hrD hbound) (by
      intro p hp
      obtain ⟨O,hO,hpO,hOt⟩ := (hlocal p hp).1
      exact ⟨O,hO,hOt⟩)
  exact ⟨r0,hr0,hrD,hreg,hcrit,hzero,hbound,hfinite⟩

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480


noncomputable section
open Set Topology Function MeasureTheory Bundle
open scoped Manifold ContDiff BigOperators ENNReal
namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
/-- (25) with one collar selected before all s,r, and the finite boundary critical set. -/
theorem B3_original_collar {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}
    (D : B1OriginalData g J) :
    ∃ r0 : ℝ, 0 < r0 ∧ r0 ≤ D.r0 ∧
      (∀ s : Circle, ∀ r : ℝ, 0 < r → r < r0 →
        mfderiv ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ) (fun q : Circle × ℝ => D.f q.1 q.2) (s, r) ≠ 0) ∧
      (collarCriticalPoints D).Finite ∧
      (∀ s ∈ collarCriticalPoints D, D.f s 0 = 0) ∧
      (∀ p ∈ interiorTangencies D.A.1.embedding D.B.1.embedding,
        r0 ≤ extendedRadial D r0 p) ∧
      (interiorTangencies D.A.1.embedding D.B.1.embedding).Finite := by
  exact original_b3_collar_all_clauses_v480 D


#print axioms B3_original_collar
end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

end
