import B1InteriorMetricChart_v475 import B1InteriorChartContinuation_v475 import B1ActualAmbientFlowMinimum_v475 import B1ActualFixedBoundaryMinima_v475 import B1InteriorCylinderPDE_v475 import B1InteriorCoefficientMeanValue_v475 import A3MetricVariationBridges import B1ActualGermLocusClosed_v475 import B1InteriorLocalZeroContinuation_v475 import Mathlib.Analysis.Complex.Polynomial.Basic import Mathlib.FieldTheory.IsAlgClosed.Basic import B1ActualCommonInteriorGraph_v475 import B1InteriorCommonCylinder_v475 import B1ActualCollarGraphUniqueness_v475 import B1CollarWindow_v468 import B1ActualGeometry_v468 import Mathlib.Topology.DiscreteSubset import Mathlib.Analysis.Normed.Module.ContinuousInverse import Mathlib.Analysis.Normed.Operator.CompleteCodomain import Mathlib.Analysis.Normed.Module.FiniteDimension import Mathlib.Analysis.Normed.Ring.Units import Mathlib.Geometry.Manifold.ContMDiffMFDeriv import DifferentialGeometry.Topology.InvarianceOfDomainManifold import B1ActualCollarTopology_v475 import OriginalB1
import B1TangencyGraph
import KnotLinkConditions
import KnotGenus
import Section5Combinatorics
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Topology.Covering.Basic

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

/-- Appendix B.3, Proposition 5.7(1),(3); (2) is the exact inherited B1 graph below. -/
theorem B3_original_interior {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}
    (D : OriginalPair g J) :
    InteriorTangencyConclusion D ∧ (interiorTangencies D.A.1.embedding D.B.1.embedding).Finite := by
  sorry

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
  sorry

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
theorem B4_original_T2 {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}
    (setting : RelativeSourceSetting g J) (nontrivial : KnotIsNontrivial K)
    (D : B1OriginalData g J) (S : IncompressibleSpanningSurface.{0} E)
    (S_minimum : IsRelativeAreaMinimizer g J S)
    (S_A : Disjoint S.1.image D.A.1.image) (S_B : Disjoint S.1.image D.B.1.image)
    (S_A_distance : (oneSkeleton E).dist (vertexOf S) (vertexOf D.A) = 1)
    (S_B_distance : (oneSkeleton E).dist (vertexOf S) (vertexOf D.B) = 1) :
    ∃ package : T2Endpoint D S, ∃ up down : Vertex.{0} E,
      SeifertSurfaces.Section5.Combinatorics.IsExchangePair (oneSkeleton E)
        (SeifertSurfaces.GenusLinking.vertexGenus E) (relativeVertexArea g J)
        (vertexOf S) (vertexOf D.B) (vertexOf D.A) up down := by
  sorry

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

/-- One original T1 producer: (45)--(48), all B.5 clauses, uniform widths/no-disc,
and Theorem 5.1(a)--(d), with fixed outputs before z. -/
theorem B5_original_T1 {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}
    (setting : RelativeSourceSetting g J) (nontrivial : KnotIsNontrivial K)
    (D : OriginalPair g J)
    (boundaries : Disjoint (exteriorBoundary D.A.1.embedding) (exteriorBoundary D.B.1.embedding))
    (tangency_nonempty : (interiorTangencies D.A.1.embedding D.B.1.embedding).Nonempty)
    (S : IncompressibleSpanningSurface.{0} E) (S_minimum : IsRelativeAreaMinimizer g J S)
    (S_A : Disjoint S.1.image D.A.1.image) (S_B : Disjoint S.1.image D.B.1.image)
    (S_A_distance : (oneSkeleton E).dist (vertexOf S) (vertexOf D.A) = 1)
    (S_B_distance : (oneSkeleton E).dist (vertexOf S) (vertexOf D.B) = 1) :
    ∃ package : T1Endpoint D S, ∃ up down : Vertex.{0} E,
      SeifertSurfaces.Section5.Combinatorics.IsExchangePair (oneSkeleton E)
        (SeifertSurfaces.GenusLinking.vertexGenus E) (relativeVertexArea g J)
        (vertexOf S) (vertexOf D.B) (vertexOf D.A) up down := by
  sorry

end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480

/- Exact paid support from B3InteriorCenteredChartV480.lean; imports and diagnostic axiom prints removed only. -/
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


/- Exact paid support from B3TwoHeightActualPDEV480.lean; imports and diagnostic axiom prints removed only. -/
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


/- Exact paid support from B3InteriorGraphSphereChartV480.lean; imports and diagnostic axiom prints removed only. -/
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


/- Exact paid support from B3InteriorGraphActualPDEV480.lean; imports and diagnostic axiom prints removed only. -/
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


/- Exact paid support from B3AffineMeanValueV480.lean; imports and diagnostic axiom prints removed only. -/
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


/- Exact paid support from B3TwoHeightCoefficientDataV480.lean; imports and diagnostic axiom prints removed only. -/
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


/- Exact paid support from B3TwoHeightCoefficientTubeV480.lean; imports and diagnostic axiom prints removed only. -/
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


/- Exact paid support from B3TwoHeightEndpointMeanValueV480.lean; imports and diagnostic axiom prints removed only. -/
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


/- Exact paid support from B3TwoHeightResidualV480.lean; imports and diagnostic axiom prints removed only. -/
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


/- Exact paid support from B3TwoHeightEllipticityV480.lean; imports and diagnostic axiom prints removed only. -/
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


/- Exact paid support from B3TwoHeightLinearEquationV480.lean; imports and diagnostic axiom prints removed only. -/

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


/- Exact paid support from B3InteriorGraphLinearEquationV480.lean; imports and diagnostic axiom prints removed only. -/

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


/- Exact paid support from B3InteriorGraphNoncoincidenceV480.lean; imports and diagnostic axiom prints removed only. -/

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


/- Exact paid support from B3InteriorFiniteOrderV480.lean; imports and diagnostic axiom prints removed only. -/

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


/- Exact paid support from B3InteriorFiniteOrderTransportV480.lean; imports and diagnostic axiom prints removed only. -/
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


/- Exact paid support from B3InteriorSignsV480.lean; imports and diagnostic axiom prints removed only. -/

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


/- Exact paid support from B3InteriorSignTransportV480.lean; imports and diagnostic axiom prints removed only. -/

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


/- Exact paid support from B3InteriorAnalyticConclusionV480.lean; imports and diagnostic axiom prints removed only. -/

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


/- Exact paid support from B3TangencySliceDerivativeV480.lean; imports and diagnostic axiom prints removed only. -/

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


/- Exact paid support from B3ArbitraryTangencyGraphV480.lean; imports and diagnostic axiom prints removed only. -/

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


/- Exact paid support from B3ArbitraryCommonSliceGraphV480.lean; imports and diagnostic axiom prints removed only. -/
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


/- Exact paid support from B3SphereChartExteriorV480.lean; imports and diagnostic axiom prints removed only. -/

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


/- Exact paid support from B3ArbitraryCommonCylinderV480.lean; imports and diagnostic axiom prints removed only. -/

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


/- Exact paid support from B3ActualInteriorGraphConstructionV480.lean; imports and diagnostic axiom prints removed only. -/

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


/- Exact paid support from B3ActualGraphAnalyticPackageV480.lean; imports and diagnostic axiom prints removed only. -/

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


/- Exact paid support from B3FlatGraphTangencyCriticalV480.lean; imports and diagnostic axiom prints removed only. -/

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


/- Exact paid support from B3ActualInteriorIsolationV480.lean; imports and diagnostic axiom prints removed only. -/

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


/- Exact paid support from B3SphereFlatSheetCriticalV480.lean; imports and diagnostic axiom prints removed only. -/
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


/- Exact paid support from B3CollarActualTangencyHeightV480.lean; imports and diagnostic axiom prints removed only. -/

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


/- Exact paid support from B3CollarParameterDerivativeV480.lean; imports and diagnostic axiom prints removed only. -/

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


/- Exact paid support from B3NativeCollarConsequencesV480.lean; imports and diagnostic axiom prints removed only. -/

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


/- Exact paid support from AuditB3CollarV480.lean; imports and diagnostic axiom prints removed only. -/
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


/- Exact paid support from B3CollarTangencyExclusionV480.lean; imports and diagnostic axiom prints removed only. -/

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


/- Exact paid support from B3CompactDiscreteFiniteV480.lean; imports and diagnostic axiom prints removed only. -/

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


/- Exact paid support from B3ContinuousRangeClosureV480.lean; imports and diagnostic axiom prints removed only. -/

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


/- Exact paid support from B3CoordinatePlaneTransportV480.lean; imports and diagnostic axiom prints removed only. -/

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


/- Exact paid support from B3ActualTangencyPairsCompactV480.lean; imports and diagnostic axiom prints removed only. -/

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


/- Exact paid support from B3TangencyImageCompactV480.lean; imports and diagnostic axiom prints removed only. -/

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
