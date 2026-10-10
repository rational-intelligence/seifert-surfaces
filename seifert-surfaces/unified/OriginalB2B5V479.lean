import OriginalB1
import B1TangencyGraph
import KnotLinkConditions
import KnotGenus
import Section5Combinatorics
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Topology.Covering.Basic

noncomputable section
open Set Topology Function MeasureTheory Bundle
open scoped Manifold ContDiff BigOperators ENNReal

namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV479
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates

variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]

variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}

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
  new_profile : ∀ u ∈ interval, ∀ r, |r| ≤ eta (base u).1 →
    newMap ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![u, r]) =
      (C.chart p hp).chart.symm ((EuclideanSpace.equiv (Fin 3) ℝ).symm
        ![u, Real.cot ((C.chart p hp).angle u / 2) * eta (base u).1 *
          SeifertSurfaces.AppendixB.roundingProfile cutoff (r / eta (base u).1), r])
  capped_coordinates : ∀ u ∈ interval,
    0 < eta (base u).1 ∧
    2 * eta (base u).1 * Real.sqrt (1 + Real.cot ((C.chart p hp).angle u / 2) ^ 2) ≤ radius ∧
    ∀ r, |r| ≤ eta (base u).1 →
      (EuclideanSpace.equiv (Fin 3) ℝ).symm
        ![u, Real.cot ((C.chart p hp).angle u / 2) * |r|, r] ∈ (C.chart p hp).chart.target ∧
      (EuclideanSpace.equiv (Fin 3) ℝ).symm
        ![u, Real.cot ((C.chart p hp).angle u / 2) * eta (base u).1 *
          SeifertSurfaces.AppendixB.roundingProfile cutoff (r / eta (base u).1), r]
          ∈ (C.chart p hp).chart.target
  normals_small : ∀ u ∈ interval, ∀ r, |r| ≤ eta (base u).1 →
    let yOld := (EuclideanSpace.equiv (Fin 3) ℝ).symm
      ![u, Real.cot ((C.chart p hp).angle u / 2) * |r|, r]
    let yNew := (EuclideanSpace.equiv (Fin 3) ℝ).symm
      ![u, Real.cot ((C.chart p hp).angle u / 2) * eta (base u).1 *
        SeifertSurfaces.AppendixB.roundingProfile cutoff (r / eta (base u).1), r]
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


end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV479
