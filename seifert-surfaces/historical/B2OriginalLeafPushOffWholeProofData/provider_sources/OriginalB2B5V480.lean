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

namespace SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
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
  sorry

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


end SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
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
  let I := 𝓘(ℝ,ℝ × Euc 2)
  let D : Set (ℝ × Euc 2) := Icc a b ×ˢ (surfaceChart p).target
  let pre : ℝ × Euc 2 → ℝ × S := fun q => (q.1,(surfaceChart p).symm q.2)
  let Φ : ℝ × Euc 2 → M := H ∘ pre
  have hpre : ContMDiffOn I (𝓘(ℝ).prod (𝓡∂ 2)) ∞ pre D :=
    contDiff_fst.contMDiff.contMDiffOn.prodMk
      ((contMDiffOn_extChartAt_symm p).comp contDiff_snd.contMDiff.contMDiffOn (fun q hq => hq.2))
  have hΦ : ContMDiffOn I (𝓡∂ 3) ∞ Φ D :=
    hH.comp hpre (fun q hq => ⟨hq.1,mem_univ _⟩)
  have hUD : UniqueMDiffOn I D :=
    ((uniqueDiffOn_Icc hab).prod (uniqueDiffOn_extChartAt_target p)).uniqueMDiffOn
  have ht := hΦ.continuousOn_tangentMapWithin (by simp) hUD
  have hd (q : ℝ × Euc 2) (hq : q ∈ D) :
      mfderivWithin 𝓘(ℝ,Euc 2) (𝓡∂ 3)
        ((fun x => H (q.1,x)) ∘ (surfaceChart p).symm) (surfaceChart p).target q.2 =
      (mfderivWithin I (𝓡∂ 3) Φ D q).comp
        (ContinuousLinearMap.inr ℝ (TangentSpace 𝓘(ℝ) q.1)
          (TangentSpace 𝓘(ℝ,Euc 2) q.2)) := by
    let lift : Euc 2 → ℝ × Euc 2 := fun y => (q.1,y)
    have hliftD : HasFDerivAt lift (ContinuousLinearMap.inr ℝ ℝ (Euc 2)) q.2 :=
      (hasFDerivAt_const q.1 q.2).prodMk (hasFDerivAt_id q.2)
    have hlift : MDifferentiableAt 𝓘(ℝ,Euc 2) I lift q.2 :=
      hliftD.differentiableAt.mdifferentiableAt
    have hchain := mfderivWithin_comp q.2
      (hΦ.mdifferentiableOn (by simp) q hq) hlift.mdifferentiableWithinAt
      (show MapsTo lift (surfaceChart p).target D from fun y hy => ⟨hq.1,hy⟩)
      ((uniqueDiffOn_extChartAt_target p q.2 hq.2).uniqueMDiffWithinAt)
    rw [mfderivWithin_eq_mfderiv
      ((uniqueDiffOn_extChartAt_target p q.2 hq.2).uniqueMDiffWithinAt) hlift,
      hliftD.hasMFDerivAt.mfderiv] at hchain
    exact hchain
  have hv (k : Fin 2) : ContinuousOn (fun q : ℝ × Euc 2 =>
      (⟨Φ q, mfderivWithin I (𝓡∂ 3) Φ D q
        ((tangentSpaceCastModel I q).symm (0,EuclideanSpace.single k 1))⟩ :
        TangentBundle (𝓡∂ 3) M)) D := by
    let ins : ℝ × Euc 2 → TangentBundle I (ℝ × Euc 2) := fun q =>
      (tangentBundleModelSpaceHomeomorph I).symm (q,(0,EuclideanSpace.single k 1))
    have hins : Continuous ins := (tangentBundleModelSpaceHomeomorph I).symm.continuous.comp
      (continuous_id.prodMk continuous_const)
    exact ht.comp hins.continuousOn (fun q hq => hq)
  letI : RiemannianBundle (fun x : M => TangentSpace (𝓡∂ 3) x) := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle (Euc 3) (fun x : M => TangentSpace (𝓡∂ 3) x) :=
    ⟨⟨g.inner,g.contMDiff.continuous,fun _ _ _ => rfl⟩⟩
  have hgram (i j : Fin 2) : ContinuousOn (fun q : ℝ × Euc 2 =>
      coordinateGram g (fun x => H (q.1,x)) p q.2 i j) D := by
    apply ((hv i).inner_bundle (hv j)).congr
    intro q hq
    unfold coordinateGram
    dsimp only
    rw [hd q hq]
    rfl
  apply ContinuousOn.sqrt
  exact continuous_id.matrix_det.comp_continuousOn (continuousOn_pi.mpr
    (fun i => continuousOn_pi.mpr (fun j => hgram i j)))

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


#print axioms B2_original_push_off

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
