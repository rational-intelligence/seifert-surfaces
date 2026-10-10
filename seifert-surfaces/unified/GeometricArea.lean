import SurfaceClasses
import ChartPartitionHelper
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped Manifold ContDiff ENNReal
open Set Topology MeasureTheory Bundle

namespace SeifertSurfaces.MetricFoundations
open Foundations
universe u v
noncomputable section

abbrev SmoothMetric (M : Type v) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold (𝓡∂ 3) ∞ M] :=
  ContMDiffRiemannianMetric (𝓡∂ 3) ∞ (Euc 3)
    (fun x : M => TangentSpace (𝓡∂ 3) x)

/-- Smooth proper embedding before Appendix A's transversality theorem.
Exact boundary preimage is required; transversality is deliberately separate. -/
structure ProperSmoothEmbedding (S : CompactOrientedSurface.{u}) (M : Type v)
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] where
  toFun : S → M
  smooth : ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ toFun
  embedding : IsEmbedding toFun
  differential_injective : ∀ x,
    Function.Injective (mfderiv (𝓡∂ 2) (𝓡∂ 3) toFun x)
  boundary_preimage : toFun ⁻¹' ((𝓡∂ 3).boundary M) = S.boundary

namespace ProperSmoothEmbedding
variable {S : CompactOrientedSurface.{u}} {M : Type v}
  [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
def continuousMap (f : ProperSmoothEmbedding S M) : C(S, M) :=
  ⟨f.toFun, f.embedding.continuous⟩
def image (f : ProperSmoothEmbedding S M) := Set.range f.toFun
def Incompressible (f : ProperSmoothEmbedding S M) : Prop :=
  ∀ x, Function.Injective (FundamentalGroup.map f.continuousMap x)
theorem neat_differential_injective (f : NeatEmbedding S M) :
    ∀ x, Function.Injective (mfderiv (𝓡∂ 2) (𝓡∂ 3) f.toFun x) := by
  exact f.smoothEmbedding.isImmersion.mfderiv_injective (by simp)
def ofNeat (f : NeatEmbedding S M) : ProperSmoothEmbedding S M :=
  ⟨f.toFun, f.smoothEmbedding.isImmersion.contMDiff,
    f.smoothEmbedding.isEmbedding, neat_differential_injective f, f.boundary_preimage⟩
end ProperSmoothEmbedding

instance surfaceMeasurable (S : CompactOrientedSurface.{u}) : MeasurableSpace S := borel S

/-- A finite measurable disjoint partition subordinate to actual extended
charts. It is integration data, never an assumed area value. -/
structure ChartPartition (S : CompactOrientedSurface.{u}) where
  count : ℕ
  center : Fin count → S
  piece : Fin count → Set S
  measurable : ∀ i, MeasurableSet (piece i)
  subordinate : ∀ i, piece i ⊆ (extChartAt (𝓡∂ 2) (center i)).source
  disjoint : Pairwise (fun i j => Disjoint (piece i) (piece j))
  covers : (⋃ i, piece i) = Set.univ

theorem chartPartition_exists (S : CompactOrientedSurface.{u}) :
    Nonempty (ChartPartition S) := by
  letI : BorelSpace S := ⟨rfl⟩
  obtain ⟨n, center, piece, hmeas, hsub, hdisj, hcover⟩ :=
    finite_measurable_partition_subordinate
      (fun x : S => (extChartAt (𝓡∂ 2) x).source)
      (fun x => by rw [extChartAt_source]; exact (chartAt (EuclideanHalfSpace 2) x).open_source)
      (fun x => mem_extChartAt_source x)
  exact ⟨⟨n, center, piece, hmeas, hsub, hdisj, hcover⟩⟩

def canonicalPartition (S : CompactOrientedSurface.{u}) : ChartPartition S :=
  Classical.choice (chartPartition_exists S)

variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]

/-- The Gram matrix of the differential of a coordinate parametrization,
computed using the actual ambient metric. The derivative is within the
half-space chart target, including boundary points. -/
def coordinateGram (g : SmoothMetric M) {S : CompactOrientedSurface.{u}}
    (f : S → M) (p : S) (y : Euc 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  let e := extChartAt (𝓡∂ 2) p
  let q := f (e.symm y)
  let d := mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 3) (f ∘ e.symm) e.target y
  fun i j => g.inner q
    (d ((tangentSpaceCastModel 𝓘(ℝ, Euc 2) y).symm (EuclideanSpace.single i 1)))
    (d ((tangentSpaceCastModel 𝓘(ℝ, Euc 2) y).symm (EuclideanSpace.single j 1)))

def coordinateAreaDensity (g : SmoothMetric M) {S : CompactOrientedSurface.{u}}
    (f : S → M) (p : S) (y : Euc 2) : ℝ :=
  Real.sqrt (Matrix.det (coordinateGram g f p y))

/-- Geometric area: sum of Lebesgue integrals of the induced metric's
Jacobian on disjoint coordinate pieces. No scalar area oracle occurs here. -/
def partitionArea (g : SmoothMetric M) {S : CompactOrientedSurface.{u}}
    (f : S → M) (P : ChartPartition S) : ℝ :=
  ∑ i, ∫ y in (extChartAt (𝓡∂ 2) (P.center i)) '' (P.piece i),
    coordinateAreaDensity g f (P.center i) y

def area (g : SmoothMetric M) {S : CompactOrientedSurface.{u}}
    (f : S → M) : ℝ := partitionArea g f (canonicalPartition S)





theorem area_nonnegative (g : SmoothMetric M)
    {S : CompactOrientedSurface.{u}} (f : ProperSmoothEmbedding S M) :
    0 ≤ area g f.toFun := by
  unfold area partitionArea
  apply Finset.sum_nonneg
  intro i _
  exact setIntegral_nonneg_of_ae (Filter.Eventually.of_forall (fun _ => Real.sqrt_nonneg _))







end
end SeifertSurfaces.MetricFoundations
