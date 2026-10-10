import BoundaryFoliation
import GeometricCategory
import Mathlib.Dynamics.Flow

noncomputable section
open Set Topology Function
open scoped Manifold ContDiff

namespace SeifertSurfaces.OriginalEndpoints
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations

universe v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}

/-- A smooth transverse boundary flow carrying each supplied longitude leaf
to a leaf of the same foliation, with its actual smooth extension to the
exterior. Both time actions are the bundled continuous additive flows. -/
structure B1SourceFoliationFlow (J : LongitudeFoliation.{v} E) where
  ambient : Flow ℝ E.Carrier
  labels : Flow ℝ Circle
  ambient_smooth : ContMDiff (𝓘(ℝ).prod (𝓡∂ 3)) (𝓡∂ 3) ∞
    (fun p : ℝ × E.Carrier => ambient p.1 p.2)
  labels_smooth : ContMDiff (𝓘(ℝ).prod (𝓡 1)) (𝓡 1) ∞
    (fun p : ℝ × Circle => labels p.1 p.2)
  leaf_image : ∀ y a, ambient y '' J.leaf a = J.leaf (labels y a)
  labels_transverse : ∀ a : Circle,
    mfderiv 𝓘(ℝ) (𝓡 1) (fun y : ℝ => labels y a) 0
      ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1) ≠ 0

/-- The scalar inward distance coordinate: its metric gradient has unit
length. This says nothing about the vector obtained by differentiating a
B-straightened chart with respect to its numerical radial coordinate. -/
def IsInwardDistanceCoordinate (g : SmoothMetric E.Carrier)
    (U : Set E.Carrier) (r : E.Carrier → ℝ) : Prop :=
  ContMDiffOn (𝓡∂ 3) 𝓘(ℝ) ∞ r U ∧
  (∀ p ∈ U, 0 ≤ r p) ∧
  (∀ p ∈ U, p ∈ (𝓡∂ 3).boundary E.Carrier ↔ r p = 0) ∧
  ∀ p ∈ U, ∃ n : TangentSpace (𝓡∂ 3) p,
    g.inner p n n = 1 ∧
    ∀ w : TangentSpace (𝓡∂ 3) p,
      g.inner p n w =
        (NormedSpace.fromTangentSpace (r p))
          (mfderivWithin (𝓡∂ 3) 𝓘(ℝ) r U p w)

end SeifertSurfaces.OriginalEndpoints
