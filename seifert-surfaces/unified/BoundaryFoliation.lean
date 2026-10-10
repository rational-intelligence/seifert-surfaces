import GeometricArea
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Calculus.Deriv.Basic

open scoped Manifold ContDiff
open Set Topology Bundle
namespace SeifertSurfaces.MetricFoundations
open Foundations
universe u
noncomputable section

variable {K : OrientedKnot} {T : TubularNeighborhood K}

structure LongitudeFoliation (E : SmoothExterior T) where
  torus : Circle × Circle → E.Carrier
  smoothEmbedding : Manifold.IsSmoothEmbedding ((𝓡 1).prod (𝓡 1)) (𝓡∂ 3) ∞ torus
  covers_boundary : Set.range torus = (𝓡∂ 3).boundary E.Carrier
  longitudeWitness : SeifertSurface.{u} E
  labelWitness : Circle
  witness_boundary : ∀ z,
    torus (labelWitness, z) = longitudeWitness.embedding.toFun
      ((longitudeWitness.boundaryCircle 0).toFun z)
  leaf_homotopy_in_torus : ∀ a b : Circle,
    ∃ H : ContinuousMap.Homotopy
      (⟨fun z => torus (a, z), smoothEmbedding.isEmbedding.continuous.comp
        (continuous_const.prodMk continuous_id)⟩ : C(Circle, E.Carrier))
      (⟨fun z => torus (b, z), smoothEmbedding.isEmbedding.continuous.comp
        (continuous_const.prodMk continuous_id)⟩ : C(Circle, E.Carrier)),
      ∀ t z, H (t, z) ∈ (𝓡∂ 3).boundary E.Carrier

namespace LongitudeFoliation
variable {E : SmoothExterior T}
def leaf (J : LongitudeFoliation.{u} E) (a : Circle) : Set E.Carrier :=
  Set.range (fun z => J.torus (a, z))
def BoundaryIn (J : LongitudeFoliation.{u} E) {S : CompactOrientedSurface.{u}}
    (f : S → E.Carrier) : Prop := ∃ a, f '' S.boundary = J.leaf a
def AmbientAnalytic (J : LongitudeFoliation.{u} E) : Prop :=
  ContMDiff ((𝓡 1).prod (𝓡 1)) (𝓡 3) ω (E.toSphere ∘ J.torus)
theorem torus_lands_boundary (J : LongitudeFoliation.{u} E) (p : Circle × Circle) :
    J.torus p ∈ (𝓡∂ 3).boundary E.Carrier := by
  rw [← J.covers_boundary]
  exact Set.mem_range_self p
def boundaryLift (J : LongitudeFoliation.{u} E) :
    Circle × Circle → ((𝓡∂ 3).boundary E.Carrier) :=
  fun p => ⟨J.torus p, torus_lands_boundary J p⟩
end LongitudeFoliation

structure AnalyticBoundaryStructure (E : SmoothExterior T) where
  charted : ChartedSpace (Euc 2) ((𝓡∂ 3).boundary E.Carrier)
  analytic : letI := charted
    IsManifold (𝓡 2) ω ((𝓡∂ 3).boundary E.Carrier)
  inclusion_smooth : letI := charted
    ContMDiff (𝓡 2) (𝓡∂ 3) ∞
      (Subtype.val : ((𝓡∂ 3).boundary E.Carrier) → E.Carrier)

def LongitudeFoliation.IntrinsicallyAnalytic (J : LongitudeFoliation.{u} E) : Prop :=
  ∃ B : AnalyticBoundaryStructure E,
    letI := B.charted
    ContMDiff ((𝓡 1).prod (𝓡 1)) (𝓡 2) ω J.boundaryLift

abbrev TorusModel := (𝓡 1).prod (𝓡 1)

end
end SeifertSurfaces.MetricFoundations
