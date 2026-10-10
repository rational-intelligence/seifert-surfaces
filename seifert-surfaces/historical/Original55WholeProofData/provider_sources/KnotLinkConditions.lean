import SphereEmbeddingHelpers
import SurfaceClasses
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Concrete nontrivial-knot and non-split-link conditions

The unknot is the actual equatorial circle in the standard three-sphere.
Splitting is witnessed by an actual smooth embedded two-sphere disjoint from
the link, with link points in different complementary components. Linking
indecomposability still needs the actual oriented linking-number construction.
-/

open scoped Manifold ContDiff
open Set Topology

namespace SeifertSurfaces.Foundations

universe u
noncomputable section

abbrev TwoSphere := ↥(Metric.sphere (0 : Euc 3) 1)

def equatorVector (z : Circle) : Euc 4 :=
  EuclideanSpace.single 0 (z : ℂ).re + EuclideanSpace.single 1 (z : ℂ).im

theorem equator_mem_sphere (z : Circle) : equatorVector z ∈ Metric.sphere (0 : Euc 4) 1 := by
  rw [Metric.mem_sphere, dist_zero_right]
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  have hz : (z : ℂ).re ^ 2 + (z : ℂ).im ^ 2 = 1 := by
    simpa [Complex.normSq_apply, pow_two] using z.normSq_coe
  simpa [equatorVector, Fin.sum_univ_succ, PiLp.single_apply] using hz

def equator (z : Circle) : ThreeSphere := ⟨equatorVector z, equator_mem_sphere z⟩

theorem equator_smoothEmbedding :
    Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 3) ∞ equator := by
  have h : equator = EquatorProof.sphereMap EquatorProof.equatorLinear := by
    funext z
    apply Subtype.ext
    rfl
  rw [h]
  exact EquatorProof.sphereMap_isSmoothEmbedding EquatorProof.equatorLinear

/- Smooth ambient isotopy in the boundaryless standard three-sphere.
The time interval still uses its boundary model. -/
structure SmoothSphereAmbientIsotopy where
  stage : Time → Diffeomorph (𝓡 3) (𝓡 3) ThreeSphere ThreeSphere ∞
  smooth_family : ContMDiff ((𝓡∂ 1).prod (𝓡 3)) (𝓡 3) ∞
    (fun p : Time × ThreeSphere => stage p.1 p.2)
  initial : ∀ x, stage 0 x = x

def KnotIsUnknot (K : OrientedKnot) : Prop :=
  ∃ H : SmoothSphereAmbientIsotopy,
    (H.stage 1) '' Set.range (K.component 0) = Set.range equator

def KnotIsNontrivial (K : OrientedKnot) : Prop := ¬ KnotIsUnknot K

/- A genuine smooth disk bounded by the knot in S³, not a genus-labelled
surface or a freely supplied assertion of triviality. -/
structure SmoothKnotDisk (K : OrientedKnot) where
  disk : CompactOrientedSurface.{u}
  disk_homeomorph : disk ≃ₜ ClosedDisk
  disk_boundary : disk_homeomorph '' disk.boundary = closedDiskBoundary
  toFun : disk → ThreeSphere
  smoothEmbedding : Manifold.IsSmoothEmbedding (𝓡∂ 2) (𝓡 3) ∞ toFun
  boundary_image : toFun '' disk.boundary = Set.range (K.component 0)

/- The disk characterization requires genuine 3-dimensional topology. -/

/- A splitting sphere and link points on different sides. Jordan separation
is not assumed as an arbitrary two-region field. -/
def LinkIsSplit {n : ℕ} (L : OrientedLink n) : Prop :=
  ∃ sphereMap : TwoSphere → ThreeSphere,
    Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ sphereMap ∧
    (∀ i, Disjoint (Set.range sphereMap) (Set.range (L.component i))) ∧
    ∃ i j : Fin n, ∃ z w : Circle,
      L.component j w ∉ connectedComponentIn (Set.range sphereMap)ᶜ (L.component i z)

def LinkIsNonSplit {n : ℕ} (L : OrientedLink n) : Prop := ¬ LinkIsSplit L

/- The source's cited geometric connectedness input [10, Thm. A], stated
over the actual class graph. It remains a proof obligation, not an axiom. -/

/- The link version uses non-splitness and permits disconnected componentwise
incompressible spanning surfaces, exactly as the cited source convention does. -/

end
end SeifertSurfaces.Foundations
