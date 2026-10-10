import TubeUtilities
import SphereSurfaceProducer

set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff
open Set Topology
namespace SeifertSurfaces.LongitudeProducers
open Foundations MetricFoundations
noncomputable section

theorem radialVector_mem_disk (z : Circle) (r : ℝ) (hr : 0 ≤ r) (h2 : r < 2) :
    r • unitVector z ∈ tubeDiskOpen := by
  change ‖r • unitVector z - 0‖ < 2
  simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, unitVector_norm] using h2
def radialDisk (z : Circle) (r : ℝ) (hr : 0 ≤ r) (h2 : r < 2) : TubeDisk :=
  ⟨r • unitVector z, radialVector_mem_disk z r hr h2⟩

def closedTubeRadius {K : OrientedKnot} (T : TubularNeighborhood K) (r : ℝ) : Set ThreeSphere :=
  T.tube 0 '' {p : TubeDomain | ‖(p.2 : Euc 2)‖ ≤ r}

structure FramedRibbon {K : OrientedKnot} (T : TubularNeighborhood K)
    (F : SphereSpanningSurface.{0} K) where
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  twice_epsilon_lt_one : 2 * epsilon < 1
  direction : Circle → Circle
  direction_smooth : ContMDiff (𝓡 1) (𝓡 1) ∞ direction
  ambient : Diffeomorph (𝓡 3) (𝓡 3) ThreeSphere ThreeSphere ∞
  fixes_core : ∀ z, ambient (K.component 0 z) = K.component 0 z
  supported : ∀ x ∉ Set.range (T.tube 0), ambient x = x
  collar : Circle × Time → F.surface
  collar_embedding : Manifold.IsSmoothEmbedding ((𝓡 1).prod (𝓡∂ 1)) (𝓡∂ 2) ∞ collar
  collar_boundary : ∀ z, collar (z, 0) = F.boundary.toFun z
  collar_neighborhood : IsOpen (collar '' {p : Circle × Time | (p.2 : ℝ) < 1})
  collar_inward : ∀ z,
    ∃ w : TangentSpace (𝓡∂ 1) (0 : Time),
      inwardCoordinate (F.boundary.toFun z)
        (mfderiv (𝓡∂ 1) (𝓡∂ 2) (fun t => collar (z, t)) 0 w) > 0
  collar_graph : ∀ z (t : Time),
    ∃ w : TubeDisk, (w : Euc 2) = (2 * epsilon * (t : ℝ)) • unitVector (direction z) ∧
      ambient (F.embedding (collar (z, t))) = T.tube 0 (z, w)
  exact_intersection :
    (ambient '' Set.range F.embedding) ∩ closedTubeRadius T (2 * epsilon) =
      (ambient ∘ F.embedding) '' Set.range collar

theorem framed_ribbon_only_small_tube {K : OrientedKnot} {T : TubularNeighborhood K}
    {F : SphereSpanningSurface.{0} K} (R : FramedRibbon T F) (x : F.surface)
    (hx : R.ambient (F.embedding x) ∈ closedTubeRadius T (2 * R.epsilon)) :
    ∃ z t, x = R.collar (z, t) := by
  have hmem : R.ambient (F.embedding x) ∈
      (R.ambient ∘ F.embedding) '' Set.range R.collar := by
    rw [← R.exact_intersection]
    exact ⟨⟨F.embedding x, ⟨x, rfl⟩, rfl⟩, hx⟩
  obtain ⟨y, ⟨⟨z, t⟩, rfl⟩, hy⟩ := hmem
  exact ⟨z, t, (F.smoothEmbedding.isEmbedding.injective
    (R.ambient.injective hy)).symm⟩

def cutSet {K : OrientedKnot} {T : TubularNeighborhood K}
    {F : SphereSpanningSurface.{0} K} (R : FramedRibbon T F) : Set F.surface :=
  (R.collar '' {p : Circle × Time | (p.2 : ℝ) < 1 / 2})ᶜ

structure CutSurface {K : OrientedKnot} {T : TubularNeighborhood K}
    {F : SphereSpanningSurface.{0} K} (R : FramedRibbon T F) where
  surface : CompactOrientedSurface.{0}
  [connected : ConnectedSpace surface]
  inclusion : C(surface, F.surface)
  embedding : IsEmbedding inclusion
  smooth_embedding : Manifold.IsSmoothEmbedding (𝓡∂ 2) (𝓡∂ 2) ∞ inclusion
  image_eq : Set.range inclusion = cutSet R
  boundary : surface.OrientedBoundaryCircle
  boundary_covers : Set.range boundary.toFun = surface.boundary
  boundary_graph : ∀ z,
    ∃ t : Time, (t : ℝ) = 1 / 2 ∧ inclusion (boundary.toFun z) = R.collar (z, t)
  collar_reparametrization : Diffeomorph (𝓡∂ 2) (𝓡∂ 2) F.surface surface ∞
  orientation_transport : ∀ x (w : Fin 2 → TangentSpace (𝓡∂ 2) x),
    surface.orientation.form (collar_reparametrization x)
      (fun i => mfderiv (𝓡∂ 2) (𝓡∂ 2) collar_reparametrization x (w i)) =
        F.surface.orientation.form x w
attribute [instance] CutSurface.connected

end
end SeifertSurfaces.LongitudeProducers
