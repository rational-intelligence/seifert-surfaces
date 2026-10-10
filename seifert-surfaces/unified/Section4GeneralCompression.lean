import Section4GeometricDefinitions

set_option autoImplicit false
noncomputable section
open Set Topology Function
open scoped Manifold ContDiff

namespace SeifertSurfaces.OriginalEndpoints.Section4
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking

/- The original general-manifold lemma 4.5 does not assume orientability of
P or Q. Their ambient manifold is oriented. This additive interface omits
surface orientation while retaining every smooth/neat condition. -/
structure CompactSmoothSurface where
  carrier : Type
  [topology : TopologicalSpace carrier]
  [charted : ChartedSpace (EuclideanHalfSpace 2) carrier]
  [smooth : IsManifold (𝓡∂ 2) ∞ carrier]
  [hausdorff : T2Space carrier]
  [secondCountable : SecondCountableTopology carrier]
  [compact : CompactSpace carrier]

attribute [instance] CompactSmoothSurface.topology CompactSmoothSurface.charted
  CompactSmoothSurface.smooth CompactSmoothSurface.hausdorff
  CompactSmoothSurface.secondCountable CompactSmoothSurface.compact
instance : CoeSort CompactSmoothSurface Type := ⟨CompactSmoothSurface.carrier⟩
def CompactSmoothSurface.boundary (S : CompactSmoothSurface) : Set S := (𝓡∂ 2).boundary S

structure GeneralNeatSurface (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] where
  surface : CompactSmoothSurface
  toFun : surface → M
  smoothEmbedding : Manifold.IsSmoothEmbedding (𝓡∂ 2) (𝓡∂ 3) ∞ toFun
  boundary_preimage : toFun ⁻¹' ((𝓡∂ 3).boundary M) = surface.boundary
  boundary_transverse : ∀ x ∈ surface.boundary,
    ∃ w : TangentSpace (𝓡∂ 2) x,
      inwardCoordinate (toFun x) (mfderiv (𝓡∂ 2) (𝓡∂ 3) toFun x w) ≠ 0

namespace GeneralNeatSurface
variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
def image (F : GeneralNeatSurface M) : Set M := Set.range F.toFun
def continuousMap (F : GeneralNeatSurface M) : C(F.surface, M) :=
  ⟨F.toFun, F.smoothEmbedding.isEmbedding.continuous⟩
def Incompressible (F : GeneralNeatSurface M) : Prop :=
  ∀ x : F.surface, Function.Injective (FundamentalGroup.map F.continuousMap x)
end GeneralNeatSurface

def forgetOrientation {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] (F : CompactNeatSurface M) :
    GeneralNeatSurface M :=
  { surface := { carrier := F.surface }
    toFun := F.embedding.toFun
    smoothEmbedding := F.embedding.smoothEmbedding
    boundary_preimage := F.embedding.boundary_preimage
    boundary_transverse := F.embedding.boundary_transverse }

structure GeneralCompressingDisk {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] (F : GeneralNeatSurface M) where
  disk : CompactOrientedSurface.{0}
  disk_homeomorph : disk ≃ₜ ClosedDisk
  disk_boundary : disk_homeomorph '' disk.boundary = closedDiskBoundary
  toFun : disk → M
  smoothEmbedding : Manifold.IsSmoothEmbedding (𝓡∂ 2) (𝓡∂ 3) ∞ toFun
  boundaryCircle : disk.OrientedBoundaryCircle
  boundary_covers : Set.range boundaryCircle.toFun = disk.boundary
  surfaceLoop : C(Circle, F.surface)
  surfaceLoop_embedded : IsEmbedding surfaceLoop
  boundary_matches : ∀ z, toFun (boundaryCircle.toFun z) = F.toFun (surfaceLoop z)
  intersection : Set.range toFun ∩ F.image = toFun '' disk.boundary
  interior_ambient : toFun '' disk.boundaryᶜ ⊆ (𝓡∂ 3).interior M
  loop_interior : Set.range surfaceLoop ⊆ F.surface.boundaryᶜ
  essential : ¬ ∃ x : F.surface,
    ContinuousMap.Homotopic surfaceLoop (ContinuousMap.const Circle x)

structure GeneralCompressionAnnulus {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M]
    {F : GeneralNeatSurface M} (D : GeneralCompressingDisk F) where
  band : C(Circle × Time, F.surface)
  embedded : IsEmbedding band
  interior_surface : Set.range band ⊆ F.surface.boundaryᶜ
  center : ∀ z, band (z, middleTime) = D.surfaceLoop z
  open_middle : IsOpen (band '' {p : Circle × Time | 0 < (p.2 : ℝ) ∧ (p.2 : ℝ) < 1})

namespace GeneralCompressionAnnulus
variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  {F : GeneralNeatSurface M} {D : GeneralCompressingDisk F} (A : GeneralCompressionAnnulus D)
def removed : Set F.surface :=
  A.band '' {p : Circle × Time | 0 < (p.2 : ℝ) ∧ (p.2 : ℝ) < 1}
abbrev Remainder := ↥A.removedᶜ

end GeneralCompressionAnnulus

end SeifertSurfaces.OriginalEndpoints.Section4
