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

theorem edge_remains (k : Fin 2) (z : Circle) :
    A.band (z, CompressionAnnulus.sideTime k) ∈ A.removedᶜ := by
  sorry
def edgePoint (k : Fin 2) (z : Circle) : A.Remainder :=
  ⟨A.band (z, CompressionAnnulus.sideTime k), A.edge_remains k z⟩

inductive Gluing : (A.Remainder ⊕ (Fin 2 × ClosedDisk)) →
    (A.Remainder ⊕ (Fin 2 × ClosedDisk)) → Prop where
  | attach (k : Fin 2) (z : Circle) :
      Gluing (.inl (A.edgePoint k z)) (.inr (k, CompressionAnnulus.capEdge z))
def SurgerySpace := Quot A.Gluing
instance : TopologicalSpace A.SurgerySpace := inferInstanceAs (TopologicalSpace (Quot A.Gluing))
def remainderInclusion (x : A.Remainder) : A.SurgerySpace := Quot.mk A.Gluing (.inl x)
def capInclusion (k : Fin 2) (x : ClosedDisk) : A.SurgerySpace := Quot.mk A.Gluing (.inr (k, x))
end GeneralCompressionAnnulus

structure GeneralActualCompression {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M]
    (F : GeneralNeatSurface M) {D : GeneralCompressingDisk F}
    (A : GeneralCompressionAnnulus D) where
  total : GeneralNeatSurface M
  realization : total.surface ≃ₜ A.SurgerySpace
  diskParam : ClosedDisk ≃ₜ D.disk
  diskParam_boundary : ∀ z,
    diskParam (CompressionAnnulus.capEdge z) = D.boundaryCircle.toFun z
  thickening : C(ClosedDisk × Time, M)
  thickening_embedded : IsEmbedding thickening
  thickening_center : ∀ x, thickening (x, middleTime) = D.toFun (diskParam x)
  thickening_lateral : ∀ z t,
    thickening (CompressionAnnulus.capEdge z, t) = F.toFun (A.band (z, t))
  thickening_interior : Set.range thickening ⊆ (𝓡∂ 3).interior M
  thickening_intersection : Set.range thickening ∩ F.image =
    Set.range (fun p : Circle × Time => F.toFun (A.band p))
  caps_disjoint : Disjoint
    (Set.range (fun x : ClosedDisk => thickening (x, CompressionAnnulus.sideTime 0)))
    (Set.range (fun x : ClosedDisk => thickening (x, CompressionAnnulus.sideTime 1)))
  caps_avoid_disk : ∀ k : Fin 2, Disjoint
    (Set.range (fun x : ClosedDisk => thickening (x, CompressionAnnulus.sideTime k)))
    (Set.range D.toFun)
  caps_attachment : ∀ k : Fin 2,
    Set.range (fun x : ClosedDisk => thickening (x, CompressionAnnulus.sideTime k)) ∩
      (F.toFun '' A.removedᶜ) =
      Set.range (fun z : Circle => F.toFun (A.band (z, CompressionAnnulus.sideTime k)))
  unrounded : C(A.SurgerySpace, M)
  unrounded_embedded : IsEmbedding unrounded
  unrounded_remainder : ∀ x : A.Remainder, unrounded (A.remainderInclusion x) = F.toFun x
  unrounded_caps : ∀ k x,
    unrounded (A.capInclusion k x) = thickening (x, CompressionAnnulus.sideTime k)
  rounding : TopologicalAmbientIsotopy M
  support : Set M
  support_open : IsOpen support
  support_seams : ∀ k z, F.toFun (A.band (z, CompressionAnnulus.sideTime k)) ∈ support
  support_away_boundary : Disjoint (closure support) ((𝓡∂ 3).boundary M)
  support_away_disk : Disjoint (closure support) (Set.range D.toFun)
  fixed_outside : ∀ t x, x ∉ support → rounding.stage t x = x
  rounded_identification : ∀ q : A.SurgerySpace,
    total.toFun (realization.symm q) = rounding.stage 1 (unrounded q)
  boundary_matches : ∀ x : A.Remainder,
    realization.symm (A.remainderInclusion x) ∈ total.surface.boundary ↔
      (x : F.surface) ∈ F.surface.boundary
  caps_interior : ∀ k x, realization.symm (A.capInclusion k x) ∉ total.surface.boundary
  boundary_fixed : ∀ x : A.Remainder, (x : F.surface) ∈ F.surface.boundary →
    total.toFun (realization.symm (A.remainderInclusion x)) = F.toFun x

structure GeneralRetainedStep {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M]
    (F G : GeneralNeatSurface M) where
  disk : GeneralCompressingDisk F
  annulus : GeneralCompressionAnnulus disk
  realization : GeneralActualCompression F annulus
  component : realization.total.surface
  component_boundary :
    (connectedComponent component ∩ realization.total.surface.boundary).Nonempty
  identification : G.surface ≃ₜ ↥(connectedComponent component)
  boundary_matches : ∀ x : G.surface,
    x ∈ G.surface.boundary ↔
      (identification x : realization.total.surface) ∈ realization.total.surface.boundary
  embedding_matches : ∀ x : G.surface,
    G.toFun x = realization.total.toFun (identification x : realization.total.surface)

end SeifertSurfaces.OriginalEndpoints.Section4
