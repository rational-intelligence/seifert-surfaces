import SurfaceInvariants

set_option autoImplicit false

open scoped Manifold ContDiff
open Set Topology

namespace SeifertSurfaces.GenusLinking
open SeifertSurfaces.Foundations

universe u
noncomputable section

variable {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)

/-- Genus is obtained from the actual source surface, never a genus label. -/
def imageGenus (A : SurfaceImage.{0} E) : ℕ :=
  surfaceGenus (Classical.choose A.2).1.surface

theorem imageGenus_independent (F : IncompressibleSpanningSurface.{0} E) :
    imageGenus E (surfaceImageOf E F) = surfaceGenus F.1.surface := by
  apply same_image_genus E
  exact Classical.choose_spec (surfaceImageOf E F).2

theorem imageGenus_isotopy_invariant (A B : SurfaceImage.{0} E)
    (h : ImageIsotopic E A B) : imageGenus E A = imageGenus E B := by
  apply isotopic_image_genus E
  change SmoothAmbientIsotopy.Rel _ _
  rw [Classical.choose_spec A.2, Classical.choose_spec B.2]
  exact h

def vertexGenus (v : Vertex.{0} E) : ℕ :=
  Quotient.lift (imageGenus E) (imageGenus_isotopy_invariant E) v

/-- The least genus among **all** Seifert surfaces, including compressible ones.
`sInf` is total on naturals; attainment below requires genuine Seifert existence. -/
def knotGenus : ℕ :=
  sInf {g | ∃ F : SeifertSurface.{0} E, surfaceGenus F.surface = g}

def genusVertices (ℓ : ℤ) : Set (Vertex.{0} E) :=
  {v | (vertexGenus E v : ℤ) ≤ ℓ}

theorem knotGenus_le_surface (F : SeifertSurface.{0} E) :
    knotGenus E ≤ surfaceGenus F.surface := by
  exact csInf_le' ⟨F, rfl⟩

theorem knotGenus_le_vertex (v : Vertex.{0} E) :
    knotGenus E ≤ vertexGenus E v := by
  refine Quotient.inductionOn v ?_
  intro A
  change knotGenus E ≤ surfaceGenus (Classical.choose A.2).1.surface
  let F := (Classical.choose A.2).1
  letI : ConnectedSpace F.surface := F.connected_for_knot
  exact knotGenus_le_surface E { toLinkSpanningSurface := F }


end
end SeifertSurfaces.GenusLinking
