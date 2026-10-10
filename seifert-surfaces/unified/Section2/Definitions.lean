import Mathlib

/-!
# Exchange structures: Definition 2.1

Source: `references/seifert-surfaces.txt`, lines 126–147 (PDF pp. 3–4).
The exchange axioms concern the one-skeleton alone. Flagness is recorded separately
for an abstract simplicial complex in `Section2.FlagComplex`.
-/

namespace SeifertSurfaces

universe u v

variable {V : Type u} {W : Type v}

/-- The two-interval is the set of common neighbours. Its use as a two-interval
in an axiom is guarded by the endpoints having extended graph distance two. -/
def twoInterval (G : SimpleGraph V) (u w : V) : Set V :=
  G.neighborSet u ∩ G.neighborSet w

/-- An apex belongs to the interval and is equal or adjacent to every member. -/
def IsIntervalApex (G : SimpleGraph V) (u w x : V) : Prop :=
  x ∈ twoInterval G u w ∧ ∀ y ∈ twoInterval G u w, x = y ∨ G.Adj x y

/-- Definition 2.1, (N1) and (N2). The complexity values form a well-founded
linear order. No chosen apex map is part of this structure. -/
structure ExchangeStructure (G : SimpleGraph V) (c : V → W)
    [LinearOrder W] [WellFoundedLT W] : Prop where
  intervalApex : ∀ u w, G.edist u w = 2 → ∃ x, IsIntervalApex G u w x
  descendingApex : ∀ u w, G.edist u w = 2 →
    ∃ x, IsIntervalApex G u w x ∧ c x < max (c u) (c w)

/-- The graph data for an exchange complex. Mathlib graph connectedness includes
nonemptiness; taking the flag complex of this graph supplies the source complex. -/
structure ExchangeGraph (G : SimpleGraph V) (c : V → W)
    [LinearOrder W] [WellFoundedLT W] : Prop extends ExchangeStructure G c where
  connected : G.Connected

variable [LinearOrder W]

/-- A downset for the complexity: every vertex of no greater complexity than a
member is also a member. -/
def ComplexityDownset (c : V → W) (D : Set V) : Prop :=
  ∀ ⦃u w : V⦄, c u ≤ c w → w ∈ D → u ∈ D

/-- The restricted complexity on a full subcomplex's vertex set. -/
def restrictedComplexity (c : V → W) (D : Set V) : D → W :=
  fun u => c u.1

/-- The vertices strictly below a vertex in complexity. -/
def strictSublevel (c : V → W) (v : V) : Set V :=
  {u | c u < c v}

/-- The descending link has exactly the lower-complexity neighbours of `v`. -/
def descendingLinkVertices (G : SimpleGraph V) (c : V → W) (v : V) : Set V :=
  {u | G.Adj v u ∧ c u < c v}

/-- Least vertex in the complexity order; injectivity gives uniqueness. -/
def IsLeastComplexityVertex (c : V → W) (v : V) : Prop :=
  ∀ u, c v ≤ c u

end SeifertSurfaces
