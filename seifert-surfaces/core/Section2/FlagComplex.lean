import Section2.Definitions

namespace SeifertSurfaces

universe u v

variable {V : Type u} {W : Type v}

/-- A flag complex is exactly the collection of nonempty finite cliques of its
one-skeleton. This records source flagness for an actual Mathlib complex. -/
def IsFlagComplex (G : SimpleGraph V) (X : AbstractSimplicialComplex V) : Prop :=
  ∀ σ : Finset V, σ ∈ X.faces ↔ σ.Nonempty ∧ G.IsClique (σ : Set V)

/-- Definition 2.1, the full source concept: a nonempty connected flag complex
whose one-skeleton carries the two exchange axioms with well-ordered complexity. -/
structure ExchangeComplex (X : AbstractSimplicialComplex V) (G : SimpleGraph V)
    (c : V → W) [LinearOrder W] [WellFoundedLT W] : Prop
    extends ExchangeGraph G c where
  flag : IsFlagComplex G X

/-- The literal full subcomplex of `X` on `D`. Vertices are elements of `D`,
and a finite set is a face exactly when its image is a face of `X`. -/
noncomputable def fullSubcomplex (X : AbstractSimplicialComplex V) (D : Set V) :
    AbstractSimplicialComplex D where
  faces := {σ | σ.map (Function.Embedding.subtype D) ∈ X.faces}
  isRelLowerSet_faces := by
    intro σ hσ
    refine ⟨?_, ?_⟩
    · exact Finset.map_nonempty.mp (X.isRelLowerSet_faces hσ).1
    · intro τ hτσ hτ
      exact (X.isRelLowerSet_faces hσ).2 (Finset.map_subset_map.mpr hτσ)
        (Finset.map_nonempty.mpr hτ)
  singleton_mem := by
    intro v
    change (({v} : Finset D).map (Function.Embedding.subtype D)) ∈ X.faces
    rw [Finset.map_singleton]
    exact X.singleton_mem ((Function.Embedding.subtype D) v)

/-- The flag complex determined by a simple graph. Only its closure/singleton
certificates are pending; the set of faces is explicitly defined. -/
noncomputable def graphFlagComplex (G : SimpleGraph V) : AbstractSimplicialComplex V where
  faces := {σ | σ.Nonempty ∧ G.IsClique (σ : Set V)}
  isRelLowerSet_faces := by
    intro σ hσ
    refine ⟨hσ.1, ?_⟩
    intro τ hτσ hτ
    exact ⟨hτ, hσ.2.subset (Finset.coe_subset.mpr hτσ)⟩
  singleton_mem := by
    intro v
    exact ⟨Finset.singleton_nonempty v, by simpa only [Finset.coe_singleton] using G.isClique_singleton v⟩

/-- A full subcomplex of a flag complex is the flag complex of its induced
graph, so its flagness is independent of the exchange axioms. -/
theorem graph_flag_complex_is_flag (G : SimpleGraph V) :
    IsFlagComplex G (graphFlagComplex G) := by
  intro σ
  rfl

/-- Full subcomplexes retain flagness with their induced one-skeleton. -/
theorem full_subcomplex_is_flag
    (X : AbstractSimplicialComplex V) (G : SimpleGraph V)
    (hflag : IsFlagComplex G X) (D : Set V) :
    IsFlagComplex (G.induce D) (fullSubcomplex X D) := by
  intro σ
  change σ.map (Function.Embedding.subtype D) ∈ X.faces ↔ _
  rw [hflag, Finset.map_nonempty, SimpleGraph.isClique_induce_iff]
  simp only [Finset.coe_map]
  rfl

end SeifertSurfaces
