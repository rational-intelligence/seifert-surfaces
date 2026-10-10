import Section2.Definitions

namespace SeifertSurfaces

universe u v

variable {V : Type u} {W : Type v} [LinearOrder W] [WellFoundedLT W]

/-- Lemma 2.2. A new well-founded linear order on the vertex type itself makes
the identity complexity injective. The refinement property is the one supplied
by the source's lexicographic well-order of complexity fibres. Neither flagness
nor connectedness nor finiteness is required. -/
theorem exists_injective_exchange_complexity
    (G : SimpleGraph V) (c : V → W) (h : ExchangeStructure G c) :
    ∃ o : LinearOrder V, letI := o;
      ∃ hwf : WellFoundedLT V, letI := hwf;
        ExchangeStructure G (id : V → V) ∧
        Function.Injective (id : V → V) ∧
        ∀ u w, c u < c w → u < w := by
  classical
  let f : V → W ×ₗ Cardinal.{u} := fun x => toLex (c x, embeddingToCardinal x)
  have hf : Function.Injective f := by
    intro x y hxy
    exact embeddingToCardinal.injective (congrArg Prod.snd hxy)
  let o : LinearOrder V := LinearOrder.lift' f hf
  let := o
  have hwf : WellFoundedLT V := InvImage.wf f wellFounded_lt
  let := hwf
  have hstrict : ∀ x y, c x < c y → x < y := by
    intro x y hxy
    exact Prod.Lex.left _ _ hxy
  refine ⟨o, hwf, ?_, Function.injective_id, hstrict⟩
  constructor
  · exact h.intervalApex
  · intro x y hxy
    obtain ⟨z, hz, hcz⟩ := h.descendingApex x y hxy
    refine ⟨z, hz, ?_⟩
    rcases lt_max_iff.mp hcz with hzx | hzy
    · exact lt_max_of_lt_left (hstrict z x hzx)
    · exact lt_max_of_lt_right (hstrict z y hzy)

end SeifertSurfaces
