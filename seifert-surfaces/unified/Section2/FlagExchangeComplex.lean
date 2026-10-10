import Section2.FlagComplex
import Section2.Heredity

namespace SeifertSurfaces

universe u v

variable {V : Type u} {W : Type v}

/-- Source-facing form of Lemma 2.4(1). -/
theorem nonempty_full_downset_exchange_complex
    [LinearOrder W] [WellFoundedLT W]
    (X : AbstractSimplicialComplex V) (G : SimpleGraph V) (c : V → W)
    (h : ExchangeComplex X G c) (hc : Function.Injective c)
    (D : Set V) (hD : ComplexityDownset c D) (hne : D.Nonempty) :
    ExchangeComplex (fullSubcomplex X D) (G.induce D)
      (restrictedComplexity c D) := by
  exact {
    toExchangeGraph := nonempty_complexity_downset_exchange_graph G c h.toExchangeGraph hc D hD hne
    flag := full_subcomplex_is_flag X G h.flag D
  }

/-- Source-facing form of Lemma 2.4(2). -/
theorem nonempty_full_descending_link_exchange_complex
    [LinearOrder W] [WellFoundedLT W]
    (X : AbstractSimplicialComplex V) (G : SimpleGraph V) (c : V → W)
    (h : ExchangeComplex X G c) (hc : Function.Injective c) (v : V)
    (hne : (descendingLinkVertices G c v).Nonempty) :
    ExchangeComplex (fullSubcomplex X (descendingLinkVertices G c v))
      (G.induce (descendingLinkVertices G c v))
      (restrictedComplexity c (descendingLinkVertices G c v)) := by
  exact {
    toExchangeGraph := nonempty_descending_link_exchange_graph G c h.toExchangeGraph hc v hne
    flag := full_subcomplex_is_flag X G h.flag (descendingLinkVertices G c v)
  }

end SeifertSurfaces
