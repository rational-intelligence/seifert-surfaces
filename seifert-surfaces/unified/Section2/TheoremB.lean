import Section2.FlagComplex
import Section2.WeakRealization
import OrdinalAssembly.Induction

namespace SeifertSurfaces

universe u v

/-- Theorem B: every exchange complex has contractible geometric realization.
`RealizationPoint X` has the actual weak topology for finite simplex inclusions.
There is no finiteness/local-finiteness hypothesis and no assumed topology or
contractibility interface. -/
theorem exchange_complex_contractible
    {V : Type u} {W : Type v} [LinearOrder W] [WellFoundedLT W]
    (X : AbstractSimplicialComplex V) (G : SimpleGraph V) (c : V → W)
    (h : ExchangeComplex X G c) :
    ContractibleSpace (RealizationPoint X) := by
  exact OrdinalAssembly.exchange_weak_realization_contractible_by_ordinal_induction X G c h

end SeifertSurfaces
