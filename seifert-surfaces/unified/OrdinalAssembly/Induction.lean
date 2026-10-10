import OrdinalAssembly.OrderType
import OrdinalAssembly.CompactContainment
import TopologyAdapters.VertexAttachment

/-!
# Theorem B: universal induction on the vertex well-order

Source: `references/seifert-surfaces.txt`, lines 211--253, PDF pp. 5--6.
The induction motive ranges over every complex with the specified vertex order
type, so it applies to descending links rather than only to one filtration.
-/

namespace SeifertSurfaces.OrdinalAssembly

universe u v

/-- The exact-order-type form of the universal source induction assertion.
Every well-ordered vertex type in `Type u`, graph, and flag exchange complex
is quantified. This transparent predicate is the induction motive, not an
assumed contractibility interface. -/
def OrderedExchangeContractibleAt (alpha : Ordinal.{u}) : Prop :=
  ∀ (V : Type u) (o : LinearOrder V), letI := o;
    ∀ hwf : WellFoundedLT V, letI := hwf;
      ∀ (X : AbstractSimplicialComplex V) (G : SimpleGraph V),
        ExchangeComplex X G (id : V → V) →
        Ordinal.type (α := V) (· < ·) = alpha →
        ContractibleSpace (RealizationPoint X)

variable {V : Type u} [LinearOrder V] [WellFoundedLT V]

/-- A supplied strong induction hypothesis applies to a literal smaller full
subtype after the restricted-identity bridge. This conclusion keeps the actual
full-subcomplex weak realization; no replacement model is used. -/
theorem full_subcomplex_contractible_from_smaller_order
    (X : AbstractSimplicialComplex V) (G : SimpleGraph V)
    (D : Set V)
    (hD : ExchangeComplex (fullSubcomplex X D) (G.induce D) (id : D → D))
    (hsmaller : Ordinal.type (α := D) (· < ·) < Ordinal.type (α := V) (· < ·))
    (ih : ∀ beta : Ordinal.{u}, beta < Ordinal.type (α := V) (· < ·) →
      OrderedExchangeContractibleAt beta) :
    ContractibleSpace (RealizationPoint (fullSubcomplex X D)) := by
  exact ih _ hsmaller D inferInstance inferInstance (fullSubcomplex X D)
    (G.induce D) hD rfl

/-- The two actual successor premises are derived from strictly smaller
exchange complexes, including the descending link as its own subtype. -/
theorem greatest_vertex_smaller_stages_contractible
    (X : AbstractSimplicialComplex V) (G : SimpleGraph V)
    (hX : ExchangeComplex X G (id : V → V)) (v : V)
    (hmax : ∀ w : V, w ≤ v)
    (hlower : (strictSublevel (id : V → V) v).Nonempty)
    (ih : ∀ beta : Ordinal.{u}, beta < Ordinal.type (α := V) (· < ·) →
      OrderedExchangeContractibleAt beta) :
    ContractibleSpace (RealizationPoint
        (fullSubcomplex X (strictSublevel (id : V → V) v))) ∧
      ContractibleSpace (RealizationPoint
        (fullSubcomplex X (descendingLinkVertices G (id : V → V) v))) := by
  constructor
  · exact full_subcomplex_contractible_from_smaller_order X G _
      (ordered_nonempty_strict_sublevel_exchange_complex X G hX v hlower)
      (strict_sublevel_order_type_lt v) ih
  · exact full_subcomplex_contractible_from_smaller_order X G _
      (ordered_nonempty_descending_link_exchange_complex X G hX v
        (descending_link_nonempty_at_greatest_with_lower_vertex X G hX v hmax hlower))
      (descending_link_order_type_lt G v) ih

/-- Source successor stage: a greatest vertex with a lower vertex is attached
along its contractible descending link using the reviewed topology endpoint. -/
theorem ordered_exchange_contractible_at_greatest_vertex
    (X : AbstractSimplicialComplex V) (G : SimpleGraph V)
    (hX : ExchangeComplex X G (id : V → V)) (v : V)
    (hmax : ∀ w : V, w ≤ v)
    (hlower : (strictSublevel (id : V → V) v).Nonempty)
    (ih : ∀ beta : Ordinal.{u}, beta < Ordinal.type (α := V) (· < ·) →
      OrderedExchangeContractibleAt beta) :
    ContractibleSpace (RealizationPoint X) := by
  obtain ⟨hdelete, hlink⟩ :=
    greatest_vertex_smaller_stages_contractible X G hX v hmax hlower ih
  exact TopologyAdapters.maximum_vertex_successor_contractible X G hX.flag id
    Function.injective_id v hmax hdelete hlink

/-- Source limit stage: each finite set has a strictly smaller nonempty
exchange full subcomplex containing it, with contractibility supplied by ih. -/
theorem finite_contractible_carriers_of_no_greatest_vertex
    (X : AbstractSimplicialComplex V) (G : SimpleGraph V)
    (hX : ExchangeComplex X G (id : V → V))
    (hnoMax : ∀ a : V, ∃ b : V, a < b)
    (ih : ∀ beta : Ordinal.{u}, beta < Ordinal.type (α := V) (· < ·) →
      OrderedExchangeContractibleAt beta) :
    ∀ F : Finset V, ∃ D : Set V,
      (∀ a ∈ F, a ∈ D) ∧ ContractibleSpace (RealizationPoint (fullSubcomplex X D)) := by
  letI : Nonempty V := hX.connected.nonempty
  intro F
  obtain ⟨v, hv, hF⟩ := finite_vertices_below_nonempty_strict_sublevel hnoMax F
  refine ⟨strictSublevel (id : V → V) v, hF, ?_⟩
  exact full_subcomplex_contractible_from_smaller_order X G _
    (ordered_nonempty_strict_sublevel_exchange_complex X G hX v hv)
    (strict_sublevel_order_type_lt v) ih

/-- The no-greatest-vertex stage concludes actual contractibility by B7.
Arbitrary infinite orders are allowed; there is no countable cofinal sequence. -/
theorem ordered_exchange_contractible_without_greatest_vertex
    (X : AbstractSimplicialComplex V) (G : SimpleGraph V)
    (hX : ExchangeComplex X G (id : V → V))
    (hnoMax : ∀ a : V, ∃ b : V, a < b)
    (ih : ∀ beta : Ordinal.{u}, beta < Ordinal.type (α := V) (· < ·) →
      OrderedExchangeContractibleAt beta) :
    ContractibleSpace (RealizationPoint X) := by
  letI : Nonempty V := hX.connected.nonempty
  exact weak_realization_contractible_of_finite_carriers X
    (finite_contractible_carriers_of_no_greatest_vertex X G hX hnoMax ih)

/-- One universal well-founded induction step. The proof splits into the
singleton base, greatest-vertex successor, and no-greatest limit alternatives.
Nonemptiness is a consequence of exchange connectedness, not an extra premise. -/
theorem ordered_exchange_contractible_induction_step
    (alpha : Ordinal.{u})
    (ih : ∀ beta : Ordinal.{u}, beta < alpha → OrderedExchangeContractibleAt beta) :
    OrderedExchangeContractibleAt alpha := by
  classical
  intro V o hwf X G hX htype
  letI := o
  letI := hwf
  have ih' : ∀ beta : Ordinal.{u}, beta < Ordinal.type (α := V) (· < ·) →
      OrderedExchangeContractibleAt beta := by
    intro beta hbeta
    exact ih beta (htype ▸ hbeta)
  by_cases hmax : ∃ v : V, ∀ w : V, w ≤ v
  · obtain ⟨v, hv⟩ := hmax
    by_cases hlower : (strictSublevel (id : V → V) v).Nonempty
    · exact ordered_exchange_contractible_at_greatest_vertex X G hX v hv hlower ih'
    · letI : Nonempty V := ⟨v⟩
      letI : Subsingleton V := subsingleton_of_empty_strict_sublevel_at_greatest v hv hlower
      exact singleton_weak_realization_contractible X
  · exact ordered_exchange_contractible_without_greatest_vertex X G hX
      (no_greatest_iff_higher_vertex.mp hmax) ih'

/-- The universal arbitrary-ordinal induction, without any added topological
assumption or bound on the vertex order type. -/
theorem all_ordered_exchange_order_types_contractible (alpha : Ordinal.{u}) :
    OrderedExchangeContractibleAt alpha := by
  exact (wellFounded_lt : WellFounded ((· < ·) : Ordinal.{u} → Ordinal.{u} → Prop)).induction
    alpha ordered_exchange_contractible_induction_step

/-- Identity complexity on an arbitrary well-ordered vertex type gives a
contractible exchange realization. -/
theorem ordered_exchange_weak_realization_contractible
    (X : AbstractSimplicialComplex V) (G : SimpleGraph V)
    (hX : ExchangeComplex X G (id : V → V)) :
    ContractibleSpace (RealizationPoint X) := by
  exact all_ordered_exchange_order_types_contractible _ V inferInstance inferInstance X G hX rfl

/-- Final bridge for the existing guarded Theorem B declaration. Lemma 2.2
changes only the vertex order, preserving `X` and its actual realization.
This new helper does not edit or shadow `exchange_complex_contractible`. -/
theorem exchange_weak_realization_contractible_by_ordinal_induction
    {V : Type u} {W : Type v} [LinearOrder W] [WellFoundedLT W]
    (X : AbstractSimplicialComplex V) (G : SimpleGraph V) (c : V → W)
    (hX : ExchangeComplex X G c) :
    ContractibleSpace (RealizationPoint X) := by
  obtain ⟨o, hwf, hordered, _⟩ := exchange_complex_refined_vertex_order X G c hX
  letI := o
  letI := hwf
  exact ordered_exchange_weak_realization_contractible X G hordered

/-- B9: each nonempty full complexity downset inherits both the isometric
graph inclusion and the actual contractible weak realization. -/
theorem nonempty_full_downset_isometric_and_contractible
    {V : Type u} {W : Type v} [LinearOrder W] [WellFoundedLT W]
    (X : AbstractSimplicialComplex V) (G : SimpleGraph V) (c : V → W)
    (hX : ExchangeComplex X G c) (hc : Function.Injective c)
    (D : Set V) (hD : ComplexityDownset c D) (hne : D.Nonempty) :
    (∀ a b : D, (G.induce D).edist a b = G.edist a.1 b.1) ∧
      ContractibleSpace (RealizationPoint (fullSubcomplex X D)) := by
  constructor
  · exact complexity_downset_edist G c hX.toExchangeGraph hc D hD
  · exact exchange_weak_realization_contractible_by_ordinal_induction
      (fullSubcomplex X D) (G.induce D) (restrictedComplexity c D)
      (nonempty_full_downset_exchange_complex X G c hX hc D hD hne)

end SeifertSurfaces.OrdinalAssembly
