import Section2.FlagExchangeComplex
import Section2.TieBreaking
import Section2.WeakRealization

/-!
# Theorem B: full-subtype and order-type alignment

Source: Lemma 2.2 and Theorem B, text lines 149--155 and 211--241.
The well-order is on the vertex type; all ordinal comparisons therefore live
in `Ordinal.{u}` regardless of the original complexity target's universe.
-/

namespace SeifertSurfaces.OrdinalAssembly

universe u v

variable {V : Type u}

/-- Lemma 2.2 lifted from exchange structures to the same actual flag complex.
Only the vertex order changes: the complex and realization remain identical. -/
theorem exchange_complex_refined_vertex_order
    {W : Type v} [LinearOrder W] [WellFoundedLT W]
    (X : AbstractSimplicialComplex V) (G : SimpleGraph V) (c : V → W)
    (hX : ExchangeComplex X G c) :
    ∃ o : LinearOrder V, letI := o;
      ∃ hwf : WellFoundedLT V, letI := hwf;
        ExchangeComplex X G (id : V → V) ∧
        ∀ a b, c a < c b → a < b := by
  obtain ⟨o, hwf, hG, hinj, hstrict⟩ :=
    exists_injective_exchange_complexity G c hX.toExchangeStructure
  let := o
  let := hwf
  have hNew : ExchangeComplex X G (id : V → V) := {
    toExchangeStructure := hG
    connected := hX.connected
    flag := hX.flag }
  exact ⟨o, hwf, hNew, hstrict⟩

variable [LinearOrder V] [WellFoundedLT V]

/-- Restricted identity complexity takes values in `V`; identity on `D` takes
values in `D`. Their comparisons agree under the subtype order, so they give
the same exchange complex. This is the exact bridge needed by the induction. -/
theorem restricted_identity_exchange_complex_iff
    (X : AbstractSimplicialComplex V) (G : SimpleGraph V) (D : Set V) :
    ExchangeComplex (fullSubcomplex X D) (G.induce D)
        (restrictedComplexity (id : V → V) D) ↔
      ExchangeComplex (fullSubcomplex X D) (G.induce D) (id : D → D) := by
  constructor <;> intro h
  · refine {
      intervalApex := h.intervalApex
      descendingApex := ?_
      connected := h.connected
      flag := h.flag }
    intro a b hab
    obtain ⟨x, hx, hlt⟩ := h.descendingApex a b hab
    refine ⟨x, hx, ?_⟩
    exact hlt
  · refine {
      intervalApex := h.intervalApex
      descendingApex := ?_
      connected := h.connected
      flag := h.flag }
    intro a b hab
    obtain ⟨x, hx, hlt⟩ := h.descendingApex a b hab
    refine ⟨x, hx, ?_⟩
    exact hlt

/-- A nonempty full downset is an exchange complex with its own identity
complexity, ready for the universal smaller-order induction hypothesis. -/
theorem ordered_full_downset_exchange_complex
    (X : AbstractSimplicialComplex V) (G : SimpleGraph V)
    (hX : ExchangeComplex X G (id : V → V))
    (D : Set V) (hD : ComplexityDownset (id : V → V) D) (hne : D.Nonempty) :
    ExchangeComplex (fullSubcomplex X D) (G.induce D) (id : D → D) := by
  exact (restricted_identity_exchange_complex_iff X G D).mp
    (nonempty_full_downset_exchange_complex X G id hX Function.injective_id D hD hne)

/-- Every strict initial segment is a downset. -/
theorem ordered_strict_sublevel_is_downset (v : V) :
    ComplexityDownset (id : V → V) (strictSublevel (id : V → V) v) := by
  intro a b hab hb
  exact hab.trans_lt hb

/-- Strict sublevels inherit exchange axioms and connectedness and are expressed
with the subtype's own identity complexity. -/
theorem ordered_nonempty_strict_sublevel_exchange_complex
    (X : AbstractSimplicialComplex V) (G : SimpleGraph V)
    (hX : ExchangeComplex X G (id : V → V)) (v : V)
    (hne : (strictSublevel (id : V → V) v).Nonempty) :
    ExchangeComplex (fullSubcomplex X (strictSublevel (id : V → V) v))
      (G.induce (strictSublevel (id : V → V) v))
      (id : strictSublevel (id : V → V) v → strictSublevel (id : V → V) v) := by
  exact ordered_full_downset_exchange_complex X G hX _
    (ordered_strict_sublevel_is_downset v) hne

/-- The descending link is another exchange complex, generally not an initial
sublevel of `X`. Its own vertex type and induced order are retained. -/
theorem ordered_nonempty_descending_link_exchange_complex
    (X : AbstractSimplicialComplex V) (G : SimpleGraph V)
    (hX : ExchangeComplex X G (id : V → V)) (v : V)
    (hne : (descendingLinkVertices G (id : V → V) v).Nonempty) :
    ExchangeComplex (fullSubcomplex X (descendingLinkVertices G (id : V → V) v))
      (G.induce (descendingLinkVertices G (id : V → V) v))
      (id : descendingLinkVertices G (id : V → V) v →
        descendingLinkVertices G (id : V → V) v) := by
  exact (restricted_identity_exchange_complex_iff X G _).mp
    (nonempty_full_descending_link_exchange_complex X G id hX Function.injective_id v hne)

/-- The order type of a strict initial segment is strictly smaller than the
ambient order type. `Ordinal.type_Iio_lt` alone states an equality, so the
generator must also use `Ordinal.typein_lt_type`. -/
theorem strict_sublevel_order_type_lt (v : V) :
    Ordinal.type (α := strictSublevel (id : V → V) v) (· < ·) <
      Ordinal.type (α := V) (· < ·) := by
  change Ordinal.type (α := Set.Iio v) (· < ·) < Ordinal.type (α := V) (· < ·)
  rw [Ordinal.type_Iio_lt]
  exact Ordinal.typein_lt_type (· < ·) v

/-- The link order-embeds in the strict initial segment. It need not be an
initial segment itself. -/
theorem descending_link_order_type_le_strict_sublevel (G : SimpleGraph V) (v : V) :
    Ordinal.type (α := descendingLinkVertices G (id : V → V) v) (· < ·) ≤
      Ordinal.type (α := strictSublevel (id : V → V) v) (· < ·) := by
  let e : ((· < ·) : descendingLinkVertices G id v →
      descendingLinkVertices G id v → Prop) ↪r
      ((· < ·) : strictSublevel id v → strictSublevel id v → Prop) :=
    RelEmbedding.ofMonotone (fun x => ⟨x.1, x.2.2⟩) (fun _ _ h => h)
  exact e.ordinal_type_le

/-- Consequently every descending link has strictly smaller order type. -/
theorem descending_link_order_type_lt (G : SimpleGraph V) (v : V) :
    Ordinal.type (α := descendingLinkVertices G (id : V → V) v) (· < ·) <
      Ordinal.type (α := V) (· < ·) := by
  exact (descending_link_order_type_le_strict_sublevel G v).trans_lt
    (strict_sublevel_order_type_lt v)

/-- The genuine limit-stage condition, equivalent to absence of a greatest
vertex in this linear order. -/
theorem no_greatest_iff_higher_vertex :
    (¬ ∃ v : V, ∀ w : V, w ≤ v) ↔ ∀ a : V, ∃ b : V, a < b := by
  classical
  simp only [not_exists, not_forall, not_le]

/-- In a nonempty order with no greatest vertex, every finite vertex set lies
in a nonempty strict initial segment. The extra vertex handles `F = ∅`. -/
theorem finite_vertices_below_nonempty_strict_sublevel [Nonempty V]
    (hnoMax : ∀ a : V, ∃ b : V, a < b) (F : Finset V) :
    ∃ v : V, (strictSublevel (id : V → V) v).Nonempty ∧ ∀ a ∈ F, a < v := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    obtain ⟨a⟩ := ‹Nonempty V›
    obtain ⟨v, hv⟩ := hnoMax a
    exact ⟨v, ⟨a, hv⟩, by simp⟩
  | @insert a F ha ih =>
    obtain ⟨v, hv, hF⟩ := ih
    rcases le_total a v with hav | hva
    · obtain ⟨b, hb⟩ := hnoMax v
      refine ⟨b, ⟨v, hb⟩, ?_⟩
      intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact hav.trans_lt hb
      · exact (hF q hq).trans hb
    · obtain ⟨b, hb⟩ := hnoMax a
      refine ⟨b, ⟨a, hb⟩, ?_⟩
      intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact hb
      · exact ((hF q hq).trans_le hva).trans hb

/-- At a greatest vertex, an empty strict sublevel forces the vertex type to
be a singleton. The vertex `v` itself supplies nonemptiness. -/
theorem subsingleton_of_empty_strict_sublevel_at_greatest
    (v : V) (hmax : ∀ w : V, w ≤ v)
    (hempty : ¬ (strictSublevel (id : V → V) v).Nonempty) :
    Subsingleton V := by
  have heq (w : V) : w = v := by
    apply le_antisymm (hmax w)
    exact not_lt.mp (fun hw => hempty ⟨w, hw⟩)
  exact ⟨fun a b => (heq a).trans (heq b).symm⟩

/-- A nonempty strict sublevel makes the greatest vertex nonleast and hence
its descending link nonempty by Lemma 2.4(2). -/
theorem descending_link_nonempty_at_greatest_with_lower_vertex
    (X : AbstractSimplicialComplex V) (G : SimpleGraph V)
    (hX : ExchangeComplex X G (id : V → V)) (v : V)
    (hmax : ∀ w : V, w ≤ v)
    (hlower : (strictSublevel (id : V → V) v).Nonempty) :
    (descendingLinkVertices G (id : V → V) v).Nonempty := by
  apply descending_link_nonempty_of_not_least G id hX.toExchangeGraph Function.injective_id v
  intro hleast
  obtain ⟨w, hw⟩ := hlower
  exact (not_lt_of_ge (hleast w)) hw

end SeifertSurfaces.OrdinalAssembly
