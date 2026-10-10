import Mathlib.Data.Prod.Lex
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Sort
import Mathlib.Order.OrderIsoNat
import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.LocallyFinite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Basic.Real.Basic
import Mathlib.Order.WellFounded
import Mathlib.SetTheory.Ordinal.Exponential
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# The discrete part of Lemma 4.8

Source: `references/seifert-surfaces.txt`, lines 469–503, Definition 4.7 and Lemma 4.8.

This file states the consequences of finite genus/area sublevels.  It does not
construct Seifert surfaces, their isotopy classes, genus, or geometric area.
In particular, `FiniteSublevels` is the outstanding geometric input 4.8(i),
not a proof or a formalization of that input.
-/

namespace SeifertSurfaces.Complexity

universe u

/-- The ambient space in which the source asserts closedness and discreteness.
It has the subspace topology and induced order from the real numbers. -/
abbrev PositiveReal := {a : ℝ // 0 < a}

/-- Genus is the first coordinate of the lexicographic order. -/
abbrev ComplexityValue := ℕ ×ₗ PositiveReal

/-- Numerical data needed by the discrete argument of Lemma 4.8.
There is deliberately no assertion that these are geometric invariants. -/
structure Data (V : Type u) where
  genus : V → ℕ
  area : V → PositiveReal

namespace Data

variable {V : Type u} (d : Data V)

/-- Definition 4.7's numerical pair, once the geometric invariants exist. -/
def value (v : V) : ComplexityValue := toLex (d.genus v, d.area v)

/-- The vertices of fixed genus with area at most a positive bound. -/
def sublevel (h : ℕ) (a : PositiveReal) : Set V :=
  {v | d.genus v = h ∧ d.area v ≤ a}

/-- Exactly the input 4.8(i) to the subsequent discrete argument. -/
def FiniteSublevels : Prop := ∀ h a, (d.sublevel h a).Finite

/-- The source's `W_h`, as a subset of the positive reals. -/
def areaValues (h : ℕ) : Set PositiveReal :=
  {a | ∃ v, d.genus v = h ∧ d.area v = a}

/-- The source's `W`, with the order induced from lexicographic complexity. -/
def attainedValues : Set ComplexityValue := Set.range d.value

/-- Auxiliary consequence of 4.8(i): bounded initial area spectra are finite. -/
theorem areaValues_sublevel_finite (hf : d.FiniteSublevels)
    (h : ℕ) (a : PositiveReal) :
    (d.areaValues h ∩ Set.Iic a).Finite := by
  have heq : d.areaValues h ∩ Set.Iic a = d.area '' d.sublevel h a := by
    ext b
    constructor
    · rintro ⟨⟨v, hv, rfl⟩, hle⟩
      exact ⟨v, ⟨hv, hle⟩, rfl⟩
    · rintro ⟨v, ⟨hv, hle⟩, rfl⟩
      exact ⟨⟨v, hv, rfl⟩, hle⟩
  rw [heq]
  exact (hf h a).image d.area

/-- The rank of an area in its fixed-genus spectrum. -/
noncomputable def areaRank (h : ℕ) (a : PositiveReal) : ℕ :=
  (d.areaValues h ∩ Set.Iio a).ncard

/-- Finite initial spectra give a strictly increasing natural rank. -/
lemma areaRank_strictMonoOn (hf : d.FiniteSublevels) (h : ℕ) :
    StrictMonoOn (d.areaRank h) (d.areaValues h) := by
  intro a ha b hb hab
  apply Set.ncard_lt_ncard
  · refine ⟨?_, ?_⟩
    · intro c hc
      exact ⟨hc.1, lt_trans hc.2 hab⟩
    · intro hba
      have : a < a := (hba ⟨ha, hab⟩).2
      exact lt_irrefl a this
  · exact (d.areaValues_sublevel_finite hf h b).subset
      (fun c hc => ⟨hc.1, (show c ≤ b from (show c < b from hc.2).le)⟩)

/-- Rank embeds each complete area fibre into the naturals. -/
noncomputable def areaOrderEmbedding (hf : d.FiniteSublevels) (h : ℕ) :
    d.areaValues h ↪o ℕ :=
  OrderEmbedding.ofStrictMono (fun a => d.areaRank h a)
    (fun a b hab => d.areaRank_strictMonoOn hf h a.property b.property hab)

/-- The second coordinate of an attained pair belongs to its genus fibre. -/
lemma attained_area_mem (x : d.attainedValues) :
    (ofLex x.val).2 ∈ d.areaValues (ofLex x.val).1 := by
  obtain ⟨v, hv⟩ := x.property
  rw [← hv]
  exact ⟨v, rfl, rfl⟩

/-- Genus together with the within-genus rank preserves lexicographic order. -/
noncomputable def attainedRankEmbedding (hf : d.FiniteSublevels) :
    d.attainedValues ↪o (ℕ ×ₗ ℕ) :=
  OrderEmbedding.ofStrictMono
    (fun x => toLex ((ofLex x.val).1, d.areaRank (ofLex x.val).1 (ofLex x.val).2))
    (by
      intro x y hxy
      rcases Prod.Lex.lt_iff.mp hxy with hg | ⟨hg, ha⟩
      · exact Prod.Lex.lt_iff.mpr (Or.inl hg)
      · apply Prod.Lex.lt_iff.mpr
        refine Or.inr ⟨hg, ?_⟩
        have hym := d.attained_area_mem y
        rw [← hg] at hym
        change d.areaRank (ofLex x.val).1 (ofLex x.val).2 <
          d.areaRank (ofLex y.val).1 (ofLex y.val).2
        rw [← hg]
        exact d.areaRank_strictMonoOn hf _ (d.attained_area_mem x) hym ha)

/-- Any positive-real spectrum with finite bounded initial segments is closed. -/
lemma isClosed_of_finite_initial (s : Set PositiveReal)
    (hf : ∀ a, (s ∩ Set.Iic a).Finite) : IsClosed s := by
  have hlocal : LocallyFinite (fun a : s => ({a.val} : Set PositiveReal)) := by
    intro x
    let b : PositiveReal := ⟨(x : ℝ) + 1, by linarith [x.property]⟩
    have hxb : x < b := by change (x : ℝ) < (x : ℝ) + 1; linarith
    refine ⟨Set.Iio b, Iio_mem_nhds hxb, ?_⟩
    apply ((hf b).preimage Subtype.val_injective.injOn).subset
    rintro a ⟨y, hy, hyb⟩
    have heq : y = a.val := Set.mem_singleton_iff.mp hy
    exact ⟨a.property, heq ▸ (show y ≤ b from (show y < b from hyb).le)⟩
  have heq : (⋃ a : s, ({a.val} : Set PositiveReal)) = s := by
    ext a
    simp
  rw [← heq]
  exact hlocal.isClosed_iUnion (fun _ => isClosed_singleton)

/-- Lemma 4.8(ii), closedness is in `ℝ_{>0}`, not in all of `ℝ`. -/
theorem areaValues_isClosed (hf : d.FiniteSublevels) (h : ℕ) :
    IsClosed (d.areaValues h) := by
  exact isClosed_of_finite_initial (d.areaValues h)
    (d.areaValues_sublevel_finite hf h)

/-- Lemma 4.8(ii): each area spectrum has discrete subspace topology. -/
theorem areaValues_discreteTopology (hf : d.FiniteSublevels) (h : ℕ) :
    DiscreteTopology (d.areaValues h) := by
  apply isDiscrete_iff_discreteTopology.mp
  apply isDiscrete_iff_forall_mem_exists_isClosed.mpr
  intro s hs
  refine ⟨s, isClosed_of_finite_initial s ?_, Set.inter_eq_left.mpr hs⟩
  intro a
  exact (d.areaValues_sublevel_finite hf h a).subset
    (fun x hx => ⟨hs hx.1, hx.2⟩)

/-- Lemma 4.8(ii), its exact finite-or-omega order-type alternative. -/
theorem areaValues_orderIso_fin_or_nat (hf : d.FiniteSublevels) (h : ℕ) :
    (∃ n : ℕ, Nonempty (d.areaValues h ≃o Fin n)) ∨
      Nonempty (d.areaValues h ≃o ℕ) := by
  classical
  let e := d.areaOrderEmbedding hf h
  by_cases hfin : Finite (d.areaValues h)
  · let := hfin
    let := Fintype.ofFinite (d.areaValues h)
    exact Or.inl ⟨Fintype.card (d.areaValues h),
      ⟨(Fintype.orderIsoFinOfCardEq (d.areaValues h) rfl).symm⟩⟩
  · let : Infinite (d.areaValues h) := not_finite_iff_infinite.mp hfin
    let : Infinite (Set.range e) := Infinite.of_injective e.orderIso e.orderIso.injective
    exact Or.inr ⟨e.orderIso.trans (Nat.Subtype.orderIsoOfNat (Set.range e)).symm⟩

/-- The well-order instance needed to express the ordinal part of 4.8(ii). -/
theorem areaValues_isWellOrder (hf : d.FiniteSublevels) (h : ℕ) :
    IsWellOrder (d.areaValues h) (· < ·) := by
  exact { wf := (d.areaOrderEmbedding hf h).wellFounded wellFounded_lt }

/-- Lemma 4.8(ii), order type at most omega.
`hW` is supplied by `areaValues_isWellOrder`, not a new geometric assumption. -/
theorem areaValues_orderType_le (hf : d.FiniteSublevels) (h : ℕ)
    (hW : IsWellOrder (d.areaValues h) (· < ·)) :
    @Ordinal.type (d.areaValues h) (· < ·) hW ≤ Ordinal.omega0 := by
  let := hW
  simpa only [Ordinal.type_nat_lt] using
    (d.areaOrderEmbedding hf h).ltEmbedding.ordinal_type_le

/-- Pure descent consequence: strict genus/area decrease is well-founded on
the original objects, even when distinct objects have the same complexity. -/
theorem value_lt_wellFounded (hf : d.FiniteSublevels) :
    WellFounded (fun v w : V => d.value v < d.value w) := by
  exact ((d.attainedRankEmbedding hf).wellFounded wellFounded_lt).onFun
    (f := fun v => (⟨d.value v, ⟨v, rfl⟩⟩ : d.attainedValues))

/-- Lemma 4.8(iii), the attained values are well-ordered. -/
theorem attainedValues_isWellOrder (hf : d.FiniteSublevels) :
    IsWellOrder d.attainedValues (· < ·) := by
  exact { wf := (d.attainedRankEmbedding hf).wellFounded wellFounded_lt }

/-- A useful equivalent route to 4.8(iii): rank each area inside its genus. -/
theorem attainedValues_orderEmbedding_nat_lex_nat (hf : d.FiniteSublevels) :
    Nonempty (d.attainedValues ↪o (ℕ ×ₗ ℕ)) := by
  exact ⟨d.attainedRankEmbedding hf⟩

/-- Lemma 4.8(iii), order type at most omega squared.
`hW` is the conclusion of the preceding well-order theorem. -/
theorem attainedValues_orderType_le (hf : d.FiniteSublevels)
    (hW : IsWellOrder d.attainedValues (· < ·)) :
    @Ordinal.type d.attainedValues (· < ·) hW ≤
      Ordinal.omega0 ^ (2 : Ordinal) := by
  let := hW
  have htype : Ordinal.type ((· < ·) : (ℕ ×ₗ ℕ) → (ℕ ×ₗ ℕ) → Prop) =
      Ordinal.omega0 ^ (2 : Ordinal) := by
    change Ordinal.type (Prod.Lex ((· < ·) : ℕ → ℕ → Prop) (· < ·)) = _
    rw [Ordinal.type_prod_lex, Ordinal.type_nat_lt]
    change Ordinal.omega0 * Ordinal.omega0 = Ordinal.omega0 ^ ((2 : ℕ) : Ordinal)
    rw [Ordinal.opow_natCast, pow_two]
  rw [← htype]
  exact (d.attainedRankEmbedding hf).ltEmbedding.ordinal_type_le

/-- The least-element clause explicitly asserted in Lemma 4.8(iii). -/
theorem attainedValues_exists_least (hf : d.FiniteSublevels)
    (s : Set d.attainedValues) (hs : s.Nonempty) :
    ∃ x ∈ s, ∀ y ∈ s, x ≤ y := by
  obtain ⟨x, hx, hmin⟩ :=
    ((d.attainedRankEmbedding hf).wellFounded wellFounded_lt).has_min s hs
  exact ⟨x, hx, fun y hy => le_of_not_gt (hmin y hy)⟩

/-- The countable sublevel exhaustion used in Lemma 4.8(iv). -/
theorem sublevels_nat_exhaust :
    (⋃ h : ℕ, ⋃ n : ℕ,
      {v : V | d.genus v = h ∧ (d.area v : ℝ) ≤ (n : ℝ)}) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro v
  obtain ⟨n, hn⟩ := exists_nat_ge (d.area v : ℝ)
  exact Set.mem_iUnion.mpr ⟨d.genus v, Set.mem_iUnion.mpr ⟨n, rfl, hn⟩⟩

/-- Lemma 4.8(iv); this concerns objects, not just their attained values. -/
theorem countable (hf : d.FiniteSublevels) : Countable V := by
  apply Set.countable_univ_iff.mp
  rw [← d.sublevels_nat_exhaust]
  apply Set.countable_iUnion
  intro h
  apply Set.countable_iUnion
  intro n
  let a : PositiveReal := ⟨(n : ℝ) + 1, by positivity⟩
  apply Set.Finite.countable
  apply (hf h a).subset
  intro v hv
  refine ⟨hv.1, ?_⟩
  change (d.area v : ℝ) ≤ (n : ℝ) + 1
  linarith [hv.2]

end Data
end SeifertSurfaces.Complexity
