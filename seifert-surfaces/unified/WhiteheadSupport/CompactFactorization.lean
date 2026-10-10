import Section2.FlagComplex
import Section2.FlagExchangeComplex
import Section2.WeakRealization
import WhiteheadSupport.BasedLoops
import TopologyAdapters.FullSubcomplexTopology

/-!
Compact-factorization obligations for Theorem B, PDF p. 6, text lines 243-252.
The full subcomplex and weak realization are the existing Section 2 objects.
Factorization is specified by its barycentric coordinates, so this interface
does not depend on a second owner's unproved choice of an inclusion adapter.
Both ambient and lifted maps carry their actual continuity certificates.
-/

namespace SeifertSurfaces.WhiteheadSupport

universe u v w

open Topology

variable {V : Type u} {W : Type v} {A : Type w}

open TopologyAdapters

/-- The exact pointwise coordinate equation for the full-subcomplex inclusion. -/
def FullPointCorrespondence (X : AbstractSimplicialComplex V) (D : Set V)
    (x : RealizationPoint X) (xD : RealizationPoint (fullSubcomplex X D)) : Prop :=
  (∀ v : D, x.weight v.1 = xD.weight v) ∧
  (∀ v : V, v ∉ D → x.weight v = 0)

/-- A continuous lift through the full subcomplex, with the ambient inclusion
expressed by its defining barycentric coordinate formula. -/
def FactorsThroughFullSubcomplex [TopologicalSpace A]
    (X : AbstractSimplicialComplex V) (D : Set V)
    (f : C(A, RealizationPoint X))
    (g : C(A, RealizationPoint (fullSubcomplex X D))) : Prop :=
  ∀ a : A, FullPointCorrespondence X D (f a) (g a)

private theorem weak_point_eq_of_weights {X : AbstractSimplicialComplex V}
    {x y : RealizationPoint X} (h : x.weight = y.weight) : x = y := by
  cases x
  cases y
  cases h
  rfl

private theorem correspondence_iff_ambient_eq (X : AbstractSimplicialComplex V)
    (D : Set V) (x : RealizationPoint X)
    (xD : RealizationPoint (fullSubcomplex X D)) :
    FullPointCorrespondence X D x xD ↔ fullToAmbient X D xD = x := by
  classical
  constructor
  · intro h
    apply weak_point_eq_of_weights
    funext v
    by_cases hv : v ∈ D
    · exact (fullToAmbient_weight_of_mem X D xD v hv).trans (h.1 ⟨v, hv⟩).symm
    · exact (fullToAmbient_weight_of_not_mem X D xD v hv).trans (h.2 v hv).symm
  · intro h
    constructor
    · intro v
      rw [← h]
      exact fullToAmbient_weight_of_mem X D xD v.1 v.2
    · intro v hv
      rw [← h]
      exact fullToAmbient_weight_of_not_mem X D xD v hv

private theorem factor_supported_map [TopologicalSpace A]
    (X : AbstractSimplicialComplex V) (D : Set V)
    (f : C(A, RealizationPoint X))
    (h : ∀ a v, v ∉ D → (f a).weight v = 0) :
    ∃ g : C(A, RealizationPoint (fullSubcomplex X D)),
      FactorsThroughFullSubcomplex X D f g := by
  let hf : ∀ a, f a ∈ fullSupportLocus X D := h
  refine ⟨fullSubcomplexFactor X D f hf, ?_⟩
  intro a
  exact (correspondence_iff_ambient_eq X D _ _).mpr
    (fullSubcomplexFactor_commutes X D f hf a)

private theorem finite_set_strict_bound [LinearOrder W] [Nonempty V]
    (c : V → W) (hnoMax : ∀ a : V, ∃ b : V, c a < c b) (F : Finset V) :
    ∃ v : V, (strictSublevel c v).Nonempty ∧ ∀ a ∈ F, c a < c v := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    obtain ⟨a⟩ := ‹Nonempty V›
    obtain ⟨v, hv⟩ := hnoMax a
    exact ⟨v, ⟨a, hv⟩, by simp⟩
  | @insert a F ha ih =>
    obtain ⟨v, hv, hF⟩ := ih
    rcases le_total (c a) (c v) with hav | hva
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
      · exact (hF q hq).trans_le hva |>.trans hb

private theorem loop_common_finite_support (X : AbstractSimplicialComplex V)
    (n : ℕ) (x : RealizationPoint X) (f : GenLoop (Fin n) (RealizationPoint X) x) :
    ∃ F : Finset V, (∀ v ∉ F, x.weight v = 0) ∧
      ∀ a v, v ∉ F → (f a).weight v = 0 := by
  classical
  obtain ⟨F, hF⟩ := compact_has_finite_vertex_support X (Set.range f.val)
    (isCompact_range f.val.continuous)
  obtain ⟨σ, hσ, hx, hsum⟩ := x.liesInFace
  refine ⟨F ∪ σ, ?_, ?_⟩
  · intro v hv
    exact hx v (fun h => hv (Finset.mem_union.mpr (Or.inr h)))
  · intro a v hv
    exact hF (f a) ⟨a, rfl⟩ v (fun h => hv (Finset.mem_union.mpr (Or.inl h)))

private theorem lift_supported_loop (X : AbstractSimplicialComplex V) (D : Set V)
    (n : ℕ) (x : RealizationPoint X) (f : GenLoop (Fin n) (RealizationPoint X) x)
    (hx : ∀ v ∉ D, x.weight v = 0)
    (hf : ∀ a v, v ∉ D → (f a).weight v = 0) :
    ∃ xD : RealizationPoint (fullSubcomplex X D),
      ∃ g : GenLoop (Fin n) (RealizationPoint (fullSubcomplex X D)) xD,
        FullPointCorrespondence X D x xD ∧
        FactorsThroughFullSubcomplex X D f.val g.val := by
  let xD := supportedToFull X D ⟨x, hx⟩
  have hbase : fullToAmbient X D xD = x :=
    congrArg Subtype.val (fullToSupported_supportedToFull X D ⟨x, hx⟩)
  let hg : ∀ a, f a ∈ fullSupportLocus X D := hf
  let fg := fullSubcomplexFactor X D f.val hg
  have hfg (a) : fullToAmbient X D (fg a) = f a :=
    fullSubcomplexFactor_commutes X D f.val hg a
  let g : GenLoop (Fin n) (RealizationPoint (fullSubcomplex X D)) xD :=
    ⟨fg, fun a ha => (fullToAmbient_injective X D)
      ((hfg a).trans ((GenLoop.boundary f a ha).trans hbase.symm))⟩
  refine ⟨xD, g, (correspondence_iff_ambient_eq X D x xD).mpr hbase, ?_⟩
  intro a
  exact (correspondence_iff_ambient_eq X D (f a) (fg a)).mpr (hfg a)

/-- Compact maps have a common finite set of supporting vertices. This concerns
the weak finite-face topology, without local finiteness of the complex. -/
theorem compact_map_has_finite_support
    [TopologicalSpace A] [CompactSpace A]
    (X : AbstractSimplicialComplex V) (f : C(A, RealizationPoint X)) :
    ∃ F : Finset V, ∀ a : A, ∀ v : V, v ∉ F → (f a).weight v = 0 := by
  obtain ⟨F, hF⟩ := compact_has_finite_vertex_support X (Set.range f)
    (isCompact_range f.continuous)
  exact ⟨F, fun a v hv => hF (f a) ⟨a, rfl⟩ v hv⟩

/-- Finite support gives an actual continuous factor through the literal full
subcomplex, rather than only a set-theoretic support bound. -/
theorem compact_map_factors_finite_full_subcomplex
    [TopologicalSpace A] [CompactSpace A]
    (X : AbstractSimplicialComplex V) (f : C(A, RealizationPoint X)) :
    ∃ F : Finset V, ∃ g : C(A, RealizationPoint (fullSubcomplex X (F : Set V))),
      FactorsThroughFullSubcomplex X (F : Set V) f g := by
  obtain ⟨F, hF⟩ := compact_map_has_finite_support X f
  obtain ⟨g, hg⟩ := factor_supported_map X (F : Set V) f hF
  exact ⟨F, g, hg⟩

/-- At a limit stage the complexity has no greatest vertex. The common finite
support is therefore contained strictly below some vertex. -/
theorem compact_map_factors_strict_sublevel
    [LinearOrder W] [Nonempty V] [TopologicalSpace A] [CompactSpace A]
    (X : AbstractSimplicialComplex V) (c : V → W)
    (hnoMax : ∀ a : V, ∃ b : V, c a < c b)
    (f : C(A, RealizationPoint X)) :
    ∃ v : V, (strictSublevel c v).Nonempty ∧
      ∃ g : C(A, RealizationPoint (fullSubcomplex X (strictSublevel c v))),
        FactorsThroughFullSubcomplex X (strictSublevel c v) f g := by
  obtain ⟨F, hF⟩ := compact_map_has_finite_support X f
  obtain ⟨v, hv, hbound⟩ := finite_set_strict_bound c hnoMax F
  refine ⟨v, hv, ?_⟩
  apply factor_supported_map
  intro a q hq
  apply hF a q
  exact fun hmem => hq (hbound q hmem)

/-- Exchange-specific factorization keeps the smaller stage's exchange axioms
as a proved conclusion. It does not assume contractibility of that stage. -/
theorem compact_map_factors_exchange_strict_sublevel
    [LinearOrder W] [WellFoundedLT W] [TopologicalSpace A] [CompactSpace A]
    (X : AbstractSimplicialComplex V) (G : SimpleGraph V) (c : V → W)
    (hX : ExchangeComplex X G c) (hc : Function.Injective c)
    (hnoMax : ∀ a : V, ∃ b : V, c a < c b)
    (f : C(A, RealizationPoint X)) :
    ∃ v : V, (strictSublevel c v).Nonempty ∧
      ExchangeComplex (fullSubcomplex X (strictSublevel c v))
        (G.induce (strictSublevel c v))
        (restrictedComplexity c (strictSublevel c v)) ∧
      ∃ g : C(A, RealizationPoint (fullSubcomplex X (strictSublevel c v))),
        FactorsThroughFullSubcomplex X (strictSublevel c v) f g := by
  let : Nonempty V := hX.connected.nonempty
  obtain ⟨v, hv, g, hg⟩ := compact_map_factors_strict_sublevel X c hnoMax f
  exact ⟨v, hv, nonempty_full_downset_exchange_complex X G c hX hc
    (strictSublevel c v) (fun _ _ hle hlt => hle.trans_lt hlt) hv, g, hg⟩

/-- The finite support of the basepoint is included even in dimension zero,
whose cube boundary is empty and hence need not meet the basepoint. -/
theorem gen_loop_factors_strict_sublevel
    [LinearOrder W]
    (X : AbstractSimplicialComplex V) (c : V → W)
    (hnoMax : ∀ a : V, ∃ b : V, c a < c b)
    (n : ℕ) (x : RealizationPoint X) (f : GenLoop (Fin n) (RealizationPoint X) x) :
    ∃ v : V,
      ∃ xD : RealizationPoint (fullSubcomplex X (strictSublevel c v)),
      ∃ g : GenLoop (Fin n)
        (RealizationPoint (fullSubcomplex X (strictSublevel c v))) xD,
      FullPointCorrespondence X (strictSublevel c v) x xD ∧
      FactorsThroughFullSubcomplex X (strictSublevel c v) f.val g.val := by
  obtain ⟨σ, hσ, hx, hsum⟩ := x.liesInFace
  obtain ⟨a, ha⟩ := (X.isRelLowerSet_faces hσ).1
  let : Nonempty V := ⟨a⟩
  obtain ⟨F, hxF, hfF⟩ := loop_common_finite_support X n x f
  obtain ⟨v, hv, hbound⟩ := finite_set_strict_bound c hnoMax F
  refine ⟨v, ?_⟩
  apply lift_supported_loop X (strictSublevel c v) n x f
  · intro q hq
    exact hxF q (fun hmem => hq (hbound q hmem))
  · intro a q hq
    exact hfF a q (fun hmem => hq (hbound q hmem))

/-- The smaller stage of a factored based loop is itself an exchange complex,
with the literal induced graph and the restricted original complexity. -/
theorem gen_loop_factors_exchange_strict_sublevel
    [LinearOrder W] [WellFoundedLT W]
    (X : AbstractSimplicialComplex V) (G : SimpleGraph V) (c : V → W)
    (hX : ExchangeComplex X G c) (hc : Function.Injective c)
    (hnoMax : ∀ a : V, ∃ b : V, c a < c b)
    (n : ℕ) (x : RealizationPoint X) (f : GenLoop (Fin n) (RealizationPoint X) x) :
    ∃ v : V, (strictSublevel c v).Nonempty ∧
      ExchangeComplex (fullSubcomplex X (strictSublevel c v))
        (G.induce (strictSublevel c v))
        (restrictedComplexity c (strictSublevel c v)) ∧
      ∃ xD : RealizationPoint (fullSubcomplex X (strictSublevel c v)),
      ∃ g : GenLoop (Fin n)
        (RealizationPoint (fullSubcomplex X (strictSublevel c v))) xD,
      FullPointCorrespondence X (strictSublevel c v) x xD ∧
      FactorsThroughFullSubcomplex X (strictSublevel c v) f.val g.val := by
  obtain ⟨v, xD, g, hxD, hg⟩ := gen_loop_factors_strict_sublevel X c hnoMax n x f
  obtain ⟨σ, hσ, hs, hsum⟩ := xD.liesInFace
  obtain ⟨a, ha⟩ := ((fullSubcomplex X (strictSublevel c v)).isRelLowerSet_faces hσ).1
  have hv : (strictSublevel c v).Nonempty := ⟨a.1, a.2⟩
  exact ⟨v, hv, nonempty_full_downset_exchange_complex X G c hX hc
    (strictSublevel c v) (fun _ _ hle hlt => hle.trans_lt hlt) hv, xD, g, hxD, hg⟩

/-- Contraction of a lifted full-subcomplex loop transports to a nullhomotopy
of the original based loop in the ambient weak realization. -/
theorem gen_loop_nullhomotopic_of_contractible_full_lift
    (X : AbstractSimplicialComplex V) (D : Set V)
    [ContractibleSpace (RealizationPoint (fullSubcomplex X D))]
    (n : ℕ) (hn : 1 ≤ n)
    (x : RealizationPoint X) (xD : RealizationPoint (fullSubcomplex X D))
    (f : GenLoop (Fin n) (RealizationPoint X) x)
    (g : GenLoop (Fin n) (RealizationPoint (fullSubcomplex X D)) xD)
    (hpoint : FullPointCorrespondence X D x xD)
    (hmap : FactorsThroughFullSubcomplex X D f.val g.val) :
    GenLoop.Homotopic f
      (GenLoop.const (N := Fin n) (X := RealizationPoint X) (x := x)) := by
  let j : C(RealizationPoint (fullSubcomplex X D), RealizationPoint X) :=
    ⟨fullToAmbient X D, continuous_fullToAmbient X D⟩
  exact cube_loop_nullhomotopic_of_contractible_factor n hn x xD j
    ((correspondence_iff_ambient_eq X D x xD).mp hpoint) f g
    (fun a => (correspondence_iff_ambient_eq X D (f a) (g a)).mp (hmap a))

/-- A version directly indexed by ordinals. Every vertex rank is below the
specified limit; finite support has a common strictly smaller ordinal bound. -/
theorem compact_map_factors_ordinal_sublevel
    [TopologicalSpace A] [CompactSpace A]
    (X : AbstractSimplicialComplex V) (rank : V → Ordinal.{u})
    (lambda : Ordinal.{u}) (hlambda : Order.IsSuccLimit lambda)
    (hbound : ∀ v : V, rank v < lambda)
    (f : C(A, RealizationPoint X)) :
    ∃ alpha : Ordinal.{u}, 0 < alpha ∧ alpha < lambda ∧
      ∃ g : C(A, RealizationPoint (fullSubcomplex X {v : V | rank v < alpha})),
        FactorsThroughFullSubcomplex X {v : V | rank v < alpha} f g := by
  classical
  obtain ⟨F, hF⟩ := compact_map_has_finite_support X f
  let alpha := Order.succ (F.sup rank)
  have ha : alpha < lambda := hlambda.succ_lt
    ((Finset.sup_lt_iff hlambda.pos).mpr (fun v _ => hbound v))
  refine ⟨alpha, lt_of_le_of_lt (zero_le : 0 ≤ F.sup rank) (Order.lt_succ _), ha, ?_⟩
  apply factor_supported_map
  intro a v hv
  apply hF a v
  intro hmem
  exact hv ((Finset.le_sup (f := rank) hmem).trans_lt (Order.lt_succ _))

/-- Based factorization with an ordinal bound also controls the specified
basepoint, independently of whether it belongs to the cube map's image. -/
theorem gen_loop_factors_ordinal_sublevel
    (X : AbstractSimplicialComplex V) (rank : V → Ordinal.{u})
    (lambda : Ordinal.{u}) (hlambda : Order.IsSuccLimit lambda)
    (hbound : ∀ v : V, rank v < lambda)
    (n : ℕ) (x : RealizationPoint X) (f : GenLoop (Fin n) (RealizationPoint X) x) :
    ∃ alpha : Ordinal.{u}, 0 < alpha ∧ alpha < lambda ∧
      ∃ xD : RealizationPoint (fullSubcomplex X {v : V | rank v < alpha}),
      ∃ g : GenLoop (Fin n)
        (RealizationPoint (fullSubcomplex X {v : V | rank v < alpha})) xD,
      FullPointCorrespondence X {v : V | rank v < alpha} x xD ∧
      FactorsThroughFullSubcomplex X {v : V | rank v < alpha} f.val g.val := by
  classical
  obtain ⟨F, hxF, hfF⟩ := loop_common_finite_support X n x f
  let alpha := Order.succ (F.sup rank)
  have ha : alpha < lambda := hlambda.succ_lt
    ((Finset.sup_lt_iff hlambda.pos).mpr (fun v _ => hbound v))
  refine ⟨alpha, lt_of_le_of_lt (zero_le : 0 ≤ F.sup rank) (Order.lt_succ _), ha, ?_⟩
  apply lift_supported_loop X {v : V | rank v < alpha} n x f
  · intro v hv
    exact hxF v (fun hmem => hv ((Finset.le_sup (f := rank) hmem).trans_lt (Order.lt_succ _)))
  · intro a v hv
    exact hfF a v (fun hmem => hv ((Finset.le_sup (f := rank) hmem).trans_lt (Order.lt_succ _)))

end SeifertSurfaces.WhiteheadSupport
