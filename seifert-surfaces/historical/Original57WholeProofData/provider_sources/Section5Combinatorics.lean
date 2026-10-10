import Mathlib
import Section5Arithmetic

/-!
# Section 5: graph consequences, conditional on genuine exchange production

These declarations formalize Proposition 5.2's combinatorial implication.
`HasExchangePairs` is the explicit unproved input corresponding to Theorem 5.1;
it is not an asserted theorem about incompressible Seifert surfaces.
Both vertices of an exchange pair precede the quantifier over later vertices.
-/

namespace SeifertSurfaces.Section5.Combinatorics

def complexity {V : Type*} (genus : V → ℕ) (area : V → ℝ) (v : V) : ℕ ×ₗ ℝ :=
  toLex (genus v, area v)

def EqualOrAdjacent {V : Type*} (G : SimpleGraph V) (v w : V) : Prop :=
  v = w ∨ G.Adj v w

/-- Definition 2.1's apex: membership and domination of every common neighbour. -/
def IsTwoIntervalApex {V : Type*} (G : SimpleGraph V) (u w apex : V) : Prop :=
  apex ∈ G.commonNeighbors u w ∧
    ∀ z ∈ G.commonNeighbors u w, EqualOrAdjacent G apex z

/-- The full graph-level conclusion (a)--(d) of Theorem 5.1, for fixed outputs.
This is a specification, not a replacement for the geometric theorem. -/
def IsExchangePair {V : Type*} (G : SimpleGraph V) (genus : V → ℕ) (area : V → ℝ)
    (x u w up down : V) : Prop :=
  (EqualOrAdjacent G up x ∧ EqualOrAdjacent G up u ∧ EqualOrAdjacent G up w) ∧
  (EqualOrAdjacent G down x ∧ EqualOrAdjacent G down u ∧ EqualOrAdjacent G down w) ∧
  (∀ z, EqualOrAdjacent G z u → EqualOrAdjacent G z w →
    EqualOrAdjacent G z up ∧ EqualOrAdjacent G z down) ∧
  (genus up + genus down ≤ genus u + genus w) ∧
  (genus up + genus down = genus u + genus w → area up + area down < area u + area w)

/-- The explicit missing geometric producer. No canonical choice function is demanded. -/
def HasExchangePairs {V : Type*} (G : SimpleGraph V) (genus : V → ℕ) (area : V → ℝ) : Prop :=
  ∀ x u w, G.dist x u = 1 → G.dist x w = 1 → G.dist u w = 2 →
    ∃ up down, IsExchangePair G genus area x u w up down

/-- Proposition 5.2(1), stronger witness-preserving reading: both given outputs are apices. -/
theorem exchange_pair_outputs_are_apices
    {V : Type*} (G : SimpleGraph V) (genus : V → ℕ) (area : V → ℝ)
    (x u w up down : V) (hdistance : G.dist u w = 2)
    (hpair : IsExchangePair G genus area x u w up down) :
    IsTwoIntervalApex G u w up ∧ IsTwoIntervalApex G u w down := by
  have hcommon : ∀ y, EqualOrAdjacent G y u → EqualOrAdjacent G y w →
      y ∈ G.commonNeighbors u w := by
    intro y hyu hyw
    rcases hyu with rfl | hyu
    · rcases hyw with heq | hadj
      · subst w
        simp at hdistance
      · have hone := G.dist_eq_one_iff_adj.mpr hadj
        omega
    · rcases hyw with rfl | hyw
      · have hone := G.dist_eq_one_iff_adj.mpr hyu.symm
        omega
      · exact G.mem_commonNeighbors.mpr ⟨hyu.symm, hyw.symm⟩
  have hsymm : ∀ v z, EqualOrAdjacent G z v → EqualOrAdjacent G v z := by
    intro v z h
    rcases h with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  rcases hpair with ⟨⟨_, hupu, hupw⟩, ⟨_, hdownu, hdownw⟩, hdominate, _, _⟩
  constructor
  · refine ⟨hcommon up hupu hupw, ?_⟩
    intro z hz
    have hz' := G.mem_commonNeighbors.mp hz
    exact hsymm up z (hdominate z (Or.inr hz'.1.symm) (Or.inr hz'.2.symm)).1
  · refine ⟨hcommon down hdownu hdownw, ?_⟩
    intro z hz
    have hz' := G.mem_commonNeighbors.mp hz
    exact hsymm down z (hdominate z (Or.inr hz'.1.symm) (Or.inr hz'.2.symm)).2

/-- Existence of a common neighbour uses Mathlib's actual graph distance. -/
theorem distance_two_has_common_neighbor
    {V : Type*} (G : SimpleGraph V) (u w : V) (hdistance : G.dist u w = 2) :
    ∃ x, G.dist x u = 1 ∧ G.dist x w = 1 := by
  have hreachable : G.Reachable u w :=
    SimpleGraph.Reachable.of_dist_ne_zero (by omega)
  have hedist : G.edist u w = 2 := by
    rw [← hreachable.coe_dist_eq_edist, hdistance]
    norm_num
  obtain ⟨x, hx⟩ := (G.edist_eq_two_iff.mp hedist).2.2
  have hx' := G.mem_commonNeighbors.mp hx
  exact ⟨x, G.dist_eq_one_iff_adj.mpr hx'.1.symm,
    G.dist_eq_one_iff_adj.mpr hx'.2.symm⟩

/-- Proposition 5.2's local descent, with the descended vertex one of the same fixed outputs. -/
theorem local_descent_at_apex
    {V : Type*} (G : SimpleGraph V) (genus : V → ℕ) (area : V → ℝ)
    (x u w up down : V) (hdistance : G.dist u w = 2)
    (hpair : IsExchangePair G genus area x u w up down)
    (hu : complexity genus area u ≤ complexity genus area x)
    (hw : complexity genus area w ≤ complexity genus area x) :
    ∃ y, (y = up ∨ y = down) ∧ IsTwoIntervalApex G u w y ∧
      complexity genus area y < complexity genus area x ∧ genus y ≤ genus x := by
  have hapices := exchange_pair_outputs_are_apices G genus area x u w up down hdistance hpair
  have hdescent := SeifertSurfaces.Section5.local_descent_of_exchange_inequalities
    (genus x) (genus u) (genus w) (genus up) (genus down)
    (area x) (area u) (area w) (area up) (area down)
    hu hw hpair.2.2.2.1 hpair.2.2.2.2
  rcases hdescent with ⟨hlt, hgenus⟩ | ⟨hlt, hgenus⟩
  · exact ⟨up, Or.inl rfl, hapices.1, hlt, hgenus⟩
  · exact ⟨down, Or.inr rfl, hapices.2, hlt, hgenus⟩

/-- Proposition 5.2(1)--(3), conditional on the explicitly missing geometric theorem
and Lemma 4.8(iii). The *same* apex satisfies descent and every genus truncation. -/
theorem descending_apex_of_exchange
    {V : Type*} (G : SimpleGraph V) (genus : V → ℕ) (area : V → ℝ)
    (hexchange : HasExchangePairs G genus area)
    (hwellFounded : WellFounded (fun v w => complexity genus area v < complexity genus area w))
    (u w : V) (hdistance : G.dist u w = 2) :
    ∃ x, IsTwoIntervalApex G u w x ∧
      complexity genus area x < max (complexity genus area u) (complexity genus area w) ∧
      ∀ bound : ℕ, genus u ≤ bound → genus w ≤ bound → genus x ≤ bound := by
  obtain ⟨initial, hinitialu, hinitialw⟩ := distance_two_has_common_neighbor G u w hdistance
  obtain ⟨up, down, hpair⟩ := hexchange initial u w hinitialu hinitialw hdistance
  have hinitialApex :=
    (exchange_pair_outputs_are_apices G genus area initial u w up down hdistance hpair).1
  obtain ⟨x, hx, hminimal⟩ :=
    hwellFounded.has_min {v | IsTwoIntervalApex G u w v} ⟨up, hinitialApex⟩
  have hdesc : complexity genus area x < max (complexity genus area u) (complexity genus area w) := by
    by_contra h
    have hmax : max (complexity genus area u) (complexity genus area w) ≤
        complexity genus area x := le_of_not_gt h
    have hu : complexity genus area u ≤ complexity genus area x :=
      (le_max_left _ _).trans hmax
    have hw : complexity genus area w ≤ complexity genus area x :=
      (le_max_right _ _).trans hmax
    have hxu := G.mem_commonNeighbors.mp hx.1
    obtain ⟨nextUp, nextDown, hnext⟩ := hexchange x u w
      (G.dist_eq_one_iff_adj.mpr hxu.1.symm)
      (G.dist_eq_one_iff_adj.mpr hxu.2.symm) hdistance
    obtain ⟨y, _, hy, hylt, _⟩ :=
      local_descent_at_apex G genus area x u w nextUp nextDown hdistance hnext hu hw
    exact hminimal y hy hylt
  refine ⟨x, hx, hdesc, ?_⟩
  intro bound hu hw
  have hgenus := SeifertSurfaces.Section5.genus_le_of_complexity_lt_max
    (genus x) (genus u) (genus w) (area x) (area u) (area w) hdesc
  exact hgenus.trans (max_le hu hw)

end SeifertSurfaces.Section5.Combinatorics
