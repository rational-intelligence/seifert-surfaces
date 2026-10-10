import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Tactic.Linarith
import Mathlib.Order.WellFounded

/-!
# Section 6: concrete support statements, pending fidelity review

Source: references/seifert-surfaces.txt, lines 58–78 and 926–1076.
These are algebraic/order support obligations, not Theorems A, C, D or the
geometric conclusions of Lemmas 6.1 and 6.2. No knot, embedding, compression,
linking-number construction or Seifert-complex realization is supplied here.
All theorem bodies intentionally remain `sorry` for the Formal Generator.
-/

namespace SeifertSection6

open scoped BigOperators

universe u v

/-- Finite linking-number data. Realization by an oriented link is a separate bridge. -/
structure LinkingMatrix (ι : Type u) where
  entry : ι → ι → ℤ
  symmetric : ∀ i j, entry i j = entry j i
  diagonal_zero : ∀ i, entry i i = 0

section Linking

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Total linking with the part of a partition opposite to `m`, not a single entry. -/
def oppositeLinkingSum (M : LinkingMatrix ι) (I : Finset ι) (m : ι) : ℤ :=
  if m ∈ I then ∑ j ∈ Iᶜ, M.entry m j else ∑ j ∈ I, M.entry m j

/-- Introduction, lines 72–76: every nontrivial cut has some nonzero row sum. -/
def LinkingIndecomposable (M : LinkingMatrix ι) : Prop :=
  ∀ I : Finset ι, I.Nonempty → Iᶜ.Nonempty →
    ∃ m : ι, oppositeLinkingSum M I m ≠ 0

/-- Exact finite obstruction consumed in Lemma 6.1, after the homology bridge. -/
theorem no_zero_partition (M : LinkingMatrix ι) (hM : LinkingIndecomposable M)
    (I : Finset ι) (hI : I.Nonempty) (hIc : Iᶜ.Nonempty)
    (hzero : ∀ m : ι, oppositeLinkingSum M I m = 0) : False := by
  obtain ⟨m, hm⟩ := hM I hI hIc
  exact hm (hzero m)

/-- The source explicitly says the condition is vacuous for a one-component link. -/
theorem linkingIndecomposable_of_subsingleton [Subsingleton ι] (M : LinkingMatrix ι) :
    LinkingIndecomposable M := by
  intro I hI hIc
  obtain ⟨x, hx⟩ := hI
  obtain ⟨y, hy⟩ := hIc
  have hxy : x = y := Subsingleton.elim x y
  exact False.elim ((Finset.mem_compl.mp hy) (hxy ▸ hx))

variable {κ : Type v} [Fintype κ] [DecidableEq κ]

/-- Boundary labels assigned to connected components, with no component lacking
boundary. `separate_sums_zero` is exactly the algebraic conclusion that must be
proved from bounding chains disjoint from the complementary sublink. This is
finite data, and is not a definition of a geometric spanning surface. -/
structure BoundaryComponentAllocation (M : LinkingMatrix ι) (κ : Type v)
    [Fintype κ] [DecidableEq κ] where
  component : ι → κ
  every_component_has_boundary : Function.Surjective component
  separate_sums_zero : ∀ (m : ι) (k : κ), k ≠ component m →
    (∑ j ∈ Finset.univ.filter (fun j => component j = k), M.entry m j) = 0

/-- A nontrivial partition of boundary-bearing components cannot survive the
linking obstruction. Turning this into `ConnectedSpace F` requires an actual
component/boundary classification theorem. -/
theorem allocation_has_one_component (M : LinkingMatrix ι)
    (hM : LinkingIndecomposable M) (B : BoundaryComponentAllocation M κ) :
    Subsingleton κ := by
  refine ⟨fun k₁ k₂ => ?_⟩
  by_contra hne
  let I := Finset.univ.filter (fun j => B.component j = k₁)
  have hmem : ∀ j, j ∈ I ↔ B.component j = k₁ := by
    intro j
    simp [I]
  obtain ⟨x, hx⟩ := B.every_component_has_boundary k₁
  obtain ⟨y, hy⟩ := B.every_component_has_boundary k₂
  have hI : I.Nonempty := ⟨x, (hmem x).mpr hx⟩
  have hIc : Iᶜ.Nonempty := by
    refine ⟨y, Finset.mem_compl.mpr ?_⟩
    intro hyI
    exact hne ((hmem y).mp hyI |>.symm.trans hy)
  apply no_zero_partition M hM I hI hIc
  intro m
  by_cases hm : m ∈ I
  · rw [oppositeLinkingSum, ite_eq_left hm]
    have hfibres :
        Finset.univ.filter
          (fun j => B.component j ∈ Finset.univ.filter (fun k => k ≠ k₁)) = Iᶜ := by
      ext j
      simp [I]
    calc
      (∑ j ∈ Iᶜ, M.entry m j) =
          ∑ k ∈ Finset.univ.filter (fun k => k ≠ k₁),
            ∑ j ∈ Finset.univ.filter (fun j => B.component j = k), M.entry m j := by
        rw [Finset.sum_fiberwise_eq_sum_filter, hfibres]
      _ = 0 := Finset.sum_eq_zero fun k hk =>
        B.separate_sums_zero m k (by
          rw [(hmem m).mp hm]
          exact (Finset.mem_filter.mp hk).2)
  · rw [oppositeLinkingSum, ite_eq_right hm]
    exact B.separate_sums_zero m k₁ (by
      intro h
      exact hm ((hmem m).mpr h.symm))

end Linking

/-- Genus and least relative area, the numerical data of Definition 4.7.
This does not define isotopy classes or construct an area minimizer. -/
structure GenusAreaData (V : Type u) where
  genus : V → ℕ
  area : V → ℝ
  area_pos : ∀ v, 0 < area v

section Truncation

variable {V : Type u} (d : GenusAreaData V)

/-- Non-strict lexicographic order: strictly smaller genus, or equal genus and
no larger area. `Prod.Lex` is the actual Lean relation. -/
def complexityLE (u v : V) : Prop :=
  Prod.Lex (fun a b : ℕ => a < b) (fun a b : ℝ => a ≤ b)
    (d.genus u, d.area u) (d.genus v, d.area v)

def GenusTruncation (ℓ : ℕ) : Set V := {v | d.genus v ≤ ℓ}

/-- Literal wording of Theorem C, lines 65–66: both inequalities at every genus. -/
def RectangularTruncation (ℓ : ℕ) (a₀ : ℝ) : Set V :=
  {v | d.genus v ≤ ℓ ∧ d.area v ≤ a₀}

/-- Set actually used in the proof, lines 948–949: no area bound below `ℓ`. -/
def LexTruncation (ℓ : ℕ) (a₀ : ℝ) : Set V :=
  {v | d.genus v < ℓ ∨ (d.genus v = ℓ ∧ d.area v ≤ a₀)}

def ComplexityDownwardClosed (D : Set V) : Prop :=
  ∀ u v, complexityLE d u v → v ∈ D → u ∈ D

theorem genusTruncation_downwardClosed (ℓ : ℕ) :
    ComplexityDownwardClosed d (GenusTruncation d ℓ) := by
  intro u v huv hv
  have hv' : d.genus v ≤ ℓ := hv
  rcases Prod.lex_def.mp huv with hlt | ⟨heq, _⟩
  · exact Nat.le_trans (Nat.le_of_lt hlt) hv'
  · change d.genus u ≤ ℓ
    change d.genus u = d.genus v at heq
    rw [heq]
    exact hv'

theorem lexTruncation_downwardClosed (ℓ : ℕ) (a₀ : ℝ) :
    ComplexityDownwardClosed d (LexTruncation d ℓ a₀) := by
  intro u v huv hv
  change d.genus v < ℓ ∨ (d.genus v = ℓ ∧ d.area v ≤ a₀) at hv
  change d.genus u < ℓ ∨ (d.genus u = ℓ ∧ d.area u ≤ a₀)
  rcases Prod.lex_def.mp huv with hlt | ⟨heq, harea⟩
  · exact Or.inl (lt_of_lt_of_le hlt (by rcases hv with h | ⟨h, _⟩ <;> omega))
  · change d.genus u = d.genus v at heq
    rcases hv with h | ⟨h, ha⟩
    · exact Or.inl (heq.symm ▸ h)
    · exact Or.inr ⟨heq.trans h, le_trans harea ha⟩

/-- Numerical hypotheses for `g(K)` and the least area at minimum genus.
Existence for the actual Seifert vertices is a separate geometric obligation. -/
structure MinimumGenusArea (d : GenusAreaData V) where
  genus : ℕ
  area : ℝ
  genus_lower : ∀ v, genus ≤ d.genus v
  witness : ∃ v, d.genus v = genus ∧ d.area v = area
  area_lower : ∀ v, d.genus v = genus → area ≤ d.area v

variable (m : MinimumGenusArea d)

theorem minimumGenusArea_pos : 0 < m.area := by
  obtain ⟨v, _, hv⟩ := m.witness
  rw [← hv]
  exact d.area_pos v

theorem genusTruncation_nonempty_iff (ℓ : ℕ) :
    (GenusTruncation d ℓ).Nonempty ↔ m.genus ≤ ℓ := by
  constructor
  · rintro ⟨v, hv⟩
    exact le_trans (m.genus_lower v) hv
  · intro h
    obtain ⟨v, hv, _⟩ := m.witness
    exact ⟨v, by simpa only [GenusTruncation, Set.mem_ofPred_eq, hv] using h⟩

/-- Exact threshold stated in the proof of Theorem C. Positivity of `a₀` alone
does not imply the right-hand side when `ℓ = m.genus`. -/
theorem lexTruncation_nonempty_iff (ℓ : ℕ) (a₀ : ℝ) :
    (LexTruncation d ℓ a₀).Nonempty ↔
      m.genus < ℓ ∨ (m.genus = ℓ ∧ m.area ≤ a₀) := by
  constructor
  · rintro ⟨v, hv⟩
    rcases hv with hv | ⟨hv, ha⟩
    · exact Or.inl (lt_of_le_of_lt (m.genus_lower v) hv)
    · by_cases h : m.genus < ℓ
      · exact Or.inl h
      · have heq : m.genus = ℓ := by
          have hlower := m.genus_lower v
          omega
        exact Or.inr ⟨heq, le_trans (m.area_lower v (hv.trans heq.symm)) ha⟩
  · intro h
    obtain ⟨v, hv, ha⟩ := m.witness
    refine ⟨v, ?_⟩
    change d.genus v < ℓ ∨ (d.genus v = ℓ ∧ d.area v ≤ a₀)
    rw [hv, ha]
    exact h

theorem rectangularTruncation_at_minimum_nonempty_iff (a₀ : ℝ) :
    (RectangularTruncation d m.genus a₀).Nonempty ↔ m.area ≤ a₀ := by
  constructor
  · rintro ⟨v, hg, ha⟩
    have heq : d.genus v = m.genus := le_antisymm hg (m.genus_lower v)
    exact le_trans (m.area_lower v heq) ha
  · intro ha
    obtain ⟨v, hv, harea⟩ := m.witness
    refine ⟨v, ?_, ?_⟩
    · rw [hv]
    · rw [harea]
      exact ha

/-- A positive threshold refuting the universal nonemptiness reading of C.
This applies to both interpretations of its second family. -/
theorem exists_positive_empty_threshold :
    ∃ a₀ : ℝ, 0 < a₀ ∧
      ¬ (LexTruncation d m.genus a₀).Nonempty ∧
      ¬ (RectangularTruncation d m.genus a₀).Nonempty := by
  have hpos := minimumGenusArea_pos d m
  refine ⟨m.area / 2, by linarith, ?_, ?_⟩
  · rw [lexTruncation_nonempty_iff d m]
    intro h
    rcases h with h | ⟨_, h⟩
    · exact (lt_irrefl _ h)
    · linarith
  · rw [rectangularTruncation_at_minimum_nonempty_iff d m]
    linarith

/-- The rectangular interpretation need not be lexicographically downward closed:
a lower-genus vertex can have larger area. The displayed hypotheses are numerical
support hypotheses, not a claim that such actual knot vertices exist. -/
theorem rectangularTruncation_not_downwardClosed (ℓ : ℕ) (a₀ : ℝ) (u v : V)
    (huv : d.genus u < d.genus v) (hvℓ : d.genus v ≤ ℓ)
    (hva : d.area v ≤ a₀) (hua : a₀ < d.area u) :
    ¬ ComplexityDownwardClosed d (RectangularTruncation d ℓ a₀) := by
  intro hclosed
  have hcomp : complexityLE d u v := Prod.Lex.left _ _ huv
  have hv : v ∈ RectangularTruncation d ℓ a₀ := ⟨hvℓ, hva⟩
  have hu := hclosed u v hcomp hv
  exact (not_le_of_gt hua) hu.2

end Truncation

/-- Euler characteristic of a compact connected orientable surface of genus `g`
with `n` boundary curves. This is a number, not a replacement for that surface. -/
def surfaceEuler (g n : ℕ) : ℤ := 2 - 2 * (g : ℤ) - (n : ℤ)

/-- Lemma 6.2's separating-compression arithmetic, after the topological proof
that one component has all boundary and the closed component is not a sphere. -/
theorem separating_compression_genus_decreases
    (g gBoundary gClosed n : ℕ) (hClosed : 1 ≤ gClosed)
    (hEuler : surfaceEuler gBoundary n =
      surfaceEuler g n + 2 - surfaceEuler gClosed 0) : gBoundary < g := by
  unfold surfaceEuler at hEuler
  have hclosed : (1 : ℤ) ≤ (gClosed : ℤ) := by exact_mod_cast hClosed
  have hdrop : (gBoundary : ℤ) < (g : ℤ) := by linarith
  exact_mod_cast hdrop

/-- Lemma 6.2's nonseparating-compression arithmetic. -/
theorem nonseparating_compression_genus (g gAfter n : ℕ)
    (hEuler : surfaceEuler gAfter n = surfaceEuler g n + 2) :
    gAfter + 1 = g := by
  unfold surfaceEuler at hEuler
  have hgenus : (gAfter : ℤ) + 1 = (g : ℤ) := by linarith
  exact_mod_cast hgenus

/-- Numerical termination only; a terminal surface being incompressible needs
the definition and the existence of compression whenever it is compressible. -/
theorem no_infinite_genus_descent :
    ¬ ∃ g : ℕ → ℕ, ∀ k, g (k + 1) < g k := by
  rintro ⟨g, hg⟩
  exact (wellFounded_iff_isEmpty_descending_chain.mp Nat.lt_wfRel.wf).false ⟨g, hg⟩

/-- Mathlib contractibility entails nonemptiness. Connecting an empty vertex set
to an empty realization requires the actual simplicial realization construction. -/
theorem empty_space_not_contractible (X : Type u) [TopologicalSpace X] [IsEmpty X] :
    ¬ ContractibleSpace X := by
  intro h
  obtain ⟨e⟩ := h.hequiv_unit'
  exact isEmptyElim (e.invFun ())

end SeifertSection6
