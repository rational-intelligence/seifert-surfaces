import Mathlib

/-!
Combinatorial statements from Sections 6 and 7. The vertex type is intended
to be `CurveComplex.Vertex S` from the foundation package; `intersect` is the
geometric intersection number on those isotopy classes. Its construction and
surface-specific properties are separate proof obligations.
-/

namespace CurveComplexGenusTwo.Topology

variable {V : Type*} [DecidableEq V]

/-- A slope `p/q` on a one-holed torus, with `none` denoting infinity. -/
abbrev FareySlope := Option ℚ

/-- Farey adjacency is determinant one for reduced slopes. Lean's rationals
store each finite slope in normalized numerator/denominator form. -/
def FareyAdjacent : FareySlope → FareySlope → Prop
  | none, none => False
  | none, some q => q.den = 1
  | some p, none => p.den = 1
  | some p, some q =>
      Int.natAbs (p.num * (q.den : ℤ) - q.num * (p.den : ℤ)) = 1

/-- The filled Farey complex is the flag complex on determinant-one edges. -/
def FareyFace (s : Finset FareySlope) : Prop :=
  (s : Set FareySlope).Pairwise FareyAdjacent

/-- Faces of the `d`-curve complex. The empty face is included, matching the
paper's Convention 8.1; a topological realization uses nonempty faces. -/
def CurveFace (intersect : V → V → ℕ) (d : ℕ) (s : Finset V) : Prop :=
  (s : Set V).Pairwise (fun a b => intersect a b ≤ d)

/-- The full subcomplex spanned by nonseparating vertices. -/
def NonseparatingFace (intersect : V → V → ℕ)
    (separating : V → Prop) (s : Finset V) : Prop :=
  CurveFace intersect 1 s ∧ ∀ v ∈ s, ¬ separating v

/-- The closed star of `v`, expressed as a face predicate. -/
def ClosedStarFace (intersect : V → V → ℕ)
    (v : V) (s : Finset V) : Prop :=
  CurveFace intersect 1 (insert v s)

/-- The link of `v`, including the empty simplex. -/
def LinkFace (intersect : V → V → ℕ)
    (v : V) (s : Finset V) : Prop :=
  v ∉ s ∧ ClosedStarFace intersect v s

/-- Section 6.4: two separating classes cannot be adjacent. The parity
and zero-intersection rigidity assumptions are distinct geometric obligations
in the one-holed-torus decomposition of a genus-two surface. -/
theorem separating_nonadjacent
    (intersect : V → V → ℕ) (separating : V → Prop)
    (hparity : ∀ a b, separating a → separating b → Even (intersect a b))
    (hzero : ∀ a b, separating a → separating b →
      intersect a b = 0 → a = b) :
    ∀ a b, separating a → separating b → a ≠ b → 1 < intersect a b := by
  intro a b ha hb hab
  have hpos : intersect a b ≠ 0 := by
    intro h
    exact hab (hzero a b ha hb h)
  obtain ⟨k, hk⟩ := hparity a b ha hb
  omega

/-- Corollary 6.5: each simplex has at most one separating vertex. -/
theorem face_at_most_one_separating
    (intersect : V → V → ℕ) (separating : V → Prop)
    (hsep : ∀ a b, separating a → separating b → a ≠ b → 1 < intersect a b)
    (s : Finset V) (hs : CurveFace intersect 1 s) :
    ∀ a ∈ s, separating a → ∀ b ∈ s, separating b → a = b := by
  intro a ha hsa b hb hsb
  by_contra hab
  have hp : intersect a b ≤ 1 := hs ha hb hab
  have hq := hsep a b hsa hsb hab
  omega

/-- Corollary 6.5: the link of a separating vertex lies in the full
nonseparating subcomplex. -/
theorem separating_link_in_nonseparating
    (intersect : V → V → ℕ) (separating : V → Prop)
    (hsep : ∀ a b, separating a → separating b → a ≠ b → 1 < intersect a b)
    (v : V) (hv : separating v) (s : Finset V)
    (hs : LinkFace intersect v s) :
    NonseparatingFace intersect separating s := by
  rcases hs with ⟨hnot, hstar⟩
  constructor
  · exact hstar.mono (Finset.subset_insert v s)
  · intro w hw hsw
    have hwv : w ≠ v := by
      intro heq
      exact hnot (heq ▸ hw)
    have hp : intersect v w ≤ 1 := hstar (Finset.mem_insert_self v s)
      (Finset.mem_insert_of_mem hw) (Ne.symm hwv)
    have hq := hsep v w hv hsw (Ne.symm hwv)
    omega

/-- Proposition 6.7 on faces: every simplex is in the nonseparating core
or in the star of a separating vertex. The disjunction is indexed over the
full, possibly infinite, set of separating vertices. -/
theorem face_core_or_separating_star
    (intersect : V → V → ℕ) (separating : V → Prop)
    (s : Finset V) (hs : CurveFace intersect 1 s) :
    NonseparatingFace intersect separating s ∨
      ∃ v : V, separating v ∧ ClosedStarFace intersect v s := by
  classical
  by_cases h : ∀ v ∈ s, ¬ separating v
  · exact Or.inl ⟨hs, h⟩
  · push Not at h
    obtain ⟨v, hv, hsep⟩ := h
    exact Or.inr ⟨v, hsep, by simpa [ClosedStarFace, Finset.insert_eq_of_mem hv] using hs⟩

/-- Corollary 6.5: a separating star meets the core precisely in its link. -/
theorem separating_star_inter_core_iff_link
    (intersect : V → V → ℕ) (separating : V → Prop)
    (v : V) (hv : separating v) (s : Finset V)
    (hs : CurveFace intersect 1 s) :
    (ClosedStarFace intersect v s ∧
      NonseparatingFace intersect separating s) ↔
      LinkFace intersect v s ∧
      NonseparatingFace intersect separating s := by
  constructor
  · rintro ⟨hstar, hcore⟩
    have hnot : v ∉ s := by
      intro hmem
      exact hcore.2 v hmem hv
    exact ⟨⟨hnot, hstar⟩, hcore⟩
  · rintro ⟨hlink, hcore⟩
    exact ⟨hlink.2, hcore⟩

/-- Corollary 6.5: distinct separating stars overlap only inside the core. -/
theorem separating_stars_overlap_in_core
    (intersect : V → V → ℕ) (separating : V → Prop)
    (hsep : ∀ a b, separating a → separating b → a ≠ b → 1 < intersect a b)
    (v w : V) (hv : separating v) (hw : separating w) (hvw : v ≠ w)
    (s : Finset V) (hvs : ClosedStarFace intersect v s)
    (hws : ClosedStarFace intersect w s) :
    NonseparatingFace intersect separating s := by
  constructor
  · exact hvs.mono (Finset.subset_insert v s)
  · intro x hx hsx
    have hxv : x ≠ v := by
      intro h
      subst x
      have hwu : intersect w v ≤ 1 := hws (Finset.mem_insert_self w s)
        (Finset.mem_insert_of_mem hx) (Ne.symm hvw)
      have hwl := hsep w v hw hv (Ne.symm hvw)
      omega
    have hxw : x ≠ w := by
      intro h
      subst x
      have hvu : intersect v w ≤ 1 := hvs (Finset.mem_insert_self v s)
        (Finset.mem_insert_of_mem hx) hvw
      have hvl := hsep v w hv hw hvw
      omega
    have hxu : intersect v x ≤ 1 := hvs (Finset.mem_insert_self v s)
      (Finset.mem_insert_of_mem hx) (Ne.symm hxv)
    have hxl := hsep v x hv hsx (Ne.symm hxv)
    omega

/-- Section 7.5, after the geometric regular-neighborhood construction:
the third vertex closes an intersection-one edge to a triangle in `C1`,
while its two new edges belong to `C0`. The existence of this `c` for genuine
curves on every closed orientable genus-`g` surface with `g ≥ 2` is the
source-specific geometric obligation. -/
def FillsIntersectionOneEdge (intersect : V → V → ℕ)
    (a b c : V) : Prop :=
  a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ intersect a b = 1 ∧
    intersect a c = 0 ∧ intersect b c = 0 ∧
    CurveFace intersect 1 ({a, b, c} : Finset V) ∧
    CurveFace intersect 0 ({a, c} : Finset V) ∧
    CurveFace intersect 0 ({b, c} : Finset V)

end CurveComplexGenusTwo.Topology
