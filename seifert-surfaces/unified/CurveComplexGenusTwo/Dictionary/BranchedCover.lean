import Mathlib

/-!
The geometric data of the genus-two quotient in §§2.1 and 4. This is a
candidate interface; constructing the specific six-point cover is a separate
proof obligation, not a field asserting the dictionary theorem.
-/

namespace CurveComplex

universe u v

/-- The local `z ↦ z²` condition at a ramification point. -/
structure SquareBranchChart (E : Type u) (S : Type v)
    [TopologicalSpace E] [TopologicalSpace S] (π : E → S) (w : E) where
  upstairs : OpenPartialHomeomorph E ℂ
  downstairs : OpenPartialHomeomorph S ℂ
  upstairs_mem : w ∈ upstairs.source
  downstairs_mem : π w ∈ downstairs.source
  upstairs_center : upstairs w = 0
  downstairs_center : downstairs (π w) = 0
  image_mem : ∀ x ∈ upstairs.source, π x ∈ downstairs.source
  square : ∀ x ∈ upstairs.source, downstairs (π x) = (upstairs x) ^ 2

/-- A connected two-sheeted cover of a sphere, with six simple branch points.
The sphere and genus-two hypotheses belong to the concrete source construction,
which supplies this structure; no curve-class correspondence is assumed here. -/
structure BranchedDoubleCover (E : Type u) (S : Type v)
    [TopologicalSpace E] [TopologicalSpace S] where
  projection : E → S
  projection_continuous : Continuous projection
  projection_surjective : Function.Surjective projection
  deck : E ≃ₜ E
  deck_involution : ∀ x, deck (deck x) = x
  branch : Finset S
  branch_card : branch.card = 6
  fixed_iff_branch : ∀ x, deck x = x ↔ projection x ∈ branch
  projection_deck : ∀ x, projection (deck x) = projection x
  fiber_pair : ∀ x y, projection x = projection y ↔ y = x ∨ y = deck x
  unbranched_cover : IsCoveringMapOn projection (branch : Set S)ᶜ
  branch_chart : ∀ x, projection x ∈ branch →
    SquareBranchChart E S projection x

namespace BranchedDoubleCover

variable {E : Type u} {S : Type v} [TopologicalSpace E] [TopologicalSpace S]

def ramification (q : BranchedDoubleCover E S) : Set E :=
  q.projection ⁻¹' (q.branch : Set S)

abbrev unramifiedTotal (q : BranchedDoubleCover E S) :=
  { x : E // x ∉ q.ramification }

abbrev unramifiedBase (q : BranchedDoubleCover E S) :=
  { y : S // y ∉ (q.branch : Set S) }

def unramifiedProjection (q : BranchedDoubleCover E S) :
    q.unramifiedTotal → q.unramifiedBase :=
  fun x => ⟨q.projection x.val, x.property⟩

/-- The complement restriction is the unbranched double covering of §2.1. -/
theorem unramified_isCoveringMap (q : BranchedDoubleCover E S) :
    IsCoveringMap q.unramifiedProjection := by
  exact q.unbranched_cover.isCoveringMap_restrictPreimage

/-- Ramification points are exactly fixed points of the deck involution. -/
theorem ramification_eq_fixed (q : BranchedDoubleCover E S) :
    q.ramification = { x | q.deck x = x } := by
  ext x
  change q.projection x ∈ (q.branch : Set S) ↔ q.deck x = x
  exact (q.fixed_iff_branch x).symm

/-- A marked point has a single preimage, as required by the local square model. -/
theorem branch_fiber_unique (q : BranchedDoubleCover E S)
    {b : S} (hb : b ∈ q.branch) : ∃! x : E, q.projection x = b := by
  obtain ⟨x, hx⟩ := q.projection_surjective b
  have hxb : q.projection x ∈ q.branch := hx ▸ hb
  have hfix : q.deck x = x := (q.fixed_iff_branch x).2 hxb
  refine ⟨x, hx, ?_⟩
  intro y hy
  have hxy : q.projection x = q.projection y := hx.trans hy.symm
  rcases (q.fiber_pair x y).1 hxy with rfl | h
  · rfl
  · exact hfix ▸ h

end BranchedDoubleCover
end CurveComplex
