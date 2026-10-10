import WhiteheadSupport.CWBackbone

/-!
Universe-polymorphic point-Whitehead obligations for Theorem B, PDF pp. 5-6.
The existing curve-complex point-Whitehead proofs accept only `X : Type 0`.
These declarations assert the needed actual topological result in every universe;
no cellular-extension or Whitehead conclusion is supplied as an assumption.
-/

namespace SeifertSurfaces.WhiteheadSupport

universe u

open Topology
open scoped ContinuousMap

/-- The point inclusion is a homotopy equivalence for a path-connected Hausdorff
CW space with trivial positive homotopy groups. -/
theorem point_whitehead_t2
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] [PathConnectedSpace X]
    (hpi : ∀ n : ℕ, 1 ≤ n → ∀ x : X,
      Subsingleton (HomotopyGroup.Pi n X x)) :
    Nonempty (X ≃ₕ Unit) := by
  exact Port.CW.cwPointWhiteheadT2_from_hpi hpi

/-- The actual contractibility conclusion used in the limit step. -/
theorem contractible_of_cw_all_pi_subsingleton_t2
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] [PathConnectedSpace X]
    (hpi : ∀ n : ℕ, 1 ≤ n → ∀ x : X,
      Subsingleton (HomotopyGroup.Pi n X x)) :
    ContractibleSpace X := by
  exact (Classical.choice (point_whitehead_t2 hpi)).contractibleSpace

end SeifertSurfaces.WhiteheadSupport
