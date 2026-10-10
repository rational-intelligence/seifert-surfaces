import CurveComplexGenusTwo.CWHurewicz.AbsoluteSmallComparison

namespace CurveComplexGenusTwo.CWHurewicz

open CategoryTheory
open scoped Simplicial

/-- Positive-degree relative cycles admit small representatives modulo an
ambient boundary and an A-supported chain. No comparison isomorphism is assumed. -/
theorem relativeCycle_has_small_representative
    (X : TopCat) (A U : Set X) (hU : closure U ⊆ interior A)
    (n : ℕ) (c : (TopCat.toSSet.obj X) _⦋n + 1⦌ →₀ ℤ)
    (hc : SingularChainImageSupported X n A (singularBoundaryFinsupp X n c)) :
    ∃ z : (TopCat.toSSet.obj X) _⦋n + 1⦌ →₀ ℤ,
      z ∈ smallSingularChains X A U (n + 1) ∧
      SingularChainImageSupported X n A (singularBoundaryFinsupp X n z) ∧
      ∃ b : (TopCat.toSSet.obj X) _⦋n + 2⦌ →₀ ℤ,
        SingularChainImageSupported X (n + 1) A
          (z - c - singularBoundaryFinsupp X (n + 1) b) := by
  obtain ⟨k, hk⟩ := singularBarycentricIterate_eventually_small_submodule
    X A U hU (n + 1) c
  refine ⟨singularBarycentricIterate X (n + 1) k c, hk, ?_,
    singularCarrierHomotopyIterate X (n + 1) k c, ?_⟩
  · rw [singularBarycentricIterate_boundary]
    exact singularBarycentricIterate_supported X n k A
      (singularBoundaryFinsupp X n c) hc
  · have heq := singularCarrierHomotopyIterate_boundary_succ X n k c
    have hres :
        singularBarycentricIterate X (n + 1) k c - c -
            singularBoundaryFinsupp X (n + 1)
              (singularCarrierHomotopyIterate X (n + 1) k c) =
          singularCarrierHomotopyIterate X n k
            (singularBoundaryFinsupp X n c) := by
      rw [← heq]
      abel
    rw [hres]
    exact singularCarrierHomotopyIterate_supported X n k A
      (singularBoundaryFinsupp X n c) hc

/-- A small relative cycle that bounds modulo A already bounds modulo A
using a small chain. This is the injectivity step for the genuine inclusion. -/
theorem relativeSmallCycle_has_small_filling
    (X : TopCat) (A U : Set X) (hU : closure U ⊆ interior A)
    (n : ℕ) (z : (TopCat.toSSet.obj X) _⦋n + 1⦌ →₀ ℤ)
    (hz : z ∈ smallSingularChains X A U (n + 1))
    (hcycle : SingularChainImageSupported X n A (singularBoundaryFinsupp X n z))
    (b : (TopCat.toSSet.obj X) _⦋n + 2⦌ →₀ ℤ)
    (hb : SingularChainImageSupported X (n + 1) A
      (z - singularBoundaryFinsupp X (n + 1) b)) :
    ∃ b' : (TopCat.toSSet.obj X) _⦋n + 2⦌ →₀ ℤ,
      b' ∈ smallSingularChains X A U (n + 2) ∧
      SingularChainImageSupported X (n + 1) A
        (z - singularBoundaryFinsupp X (n + 1) b') := by
  obtain ⟨k, hk⟩ := singularBarycentricIterate_eventually_small_submodule
    X A U hU (n + 2) b
  let b' := singularBarycentricIterate X (n + 2) k b -
    singularCarrierHomotopyIterate X (n + 1) k z
  refine ⟨b', ?_, ?_⟩
  · exact (smallSingularChains X A U (n + 2)).sub_mem hk
      (smallSingularChains_carrierHomotopyIterate X A U (n + 1) k z hz)
  · have hbd := singularBarycentricIterate_boundary X (n + 1) k b
    have hht := singularCarrierHomotopyIterate_boundary_succ X n k z
    have heq : z - singularBoundaryFinsupp X (n + 1) b' =
        singularBarycentricIterate X (n + 1) k
          (z - singularBoundaryFinsupp X (n + 1) b) -
          singularCarrierHomotopyIterate X n k (singularBoundaryFinsupp X n z) := by
      dsimp [b']
      rw [map_sub, hbd]
      have hpartial : singularBoundaryFinsupp X (n + 1)
          (singularCarrierHomotopyIterate X (n + 1) k z) =
          singularBarycentricIterate X (n + 1) k z - z -
            singularCarrierHomotopyIterate X n k
              (singularBoundaryFinsupp X n z) := by
        rw [← hht]
        abel
      rw [hpartial]
      simp only [map_sub]
      abel
    rw [heq]
    have hleft := singularBarycentricIterate_supported X (n + 1) k A
      (z - singularBoundaryFinsupp X (n + 1) b) hb
    have hright := singularCarrierHomotopyIterate_supported X n k A
      (singularBoundaryFinsupp X n z) hcycle
    classical
    intro x hx
    rcases Finset.mem_union.mp (Finsupp.support_sub hx) with hx | hx
    · exact hleft x hx
    · exact hright x hx

end CurveComplexGenusTwo.CWHurewicz
