import CurveComplexGenusTwo.CWHurewicz.AbsoluteSmallComparison
import CurveComplexGenusTwo.CWHurewicz.RelativeSmallStatements

namespace CurveComplexGenusTwo.CWHurewicz

open CategoryTheory
open scoped Simplicial

/-- Actual ambient singular chains whose support simplices lie wholly in A. -/
def excisionSubspaceChains (X : TopCat) (A : Set X) (n : ℕ) :
    Submodule ℤ ((TopCat.toSSet.obj X) _⦋n⦌ →₀ ℤ) :=
  Finsupp.supported ℤ ℤ
    {x | Set.range (TopCat.toSSetObjEquiv X (.op ⦋n⦌) x) ⊆ A}

/-- Positive-degree relative cycles, represented by ambient chains. -/
noncomputable def excisionRelativeCycles (X : TopCat) (A : Set X) (n : ℕ) :=
  (excisionSubspaceChains X A n).comap (singularBoundaryFinsupp X n)

/-- Relative null classes before restriction to the relative cycle module. -/
noncomputable def excisionRelativeBoundaries (X : TopCat) (A : Set X) (n : ℕ) :=
  LinearMap.range (singularBoundaryFinsupp X (n + 1)) ⊔
    excisionSubspaceChains X A (n + 1)

noncomputable def excisionSmallRelativeCycles (X : TopCat) (A U : Set X) (n : ℕ) :=
  smallSingularChains X A U (n + 1) ⊓ excisionRelativeCycles X A n

/-- Null classes with fillings restricted to the small singular subcomplex. -/
noncomputable def excisionSmallRelativeBoundaries (X : TopCat) (A U : Set X)
    (n : ℕ) :=
  LinearMap.range ((singularBoundaryFinsupp X (n + 1)).comp
    (smallSingularChains X A U (n + 2)).subtype) ⊔
    excisionSubspaceChains X A (n + 1)

/-- Explicit relative homology in degree n+1. -/
noncomputable abbrev excisionRelativeHomology (X : TopCat) (A : Set X) (n : ℕ) :=
  excisionRelativeCycles X A n ⧸
    (excisionRelativeBoundaries X A n).comap (excisionRelativeCycles X A n).subtype

noncomputable abbrev excisionSmallRelativeHomology
    (X : TopCat) (A U : Set X) (n : ℕ) :=
  excisionSmallRelativeCycles X A U n ⧸
    (excisionSmallRelativeBoundaries X A U n).comap
      (excisionSmallRelativeCycles X A U n).subtype

/-- Inclusion of small relative cycles into ambient relative cycles. -/
noncomputable def excisionRelativeCycleInclusion
    (X : TopCat) (A U : Set X) (n : ℕ) :
    excisionSmallRelativeCycles X A U n →ₗ[ℤ] excisionRelativeCycles X A n :=
  (excisionSmallRelativeCycles X A U n).subtype.codRestrict
    (excisionRelativeCycles X A n) (fun z => z.2.2)

/-- The actual map induced by inclusion on relative quotient homology. -/
noncomputable def excisionRelativeHomologyInclusion
    (X : TopCat) (A U : Set X) (n : ℕ) :
    excisionSmallRelativeHomology X A U n →ₗ[ℤ] excisionRelativeHomology X A n :=
  Submodule.mapQ _ _ (excisionRelativeCycleInclusion X A U n) (by
    intro z hz
    change z.1 ∈ excisionRelativeBoundaries X A n
    obtain ⟨v, ⟨b, rfl⟩, a, ha, hsum⟩ := Submodule.mem_sup.mp hz
    exact Submodule.mem_sup.mpr ⟨_, ⟨b.1, rfl⟩, a, ha, hsum⟩)

theorem excisionRelativeHomologyInclusion_bijective
    (X : TopCat) (A U : Set X) (hU : closure U ⊆ interior A) (n : ℕ) :
    Function.Bijective (excisionRelativeHomologyInclusion X A U n) := by
  let sb := (excisionSmallRelativeBoundaries X A U n).comap
    (excisionSmallRelativeCycles X A U n).subtype
  let ab := (excisionRelativeBoundaries X A n).comap
    (excisionRelativeCycles X A n).subtype
  constructor
  · apply (LinearMap.ker_eq_bot).mp
    apply (LinearMap.ker_eq_bot').mpr
    intro q hq
    obtain ⟨z, rfl⟩ := sb.mkQ_surjective q
    change ab.mkQ (excisionRelativeCycleInclusion X A U n z) = 0 at hq
    have hzab := (Submodule.Quotient.mk_eq_zero ab).mp hq
    change z.1 ∈ excisionRelativeBoundaries X A n at hzab
    obtain ⟨v, ⟨b, rfl⟩, a, ha, hsum⟩ := Submodule.mem_sup.mp hzab
    have hb : SingularChainImageSupported X (n + 1) A
        (z.1 - singularBoundaryFinsupp X (n + 1) b) := by
      have heq : z.1 - singularBoundaryFinsupp X (n + 1) b = a := by
        rw [← hsum]
        abel
      rw [heq]
      exact fun x hx => ha hx
    obtain ⟨b', hsmall, hfill⟩ := relativeSmallCycle_has_small_filling
      X A U hU n z.1 z.2.1 (fun x hx => z.2.2 hx) b hb
    apply (Submodule.Quotient.mk_eq_zero sb).mpr
    change z.1 ∈ excisionSmallRelativeBoundaries X A U n
    apply Submodule.mem_sup.mpr
    exact ⟨_, ⟨⟨b', hsmall⟩, rfl⟩,
      z.1 - singularBoundaryFinsupp X (n + 1) b', (fun x hx => hfill x hx), by
        simp only [LinearMap.comp_apply, Submodule.subtype_apply]
        abel⟩
  · intro q
    obtain ⟨z, rfl⟩ := ab.mkQ_surjective q
    obtain ⟨w, hw, hc, b, hb⟩ := relativeCycle_has_small_representative
      X A U hU n z.1 (fun x hx => z.2 hx)
    let ws : excisionSmallRelativeCycles X A U n := ⟨w, hw, fun x hx => hc x hx⟩
    refine ⟨sb.mkQ ws, ?_⟩
    change ab.mkQ (excisionRelativeCycleInclusion X A U n ws) = ab.mkQ z
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    change w - z.1 ∈ excisionRelativeBoundaries X A n
    apply Submodule.mem_sup.mpr
    exact ⟨_, ⟨b, rfl⟩,
      w - z.1 - singularBoundaryFinsupp X (n + 1) b, (fun x hx => hb x hx), by abel⟩

/-- The equivalence whose forward map is the actual inclusion-induced map. -/
noncomputable def excisionRelativeHomologyEquiv
    (X : TopCat) (A U : Set X) (hU : closure U ⊆ interior A) (n : ℕ) :
    excisionSmallRelativeHomology X A U n ≃ₗ[ℤ] excisionRelativeHomology X A n :=
  LinearEquiv.ofBijective (excisionRelativeHomologyInclusion X A U n)
    (excisionRelativeHomologyInclusion_bijective X A U hU n)

theorem excisionRelativeHomologyEquiv_forward
    (X : TopCat) (A U : Set X) (hU : closure U ⊆ interior A) (n : ℕ) :
    (excisionRelativeHomologyEquiv X A U hU n).toLinearMap =
      excisionRelativeHomologyInclusion X A U n := by
  rfl

theorem excisionRelativeHomologyEquiv_inverse_inclusion
    (X : TopCat) (A U : Set X) (hU : closure U ⊆ interior A) (n : ℕ)
    (q : excisionSmallRelativeHomology X A U n) :
    (excisionRelativeHomologyEquiv X A U hU n).symm
      (excisionRelativeHomologyInclusion X A U n q) = q := by
  exact (excisionRelativeHomologyEquiv X A U hU n).symm_apply_apply q

theorem excisionRelativeHomologyEquiv_inclusion_inverse
    (X : TopCat) (A U : Set X) (hU : closure U ⊆ interior A) (n : ℕ)
    (q : excisionRelativeHomology X A n) :
    excisionRelativeHomologyInclusion X A U n
      ((excisionRelativeHomologyEquiv X A U hU n).symm q) = q := by
  exact (excisionRelativeHomologyEquiv X A U hU n).apply_symm_apply q

end CurveComplexGenusTwo.CWHurewicz
