import CurveComplexGenusTwo.CWHurewicz.ExcisedChainIdentification

namespace CurveComplexGenusTwo.CWHurewicz
open CategoryTheory
open scoped Simplicial

/-- The degreewise actual relative chains of the excised pair, in free-chain form. -/
noncomputable abbrev excisedRelativeChainQuotient (X : TopCat) (A U : Set X) (n : ℕ) :=
  ((TopCat.toSSet.obj (TopCat.of (Excised X U))) _⦋n⦌ →₀ ℤ) ⧸
    excisionSubspaceChains (TopCat.of (Excised X U)) (excisedSubspace A U) n

noncomputable abbrev smallRelativeChainQuotient (X : TopCat) (A U : Set X) (n : ℕ) :=
  smallSingularChains X A U n ⧸
    (excisionSubspaceChains X A n).comap (smallSingularChains X A U n).subtype

noncomputable def excisedChainPushToSmall (X : TopCat) (A U : Set X) (n : ℕ) :
    ((TopCat.toSSet.obj (TopCat.of (Excised X U))) _⦋n⦌ →₀ ℤ) →ₗ[ℤ]
      smallSingularChains X A U n :=
  (excisedChainPush X U n).codRestrict _ (by
    intro c
    rw [smallSingularChains_eq_sup]
    apply Submodule.mem_sup_left
    rw [← excisedChainPush_range]
    exact ⟨c, rfl⟩)

/-- Quotient map induced by the actual excision inclusion, with small target. -/
noncomputable def excisedRelativeChainQuotientMap
    (X : TopCat) (A U : Set X) (n : ℕ) :
    excisedRelativeChainQuotient X A U n →ₗ[ℤ] smallRelativeChainQuotient X A U n :=
  Submodule.mapQ _ _ (excisedChainPushToSmall X A U n) (by
    intro c hc
    exact (excisedChainPush_subspace_iff X A U n c).mpr hc)

theorem excisedRelativeChainQuotientMap_bijective
    (X : TopCat) (A U : Set X) (n : ℕ) :
    Function.Bijective (excisedRelativeChainQuotientMap X A U n) := by
  let sa := excisionSubspaceChains (TopCat.of (Excised X U)) (excisedSubspace A U) n
  let sb := (excisionSubspaceChains X A n).comap (smallSingularChains X A U n).subtype
  constructor
  · apply (LinearMap.ker_eq_bot).mp
    apply (LinearMap.ker_eq_bot').mpr
    intro q hq
    obtain ⟨c, rfl⟩ := sa.mkQ_surjective q
    change sb.mkQ (excisedChainPushToSmall X A U n c) = 0 at hq
    have hc := (Submodule.Quotient.mk_eq_zero sb).mp hq
    apply (Submodule.Quotient.mk_eq_zero sa).mpr
    exact (excisedChainPush_subspace_iff X A U n c).mp hc
  · intro q
    obtain ⟨z, rfl⟩ := sb.mkQ_surjective q
    have hz := (congrArg (fun s : Submodule ℤ
      ((TopCat.toSSet.obj X) _⦋n⦌ →₀ ℤ) => z.1 ∈ s)
      (smallSingularChains_eq_sup X A U n)).mp z.2
    obtain ⟨v, hv, a, ha, heq⟩ := Submodule.mem_sup.mp hz
    rw [← excisedChainPush_range] at hv
    obtain ⟨c, rfl⟩ := hv
    refine ⟨sa.mkQ c, ?_⟩
    change sb.mkQ (excisedChainPushToSmall X A U n c) = sb.mkQ z
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    change excisedChainPush X U n c - z.1 ∈ excisionSubspaceChains X A n
    have hdiff : excisedChainPush X U n c - z.1 = -a := by rw [← heq]; abel
    rw [hdiff]
    exact (excisionSubspaceChains X A n).neg_mem ha

noncomputable def excisedRelativeChainQuotientEquiv
    (X : TopCat) (A U : Set X) (n : ℕ) :
    excisedRelativeChainQuotient X A U n ≃ₗ[ℤ] smallRelativeChainQuotient X A U n :=
  LinearEquiv.ofBijective (excisedRelativeChainQuotientMap X A U n)
    (excisedRelativeChainQuotientMap_bijective X A U n)

end CurveComplexGenusTwo.CWHurewicz
