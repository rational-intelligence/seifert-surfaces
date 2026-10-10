import CurveComplexGenusTwo.CWHurewicz.ConnectingNaturality
import CurveComplexGenusTwo.CWHurewicz.ExcisionClean

namespace CurveComplexGenusTwo.CWHurewicz

open CategoryTheory CategoryTheory.Limits Topology

private noncomputable abbrev F :=
  (AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
    (ModuleCat.of ℤ ℤ)

private noncomputable abbrev G (n : ℕ) :=
  (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
    (ModuleCat.of ℤ ℤ)

private def excisionInclusionXMap
    {X : Type} [TopologicalSpace X] (U : Set X) :
    C(Excised X U, X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

private lemma excisionInclusionXMap_morphism
    {X : Type} [TopologicalSpace X] (U : Set X) :
    TopCat.ofHom (excisionInclusionXMap U) = excisionInclusionX X U := by
  ext z
  rfl

noncomputable def excisionHomologyMap_connecting
    {X : Type} [TopologicalSpace X] (A U : Set X) (n : ℕ) :
      relativeHomology (Excised X U) (excisedSubspace A U) n ⟶
      relativeHomology X A n :=
  HomologicalComplex.homologyMap (excisionRelativeChainMap A U) n

private lemma excisionPairMapOnSubspace_eq
    {X : Type} [TopologicalSpace X] (A U : Set X) :
    pairMapOnSubspace (excisedSubspace A U) A (excisionInclusionXMap U)
        (fun z hz => by change z.val ∈ A at hz; exact hz) = excisionInclusionA A U := by
  ext z
  rfl

private lemma excisionPairRelativeChainMap_eq
    {X : Type} [TopologicalSpace X] (A U : Set X) :
    pairRelativeChainMap (excisedSubspace A U) A (excisionInclusionXMap U)
        (fun z hz => by change z.val ∈ A at hz; exact hz) = excisionRelativeChainMap A U := by
  dsimp [pairRelativeChainMap, excisionRelativeChainMap]
  rfl

private lemma excisionPairRelativeHomologyMap_eq
    {X : Type} [TopologicalSpace X] (A U : Set X) (n : ℕ) :
      pairRelativeHomologyMap (excisedSubspace A U) A (excisionInclusionXMap U)
        (fun z hz => by change z.val ∈ A at hz; exact hz) n =
      excisionHomologyMap_connecting A U n := by
  dsimp [pairRelativeHomologyMap, excisionHomologyMap_connecting]
  rw [excisionPairRelativeChainMap_eq]

set_option backward.isDefEq.respectTransparency false in
theorem excisionConnecting_natural
    {X : Type} [TopologicalSpace X] (A U : Set X)
    (_hU : closure U ⊆ interior A) (n : ℕ) :
    relativeConnecting (Excised X U) (excisedSubspace A U) n ≫
        (G n).map (excisionInclusionA A U) =
      excisionHomologyMap_connecting A U (n + 1) ≫
        relativeConnecting X A n := by
  have hpair := relativeConnecting_natural
    (excisedSubspace A U) A (excisionInclusionXMap U)
    (fun z hz => by change z.val ∈ A at hz; exact hz) n
  rw [excisionPairMapOnSubspace_eq] at hpair
  rw [excisionPairRelativeHomologyMap_eq] at hpair
  exact hpair

#print axioms excisionPairMapOnSubspace_eq
#print axioms excisionPairRelativeChainMap_eq
#print axioms excisionConnecting_natural

end CurveComplexGenusTwo.CWHurewicz
