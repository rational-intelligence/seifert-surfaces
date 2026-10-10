import CurveComplexGenusTwo.CWHurewicz.CWRelativeClean

namespace CurveComplexGenusTwo.CWHurewicz

open CategoryTheory CategoryTheory.Limits Topology

abbrev Excised (X : Type) [TopologicalSpace X] (U : Set X) := ↥(Uᶜ)

def excisedSubspace {X : Type} [TopologicalSpace X]
    (A U : Set X) : Set (Excised X U) :=
  {x | x.val ∈ A}

def excisionInclusionX (X : Type) [TopologicalSpace X] (U : Set X) :
    TopCat.of (Excised X U) ⟶ TopCat.of X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

def excisionInclusionA {X : Type} [TopologicalSpace X]
    (A U : Set X) :
    TopCat.of ↥(excisedSubspace A U) ⟶ TopCat.of ↥A :=
  TopCat.ofHom ⟨fun z => ⟨z.val.val, z.property⟩, by fun_prop⟩

theorem excisionPairSquare {X : Type} [TopologicalSpace X] (A U : Set X) :
    pairInclusion (Excised X U) (excisedSubspace A U) ≫
        excisionInclusionX X U =
      excisionInclusionA A U ≫ pairInclusion X A := by
  ext z
  rfl

theorem excisionRelativeChainMap_condition
    {X : Type} [TopologicalSpace X] (A U : Set X) :
    let F := (AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
      (ModuleCat.of ℤ ℤ)
    F.map (pairInclusion (Excised X U) (excisedSubspace A U)) ≫
      (F.map (excisionInclusionX X U) ≫
        cokernel.π (F.map (pairInclusion X A))) = 0 := by
  dsimp
  rw [← Category.assoc, ← Functor.map_comp, excisionPairSquare A U,
    Functor.map_comp, Category.assoc, cokernel.condition, comp_zero]

noncomputable def excisionRelativeChainMap {X : Type} [TopologicalSpace X]
    (A U : Set X) :
    relativeSingularChains (Excised X U) (excisedSubspace A U) ⟶
      relativeSingularChains X A := by
  let F := (AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
    (ModuleCat.of ℤ ℤ)
  exact cokernel.desc
    (F.map (pairInclusion (Excised X U) (excisedSubspace A U)))
    (F.map (excisionInclusionX X U) ≫
      cokernel.π (F.map (pairInclusion X A)))
    (excisionRelativeChainMap_condition A U)

end CurveComplexGenusTwo.CWHurewicz
