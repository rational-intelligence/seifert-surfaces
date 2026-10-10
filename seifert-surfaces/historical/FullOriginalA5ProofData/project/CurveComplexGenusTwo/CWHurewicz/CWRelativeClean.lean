import CurveComplexGenusTwo.CWHurewicz.CWBasic

namespace CurveComplexGenusTwo.CWHurewicz

open CategoryTheory CategoryTheory.Limits Topology

def pairInclusion (X : Type) [TopologicalSpace X] (A : Set X) :
    TopCat.of ↥A ⟶ TopCat.of X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

noncomputable abbrev singularChains (X : Type) [TopologicalSpace X] :
    ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X)

noncomputable def relativeSingularChains (X : Type) [TopologicalSpace X]
    (A : Set X) : ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  cokernel (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
    (ModuleCat.of ℤ ℤ)).map (pairInclusion X A))

noncomputable abbrev relativeHomology (X : Type) [TopologicalSpace X]
    (A : Set X) (n : ℕ) : ModuleCat.{0} ℤ :=
  (relativeSingularChains X A).homology n

noncomputable def homologyInclusion (X : Type) [TopologicalSpace X]
    (A : Set X) (n : ℕ) : H ↥A n ⟶ H X n :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
    (ModuleCat.of ℤ ℤ)).map (pairInclusion X A)

noncomputable def homologyToRelative (X : Type) [TopologicalSpace X]
    (A : Set X) (n : ℕ) : H X n ⟶ relativeHomology X A n :=
  HomologicalComplex.homologyMap
    (cokernel.π (((AlgebraicTopology.singularChainComplexFunctor
      (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)).map (pairInclusion X A))) n

end CurveComplexGenusTwo.CWHurewicz
