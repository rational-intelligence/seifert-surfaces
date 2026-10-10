import CurveComplexGenusTwo.CWHurewicz.CWRelativeClean
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Topology.Category.TopCat.EpiMono

namespace CurveComplexGenusTwo.CWHurewicz

open CategoryTheory CategoryTheory.Limits Topology

private noncomputable abbrev F :=
  (AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
    (ModuleCat.of ℤ ℤ)

private instance pairInclusion_mono {X : Type} [TopologicalSpace X] (A : Set X) :
    Mono (pairInclusion X A) :=
  (TopCat.mono_iff_injective _).mpr Subtype.val_injective

private instance chainInclusion_mono {X : Type} [TopologicalSpace X] (A : Set X) :
    Mono (F.map (pairInclusion X A)) :=
  F.map_mono _

private noncomputable def relativeChainShortComplex (X : Type) [TopologicalSpace X]
    (A : Set X) : ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ) :=
  ShortComplex.mk (F.map (pairInclusion X A))
    (cokernel.π (F.map (pairInclusion X A)))
    (cokernel.condition _)

private lemma relativeChainShortExact (X : Type) [TopologicalSpace X]
    (A : Set X) : (relativeChainShortComplex X A).ShortExact where
  exact := ShortComplex.exact_cokernel _
  mono_f := by
    dsimp [relativeChainShortComplex]
    infer_instance
  epi_g := by
    dsimp [relativeChainShortComplex]
    infer_instance

/-- Connecting morphism of the singular-chain short exact sequence. -/
noncomputable def relativeConnecting (X : Type) [TopologicalSpace X]
    (A : Set X) (n : ℕ) : relativeHomology X A (n + 1) ⟶ H ↥A n :=
  (relativeChainShortExact X A).δ (n + 1) n (by simp)

end CurveComplexGenusTwo.CWHurewicz
