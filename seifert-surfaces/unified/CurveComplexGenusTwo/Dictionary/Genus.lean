import CurveComplexGenusTwo.Foundations.Definitions

/-!
Candidate genus model; imports the stable Definitions module after integration.
-/

namespace CurveComplex

open scoped Manifold ContDiff

noncomputable def integralHomology (S : Type) [TopologicalSpace S] (n : ℕ) :
    ModuleCat.{0,0} ℤ :=
  ((AlgebraicTopology.singularHomologyFunctor.{0,0,1} (ModuleCat.{0,0} ℤ) n).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of S)

def IsGenus (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] (g : ℕ) : Prop :=
  Nonempty S ∧ Nonempty (ClosedSurface S) ∧
  Nonempty (integralHomology S 2 ≅ ModuleCat.of ℤ ℤ) ∧
  Nonempty (integralHomology S 1 ≅ ModuleCat.of ℤ (Fin (2 * g) → ℤ))

end CurveComplex
