import SurfaceInvariants
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

set_option autoImplicit false

open scoped Manifold ContDiff Simplicial BigOperators
open CategoryTheory Convexity
open Set Topology

namespace SeifertSurfaces.GenusLinking.CircleConstruction
open SeifertSurfaces.Foundations

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Integral singular chains and homology of the actual space. -/
abbrev integralChains (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))

abbrev integralHomology (X : Type) [TopologicalSpace X] (k : ℕ) :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))

/-- One singular simplex tracing the positively parametrized circle once. -/
def circleLoopSimplex : (TopCat.toSSet.obj (TopCat.of Circle)) _⦋1⦌ :=
  (TopCat.toSSetObjEquiv (TopCat.of Circle) (.op ⦋1⦌)).symm
    ⟨fun z : StdSimplex ℝ (Fin 2) => Circle.exp (2 * Real.pi * z.weights 1),
      Circle.exp.continuous.comp
        (continuous_const.mul (StdSimplex.continuous_weights_apply ℝ 1))⟩

def circleLoopChain : ModuleCat.of ℤ ℤ ⟶ (integralChains Circle).X 1 :=
  (TopCat.toSSet.obj (TopCat.of Circle)).ιChainComplex circleLoopSimplex

theorem circleLoopChain_boundary : circleLoopChain ≫ (integralChains Circle).d 1 0 = 0 := by
  change (TopCat.toSSet.obj (TopCat.of Circle)).ιChainComplex circleLoopSimplex ≫
    ((TopCat.toSSet.obj (TopCat.of Circle)).chainComplex (ModuleCat.of ℤ ℤ)).d (0 + 1) 0 = 0
  rw [SSet.ιChainComplex_d]
  have hfaces : (TopCat.toSSet.obj (TopCat.of Circle)).δ 0 circleLoopSimplex =
      (TopCat.toSSet.obj (TopCat.of Circle)).δ 1 circleLoopSimplex := by
    apply (TopCat.toSSetObj₀Equiv (X := TopCat.of Circle)).injective
    rw [← TopCat.toSSetObj₁Equiv_apply_one, ← TopCat.toSSetObj₁Equiv_apply_zero]
    dsimp [TopCat.toSSetObj₁Equiv, circleLoopSimplex]
    simp only [TopCat.stdSimplexHomeomorphI]
    change Circle.exp (2 * Real.pi * (StdSimplex.homeomorphI.symm (TopCat.I.homeomorph.{0} 1)).weights 1) =
      Circle.exp (2 * Real.pi * (StdSimplex.homeomorphI.symm (TopCat.I.homeomorph.{0} 0)).weights 1)
    simp
  simp [Fin.sum_univ_two, hfaces]

/-- Concrete class of the once-around singular cycle, not an arbitrary generator. -/
def circleFundamentalClass : integralHomology Circle 1 :=
  (((integralChains Circle).liftCycles circleLoopChain 0 (by simp) circleLoopChain_boundary) ≫
    (integralChains Circle).homologyπ 1) 1


end
end SeifertSurfaces.GenusLinking.CircleConstruction
