import CurveComplexGenusTwo.CWHurewicz.SingularRealization.GeometryHeaders
import Mathlib.AlgebraicTopology.SimplicialSet.Finite
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
open CategoryTheory Convexity
open scoped Simplicial
noncomputable section
namespace CurveComplexGenusTwo.CWHurewicz.FiniteSingularCarrier
open SingularApproximation
theorem finite_realization_compactSpace (S : SSet.{0}) [S.Finite] : CompactSpace (SSet.toTop.obj S) := by
  let P := Σ s : S.N, StdSimplex ℝ (Fin (s.dim + 1))
  let p : P → SSet.toTop.obj S := fun z =>
    SSet.toTop.map (SSet.yonedaEquiv.symm z.1.simplex)
      (⦋z.1.dim⦌.toTopHomeo.symm z.2)
  have hc : Continuous p := by
    apply continuous_sigma
    intro s
    exact (SSet.toTop.map (SSet.yonedaEquiv.symm s.simplex)).hom.continuous.comp
      ⦋s.dim⦌.toTopHomeo.symm.continuous
  have hs : Function.Surjective p := by
    intro x
    obtain ⟨n, s, t, ht⟩ := realization_nondegenerate_representation S x
    refine ⟨⟨SSet.N.mk s.val s.property, ⦋n⦌.toTopHomeo t⟩, ?_⟩
    change SSet.toTop.map (SSet.yonedaEquiv.symm s.val)
      (⦋n⦌.toTopHomeo.symm (⦋n⦌.toTopHomeo t)) = x
    rw [Homeomorph.symm_apply_apply]
    exact ht
  exact hs.compactSpace hc
end CurveComplexGenusTwo.CWHurewicz.FiniteSingularCarrier
