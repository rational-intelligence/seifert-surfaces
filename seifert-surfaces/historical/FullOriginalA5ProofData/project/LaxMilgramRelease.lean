import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.MeasureTheory.Function.L2Space

noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff
namespace SeifertSurfaces.WeakSchauder

theorem real_lax_milgram {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [CompleteSpace X]
    (b : X × X → ℝ) (hb : IsBoundedBilinearMap ℝ b)
    (κ : ℝ) (hκ : 0 < κ) (hcoercive : ∀ x, κ * ‖x‖ ^ 2 ≤ b (x, x))
    (ℓ : X →L[ℝ] ℝ) :
    ∃! x : X, ∀ y : X, b (x, y) = ℓ y := by
  let B : X →L[ℝ] X →L[ℝ] ℝ := hb.toContinuousLinearMap
  have hB : IsCoercive B := ⟨κ, hκ, fun x => by
    simpa [B, pow_two, mul_assoc] using hcoercive x⟩
  let T : X ≃L[ℝ] X := hB.continuousLinearEquivOfBilin
  let z : X := (InnerProductSpace.toDual ℝ X).symm ℓ
  refine ⟨T.symm z, ?_, ?_⟩
  · intro y
    calc
      b (T.symm z, y) = inner ℝ (T (T.symm z)) y :=
        (hB.continuousLinearEquivOfBilin_apply (T.symm z) y).symm
      _ = inner ℝ z y := by rw [T.apply_symm_apply]
      _ = ℓ y := InnerProductSpace.toDual_symm_apply
  · intro x hx
    apply T.injective
    rw [T.apply_symm_apply]
    apply (InnerProductSpace.toDual ℝ X).injective
    ext y
    change inner ℝ (T x) y = inner ℝ z y
    rw [hB.continuousLinearEquivOfBilin_apply]
    exact (hx y).trans InnerProductSpace.toDual_symm_apply.symm

end SeifertSurfaces.WeakSchauder
