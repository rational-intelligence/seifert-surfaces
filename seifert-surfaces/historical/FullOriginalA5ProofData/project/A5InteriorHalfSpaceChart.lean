import A5NativeCoordinateTransport
import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations

/-- An actual smooth half-space chart around an arbitrary point of the
plane, with its entire source contained in the interior of the model. -/
def interiorHalfSpaceCoordinates (a : Euc 2) :
    PartialDiffeomorph (𝓡∂ 2) 𝓘(ℝ, Euc 2) (EuclideanHalfSpace 2) (Euc 2) ∞ := by
  let b : Euc 2 := EuclideanSpace.single 0 (1 : ℝ)
  let Q : Euc 2 → Euc 2 := fun y => y - a + b
  let R : Euc 2 → Euc 2 := fun y => y + a - b
  have hQR (y : Euc 2) : Q (R y) = y := by dsimp [Q, R]; abel
  have hRQ (y : Euc 2) : R (Q y) = y := by dsimp [Q, R]; abel
  refine {
    toFun := fun z => R ((𝓡∂ 2) z)
    invFun := fun y => (𝓡∂ 2).symm (Q y)
    source := {z | 0 < ((𝓡∂ 2) z) 0}
    target := {y | 0 < (Q y) 0}
    map_source' := ?_
    map_target' := ?_
    left_inv' := ?_
    right_inv' := ?_
    open_source := ?_
    open_target := ?_
    contMDiffOn_toFun := ?_
    contMDiffOn_invFun := ?_ }
  · intro z hz
    simpa only [mem_ofPred_eq, hQR] using hz
  · intro y hy
    change 0 < (Q y) 0 at hy
    have hyR : Q y ∈ range (𝓡∂ 2) := by
      rw [range_modelWithCornersEuclideanHalfSpace]
      exact le_of_lt hy
    change 0 < ((𝓡∂ 2) ((𝓡∂ 2).symm (Q y))) 0
    rwa [(𝓡∂ 2).right_inv hyR]
  · intro z hz
    rw [hQR, (𝓡∂ 2).left_inv]
  · intro y hy
    change 0 < (Q y) 0 at hy
    have hyR : Q y ∈ range (𝓡∂ 2) := by
      rw [range_modelWithCornersEuclideanHalfSpace]
      exact le_of_lt hy
    rw [(𝓡∂ 2).right_inv hyR, hRQ]
  · exact isOpen_lt continuous_const
      ((EuclideanSpace.proj 0).continuous.comp (𝓡∂ 2).continuous)
  · exact isOpen_lt continuous_const
      ((EuclideanSpace.proj 0).continuous.comp
        ((continuous_id.sub continuous_const).add continuous_const))
  · exact (((contDiff_id.add contDiff_const).sub contDiff_const).contMDiff.comp
      (𝓡∂ 2).contMDiff).contMDiffOn
  · exact (𝓡∂ 2).contMDiffOn_symm.comp
      (((contDiff_id.sub contDiff_const).add contDiff_const).contMDiff.contMDiffOn)
      (fun y hy => by
        change 0 < (Q y) 0 at hy
        rw [range_modelWithCornersEuclideanHalfSpace]
        exact le_of_lt hy)

theorem interiorHalfSpaceCoordinates_mem_target (a : Euc 2) :
    a ∈ (interiorHalfSpaceCoordinates a).target := by
  change 0 < (a - a + (EuclideanSpace.single 0 (1 : ℝ) : Euc 2)) 0
  simp

theorem interiorHalfSpaceCoordinates_source_avoids_boundary (a : Euc 2) :
    Disjoint (interiorHalfSpaceCoordinates a).source
      ((𝓡∂ 2).boundary (EuclideanHalfSpace 2)) := by
  apply Set.disjoint_left.mpr
  intro z hz hb
  change 0 < ((𝓡∂ 2) z) 0 at hz
  have hi : (𝓡∂ 2).IsInteriorPoint z := by
    change extChartAt (𝓡∂ 2) z z ∈ interior (range (𝓡∂ 2))
    rw [interior_range_modelWithCornersEuclideanHalfSpace]
    simpa using hz
  exact ((𝓡∂ 2).isInteriorPoint_iff_not_isBoundaryPoint z).mp hi hb

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
