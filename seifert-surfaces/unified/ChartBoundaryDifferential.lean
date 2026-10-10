import MovingFiniteCover
import Mathlib.Geometry.Manifold.PartitionOfUnity

open scoped Manifold ContDiff
open Set Filter Topology Bundle
namespace SeifertSurfaces.Foundations.AmbientNeatTransport
noncomputable section
universe v
variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]

/-- Chart inverse differentials send vectors tangent to the model boundary to
vectors tangent to the actual ambient boundary. -/
theorem chart_inverse_boundary_differential
    (d : OpenPartialHomeomorph M (EuclideanHalfSpace 3))
    (hd : d ∈ IsManifold.maximalAtlas (𝓡∂ 3) ∞ M)
    {y : M} (hy : y ∈ d.source) (hyb : y ∈ (𝓡∂ 3).boundary M)
    (v : Euc 3) (hv : v 0 = 0) :
    (show Euc 3 from mfderivWithin 𝓘(ℝ, Euc 3) (𝓡∂ 3) (d.extend (𝓡∂ 3)).symm
      (range (𝓡∂ 3)) ((d.extend (𝓡∂ 3)) y) ((NormedSpace.fromTangentSpace ((d.extend (𝓡∂ 3)) y)).symm v)) 0 = 0 := by
  let z := (d.extend (𝓡∂ 3)) y
  let q : Euc 3 → ℝ := fun w => extChartAt (𝓡∂ 3) y ((d.extend (𝓡∂ 3)).symm w) 0
  let B : Euc 3 →L[ℝ] Euc 3 := (mfderivWithin 𝓘(ℝ, Euc 3) (𝓡∂ 3) (d.extend (𝓡∂ 3)).symm
    (range (𝓡∂ 3)) z).comp (NormedSpace.fromTangentSpace z).symm.toContinuousLinearMap
  have hz : z ∈ range (𝓡∂ 3) := mem_range_self (d y)
  have hz0 : z 0 = 0 := (chart_boundary_normal_iff d hd hy).mp hyb
  have hdi := mdifferentiableWithinAt_extend_symm
    (IsManifold.maximalAtlas_subset_of_le (by simp : (1 : ℕ∞ω) ≤ ∞) hd)
    ((d.extend (𝓡∂ 3)).map_source (by simpa using hy))
  have hi : (d.extend (𝓡∂ 3)).symm z = y := (d.extend (𝓡∂ 3)).left_inv (by simpa using hy)
  have hpref := mdifferentiableAt_extChartAt (I := 𝓡∂ 3) (mem_chart_source _ y)
  have hpref' : MDifferentiableAt (𝓡∂ 3) 𝓘(ℝ, Euc 3) (extChartAt (𝓡∂ 3) y)
      ((d.extend (𝓡∂ 3)).symm z) := hi.symm ▸ hpref
  have hcomp := hpref'.comp_mdifferentiableWithinAt z hdi
  have hproj := mfderiv_comp_mfderivWithin z
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).differentiableAt.mdifferentiableAt hcomp ((𝓡∂ 3).uniqueDiffOn z hz).uniqueMDiffWithinAt
  have hchain := mfderiv_comp_mfderivWithin z hpref' hdi ((𝓡∂ 3).uniqueDiffOn z hz).uniqueMDiffWithinAt
  change mfderivWithin 𝓘(ℝ, Euc 3) 𝓘(ℝ, ℝ) q (range (𝓡∂ 3)) z = _ at hproj
  rw [mfderiv_eq_fderiv,ContinuousLinearMap.fderiv,hchain,hi,mfderiv_extChartAt_self] at hproj
  have hL : fderivWithin ℝ q (range (𝓡∂ 3)) z =
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).comp B := by
    ext w
    have hh := congrArg (fun L => NormedSpace.fromTangentSpace (q z)
      (L ((NormedSpace.fromTangentSpace z).symm w))) hproj
    rw [mfderivWithin_eq_fderivWithin] at hh
    change fderivWithin ℝ q (range (𝓡∂ 3)) z w = (B w) 0 at hh
    exact hh

  have hqz : q z = 0 := by
    change extChartAt (𝓡∂ 3) y ((d.extend (𝓡∂ 3)).symm z) 0 = 0
    rw [hi]
    have hb := hyb
    change (𝓡∂ 3).IsBoundaryPoint y at hb
    rw [ModelWithCorners.isBoundaryPoint_iff,frontier_range_modelWithCornersEuclideanHalfSpace] at hb
    exact hb.symm
  have hmin : IsLocalMinOn q (range (𝓡∂ 3)) z := by
    filter_upwards [] with w
    rw [hqz]
    exact (chartAt (EuclideanHalfSpace 3) y ((d.extend (𝓡∂ 3)).symm w)).property
  have hnonneg (w : Euc 3) (hw : 0 ≤ w 0) : 0 ≤ (B w) 0 := by
    have hh := hmin.fderivWithin_nonneg
      (mem_posTangentConeAt_of_segment_subset ((𝓡∂ 3).convex_range.segment_subset hz
        (by rw [range_modelWithCornersEuclideanHalfSpace]
            change 0 ≤ (z+w) 0
            simpa only [PiLp.add_apply,hz0,zero_add] using hw)))
    rw [hL] at hh
    exact hh
  have hle : (B v) 0 ≤ 0 := by
    have hh := hnonneg (-v) (by simp [hv])
    simpa only [map_neg,PiLp.neg_apply,neg_nonneg] using hh
  change (B v) 0 = 0
  exact le_antisymm hle (hnonneg v (by simp [hv]))

end
end SeifertSurfaces.Foundations.AmbientNeatTransport
