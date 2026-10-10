import EndpointGeometry
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Function Filter
open scoped Manifold ContDiff Topology
namespace SeifertSurfaces.OriginalEndpoints.A7Support
open SeifertSurfaces.Foundations SeifertSurfaces.AppendixACoordinates
universe u
variable {d : ℕ} [NeZero d]
  {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace d) M]
  [IsManifold (𝓡∂ d) ∞ M]

theorem inwardCoordinate_eq_coordinate (x : M) (v : TangentSpace (𝓡∂ d) x) :
    inwardCoordinate x v = (show EuclideanSpace ℝ (Fin d) from v) 0 := by
  unfold inwardCoordinate
  rw [mfderiv_extChartAt_self]
  rfl

theorem boundary_minimum_covector_nonneg {q : M → ℝ} {x : M}
    (hq : MDifferentiableAt (𝓡∂ d) 𝓘(ℝ) q x)
    (hx : x ∈ (𝓡∂ d).boundary M) (hqx : q x = 0)
    (hmin : ∀ᶠ y in 𝓝 x, 0 ≤ q y)
    (w : EuclideanSpace ℝ (Fin d)) (hw : 0 ≤ w 0) :
    0 ≤ (show ℝ from mfderiv (𝓡∂ d) 𝓘(ℝ) q x w) := by
  let z := extChartAt (𝓡∂ d) x x
  have hz0 : z 0 = 0 := by
    have hb : z ∈ frontier (range (𝓡∂ d)) := hx
    rw [frontier_range_modelWithCornersEuclideanHalfSpace] at hb
    exact hb.symm
  have hmin' : IsLocalMinOn (writtenInExtChartAt (𝓡∂ d) 𝓘(ℝ) x q)
      (range (𝓡∂ d)) z := by
    have ht := (contMDiffWithinAt_extChartAt_symm_range (I := 𝓡∂ d) (n := ∞) x
      (mem_extChartAt_target x)).continuousWithinAt.tendsto
    have he : (extChartAt (𝓡∂ d) x).symm z = x :=
      (extChartAt (𝓡∂ d) x).left_inv (mem_extChartAt_source x)
    have hm : ∀ᶠ y in 𝓝[range (𝓡∂ d)] z,
        0 ≤ q ((extChartAt (𝓡∂ d) x).symm y) := ht.eventually (he.symm ▸ hmin)
    filter_upwards [hm] with y hy
    change q ((extChartAt (𝓡∂ d) x).symm z) ≤ q ((extChartAt (𝓡∂ d) x).symm y)
    rw [he,hqx]
    exact hy
  rw [hq.mfderiv]
  apply hmin'.fderivWithin_nonneg
  apply mem_posTangentConeAt_of_segment_subset
  apply (𝓡∂ d).convex_range.segment_subset (mem_range_self _)
  rw [range_modelWithCornersEuclideanHalfSpace]
  change 0 ≤ (z+w) 0
  simpa only [PiLp.add_apply,hz0,zero_add] using hw

/-- A nonnegative smooth defining function at a native boundary point kills
all tangential directions. Only its actual local minimum is used. -/
theorem boundary_minimum_covector {q : M → ℝ} {x : M}
    (hq : MDifferentiableAt (𝓡∂ d) 𝓘(ℝ) q x)
    (hx : x ∈ (𝓡∂ d).boundary M) (hqx : q x = 0)
    (hmin : ∀ᶠ y in 𝓝 x, 0 ≤ q y)
    (v : TangentSpace (𝓡∂ d) x) (hv : inwardCoordinate x v = 0) :
    mfderiv (𝓡∂ d) 𝓘(ℝ) q x v = 0 := by
  let z := extChartAt (𝓡∂ d) x x
  have hz0 : z 0 = 0 := by
    have hb : z ∈ frontier (range (𝓡∂ d)) := hx
    rw [frontier_range_modelWithCornersEuclideanHalfSpace] at hb
    exact hb.symm
  have hmin' : IsLocalMinOn (writtenInExtChartAt (𝓡∂ d) 𝓘(ℝ) x q)
      (range (𝓡∂ d)) z := by
    have ht := (contMDiffWithinAt_extChartAt_symm_range (I := 𝓡∂ d) (n := ∞) x
      (mem_extChartAt_target x)).continuousWithinAt.tendsto
    have he : (extChartAt (𝓡∂ d) x).symm z = x :=
      (extChartAt (𝓡∂ d) x).left_inv (mem_extChartAt_source x)
    have hm : ∀ᶠ w in 𝓝[range (𝓡∂ d)] z,
        0 ≤ q ((extChartAt (𝓡∂ d) x).symm w) := ht.eventually (he.symm ▸ hmin)
    filter_upwards [hm] with w hw
    change q ((extChartAt (𝓡∂ d) x).symm z) ≤ q ((extChartAt (𝓡∂ d) x).symm w)
    rw [he,hqx]
    exact hw
  have hnonneg (w : EuclideanSpace ℝ (Fin d)) (hw : 0 ≤ w 0) :
      0 ≤ (show ℝ from mfderiv (𝓡∂ d) 𝓘(ℝ) q x w) := by
    rw [hq.mfderiv]
    apply hmin'.fderivWithin_nonneg
    apply mem_posTangentConeAt_of_segment_subset
    apply (𝓡∂ d).convex_range.segment_subset (mem_range_self _)
    rw [range_modelWithCornersEuclideanHalfSpace]
    change 0 ≤ (z+w) 0
    simpa only [PiLp.add_apply,hz0,zero_add] using hw
  rw [inwardCoordinate_eq_coordinate] at hv
  let w : EuclideanSpace ℝ (Fin d) := v
  have hw : w 0 = 0 := hv
  have hle := hnonneg (-w) (by simp only [PiLp.neg_apply,hw,neg_zero,le_refl])
  have hge := hnonneg w (by rw [hw])
  change 0 ≤ (show ℝ from mfderiv (𝓡∂ d) 𝓘(ℝ) q x (-(show TangentSpace (𝓡∂ d) x from w))) at hle
  rw [map_neg] at hle
  change (show ℝ from mfderiv (𝓡∂ d) 𝓘(ℝ) q x v) = 0
  exact le_antisymm (neg_nonneg.mp hle) hge

end SeifertSurfaces.OriginalEndpoints.A7Support
