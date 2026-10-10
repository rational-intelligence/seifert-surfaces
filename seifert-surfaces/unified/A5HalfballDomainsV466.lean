import A5InteriorChartDerivativeV466
import Mathlib.Analysis.Convex.Topology

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff
open SeifertSurfaces.Foundations
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.GlobalSmoothSource
universe u

/-- Small chart domains have a connected, nonempty manifold interior, also at boundary centers. -/
theorem a5_connected_interior_chart_neighborhood (S : A5CompactSmoothCarrier.{u}) (p : S) :
    ∃ U : Set S, IsOpen U ∧ p ∈ U ∧ U ⊆ (extChartAt (𝓡∂ 2) p).source ∧
      IsPreconnected (U ∩ (𝓡∂ 2).interior S) ∧ (U ∩ (𝓡∂ 2).interior S).Nonempty := by
  let c := extChartAt (𝓡∂ 2) p
  let y := c p
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhdsWithin_iff.mp
    (extChartAt_target_mem_nhdsWithin (I := 𝓡∂ 2) p)
  let U : Set S := c.source ∩ c ⁻¹' Metric.ball y r
  let V : Set (Euc 2) := Metric.ball y r ∩ interior (range (𝓡∂ 2))
  have hVopen : IsOpen V := Metric.isOpen_ball.inter isOpen_interior
  have hVsub : V ⊆ c.target := fun z hz => hball ⟨hz.1,interior_subset hz.2⟩
  have hVint : V ⊆ interior c.target := by
    rw [← hVopen.interior_eq]
    exact interior_mono hVsub
  have hUopen : IsOpen U := isOpen_extChartAt_preimage' p Metric.isOpen_ball
  have hpeq : p ∈ U := ⟨mem_extChartAt_source p,Metric.mem_ball_self hr⟩
  have himage : c.symm '' V = U ∩ (𝓡∂ 2).interior S := by
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      have hzs := c.map_target (hVsub hz)
      have hright := c.right_inv (hVsub hz)
      refine ⟨⟨hzs,by simpa only [mem_preimage,hright] using hz.1⟩,?_⟩
      change (𝓡∂ 2).IsInteriorPoint (c.symm z)
      apply ((𝓡∂ 2).isInteriorPoint_iff_of_mem_atlas (n := (∞ : ℕ∞ω)) (by simp)
        (chart_mem_atlas (EuclideanHalfSpace 2) p)
        (by simpa only [c,extChartAt_source] using hzs)).mpr
      change c (c.symm z) ∈ interior c.target
      rw [hright]
      exact hVint hz
    · rintro ⟨hx,hi⟩
      have hxi : c x ∈ interior c.target := by
        exact ((𝓡∂ 2).isInteriorPoint_iff_of_mem_atlas (n := (∞ : ℕ∞ω)) (by simp)
          (chart_mem_atlas (EuclideanHalfSpace 2) p)
          (by simpa only [c,extChartAt_source] using hx.1)).mp hi
      refine ⟨c x,⟨hx.2,?_⟩,c.left_inv hx.1⟩
      exact interior_mono (extChartAt_target_subset_range p) hxi
  have hVpre : IsPreconnected V :=
    ((convex_ball y r).inter (𝓡∂ 2).convex_range.interior).isPreconnected
  have hVnon : V.Nonempty := by
    have hy : y ∈ closure (interior (range (𝓡∂ 2))) :=
      (𝓡∂ 2).range_subset_closure_interior (mem_range_self _)
    obtain ⟨z,hzball,hzint⟩ := mem_closure_iff.mp hy (Metric.ball y r)
      Metric.isOpen_ball (Metric.mem_ball_self hr)
    exact ⟨z,hzball,hzint⟩
  refine ⟨U,hUopen,hpeq,inter_subset_left,?_,?_⟩
  · rw [←himage]
    exact hVpre.image c.symm ((continuousOn_extChartAt_symm p).mono hVsub)
  · rw [←himage]
    exact hVnon.image c.symm

#print axioms a5_connected_interior_chart_neighborhood
end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.GlobalSmoothSource
