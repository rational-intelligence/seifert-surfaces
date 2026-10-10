import ChartBoundaryDifferential

open scoped Manifold ContDiff
open Set Filter Topology
namespace SeifertSurfaces.Foundations.AmbientNeatTransport
noncomputable section
universe v
variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]

/-- The differential of every smooth ambient chart preserves boundary tangent
vectors. This concerns the actual chart differential, not a chosen trivialization. -/
theorem chart_forward_boundary_differential
    (d : OpenPartialHomeomorph M (EuclideanHalfSpace 3))
    (hd : d ∈ IsManifold.maximalAtlas (𝓡∂ 3) ∞ M)
    {y : M} (hy : y ∈ d.source) (hyb : y ∈ (𝓡∂ 3).boundary M)
    (v : TangentSpace (𝓡∂ 3) y) (hv : inwardCoordinate y v = 0) :
    (show Euc 3 from mfderiv (𝓡∂ 3) 𝓘(ℝ,Euc 3) (d.extend (𝓡∂ 3)) y v) 0 = 0 := by
  let q : M → ℝ := fun x => d.extend (𝓡∂ 3) x 0
  have hdd := (d.contMDiffOn_extend hd).mdifferentiableOn (by simp)
    |>.mdifferentiableAt (d.open_source.mem_nhds hy)
  have hqd : MDifferentiableAt (𝓡∂ 3) 𝓘(ℝ,ℝ) q y :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).differentiableAt.mdifferentiableAt.comp y hdd
  have hchain : mfderiv (𝓡∂ 3) 𝓘(ℝ,ℝ) q y =
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).comp
        (mfderiv (𝓡∂ 3) 𝓘(ℝ,Euc 3) (d.extend (𝓡∂ 3)) y) := by
    have h := mfderiv_comp y
      ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).differentiableAt.mdifferentiableAt) hdd
    rw [mfderiv_eq_fderiv,ContinuousLinearMap.fderiv] at h
    exact h
  have hqy : q y = 0 := (chart_boundary_normal_iff d hd hy).mp hyb
  let z := extChartAt (𝓡∂ 3) y y
  have hz0 : z 0 = 0 := by
    have hb := hyb
    change (𝓡∂ 3).IsBoundaryPoint y at hb
    rw [ModelWithCorners.isBoundaryPoint_iff,
      frontier_range_modelWithCornersEuclideanHalfSpace] at hb
    exact hb.symm
  have hmin : IsLocalMinOn (writtenInExtChartAt (𝓡∂ 3) 𝓘(ℝ,ℝ) y q)
      (range (𝓡∂ 3)) z := by
    filter_upwards [] with w
    change q ((extChartAt (𝓡∂ 3) y).symm z) ≤ q ((extChartAt (𝓡∂ 3) y).symm w)
    rw [extChartAt_to_inv,hqy]
    exact (d ((extChartAt (𝓡∂ 3) y).symm w)).property
  have hnonneg (w : Euc 3) (hw : 0 ≤ w 0) :
      0 ≤ (show ℝ from mfderiv (𝓡∂ 3) 𝓘(ℝ,ℝ) q y w) := by
    rw [hqd.mfderiv]
    apply hmin.fderivWithin_nonneg
    apply mem_posTangentConeAt_of_segment_subset
    apply (𝓡∂ 3).convex_range.segment_subset (mem_range_self _)
    rw [range_modelWithCornersEuclideanHalfSpace]
    change 0 ≤ (z+w) 0
    simpa only [PiLp.add_apply,hz0,zero_add] using hw
  rw [inwardCoordinate_eq] at hv
  let w : Euc 3 := v
  have hw : w 0 = 0 := hv
  have hle := hnonneg (-w) (by simp only [PiLp.neg_apply,hw,neg_zero,le_refl])
  have hge := hnonneg w (by rw [hw])
  have heq : (show ℝ from mfderiv (𝓡∂ 3) 𝓘(ℝ,ℝ) q y v) = 0 := by
    change 0 ≤ (show ℝ from mfderiv (𝓡∂ 3) 𝓘(ℝ,ℝ) q y
      (-(show TangentSpace (𝓡∂ 3) y from w))) at hle
    rw [map_neg] at hle
    exact le_antisymm (neg_nonneg.mp hle) hge
  rw [hchain] at heq
  exact heq

end
end SeifertSurfaces.Foundations.AmbientNeatTransport
