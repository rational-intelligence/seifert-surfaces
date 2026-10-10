import EndpointGeometry
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Function Filter
open scoped Manifold ContDiff Topology
namespace SeifertSurfaces.OriginalEndpoints.A7Support
universe u
variable {n : ℕ} [NeZero n] {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

theorem chart_boundary_coordinate_iff (x y : M)
    (hy : y ∈ (chartAt (EuclideanHalfSpace n) x).source) :
    y ∈ (𝓡∂ n).boundary M ↔ (extChartAt (𝓡∂ n) x y) 0 = 0 := by
  let e := extChartAt (𝓡∂ n) x
  have het : e y ∈ e.target := e.map_source (by rwa [extChartAt_source])
  have hr : e y ∈ range (𝓡∂ n) := extChartAt_target_subset_range x het
  have hnn : 0 ≤ e y 0 := by
    simpa only [range_modelWithCornersEuclideanHalfSpace,mem_ofPred_eq] using hr
  have hB : IsOpen ((𝓡∂ n).symm ⁻¹' (chartAt (EuclideanHalfSpace n) x).target) :=
    (chartAt (EuclideanHalfSpace n) x).open_target.preimage (𝓡∂ n).continuous_symm
  have hi : e y ∈ interior e.target ↔ 0 < e y 0 := by
    change e y ∈ interior (extChartAt (𝓡∂ n) x).target ↔ _
    rw [extChartAt_target,interior_inter,hB.interior_eq,interior_range_modelWithCornersEuclideanHalfSpace]
    constructor
    · exact fun hz => hz.2
    · intro hz
      refine ⟨?_,hz⟩
      have ht := het
      change e y ∈ (extChartAt (𝓡∂ n) x).target at ht
      rw [extChartAt_target] at ht
      exact ht.1
  have hbi := (𝓡∂ n).isBoundaryPoint_iff_of_mem_atlas (n := ∞) (by simp)
    (chart_mem_atlas (EuclideanHalfSpace n) x) hy
  change y ∈ (𝓡∂ n).boundary M ↔ e y 0 = 0
  change (𝓡∂ n).IsBoundaryPoint y ↔ e y 0 = 0
  rw [hbi]
  change e y ∈ frontier e.target ↔ e y 0 = 0
  rw [mem_frontier_iff_notMem_interior het,hi]
  exact ⟨fun hz => le_antisymm (le_of_not_gt hz) hnn,fun hz => by rw [hz]; exact lt_irrefl 0⟩

end SeifertSurfaces.OriginalEndpoints.A7Support
