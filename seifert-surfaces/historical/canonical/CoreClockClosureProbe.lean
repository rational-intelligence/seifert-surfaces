import OriginalA25SourceDefinitionsV464
import A5NativeSeamSector
import A5NativeLocalCover

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology MeasureTheory Filter
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
noncomputable section

namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal

/-- The repaired inner core clock is obtained by shrinking within the actual
open neighbourhood. Its closed image remains inside that same neighbourhood. -/
theorem continuous_seam_core_closure
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (edge : ℝ → X) (hedge : ContinuousOn edge (Ioo (-1 : ℝ) 1))
    (U : Set X) (hU : IsOpen U) (hzero : edge 0 ∈ U) :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧ closure (edge '' Ioo (-c) c) ⊆ U := by
  have hz : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := ⟨neg_one_lt_zero, zero_lt_one⟩
  have hc : ContinuousAt edge 0 := (hedge 0 hz).continuousAt (isOpen_Ioo.mem_nhds hz)
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp (hc (hU.mem_nhds hzero))
  let c := min δ 1 / 2
  have hcp : 0 < c := half_pos (lt_min hδ zero_lt_one)
  have hcδ : c < δ := by
    have := min_le_left δ 1
    dsimp only [c]
    linarith
  have hc1 : c < 1 := by
    have := min_le_right δ 1
    dsimp only [c]
    linarith
  have hsub : Icc (-c) c ⊆ Ioo (-1 : ℝ) 1 := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have him : edge '' Icc (-c) c ⊆ U := by
    rintro x ⟨t, ht, rfl⟩
    apply hδU
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  have hclosed : IsClosed (edge '' Icc (-c) c) :=
    (isCompact_Icc.image_of_continuousOn (hedge.mono hsub)).isClosed
  refine ⟨c, hcp, hc1, ?_⟩
  exact (closure_minimal (image_mono Ioo_subset_Icc_self) hclosed).trans him

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
