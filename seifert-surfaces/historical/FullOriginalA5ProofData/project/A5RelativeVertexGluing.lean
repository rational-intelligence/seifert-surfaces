import A5RelativeClosedGluing
import A5FiniteVertexLimits
import A5PuncturedPlane

set_option autoImplicit false
open scoped ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations

/-- Connected punctured planar neighborhoods force the vertex values of
finitely many continuous fields on relatively closed incident regions to
agree. The compact localization is constructed inside the actual domain. -/
theorem finite_relative_incident_limits_agree
    {Y ι : Type*} [TopologicalSpace Y] [T2Space Y] [Finite ι]
    (U : Set (Euc 2)) (hU : IsOpen U) (x : Euc 2) (hx : x ∈ U)
    (regions : ι → Set (Euc 2))
    (hclosed : ∀ i, closure (regions i) ∩ U ⊆ regions i)
    (hcover : (⋃ i, regions i) = U)
    (hacc : ∀ i, x ∈ closure (regions i \ {x}))
    (g : ι → Euc 2 → Y) (hg : ∀ i, ContinuousWithinAt (g i) (regions i) x)
    (hmatch : ∀ i j y, y ∈ regions i → y ∈ regions j → y ≠ x → g i y = g j y) :
    ∀ i j, g i x = g j x := by
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  let K := Metric.closedBall x (r / 2)
  have hr2 : 0 < r / 2 := half_pos hr
  have hKU : K ⊆ U := fun y hy => hrU
    (show dist y x < r from (show dist y x ≤ r / 2 from hy).trans_lt (half_lt_self hr))
  have hK : K ∈ 𝓝 x := Metric.closedBall_mem_nhds x hr2
  let R (i : ι) := regions i ∩ K
  have hRc (i : ι) : IsClosed (R i) := by
    apply closure_subset_iff_isClosed.mp
    intro y hy
    have h1 : y ∈ closure (regions i) := closure_mono inter_subset_left hy
    have h2 : y ∈ K := Metric.isClosed_closedBall.closure_subset_iff.mpr inter_subset_right hy
    exact ⟨hclosed i ⟨h1, hKU h2⟩, h2⟩
  have hRcover : (⋃ i, R i) ∈ 𝓝 x := by
    apply mem_of_superset hK
    intro y hy
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover.symm ▸ hKU hy)
    exact mem_iUnion.mpr ⟨i, hi, hy⟩
  have hRacc (i : ι) : x ∈ closure (R i \ {x}) := by
    apply mem_closure_iff_nhds.mpr
    intro V hV
    obtain ⟨y, hy, hi⟩ := mem_closure_iff_nhds.mp (hacc i) _ (inter_mem hV hK)
    exact ⟨y, hy.1, ⟨hi.1, hy.2⟩, hi.2⟩
  exact finite_incident_limits_agree x R hRc hRcover hRacc g
    (fun i => (hg i).mono inter_subset_left)
    (fun i j y hi hj hy => hmatch i j y hi.1 hj.1 hy)
    (punctured_chart_neighborhoods (OpenPartialHomeomorph.refl _) x (mem_univ _))

/-- For finite incident projected regions, unique differentiability itself
provides the needed accumulation. Derivative matching is required only away
from the remaining vertex. -/
theorem C1_graph_on_open_across_finite_vertex
    {W ι : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [Finite ι]
    (U : Set (Euc 2)) (hU : IsOpen U) (x : Euc 2) (hx : x ∈ U)
    (regions : ι → Set (Euc 2))
    (hclosed : ∀ i, closure (regions i) ∩ U ⊆ regions i)
    (hcover : (⋃ i, regions i) = U)
    (hincident : ∀ i, x ∈ regions i)
    (hunique : ∀ i, UniqueDiffOn ℝ (regions i))
    (f : Euc 2 → W) (hf : ∀ i, ContDiffOn ℝ 1 f (regions i))
    (hmatch : ∀ i j y, y ∈ regions i → y ∈ regions j → y ≠ x →
      fderivWithin ℝ f (regions i) y = fderivWithin ℝ f (regions j) y) :
    ContDiffOn ℝ 1 f U := by
  have hacc (i : ι) : x ∈ closure (regions i \ {x}) := by
    exact mem_closure_iff_nhds.mpr (clusterPt_principal_iff.mp
      (accPt_principal_iff_clusterPt.mp (hunique i x (hincident i)).accPt))
  have hvertex := finite_relative_incident_limits_agree U hU x hx regions hclosed hcover hacc
    (fun i => fderivWithin ℝ f (regions i))
    (fun i => (hf i).continuousOn_fderivWithin (hunique i) le_rfl x (hincident i)) hmatch
  apply C1_of_relatively_closed_regions_derivatives_agree U hU regions hclosed hcover hunique f hf
  intro i j y hi hj
  by_cases hy : y = x
  · subst y
    exact hvertex i j
  · exact hmatch i j y hi hj hy

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
