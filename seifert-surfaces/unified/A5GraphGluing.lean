import A5FiniteC1Gluing
import Mathlib.Analysis.Calculus.FDeriv.Comp
import A5FiniteVertexLimits
import A5PuncturedPlane

set_option autoImplicit false
open scoped ContDiff
open Set Topology
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal

/-- Finite closed-region C1 gluing constructs the shared derivative field
from equality of the actual within derivatives on overlaps. -/
theorem C1_of_finite_closed_regions_derivatives_agree
    {V W ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [Finite ι]
    (regions : ι → Set V) (hclosed : ∀ i, IsClosed (regions i))
    (hunique : ∀ i, UniqueDiffOn ℝ (regions i))
    (f : V → W) (hf : ∀ i, ContDiffOn ℝ 1 f (regions i))
    (hmatch : ∀ i j x, x ∈ regions i → x ∈ regions j →
      fderivWithin ℝ f (regions i) x = fderivWithin ℝ f (regions j) x) :
    ContDiffOn ℝ 1 f (⋃ i, regions i) := by
  classical
  let D : V → V →L[ℝ] W := fun x => if h : ∃ i, x ∈ regions i then
    fderivWithin ℝ f (regions (Classical.choose h)) x else 0
  have hD (i : ι) (x : V) (hx : x ∈ regions i) :
      D x = fderivWithin ℝ f (regions i) x := by
    dsimp only [D]
    have hex : ∃ j, x ∈ regions j := ⟨i, hx⟩
    rw [dite_eq_left hex]
    exact hmatch _ i x (Classical.choose_spec hex) hx
  apply C1_of_finite_closed_regions regions hclosed
    (fun x hx => by
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact (hunique i x hi).mono (subset_iUnion regions i)) f D
  · intro i x hx
    rw [hD i x hx]
    exact ((hf i).differentiableOn (by norm_num) x hx).hasFDerivWithinAt
  · intro i
    exact ((hf i).continuousOn_fderivWithin (hunique i) le_rfl).congr (fun x hx => hD i x hx)

/-- Two sections of the same linear projection with the same tangent image
have equal derivatives. This is the linear algebra used at an interface. -/
theorem section_derivatives_eq_of_range_eq
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (P : W →L[ℝ] V) (A B : V →L[ℝ] W)
    (hA : P.comp A = ContinuousLinearMap.id ℝ V)
    (hB : P.comp B = ContinuousLinearMap.id ℝ V)
    (hAB : A.toLinearMap.range = B.toLinearMap.range) : A = B := by
  apply ContinuousLinearMap.ext
  intro v
  have hm : A v ∈ B.toLinearMap.range := hAB ▸ ⟨v, rfl⟩
  obtain ⟨w, hw⟩ := hm
  have he : w = v := by
    have hv := congrArg (fun L : V →L[ℝ] V => L v) hA
    have hw' := congrArg (fun L : V →L[ℝ] V => L w) hB
    change P (A v) = v at hv
    change P (B w) = w at hw'
    change B w = A v at hw
    rw [hw, hv] at hw'
    exact hw'.symm
  change B w = A v at hw
  rw [he] at hw
  exact hw.symm

/-- C1 sections over finitely many closed curved regions glue to a C1
section when their tangent planes agree at every actual overlap. -/
theorem C1_graph_gluing_of_tangent_planes
    {V W ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [Finite ι]
    (regions : ι → Set V) (hclosed : ∀ i, IsClosed (regions i))
    (hunique : ∀ i, UniqueDiffOn ℝ (regions i))
    (G : V → W) (P : W →L[ℝ] V)
    (hG : ∀ i, ContDiffOn ℝ 1 G (regions i))
    (hsection : ∀ x ∈ ⋃ i, regions i, P (G x) = x)
    (htangent : ∀ i j x, x ∈ regions i → x ∈ regions j →
      (fderivWithin ℝ G (regions i) x).toLinearMap.range =
        (fderivWithin ℝ G (regions j) x).toLinearMap.range) :
    ContDiffOn ℝ 1 G (⋃ i, regions i) := by
  have hder (i : ι) (x : V) (hx : x ∈ regions i) :
      P.comp (fderivWithin ℝ G (regions i) x) = ContinuousLinearMap.id ℝ V := by
    have he : EqOn (P ∘ G) id (regions i) := fun y hy =>
      hsection y (mem_iUnion.mpr ⟨i, hy⟩)
    have hd := P.hasFDerivAt.comp_hasFDerivWithinAt x
      (((hG i).differentiableOn (by norm_num)) x hx).hasFDerivWithinAt
    have hc : HasFDerivWithinAt id (P.comp (fderivWithin ℝ G (regions i) x)) (regions i) x :=
      hd.congr he.symm (he hx).symm
    exact (hc.fderivWithin (hunique i x hx)).symm.trans
      ((hasFDerivWithinAt_id x (regions i)).fderivWithin (hunique i x hx))
  apply C1_of_finite_closed_regions_derivatives_agree regions hclosed hunique G hG
  intro i j x hi hj
  exact section_derivatives_eq_of_range_eq P _ _ (hder i x hi) (hder j x hj)
    (htangent i j x hi hj)

/-- Once the actual projected pieces form one graph, C1 regularity extends
across their common vertex. Agreement is required only away from the vertex;
connected punctured neighborhoods force the missing derivative agreement. -/
theorem C1_graph_across_finite_vertex
    {W ι : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [Finite ι]
    (x : SeifertSurfaces.Foundations.Euc 2)
    (regions : ι → Set (SeifertSurfaces.Foundations.Euc 2))
    (hclosed : ∀ i, IsClosed (regions i))
    (hunique : ∀ i, UniqueDiffOn ℝ (regions i))
    (hcover : (⋃ i, regions i) ∈ 𝓝 x)
    (hacc : ∀ i, x ∈ closure (regions i \ {x}))
    (G : SeifertSurfaces.Foundations.Euc 2 → W)
    (hG : ∀ i, ContDiffOn ℝ 1 G (regions i))
    (hmatch : ∀ i j y, y ∈ regions i → y ∈ regions j → y ≠ x →
      fderivWithin ℝ G (regions i) y = fderivWithin ℝ G (regions j) y) :
    ContDiffOn ℝ 1 G (⋃ i, regions i) := by
  have hxi (i : ι) : x ∈ regions i :=
    (hclosed i).closure_subset_iff.mpr sdiff_subset (hacc i)
  have hvertex := finite_incident_limits_agree x regions hclosed hcover hacc
    (fun i => fderivWithin ℝ G (regions i))
    (fun i => (hG i).continuousOn_fderivWithin (hunique i) le_rfl x (hxi i))
    hmatch (punctured_chart_neighborhoods (OpenPartialHomeomorph.refl _) x (mem_univ _))
  apply C1_of_finite_closed_regions_derivatives_agree regions hclosed hunique G hG
  intro i j y hyi hyj
  by_cases hy : y = x
  · subst y
    exact hvertex i j
  · exact hmatch i j y hyi hyj hy

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
