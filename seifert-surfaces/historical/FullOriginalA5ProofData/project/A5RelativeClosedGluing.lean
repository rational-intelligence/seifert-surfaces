import A5GraphGluing

set_option autoImplicit false
open scoped ContDiff
open Set Topology
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal

/-- Finite C1 gluing only needs regions closed relative to the actual open
graph domain. No artificial closed-ball boundary or convexity is imposed. -/
theorem C1_of_finite_relatively_closed_regions
    {V W ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [Finite ι]
    (U : Set V) (hU : IsOpen U) (regions : ι → Set V)
    (hclosed : ∀ i, closure (regions i) ∩ U ⊆ regions i)
    (hcover : (⋃ i, regions i) = U)
    (f : V → W) (D : V → V →L[ℝ] W)
    (hd : ∀ i x, x ∈ regions i → HasFDerivWithinAt f (D x) (regions i) x)
    (hD : ∀ i, ContinuousOn D (regions i)) : ContDiffOn ℝ 1 f U := by
  classical
  let _ := Fintype.ofFinite ι
  have hat (x : V) (hx : x ∈ U) (s : Finset ι) :
      HasFDerivWithinAt f (D x) (⋃ i ∈ s, regions i) x ∧
      ContinuousWithinAt D (⋃ i ∈ s, regions i) x := by
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty]
      exact ⟨HasFDerivWithinAt.of_notMem_closure (by simp),
        continuousWithinAt_of_notMem_closure (by simp)⟩
    | @insert i s hi ih =>
      have hdi : HasFDerivWithinAt f (D x) (regions i) x ∧
          ContinuousWithinAt D (regions i) x := by
        by_cases hxi : x ∈ regions i
        · exact ⟨hd i x hxi, hD i x hxi⟩
        · have hnot : x ∉ closure (regions i) := fun hc => hxi (hclosed i ⟨hc, hx⟩)
          exact ⟨HasFDerivWithinAt.of_notMem_closure hnot,
            continuousWithinAt_of_notMem_closure hnot⟩
      simpa only [Finset.mem_insert, iUnion_iUnion_eq_or_left] using
        And.intro (hdi.1.union ih.1) (hdi.2.union ih.2)
  have hall (x : V) (hx : x ∈ U) :
      HasFDerivWithinAt f (D x) U x ∧ ContinuousWithinAt D U x := by
    simpa [hcover] using hat x hx Finset.univ
  rw [show (1 : ℕ∞ω) = 0 + 1 by rfl,
    contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hU.uniqueDiffOn]
  exact ⟨by simp, D, contDiffOn_zero.mpr (fun x hx => (hall x hx).2),
    fun x hx => (hall x hx).1⟩

/-- Equality of actual within derivatives on all overlaps constructs the
single derivative field on a finite cover of a genuine open graph domain. -/
theorem C1_of_relatively_closed_regions_derivatives_agree
    {V W ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [Finite ι]
    (U : Set V) (hU : IsOpen U) (regions : ι → Set V)
    (hclosed : ∀ i, closure (regions i) ∩ U ⊆ regions i)
    (hcover : (⋃ i, regions i) = U)
    (hunique : ∀ i, UniqueDiffOn ℝ (regions i))
    (f : V → W) (hf : ∀ i, ContDiffOn ℝ 1 f (regions i))
    (hmatch : ∀ i j x, x ∈ regions i → x ∈ regions j →
      fderivWithin ℝ f (regions i) x = fderivWithin ℝ f (regions j) x) :
    ContDiffOn ℝ 1 f U := by
  classical
  let D : V → V →L[ℝ] W := fun x => if h : ∃ i, x ∈ regions i then
    fderivWithin ℝ f (regions (Classical.choose h)) x else 0
  have he (i : ι) (x : V) (hx : x ∈ regions i) :
      D x = fderivWithin ℝ f (regions i) x := by
    dsimp only [D]
    have hex : ∃ j, x ∈ regions j := ⟨i, hx⟩
    rw [dite_eq_left hex]
    exact hmatch _ i x (Classical.choose_spec hex) hx
  apply C1_of_finite_relatively_closed_regions U hU regions hclosed hcover f D
  · intro i x hx
    rw [he i x hx]
    exact ((hf i x hx).differentiableWithinAt (by norm_num)).hasFDerivWithinAt
  · intro i
    exact ((hf i).continuousOn_fderivWithin (hunique i) le_rfl).congr (fun x hx => he i x hx)

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
