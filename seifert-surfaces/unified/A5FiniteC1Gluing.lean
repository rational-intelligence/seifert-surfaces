import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.LocallyFinite

set_option autoImplicit false
open scoped ContDiff
open Set Topology
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal

/-- C1 gluing across finitely many closed regions when the actual derivative
field agrees on the interfaces. The regions need not be convex or sectors. -/
theorem C1_of_finite_closed_regions
    {V W ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [Finite ι]
    (regions : ι → Set V) (hclosed : ∀ i, IsClosed (regions i))
    (hunique : UniqueDiffOn ℝ (⋃ i, regions i))
    (f : V → W) (D : V → V →L[ℝ] W)
    (hd : ∀ i x, x ∈ regions i → HasFDerivWithinAt f (D x) (regions i) x)
    (hD : ∀ i, ContinuousOn D (regions i)) :
    ContDiffOn ℝ 1 f (⋃ i, regions i) := by
  classical
  let _ := Fintype.ofFinite ι
  have hder (x : V) (s : Finset ι) :
      HasFDerivWithinAt f (D x) (⋃ i ∈ s, regions i) x := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      have hdi : HasFDerivWithinAt f (D x) (regions i) x := by
        by_cases hx : x ∈ regions i
        · exact hd i x hx
        · exact HasFDerivWithinAt.of_notMem_closure (by simpa [(hclosed i).closure_eq] using hx)
      simpa only [Finset.mem_insert, iUnion_iUnion_eq_or_left] using hdi.union ih
  have hall (x : V) : HasFDerivWithinAt f (D x) (⋃ i, regions i) x := by
    simpa using hder x Finset.univ
  have hDc : ContinuousOn D (⋃ i, regions i) :=
    (locallyFinite_of_finite regions).continuousOn_iUnion hclosed hD
  rw [show (1 : ℕ∞ω) = 0 + 1 by rfl,
    contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hunique]
  exact ⟨by simp, D, contDiffOn_zero.mpr hDc, fun x _ => hall x⟩

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
