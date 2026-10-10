import NativeBoundaryFiniteHolderAlgebra

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity

theorem NativeCapHolder.prodMk
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {K : Set E2} (hKD : UniqueDiffOn ℝ K) {α : ℝ≥0} {n : ℕ}
    {f : E2 → F} {g : E2 → G}
    (hf : NativeCapHolder K α n f) (hg : NativeCapHolder K α n g) :
    NativeCapHolder K α n (fun x => (f x, g x)) := by
  apply ((hf.comp_linear hKD (ContinuousLinearMap.inl ℝ F G)).add hKD
      (hg.comp_linear hKD (ContinuousLinearMap.inr ℝ F G))).congr
  intro x _
  ext <;> simp

theorem native_capHolder_of_partials
    (c : E2) (hcf : c 0 = 0) (r : ℝ) (hr : 0 < r)
    (K0 : Set E2) (hsub : nativeClosedBoundaryCap c r ⊆ K0)
    (v : E2 → ℝ) (hv : DifferentiableOn ℝ v K0)
    (α : ℝ≥0) (hα : 0 < α) (n : ℕ)
    (hparts : ∀ i : Fin 2, NativeCapHolder (nativeClosedBoundaryCap c r) α n
      (fun x => fderivWithin ℝ v K0 x (coordinateVector 2 i))) :
    NativeCapHolder (nativeClosedBoundaryCap c r) α (n + 1) v := by
  let K := nativeClosedBoundaryCap c r
  have hKD := nativeClosedBoundaryCap_uniqueDiffOn c r hr hcf
  have hp : ∀ i : Fin 2, NativeCapHolder K α n
      (fun x => fderivWithin ℝ v K x (coordinateVector 2 i)) := by
    intro i
    apply (hparts i).congr
    intro x hx
    dsimp only
    rw [fderivWithin_subset hsub (hKD x hx) (hv x (hsub hx))]
  have hD : ContDiffOn ℝ n (fderivWithin ℝ v K) K :=
    (NativeCapHolder.assemble_clm hKD (fderivWithin ℝ v K) hp).contDiffOn hα
  refine ⟨?_, hp⟩
  simpa only [Nat.cast_add, Nat.cast_one] using
    contDiffOn_succ_of_fderivWithin (hv.mono hsub) (by simp) hD

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
