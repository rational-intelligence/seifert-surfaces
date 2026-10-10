import NativeBoundaryClosedLinearDifference

set_option autoImplicit false
set_option maxHeartbeats 50000
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity

def nativeMatrixOfCLM (L : E2 →L[ℝ] E2) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => L (coordinateVector 2 j) i

theorem nativeMatrixOfCLM_toEuclideanCLM (L : E2 →L[ℝ] E2) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2) (nativeMatrixOfCLM L) = L := by
  ext ξ i
  have he : ξ = ξ 0 • coordinateVector 2 0 + ξ 1 • coordinateVector 2 1 := by
    ext j
    fin_cases j <;> simp [coordinateVector]
  have hL := congrArg L he
  simp only [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct, Fin.sum_univ_two, nativeMatrixOfCLM]
  rw [hL]
  simp only [map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

theorem native_holder_matrix_of_clm
    (K : Set E2) (a : E2 → E2 →L[ℝ] E2) (α : ℝ≥0)
    (ha : ∃ C, HolderOnWith C α a K) :
    ∃ H, ∀ i j, HolderOnWith H α (fun x => nativeMatrixOfCLM (a x) i j) K := by
  obtain ⟨C, hC⟩ := ha
  refine ⟨C, ?_⟩
  intro i j
  apply native_holder_of_norm_distance_bound
  intro x hx y hy
  have hd : ‖a x - a y‖ ≤ (C : ℝ) * dist x y ^ (α : ℝ) := by
    simpa only [dist_eq_norm] using hC.dist_le hx hy
  calc
    _ ≤ ‖(a x - a y) (coordinateVector 2 j)‖ := by
      simpa only [nativeMatrixOfCLM, sub_apply, PiLp.sub_apply] using
        PiLp.norm_apply_le ((a x - a y) (coordinateVector 2 j)) i (p := 2)
    _ ≤ ‖a x - a y‖ * ‖coordinateVector 2 j‖ := (a x - a y).le_opNorm _
    _ = ‖a x - a y‖ := by simp [coordinateVector, PiLp.norm_single]
    _ ≤ _ := hd

/-- Extension of an actual closed-cap principal operator, with exactly the
same coercivity constant and a common entry bound on the whole plane. -/
theorem native_C1_principal_matrix_extension
    (c : E2) (hcf : c 0 = 0) (r κ M : ℝ) (hr : 0 < r)
    (a : E2 → E2 →L[ℝ] E2) (α : ℝ≥0) (hα1 : α ≤ 1)
    (ha : ContDiffOn ℝ 1 a (nativeClosedBoundaryCap c r))
    (hbound : ∀ x ∈ nativeClosedBoundaryCap c r,
      (∀ ξ : E2, κ * ‖ξ‖ ^ 2 ≤ inner ℝ (a x ξ) ξ) ∧ ‖a x‖ ≤ M) :
    ∃ H : ℝ≥0, ∃ A : E2 → Matrix (Fin 2) (Fin 2) ℝ,
      EqOn A (fun x => nativeMatrixOfCLM (a x)) (nativeClosedBoundaryCap c r) ∧
      (∀ i j, HolderWith H α (fun x => A x i j)) ∧
      (∀ x ξ, κ * ‖ξ‖ ^ 2 ≤ inner ℝ
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2) (A x) ξ) ξ ∧ ∀ i j, |A x i j| ≤ M) := by
  obtain ⟨Ca, hCa⟩ := native_contDiffOn_cap_holder c r hr a α hα1 ha
  obtain ⟨H, hH⟩ := native_holder_matrix_of_clm _ a α ⟨Ca, hCa⟩
  obtain ⟨A, hAEq, hAH, hAb⟩ := native_holder_matrix_extension_on_cap c r hr.le hcf.ge
    (fun x => nativeMatrixOfCLM (a x)) H α κ M hH (by
      intro x hx ξ
      refine ⟨by rw [nativeMatrixOfCLM_toEuclideanCLM]; exact (hbound x hx).1 ξ, ?_⟩
      intro i j
      calc
        _ ≤ ‖a x (coordinateVector 2 j)‖ := PiLp.norm_apply_le _ i (p := 2)
        _ ≤ ‖a x‖ * ‖coordinateVector 2 j‖ := (a x).le_opNorm _
        _ ≤ M := by simpa [coordinateVector, PiLp.norm_single] using (hbound x hx).2)
  exact ⟨H, A, hAEq, hAH, hAb⟩

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
