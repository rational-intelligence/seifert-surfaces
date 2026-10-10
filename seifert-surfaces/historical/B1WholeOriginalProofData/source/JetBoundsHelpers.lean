import LocalizationBasic

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology BigOperators ContDiff
namespace SeifertSurfaces.QuasilinearLocalization.Helpers
open SeifertSurfaces.AppendixACoordinates

section PartialDerivatives
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma fderiv_x_slice (f : Jet → F) (j : Jet) (hf : DifferentiableAt ℝ f j) :
    fderiv ℝ (fun x : E2 => f (x, j.2.1, j.2.2)) j.1 =
      (fderiv ℝ f j).comp (ContinuousLinearMap.inl ℝ E2 (ℝ × E2)) := by
  have hs : HasFDerivAt (fun x : E2 => (x, j.2))
      (ContinuousLinearMap.inl ℝ E2 (ℝ × E2)) j.1 :=
    (hasFDerivAt_id (𝕜 := ℝ) j.1).prodMk (hasFDerivAt_const (𝕜 := ℝ) j.2 j.1)
  exact (hf.hasFDerivAt.comp j.1 hs).fderiv

lemma fderiv_z_slice (f : Jet → F) (j : Jet) (hf : DifferentiableAt ℝ f j) :
    fderiv ℝ (fun z : ℝ => f (j.1, z, j.2.2)) j.2.1 =
      (fderiv ℝ f j).comp ((ContinuousLinearMap.inr ℝ E2 (ℝ × E2)).comp
        (ContinuousLinearMap.inl ℝ ℝ E2)) := by
  have hs : HasFDerivAt (fun z : ℝ => (j.1, z, j.2.2))
      ((ContinuousLinearMap.inr ℝ E2 (ℝ × E2)).comp
        (ContinuousLinearMap.inl ℝ ℝ E2)) j.2.1 := by
    simpa using (((ContinuousLinearMap.inr ℝ E2 (ℝ × E2)).comp
      (ContinuousLinearMap.inl ℝ ℝ E2)).hasFDerivAt.add_const (j.1, (0, j.2.2)))
  exact (hf.hasFDerivAt.comp j.2.1 hs).fderiv

lemma fderiv_p_slice (f : Jet → F) (j : Jet) (hf : DifferentiableAt ℝ f j) :
    fderiv ℝ (fun p : E2 => f (j.1, j.2.1, p)) j.2.2 =
      (fderiv ℝ f j).comp ((ContinuousLinearMap.inr ℝ E2 (ℝ × E2)).comp
        (ContinuousLinearMap.inr ℝ ℝ E2)) := by
  have hs : HasFDerivAt (fun p : E2 => (j.1, j.2.1, p))
      ((ContinuousLinearMap.inr ℝ E2 (ℝ × E2)).comp
        (ContinuousLinearMap.inr ℝ ℝ E2)) j.2.2 := by
    simpa using (((ContinuousLinearMap.inr ℝ E2 (ℝ × E2)).comp
      (ContinuousLinearMap.inr ℝ ℝ E2)).hasFDerivAt.add_const (j.1, (j.2.1, 0)))
  exact (hf.hasFDerivAt.comp j.2.2 hs).fderiv

lemma norm_fderiv_x_slice_le (f : Jet → F) (j : Jet) (hf : DifferentiableAt ℝ f j) :
    ‖fderiv ℝ (fun x : E2 => f (x, j.2.1, j.2.2)) j.1‖ ≤ ‖fderiv ℝ f j‖ := by
  rw [fderiv_x_slice f j hf]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  simpa using (fderiv ℝ f j).le_opNorm (x, 0)

lemma norm_fderiv_z_slice_one_le (f : Jet → F) (j : Jet) (hf : DifferentiableAt ℝ f j) :
    ‖fderiv ℝ (fun z : ℝ => f (j.1, z, j.2.2)) j.2.1 1‖ ≤ ‖fderiv ℝ f j‖ := by
  rw [fderiv_z_slice f j hf]
  simpa using (fderiv ℝ f j).le_opNorm (0, (1, 0))

lemma norm_fderiv_p_slice_le (f : Jet → F) (j : Jet) (hf : DifferentiableAt ℝ f j) :
    ‖fderiv ℝ (fun p : E2 => f (j.1, j.2.1, p)) j.2.2‖ ≤ ‖fderiv ℝ f j‖ := by
  rw [fderiv_p_slice f j hf]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro p
  simpa using (fderiv ℝ f j).le_opNorm (0, (0, p))
lemma compact_C2_bounds (J K : Set Jet) (hJ : IsOpen J) (hK : IsCompact K)
    (hKJ : K ⊆ J) (f : Jet → F) (hf : ContDiffOn ℝ ∞ f J) :
    ∃ C : ℝ, ∀ j ∈ K, ‖f j‖ ≤ C ∧ ‖fderiv ℝ f j‖ ≤ C ∧
      ∀ m : ℕ, m ≤ 2 → ‖iteratedFDeriv ℝ m f j‖ ≤ C := by
  have hc : ContinuousOn (fun j => ‖f j‖ + ‖fderiv ℝ f j‖ +
      ‖iteratedFDeriv ℝ 0 f j‖ + ‖iteratedFDeriv ℝ 1 f j‖ +
      ‖iteratedFDeriv ℝ 2 f j‖) J :=
    (((hf.continuousOn.norm.add (hf.continuousOn_fderiv_of_isOpen hJ (by simp)).norm).add
      (ContinuousOn.continuousOn_iteratedFDeriv hf hJ (by simp : (0 : ℕ∞ω) ≤ ∞)).norm).add
      (ContinuousOn.continuousOn_iteratedFDeriv hf hJ (by simp : (1 : ℕ∞ω) ≤ ∞)).norm).add
      (ContinuousOn.continuousOn_iteratedFDeriv hf hJ (by simp : (2 : ℕ∞ω) ≤ ∞)).norm
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hc.mono hKJ)
  refine ⟨C, ?_⟩
  intro j hj
  have hsum := hC j hj
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hsum
  have h0 := norm_nonneg (iteratedFDeriv ℝ 0 f j)
  have h1 := norm_nonneg (iteratedFDeriv ℝ 1 f j)
  have h2 := norm_nonneg (iteratedFDeriv ℝ 2 f j)
  have hd := norm_nonneg (fderiv ℝ f j)
  have hv := norm_nonneg (f j)
  refine ⟨by linarith, by linarith, ?_⟩
  intro m hm
  interval_cases m <;> linarith

end PartialDerivatives

end SeifertSurfaces.QuasilinearLocalization.Helpers
