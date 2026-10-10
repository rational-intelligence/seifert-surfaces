import AppendixACoordinates

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology BigOperators ContDiff
namespace SeifertSurfaces.QuasilinearLocalization.Helpers
open SeifertSurfaces.AppendixACoordinates

lemma gradient_apply (u : E2 → ℝ) (x : E2) (i : Fin 2) :
    planarGradient u x i = fderiv ℝ u x (coordinateVector 2 i) := by
  fin_cases i <;> simp [planarGradient, coordinateVector, PiLp.single_apply]

lemma gradient_dual (u : E2 → ℝ) (x : E2) :
    (InnerProductSpace.toDual ℝ E2) (planarGradient u x) = fderiv ℝ u x := by
  let v := (InnerProductSpace.toDual ℝ E2).symm (fderiv ℝ u x)
  have hv : v = planarGradient u x := by
    ext i
    rw [gradient_apply]
    have hi := EuclideanSpace.inner_single_right (i := i) (a := (1 : ℝ)) v
    have hmap : (InnerProductSpace.toDual ℝ E2) v = fderiv ℝ u x := by simp [v]
    calc
      v i = inner ℝ v (EuclideanSpace.single i (1 : ℝ)) := by simpa using hi.symm
      _ = ((InnerProductSpace.toDual ℝ E2) v) (EuclideanSpace.single i 1) := by
        rw [InnerProductSpace.toDual_apply_apply]
      _ = _ := by rw [hmap]; rfl
  rw [← hv]
  simp [v]

lemma gradient_continuousOn (Ω : Set E2) (hΩ : IsOpen Ω) (u : E2 → ℝ)
    (hu : ContDiffOn ℝ 1 u Ω) : ContinuousOn (planarGradient u) Ω := by
  unfold planarGradient
  apply continuousOn_finsetSum
  intro i hi
  exact ((hu.continuousOn_fderiv_of_isOpen hΩ le_rfl).clm_apply continuousOn_const).smul
    continuousOn_const

lemma gradient_continuous (u : E2 → ℝ) (hu : ContDiff ℝ ∞ u) :
    Continuous (planarGradient u) := by
  unfold planarGradient
  exact continuous_finsetSum _ fun i _ =>
    ((hu.continuous_fderiv (by simp)).clm_apply continuous_const).smul continuous_const

lemma gradient_zero_off_tsupport (u : E2 → ℝ) {x : E2} (hx : x ∉ tsupport u) :
    planarGradient u x = 0 := by
  simp [planarGradient, fderiv_of_notMem_tsupport ℝ hx]

lemma inner_gradient_support_subset (A : E2 → E2) (φ : E2 → ℝ) :
    support (fun x => inner ℝ (A x) (planarGradient φ x)) ⊆ tsupport φ := by
  intro x hx
  contrapose! hx
  simp [mem_support, gradient_zero_off_tsupport φ hx]

lemma mul_test_support_subset (B φ : E2 → ℝ) :
    support (fun x => B x * φ x) ⊆ tsupport φ := by
  intro x hx
  contrapose! hx
  simp [mem_support, image_eq_zero_of_notMem_tsupport hx]

lemma continuousOn_supported_integrable (Ω K : Set E2) (f : E2 → ℝ)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hf : ContinuousOn f Ω)
    (hsupp : support f ⊆ K) : Integrable f := by
  apply (integrableOn_iff_integrable_of_support_subset hsupp).mp
  exact (hf.mono hKΩ).integrableOn_compact hK

end SeifertSurfaces.QuasilinearLocalization.Helpers
