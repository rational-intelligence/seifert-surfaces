import L2Pairing

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology BigOperators ContDiff ENNReal
namespace SeifertSurfaces.QuasilinearProviderBridge
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.QuasilinearLocalization

namespace Helpers

lemma vector_component_memLp {d : ℕ} [NeZero d] (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hG : MemLp G 2 μ) (i : Fin d) :
    MemLp (fun x => G x i) 2 μ := by
  apply hG.norm.mono' ((EuclideanSpace.proj i).continuous.comp_aestronglyMeasurable hG.aestronglyMeasurable)
  exact ae_of_all _ fun x => PiLp.norm_apply_le (G x) i

lemma integral_pairing_sum {d : ℕ} [NeZero d] (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (F G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hF : ∀ i, MemLp (fun x => F x i) 2 μ) (hG : ∀ i, MemLp (fun x => G x i) 2 μ) :
    (∫ x, inner ℝ (F x) (G x) ∂μ) = ∑ i : Fin d, ∫ x, F x i * G x i ∂μ := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mul_comm (G _ _)]
  exact integral_finsetSum _ (fun i _ => (hF i).integrable_mul (hG i))

lemma integrable_pairing {d : ℕ} [NeZero d] (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (F G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hF : ∀ i, MemLp (fun x => F x i) 2 μ) (hG : ∀ i, MemLp (fun x => G x i) 2 μ) :
    Integrable (fun x => inner ℝ (F x) (G x)) μ := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mul_comm (G _ _)]
  exact integrable_finsetSum _ (fun i _ => (hF i).integrable_mul (hG i))

lemma elliptic_flux_memLp {d : ℕ} [NeZero d] {B : Set (EuclideanSpace ℝ (Fin d))}
    (A : DeGiorgi.EllipticCoeff d B) (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hG : MemLp G 2 (volume.restrict B)) :
    MemLp (fun y => DeGiorgi.matMulE (A.a y) (G y)) 2 (volume.restrict B) := by
  apply MemLp.of_eval_piLp
  intro i
  have hm : AEStronglyMeasurable (fun y => DeGiorgi.matMulE (A.a y) (G y) i)
      (volume.restrict B) := by
    change AEStronglyMeasurable (fun y => ∑ j, A.a y i j * G y j) (volume.restrict B)
    apply Finset.aestronglyMeasurable_fun_sum
    intro j hj
    exact (A.measurable_comp i j).aestronglyMeasurable.mul
      (vector_component_memLp _ _ hG j).aestronglyMeasurable
  apply (hG.norm.const_mul A.Λ).mono' hm
  filter_upwards [A.mixed_bound] with y hy
  have h := hy (G y) (EuclideanSpace.single i 1)
  simpa [EuclideanSpace.inner_single_left, EuclideanSpace.norm_single, Real.norm_eq_abs] using h

lemma gradient3_apply (ψ : E3 → ℝ) (y : E3) (i : Fin 3) :
    gradient3 ψ y i = fderiv ℝ ψ y (EuclideanSpace.single i 1) := by
  fin_cases i <;> simp [gradient3, Fin.sum_univ_succ, coordinateVector, EuclideanSpace.single]

end Helpers

theorem R3_smooth_homogeneous_tests_extend_to_H01
    (B : Set E3) (hB : IsOpen B) (hBbdd : Bornology.IsBounded B)
    (A : DeGiorgi.EllipticCoeff 3 B) (V : E3 → ℝ)
    (hV : DeGiorgi.MemW1pWitness 2 V B)
    (hweak : LiftWeakEquation B A.a hV.weakGrad) :
    ProviderHomogeneousEquation B A V := by
  refine ⟨hV.memW1p, ?_⟩
  intro hw ψ hψ hψw
  let F : E3 → E3 := fun y => DeGiorgi.matMulE (A.a y) (hw.weakGrad y)
  have hF : MemLp F 2 (volume.restrict B) :=
    Helpers.elliptic_flux_memLp A hw.weakGrad hw.weakGrad_memLp
  have hFc := Helpers.vector_component_memLp (volume.restrict B) F hF
  refine ⟨Helpers.integrable_pairing _ F _ hFc hψw.weakGrad_component_memLp, ?_⟩
  obtain ⟨hψa, φ, hφ, hφc, hφB, hconv, hconvD⟩ := hψ.2
  have hD (i : Fin 3) (n : ℕ) : MemLp (fun y => gradient3 (φ n) y i) 2 (volume.restrict B) := by
    simp only [Helpers.gradient3_apply]
    exact ((((hφ n).fderiv_right (m := (⊤ : ℕ∞)) (by norm_cast)).clm_apply contDiff_const).continuous.memLp_of_hasCompactSupport
      ((hφc n).fderiv_apply (𝕜 := ℝ) _)).restrict B
  have hlimD (i : Fin 3) := Helpers.l2_pairing_tendsto (hFc i)
    (hψa.weakGrad_component_memLp i) (hD i)
    (show Tendsto (fun n => eLpNorm (fun y => gradient3 (φ n) y i - hψa.weakGrad y i)
      2 (volume.restrict B)) atTop (𝓝 0) by simpa only [Helpers.gradient3_apply] using hconvD i)
  have hlim : Tendsto (fun n => ∫ y in B, inner ℝ (F y) (gradient3 (φ n) y))
      atTop (𝓝 (∫ y in B, inner ℝ (F y) (hψa.weakGrad y))) := by
    simp_rw [Helpers.integral_pairing_sum _ F _ hFc (fun i => hD i _),
      Helpers.integral_pairing_sum _ F _ hFc hψa.weakGrad_component_memLp]
    exact tendsto_finsetSum _ (fun i _ => hlimD i)
  have hzero (n : ℕ) : (∫ y in B, inner ℝ (F y) (gradient3 (φ n) y)) = 0 := by
    rw [← (hweak (φ n) (hφ n) (hφc n) (hφB n)).2]
    apply integral_congr_ae
    filter_upwards [Helpers.weakGrad_ae_eq hB hw hV] with y hy
    simp only [F, hy, DeGiorgi.matMulE, matrixAction]
  have hz : (∫ y in B, inner ℝ (F y) (hψa.weakGrad y)) = 0 := by
    exact tendsto_nhds_unique hlim (by simpa only [hzero] using
      (tendsto_const_nhds (x := (0 : ℝ)) : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))
  rw [← hz]
  apply integral_congr_ae
  filter_upwards [Helpers.weakGrad_ae_eq hB hψw hψa] with y hy
  rw [hy]

end SeifertSurfaces.QuasilinearProviderBridge
