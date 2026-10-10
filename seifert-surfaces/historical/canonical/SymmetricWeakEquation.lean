import WeakDivergenceData
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.MeasureTheory.Function.L2Space

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace SeifertSurfaces.WeakSchauder

theorem weak_mixed_integral_comm (Ω : Set V) (h : V → ℝ) (hh : H1Witness h Ω)
    (φ : V → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (hφΩ : tsupport φ ⊆ Ω) (i j : Fin 3) :
    (∫ x in Ω, hh.weakGrad x j * (fderiv ℝ φ x) (EuclideanSpace.single i 1)) =
      ∫ x in Ω, hh.weakGrad x i * (fderiv ℝ φ x) (EuclideanSpace.single j 1) := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ φ) := hφ.fderiv_right (by simp)
  have hi := hh.isWeakGrad j (fun x => (fderiv ℝ φ x) (EuclideanSpace.single i 1))
    (hd.clm_apply contDiff_const) (hφc.fderiv_apply (𝕜 := ℝ) _)
    ((tsupport_fderiv_apply_subset ℝ _).trans hφΩ)
  have hj := hh.isWeakGrad i (fun x => (fderiv ℝ φ x) (EuclideanSpace.single j 1))
    (hd.clm_apply contDiff_const) (hφc.fderiv_apply (𝕜 := ℝ) _)
    ((tsupport_fderiv_apply_subset ℝ _).trans hφΩ)
  have heq (x : V) :
      (fderiv ℝ (fun y => (fderiv ℝ φ y) (EuclideanSpace.single i 1)) x)
        (EuclideanSpace.single j 1) =
      (fderiv ℝ (fun y => (fderiv ℝ φ y) (EuclideanSpace.single j 1)) x)
        (EuclideanSpace.single i 1) := by
    rw [fderiv_clm_apply (hd.differentiable (by simp) x) (differentiableAt_const _),
      fderiv_clm_apply (hd.differentiable (by simp) x) (differentiableAt_const _)]
    simpa using (hφ.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)
      (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)
  have hess : (∫ x in Ω, h x *
      (fderiv ℝ (fun y => (fderiv ℝ φ y) (EuclideanSpace.single i 1)) x)
        (EuclideanSpace.single j 1)) =
      ∫ x in Ω, h x *
      (fderiv ℝ (fun y => (fderiv ℝ φ y) (EuclideanSpace.single j 1)) x)
        (EuclideanSpace.single i 1) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => congrArg (fun z : ℝ => h x * z) (heq x)
  linarith

theorem real_inner_toLp (μ : Measure V) {f g : V → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  simp [hx, hy, mul_comm]

theorem tendsto_integral_mul_of_L2 (μ : Measure V) {f g : V → ℝ} {gseq : ℕ → V → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (hseq : ∀ n, MemLp (gseq n) 2 μ)
    (hconv : Tendsto (fun n => eLpNorm (gseq n - g) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, f x * gseq n x ∂μ) atTop (𝓝 (∫ x, f x * g x ∂μ)) := by
  have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' gseq hseq g hg).mpr hconv
  have ht' := (tendsto_const_nhds (x := hf.toLp f)).inner ht (𝕜 := ℝ)
  simpa only [real_inner_toLp] using ht'

theorem weak_H01_mixed_integral_comm (Ω : Set V) (hΩ : IsOpen Ω)
    (h : V → ℝ) (hh : H1Witness h Ω) (φ : V → ℝ) (hφ : DeGiorgi.MemH01 φ Ω)
    (hφw : H1Witness φ Ω) (i j : Fin 3) :
    (∫ x in Ω, hh.weakGrad x j * hφw.weakGrad x i) =
      ∫ x in Ω, hh.weakGrad x i * hφw.weakGrad x j := by
  obtain ⟨hw, ψ, hψ, hψc, hψΩ, -, hconv⟩ := hφ.2
  have hD (k : Fin 3) (n : ℕ) : MemLp
      (fun x => (fderiv ℝ (ψ n) x) (EuclideanSpace.single k 1)) 2 (volume.restrict Ω) := by
    exact (((hψ n).fderiv_right (show (↑(⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ↑(⊤ : ℕ∞) by simp)).clm_apply
      contDiff_const).continuous.memLp_of_hasCompactSupport
      ((hψc n).fderiv_apply (𝕜 := ℝ) _) |>.restrict Ω
  have hi := tendsto_integral_mul_of_L2 (volume.restrict Ω)
    (hh.weakGrad_component_memLp j) (hw.weakGrad_component_memLp i) (hD i) (hconv i)
  have hj := tendsto_integral_mul_of_L2 (volume.restrict Ω)
    (hh.weakGrad_component_memLp i) (hw.weakGrad_component_memLp j) (hD j) (hconv j)
  have heq : (fun n => ∫ x in Ω, hh.weakGrad x j *
      (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1)) =
      fun n => ∫ x in Ω, hh.weakGrad x i *
      (fderiv ℝ (ψ n) x) (EuclideanSpace.single j 1) := by
    funext n
    exact weak_mixed_integral_comm Ω h hh (ψ n) (hψ n) (hψc n) (hψΩ n) i j
  have hlim := tendsto_nhds_unique (heq ▸ hi) hj
  have hgrad (k : Fin 3) : (fun x => hw.weakGrad x k) =ᵐ[volume.restrict Ω]
      fun x => hφw.weakGrad x k :=
    (hw.isWeakGrad k).ae_eq hΩ (hφw.isWeakGrad k)
      ((hw.weakGrad_component_memLp k).locallyIntegrable (by norm_num))
      ((hφw.weakGrad_component_memLp k).locallyIntegrable (by norm_num))
  calc
    _ = ∫ x in Ω, hh.weakGrad x j * hw.weakGrad x i := by
      apply integral_congr_ae
      filter_upwards [hgrad i] with x hx
      rw [hx]
    _ = ∫ x in Ω, hh.weakGrad x i * hw.weakGrad x j := hlim
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hgrad j] with x hx
      rw [hx]

theorem matrix_pairing_sum (A : Mat) (x y : V) :
    inner ℝ (DeGiorgi.matMulE A x) y =
      ∑ i : Fin 3, ∑ j : Fin 3, A i j * x j * y i := by
  simp [DeGiorgi.matMulE, PiLp.inner_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

theorem constant_pairing_integrable (A : Mat) (Ω : Set V) (G H : V → V)
    (hG : ∀ j : Fin 3, MemLp (fun x => G x j) 2 (volume.restrict Ω))
    (hH : ∀ i : Fin 3, MemLp (fun x => H x i) 2 (volume.restrict Ω)) :
    IntegrableOn (fun x => inner ℝ (DeGiorgi.matMulE A (G x)) (H x)) Ω := by
  simp only [matrix_pairing_sum]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  simpa only [Pi.mul_apply, mul_assoc] using ((hG j).integrable_mul (hH i)).const_mul (A i j)

theorem constant_pairing_integral (A : Mat) (Ω : Set V) (G H : V → V)
    (hG : ∀ j : Fin 3, MemLp (fun x => G x j) 2 (volume.restrict Ω))
    (hH : ∀ i : Fin 3, MemLp (fun x => H x i) 2 (volume.restrict Ω)) :
    (∫ x in Ω, inner ℝ (DeGiorgi.matMulE A (G x)) (H x)) =
      ∑ i : Fin 3, ∑ j : Fin 3, A i j * ∫ x in Ω, G x j * H x i := by
  have hint (i j : Fin 3) : Integrable (fun x => A i j * G x j * H x i)
      (volume.restrict Ω) := by
    simpa only [Pi.mul_apply, mul_assoc] using ((hG j).integrable_mul (hH i)).const_mul (A i j)
  simp only [matrix_pairing_sum]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hint i j)]
  apply Finset.sum_congr rfl
  intro j _
  simp only [mul_assoc, integral_const_mul]

theorem constant_symmetric_pairing_integral (A : Mat) (Ω : Set V) (hΩ : IsOpen Ω)
    (h : V → ℝ) (hh : H1Witness h Ω) (φ : V → ℝ) (hφ : DeGiorgi.MemH01 φ Ω)
    (hφw : H1Witness φ Ω) :
    (∫ x in Ω, inner ℝ (DeGiorgi.matMulE A (hh.weakGrad x)) (hφw.weakGrad x)) =
      ∫ x in Ω, inner ℝ (DeGiorgi.matMulE (symmetricPart A) (hh.weakGrad x))
        (hφw.weakGrad x) := by
  rw [constant_pairing_integral A Ω hh.weakGrad hφw.weakGrad
    hh.weakGrad_component_memLp hφw.weakGrad_component_memLp,
    constant_pairing_integral (symmetricPart A) Ω hh.weakGrad hφw.weakGrad
    hh.weakGrad_component_memLp hφw.weakGrad_component_memLp]
  let F (i j : Fin 3) : ℝ := ∫ x in Ω, hh.weakGrad x j * hφw.weakGrad x i
  have hF (i j : Fin 3) : F i j = F j i :=
    weak_H01_mixed_integral_comm Ω hΩ h hh φ hφ hφw i j
  change (∑ i, ∑ j, A i j * F i j) = ∑ i, ∑ j, symmetricPart A i j * F i j
  simp only [symmetricPart, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply,
    smul_eq_mul, mul_add, add_mul, Finset.sum_add_distrib]
  have ht : (∑ i : Fin 3, ∑ j : Fin 3, (1 / 2 : ℝ) * A j i * F i j) =
      ∑ i : Fin 3, ∑ j : Fin 3, (1 / 2 : ℝ) * A i j * F i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hF j i]
  rw [ht]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  ring

theorem constant_symmetric_part_equation (center : V) (R : ℝ) (hR : 0 < R)
    (A : Mat) (h : V → ℝ) (hh : H1Witness h (Metric.ball center R)) :
    WeakEquation (fun _ => A) hh ↔ WeakEquation (fun _ => symmetricPart A) hh := by
  constructor
  · intro hw φ hφ hφw
    refine ⟨constant_pairing_integrable _ _ _ _ hh.weakGrad_component_memLp
      hφw.weakGrad_component_memLp, ?_⟩
    rw [← constant_symmetric_pairing_integral A _ Metric.isOpen_ball h hh φ hφ hφw]
    exact (hw φ hφ hφw).2
  · intro hw φ hφ hφw
    refine ⟨constant_pairing_integrable _ _ _ _ hh.weakGrad_component_memLp
      hφw.weakGrad_component_memLp, ?_⟩
    rw [constant_symmetric_pairing_integral A _ Metric.isOpen_ball h hh φ hφ hφw]
    exact (hw φ hφ hφw).2

end SeifertSurfaces.WeakSchauder
