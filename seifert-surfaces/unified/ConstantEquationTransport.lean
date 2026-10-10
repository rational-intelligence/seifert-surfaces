import LinearSobolevTransport
import ApprovedDataClosure

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace SeifertSurfaces.WeakSchauder

theorem gradient_pairing_clm (L : V →L[ℝ] ℝ) (v : V) :
    inner ℝ v (WithLp.toLp 2 (fun i => L (EuclideanSpace.single i 1))) = L v := by
  rw [clm_coordinate_sum]
  simp [PiLp.inner_apply, mul_comm]

theorem constant_weak_smooth_integral (A : Mat) (Ω : Set V) (hΩ : IsOpen Ω)
    (h : V → ℝ) (hh : H1Witness h Ω) (hw : WeakEquation (fun _ => A) hh)
    (φ : V → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (hφΩ : tsupport φ ⊆ Ω) :
    (∫ x in Ω, (fderiv ℝ φ x) (DeGiorgi.matMulE A (hh.weakGrad x))) = 0 := by
  let w := DeGiorgi.MemW1pWitness.restrict hΩ (subset_univ Ω)
    (DeGiorgi.MemW1pWitness.ofContDiffHasCompactSupport (p := 2) hφ hφc)
  have he := (hw φ
    (DeGiorgi.memW01p_of_contDiff_hasCompactSupport_subset hΩ hφ hφc hφΩ) w).2
  change (∫ x in Ω, inner ℝ (DeGiorgi.matMulE A (hh.weakGrad x))
    (WithLp.toLp 2 (fun i => (fderiv ℝ φ x) (EuclideanSpace.single i 1)))) = 0 at he
  simpa only [gradient_pairing_clm] using he

theorem constant_weak_of_smooth_integral (A : Mat) (Ω : Set V) (hΩ : IsOpen Ω)
    (h : V → ℝ) (hh : H1Witness h Ω)
    (hsmooth : ∀ (φ : V → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω → (∫ x in Ω, (fderiv ℝ φ x) (DeGiorgi.matMulE A (hh.weakGrad x))) = 0) :
    WeakEquation (fun _ => A) hh := by
  intro φ hφ hφw
  refine ⟨constant_pairing_integrable A Ω _ _ hh.weakGrad_component_memLp
    hφw.weakGrad_component_memLp, ?_⟩
  obtain ⟨hw, ψ, hψ, hψc, hψΩ, -, hconv⟩ := hφ.2
  have hD (k : Fin 3) (n : ℕ) : MemLp
      (fun x => (fderiv ℝ (ψ n) x) (EuclideanSpace.single k 1)) 2 (volume.restrict Ω) := by
    have hd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (ψ n)) := (hψ n).fderiv_right (by simp)
    exact ((hd.clm_apply contDiff_const).continuous.memLp_of_hasCompactSupport
      ((hψc n).fderiv_apply (𝕜 := ℝ) _)).restrict Ω
  have ht (i j : Fin 3) := tendsto_integral_mul_of_L2 (volume.restrict Ω)
    (hh.weakGrad_component_memLp j) (hw.weakGrad_component_memLp i) (hD i) (hconv i)
  have hsum : Tendsto
      (fun n => ∑ i : Fin 3, ∑ j : Fin 3, A i j *
        ∫ x in Ω, hh.weakGrad x j * (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1)) atTop
      (𝓝 (∑ i : Fin 3, ∑ j : Fin 3, A i j * ∫ x in Ω, hh.weakGrad x j * hw.weakGrad x i)) := by
    apply tendsto_finsetSum
    intro i _
    apply tendsto_finsetSum
    intro j _
    exact tendsto_const_nhds.mul (ht i j)
  have hz (n : ℕ) : (∑ i : Fin 3, ∑ j : Fin 3, A i j *
      ∫ x in Ω, hh.weakGrad x j * (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1)) = 0 := by
    change (∑ i : Fin 3, ∑ j : Fin 3, A i j *
      ∫ x in Ω, hh.weakGrad x j * classicalGradient (ψ n) x i) = 0
    rw [← constant_pairing_integral A Ω hh.weakGrad
      (fun x => classicalGradient (ψ n) x) hh.weakGrad_component_memLp (fun i => hD i n)]
    simpa only [classicalGradient, gradient_pairing_clm] using hsmooth (ψ n) (hψ n) (hψc n) (hψΩ n)
  simp_rw [hz] at hsum
  have hlim := tendsto_nhds_unique hsum tendsto_const_nhds
  rw [constant_pairing_integral A Ω _ _ hh.weakGrad_component_memLp hφw.weakGrad_component_memLp]
  rw [← hlim]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  apply integral_congr_ae
  have hgrad := (hw.isWeakGrad i).ae_eq hΩ (hφw.isWeakGrad i)
    ((hw.weakGrad_component_memLp i).locallyIntegrable (by norm_num))
    ((hφw.weakGrad_component_memLp i).locallyIntegrable (by norm_num))
  filter_upwards [hgrad] with x hx
  rw [hx]

theorem constant_equation_to_laplace (center : V) (R : ℝ) (hR : 0 < R)
    (A : Mat) (P : V ≃L[ℝ] V)
    (hfactor : ∀ ξ : V, DeGiorgi.matMulE (symmetricPart A) ξ =
      P (P.toContinuousLinearMap.adjoint ξ))
    (h : V → ℝ) (hh : H1Witness h (Metric.ball center R))
    (hweak : WeakEquation (fun _ => A) hh) :
    ∃ hw : H1Witness (fun y => h (P y)) (pulledBackBall P center R),
      (∀ y, hw.weakGrad y = P.toContinuousLinearMap.adjoint (hh.weakGrad (P y))) ∧
      WeakEquation (fun _ => (1 : Mat)) hw := by
  let hw : H1Witness (fun y => h (P y)) (pulledBackBall P center R) :=
    linear_pullback_witness P (Metric.ball center R) h hh
  refine ⟨hw, fun _ => rfl, ?_⟩
  have hΩ : IsOpen (pulledBackBall P center R) := Metric.isOpen_ball.preimage P.continuous
  apply constant_weak_of_smooth_integral _ _ hΩ _ hw
  intro φ hφ hφc hφΩ
  let ψ : V → ℝ := fun x => φ (P.symm x)
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := hφ.comp P.symm.contDiff
  have hψc : HasCompactSupport ψ := hφc.comp_homeomorph P.symm.toHomeomorph
  have hψΩ : tsupport ψ ⊆ Metric.ball center R := by
    rw [show ψ = φ ∘ P.symm.toHomeomorph from rfl, tsupport_comp_eq_preimage]
    intro x hx
    have ht := hφΩ hx
    change P (P.symm x) ∈ Metric.ball center R at ht
    simpa using ht
  have hdψ (x : V) : fderiv ℝ ψ x =
      (fderiv ℝ φ (P.symm x)).comp P.symm.toContinuousLinearMap :=
    ((hφ.differentiable (by simp) (P.symm x)).hasFDerivAt.comp x P.symm.hasFDerivAt).fderiv
  have hid (y : V) : (fderiv ℝ φ y) (DeGiorgi.matMulE (1 : Mat) (hw.weakGrad y)) =
      (fderiv ℝ ψ (P y)) (DeGiorgi.matMulE (symmetricPart A) (hh.weakGrad (P y))) := by
    rw [hdψ, hfactor]
    simp [hw, linear_pullback_witness, DeGiorgi.matMulE]
  simp_rw [hid]
  change (∫ y in P ⁻¹' Metric.ball center R,
    (fderiv ℝ ψ (P y)) (DeGiorgi.matMulE (symmetricPart A) (hh.weakGrad (P y)))) = 0
  rw [linear_pullback_integral P (Metric.ball center R)
    (fun x => (fderiv ℝ ψ x) (DeGiorgi.matMulE (symmetricPart A) (hh.weakGrad x))),
    constant_weak_smooth_integral _ _ Metric.isOpen_ball h hh
      ((constant_symmetric_part_equation center R hR A h hh).mp hweak) ψ hψ hψc hψΩ,
    mul_zero]

end SeifertSurfaces.WeakSchauder
