import NativeWeakJetLocality
import DifferentialGeometry.Analysis.Integration.LpNorm

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
set_option autoImplicit false
set_option maxHeartbeats 0

private def native_supported_W12 (U : Set E2) (u : E2 → ℝ) (du : E2 → E2)
    (hu : H1On U u du) : DeGiorgi.MemW1pWitness 2 u U where
  memLp := hu.2.1
  weakGrad := du
  weakGrad_component_memLp := fun j => hu.2.2.eval_piLp j
  isWeakGrad := by
    intro j phi hp hc hs
    have hbasis : EuclideanSpace.single j 1 = coordinateVector 2 j := by
      ext k
      simp [coordinateVector, EuclideanSpace.single]
    rw [hbasis]
    exact hu.1.2.2 phi hp hc hs j

private theorem native_H1_supported_is_H10
    (U K : Set E2) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (u : E2 → ℝ) (du : E2 → E2) (hu : H1On U u du)
    (hsu : tsupport u ⊆ K) (hsdu : ∀ i, tsupport (fun x => du x i) ⊆ K) :
    H10On U u du := by
  classical
  let w := native_supported_W12 U u du hu
  let w2 : DeGiorgi.MemW1pWitness (ENNReal.ofReal 2) u U :=
    { memLp := by simpa using hu.2.1
      weakGrad := du
      weakGrad_component_memLp := fun i => by simpa using hu.2.2.eval_piLp i
      isWeakGrad := w.isWeakGrad }
  have hsu' : tsupport u ⊆ K := hsu
  have hsdu' : ∀ i, tsupport (fun x => w2.weakGrad x i) ⊆ K := by
    intro i
    simpa [w2] using hsdu i
  obtain ⟨phi, hps, hpc, hpt, hp0, hpd0⟩ :=
    DeGiorgi.exists_smooth_W1p_approx_of_supportedWitness hU (by norm_num : (1 : ℝ) < 2)
      w2 hK hKU hsu' hsdu'
  have hLp (n : ℕ) : MemLp (phi n) 2 (volume.restrict U) :=
    ((hps n).continuous.memLp_of_hasCompactSupport (μ := volume) (hpc n)).restrict U
  have hdLp (n : ℕ) (i : Fin 2) :
      MemLp (fun x => fderiv ℝ (phi n) x (coordinateVector 2 i)) 2 (volume.restrict U) :=
    (((hps n).continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      ((hpc n).fderiv_apply ℝ (coordinateVector 2 i)) |>.restrict U
  have hscalar (f : ℕ → E2 → ℝ)
      (hf : ∀ n, MemLp (f n) 2 (volume.restrict U))
      (ht : Tendsto (fun n => eLpNorm (f n) 2 (volume.restrict U)) atTop (𝓝 0)) :
      Tendsto (fun n => ∫ x in U, (f n x)^2) atTop (𝓝 0) := by
    have h := ((ENNReal.tendsto_toReal (a := 0) (by simp)).comp ht).pow 2
    simp only [ENNReal.toReal_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at h
    exact h.congr (fun n => (DifferentialGeometry.Analysis.Integration.integral_sq_eq_l2 (hf n)).symm)
  have hv0 : Tendsto (fun n => ∫ x in U, (phi n x - u x)^2) atTop (𝓝 0) := by
    apply hscalar (fun n x => phi n x - u x) (fun n => (hLp n).sub hu.2.1)
    simpa using hp0
  have hd0 (i : Fin 2) : Tendsto
      (fun n => ∫ x in U, (fderiv ℝ (phi n) x (coordinateVector 2 i) - du x i)^2)
      atTop (𝓝 0) := by
    apply hscalar (fun n x => fderiv ℝ (phi n) x (coordinateVector 2 i) - du x i)
      (fun n => (hdLp n i).sub (hu.2.2.eval_piLp i))
    have hbasis : EuclideanSpace.single i 1 = coordinateVector 2 i := by
      ext j
      simp [coordinateVector, EuclideanSpace.single]
    simpa [hbasis, w2, native_supported_W12] using hpd0 i
  have hgradCoord (n : ℕ) (x : E2) (i : Fin 2) :
      planarGradient (phi n) x i = fderiv ℝ (phi n) x (coordinateVector 2 i) := by
    fin_cases i <;> simp [planarGradient, Fin.sum_univ_two, coordinateVector]
  have herror (n : ℕ) :
      (∫ x in U, |u x - phi n x| ^ 2 + ‖du x - planarGradient (phi n) x‖ ^ 2) =
      (∫ x in U, (phi n x - u x)^2) +
        (∫ x in U, (fderiv ℝ (phi n) x (coordinateVector 2 0) - du x 0)^2) +
        (∫ x in U, (fderiv ℝ (phi n) x (coordinateVector 2 1) - du x 1)^2) := by
    have hi0 := ((hdLp n 0).sub (hu.2.2.eval_piLp 0)).integrable_sq
    have hi1 := ((hdLp n 1).sub (hu.2.2.eval_piLp 1)).integrable_sq
    have hiv := ((hLp n).sub hu.2.1).integrable_sq
    simp only [Pi.sub_apply] at hi0 hi1 hiv
    have hpoint : ∀ x, |u x - phi n x| ^ 2 + ‖du x - planarGradient (phi n) x‖ ^ 2 =
        (phi n x - u x)^2 +
          ((fderiv ℝ (phi n) x (coordinateVector 2 0) - du x 0)^2) +
          ((fderiv ℝ (phi n) x (coordinateVector 2 1) - du x 1)^2) := by
      intro x
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, sq_abs]
      simp only [PiLp.sub_apply, hgradCoord]
      ring
    calc
      _ = ∫ x in U, ((phi n x - u x)^2 +
          ((fderiv ℝ (phi n) x (coordinateVector 2 0) - du x 0)^2) +
          ((fderiv ℝ (phi n) x (coordinateVector 2 1) - du x 1)^2)) :=
        integral_congr_ae (Filter.Eventually.of_forall hpoint)
      _ = _ := by
        have hadd := integral_add (hiv.add hi0) hi1
        simp only [Pi.add_apply] at hadd
        rw [hadd, integral_add hiv hi0]
  have ht : Tendsto
      (fun n => ∫ x in U, |u x - phi n x| ^ 2 + ‖du x - planarGradient (phi n) x‖ ^ 2)
      atTop (𝓝 0) := by
    have h := (hv0.add (hd0 0)).add (hd0 1)
    simp only [add_zero] at h
    exact h.congr (fun n => (herror n).symm)
  refine ⟨hu, ?_⟩
  intro eps heps
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds heps)).exists
  exact ⟨phi n, hps n, hpc n, hpt n, hn⟩

#print axioms native_H1_supported_is_H10
