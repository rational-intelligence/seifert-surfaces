import WeakDerivativeLimit

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology BigOperators ContDiff
namespace SeifertSurfaces.QuasilinearProviderBridge.EnergyHelpers
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.QuasilinearLocalization

theorem exists_classical_gradient_weak_limit
    (B : Set E2) (hB : IsOpen B) (f : E2 → ℝ) (fseq : ℕ → E2 → ℝ)
    (hf : MemLp f 2 (volume.restrict B))
    (hC1 : ∀ n, ContDiffOn ℝ 1 (fseq n) B)
    (hG : ∀ n, MemLp (planarGradient (fseq n)) 2 (volume.restrict B))
    (C : ℝ) (hC : 0 ≤ C)
    (henergy : ∀ n, (∫ x in B, ‖planarGradient (fseq n) x‖ ^ 2) ≤ C)
    (hlimit : ∀ (i : Fin 2) (φ : E2 → ℝ), ContDiff ℝ ∞ φ →
      HasCompactSupport φ → tsupport φ ⊆ B →
      Tendsto (fun n => ∫ x in B, fseq n x * (fderiv ℝ φ x) (EuclideanSpace.single i 1))
        atTop (𝓝 (∫ x in B, f x * (fderiv ℝ φ x) (EuclideanSpace.single i 1)))) :
    ∃ (G : Lp E2 2 (volume.restrict B)) (s : ℕ → ℕ), StrictMono s ∧
      (∀ n, ‖(hG (s n)).toLp (planarGradient (fseq (s n)))‖ ≤ C + 1) ∧
      (∀ v : Lp E2 2 (volume.restrict B),
        Tendsto (fun n => inner ℝ ((hG (s n)).toLp (planarGradient (fseq (s n)))) v)
          atTop (𝓝 (inner ℝ G v))) ∧
      DeGiorgi.HasWeakGrad (G : E2 → E2) f B := by
  let Gseq : ℕ → Lp E2 2 (volume.restrict B) := fun n => (hG n).toLp (planarGradient (fseq n))
  have hnorm (n : ℕ) : ‖Gseq n‖ ≤ C + 1 := by
    have heq : ‖Gseq n‖ ^ 2 = ∫ x in B, ‖planarGradient (fseq n) x‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq]
      rw [show inner ℝ (Gseq n) (Gseq n) = _ from vector_inner_toLp _ (hG n) (hG n)]
      simp only [real_inner_self_eq_norm_sq]
    have hh := henergy n
    rw [← heq] at hh
    nlinarith [sq_nonneg (‖Gseq n‖ - 1), sq_nonneg C]
  haveI := planar_L2_separable B
  obtain ⟨G, s, hs, hweak⟩ := hilbert_weak_subsequence Gseq (C + 1) hnorm
  refine ⟨G, s, hs, fun n => hnorm (s n), hweak, ?_⟩
  intro i φ hφ hφc hφB
  have hφLp : MemLp φ 2 (volume.restrict B) :=
    (hφ.continuous.memLp_of_hasCompactSupport hφc).restrict B
  let Vφ : E2 → E2 := fun x => φ x • EuclideanSpace.single i 1
  have hVLp : MemLp Vφ 2 (volume.restrict B) := by
    apply hφLp.norm.mono' (hφLp.aestronglyMeasurable.smul_const _)
    exact ae_of_all _ fun x => by simp [Vφ, norm_smul, PiLp.norm_single]
  have hwp := hweak (hVLp.toLp Vφ)
  have hsource (n : ℕ) : inner ℝ (Gseq (s n)) (hVLp.toLp Vφ) =
      ∫ x in B, planarGradient (fseq (s n)) x i * φ x := by
    rw [show inner ℝ (Gseq (s n)) (hVLp.toLp Vφ) = _ from vector_inner_toLp _ (hG (s n)) hVLp]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by simp [Vφ, real_inner_smul_right, EuclideanSpace.inner_single_right, mul_comm]
  have htarget : inner ℝ G (hVLp.toLp Vφ) = ∫ x in B, G x i * φ x := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hVLp.coeFn_toLp] with x hx
    simp [hx, Vφ, real_inner_smul_right, EuclideanSpace.inner_single_right, mul_comm]
  rw [htarget] at hwp
  simp only [hsource] at hwp
  have hl := (hlimit i φ hφ hφc hφB).comp hs.tendsto_atTop
  have heq (n : ℕ) : (∫ x in B, fseq (s n) x * (fderiv ℝ φ x) (EuclideanSpace.single i 1)) =
      -(∫ x in B, planarGradient (fseq (s n)) x i * φ x) :=
    SeifertSurfaces.QuasilinearProviderBridge.Helpers.C1_hasWeakGrad B hB _ (hC1 (s n)) i φ hφ hφc hφB
  simp only [Function.comp_def] at hl
  simp only [heq] at hl
  exact tendsto_nhds_unique hl hwp.neg

end SeifertSurfaces.QuasilinearProviderBridge.EnergyHelpers
