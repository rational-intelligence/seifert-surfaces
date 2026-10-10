import WeakTestExtension

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology BigOperators ContDiff
namespace SeifertSurfaces.QuasilinearProviderBridge.EnergyHelpers
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.QuasilinearLocalization

theorem weak_witness_gradient_ae (B : Set E2) (hB : IsOpen B) (v : E2 → ℝ)
    (hv hw : DeGiorgi.MemW1pWitness 2 v B) :
    hv.weakGrad =ᵐ[volume.restrict B] hw.weakGrad := by
  have hi (i : Fin 2) : (fun x => hv.weakGrad x i) =ᵐ[volume.restrict B]
      fun x => hw.weakGrad x i :=
    (hv.isWeakGrad i).ae_eq hB (hw.isWeakGrad i)
      ((hv.weakGrad_component_memLp i).locallyIntegrable (by norm_num))
      ((hw.weakGrad_component_memLp i).locallyIntegrable (by norm_num))
  filter_upwards [ae_all_iff.mpr hi] with x hx
  ext i
  exact hx i

theorem rough_smooth_tests_extend_to_H01
    (B : Set E2) (hB : IsOpen B) (hBbdd : Bornology.IsBounded B)
    (C : LinearizedCoefficients) (v : E2 → ℝ)
    (κ M : ℝ) (hbound : CoefficientBounds B C κ M)
    (hmeas : CoefficientMeasurableOn B C)
    (hsol : DeGiorgi.MemW1pWitness 2 v B)
    (hweak : LinearWeakEquation B C v hsol.weakGrad) :
    ProviderLinearWeakEquation B C v := by
  refine ⟨hsol.memW1p, ?_⟩
  intro hv φ hφ hφw
  let F := linearizedFlux C v hv.weakGrad
  let S := linearizedSource C v hv.weakGrad
  obtain ⟨hF, hS⟩ := linearized_fields_memLp B hB hBbdd C v hv.weakGrad κ M hbound
    hmeas hv.memLp hv.weakGrad_memLp
  change MemLp F 2 (volume.restrict B) at hF
  change MemLp S 2 (volume.restrict B) at hS
  have hFcomp := vector_component_memLp (volume.restrict B) F hF
  have hFφ := integrable_pairing (volume.restrict B) F hφw.weakGrad hF hφw.weakGrad_memLp
  have hSφ : Integrable (fun x => S x * φ x) (volume.restrict B) :=
    hS.integrable_mul hφw.memLp
  refine ⟨hFφ, hSφ, ?_⟩
  obtain ⟨hw, ψ, hψ, hψc, hψB, hconv, hconvD⟩ := hφ.2
  have hψLp (n : ℕ) : MemLp (ψ n) 2 (volume.restrict B) :=
    ((hψ n).continuous.memLp_of_hasCompactSupport (hψc n)).restrict B
  have hD (i : Fin 2) (n : ℕ) : MemLp
      (fun x => planarGradient (ψ n) x i) 2 (volume.restrict B) := by
    simp only [SeifertSurfaces.QuasilinearLocalization.Helpers.gradient_apply]
    exact (((hψ n).fderiv_right (show (↑(⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ↑(⊤ : ℕ∞) by simp)).clm_apply
      contDiff_const).continuous.memLp_of_hasCompactSupport
      ((hψc n).fderiv_apply (𝕜 := ℝ) _) |>.restrict B
  have hFD (n : ℕ) := integrable_pairing_components (volume.restrict B) F
    (planarGradient (ψ n)) hFcomp (fun i => hD i n)
  have hlimD (i : Fin 2) := tendsto_integral_mul_of_L2 (volume.restrict B)
    (hFcomp i) (hw.weakGrad_component_memLp i) (hD i)
    (show Tendsto (fun n => eLpNorm ((fun x => planarGradient (ψ n) x i) -
      (fun x => hw.weakGrad x i)) 2 (volume.restrict B)) atTop (𝓝 0) by
      change Tendsto (fun n => eLpNorm (fun x => planarGradient (ψ n) x i -
        hw.weakGrad x i) 2 (volume.restrict B)) atTop (𝓝 0)
      simpa only [SeifertSurfaces.QuasilinearLocalization.Helpers.gradient_apply,
        coordinateVector] using hconvD i)
  have hlimF : Tendsto (fun n => ∫ x in B, inner ℝ (F x) (planarGradient (ψ n) x))
      atTop (𝓝 (∫ x in B, inner ℝ (F x) (hw.weakGrad x))) := by
    simp_rw [integral_pairing_sum (volume.restrict B) F _ hFcomp (fun i => hD i _),
      integral_pairing_sum (volume.restrict B) F _ hFcomp hw.weakGrad_component_memLp]
    exact tendsto_finsetSum _ (fun i _ => hlimD i)
  have hlimS := tendsto_integral_mul_of_L2 (volume.restrict B) hS hw.memLp hψLp hconv
  have heq (n : ℕ) : (∫ x in B, inner ℝ (F x) (planarGradient (ψ n) x) - S x * ψ n x) = 0 := by
    rw [← (hweak (ψ n) (hψ n) (hψc n) (hψB n)).2.2]
    apply integral_congr_ae
    filter_upwards [weak_witness_gradient_ae B hB v hv hsol] with x hx
    simp only [F, S, linearizedFlux, linearizedSource, hx]
  have hzero : (∫ x in B, inner ℝ (F x) (hw.weakGrad x)) -
      (∫ x in B, S x * φ x) = 0 := by
    apply tendsto_nhds_unique (hlimF.sub hlimS)
    have heq' (n : ℕ) : (∫ x in B, inner ℝ (F x) (planarGradient (ψ n) x)) -
        (∫ x in B, S x * ψ n x) = 0 := by
      rw [← integral_sub (hFD n) (show Integrable (fun x => S x * ψ n x)
        (volume.restrict B) from hS.integrable_mul (hψLp n))]
      exact heq n
    simpa only [heq'] using (tendsto_const_nhds (x := (0 : ℝ)) :
      Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hgrad (i : Fin 2) : (fun x => hw.weakGrad x i) =ᵐ[volume.restrict B]
      fun x => hφw.weakGrad x i :=
    (hw.isWeakGrad i).ae_eq hB (hφw.isWeakGrad i)
      ((hw.weakGrad_component_memLp i).locallyIntegrable (by norm_num))
      ((hφw.weakGrad_component_memLp i).locallyIntegrable (by norm_num))
  have heqgrad : hw.weakGrad =ᵐ[volume.restrict B] hφw.weakGrad := by
    filter_upwards [ae_all_iff.mpr hgrad] with x hx
    ext i
    exact hx i
  change (∫ x in B, inner ℝ (F x) (hφw.weakGrad x) - S x * φ x) = 0
  rw [integral_sub hFφ hSφ, ← hzero]
  congr 1
  apply integral_congr_ae
  filter_upwards [heqgrad] with x hx
  rw [hx]


end SeifertSurfaces.QuasilinearProviderBridge.EnergyHelpers
