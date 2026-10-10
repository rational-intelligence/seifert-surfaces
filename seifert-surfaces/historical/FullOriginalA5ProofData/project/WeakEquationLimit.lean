import VariablePairingLimit
import RoughTestExtension

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology BigOperators ContDiff
namespace SeifertSurfaces.QuasilinearProviderBridge.EnergyHelpers
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.QuasilinearLocalization

theorem linear_weak_equation_restrict (B D : Set E2) (hsub : B ⊆ D)
    (C : LinearizedCoefficients) (v : E2 → ℝ) (G : E2 → E2)
    (hw : LinearWeakEquation D C v G) : LinearWeakEquation B C v G := by
  intro φ hφ hφc hφB
  obtain ⟨hF, hS, he⟩ := hw φ hφ hφc (hφB.trans hsub)
  refine ⟨hF.mono_set hsub, hS.mono_set hsub, ?_⟩
  have hz (x : E2) (hx : x ∉ B) :
      inner ℝ (linearizedFlux C v G x) (planarGradient φ x) - linearizedSource C v G x * φ x = 0 := by
    have ht : x ∉ tsupport φ := fun h => hx (hφB h)
    simp [SeifertSurfaces.QuasilinearLocalization.Helpers.gradient_zero_off_tsupport φ ht,
      image_eq_zero_of_notMem_tsupport ht]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => hz x (fun h => hx (hsub h)))] at he
  exact he

theorem linear_weak_equation_congr_grad (B : Set E2) (C : LinearizedCoefficients)
    (v : E2 → ℝ) (G H : E2 → E2) (heq : G =ᵐ[volume.restrict B] H)
    (hw : LinearWeakEquation B C v G) : LinearWeakEquation B C v H := by
  intro φ hφ hφc hφB
  obtain ⟨hF, hS, hi⟩ := hw φ hφ hφc hφB
  have hF' : (fun x => inner ℝ (linearizedFlux C v G x) (planarGradient φ x)) =ᵐ[volume.restrict B]
      (fun x => inner ℝ (linearizedFlux C v H x) (planarGradient φ x)) := by
    filter_upwards [heq] with x hx
    simp only [linearizedFlux, hx]
  have hS' : (fun x => linearizedSource C v G x * φ x) =ᵐ[volume.restrict B]
      (fun x => linearizedSource C v H x * φ x) := by
    filter_upwards [heq] with x hx
    simp only [linearizedSource, hx]
  exact ⟨hF.congr hF', hS.congr hS', (integral_congr_ae (hF'.sub hS')).symm.trans hi⟩

set_option maxHeartbeats 600000 in
theorem linear_weak_equation_of_limits
    (B : Set E2) (hB : IsOpen B) (hBbdd : Bornology.IsBounded B)
    (Cseq : ℕ → LinearizedCoefficients) (C : LinearizedCoefficients)
    (vseq : ℕ → E2 → ℝ) (v : E2 → ℝ)
    (Gseq : ℕ → Lp E2 2 (volume.restrict B)) (G : Lp E2 2 (volume.restrict B))
    (κ M L : ℝ) (hboundseq : ∀ n, CoefficientBounds B (Cseq n) κ M)
    (hbound : CoefficientBounds B C κ M)
    (hmeasseq : ∀ n, CoefficientMeasurableOn B (Cseq n)) (hmeas : CoefficientMeasurableOn B C)
    (hvmseq : ∀ n, MemLp (vseq n) 2 (volume.restrict B)) (hvm : MemLp v 2 (volume.restrict B))
    (hvbseq : ∀ n, ∀ x ∈ B, |vseq n x| ≤ M)
    (hGn : ∀ n, ‖Gseq n‖ ≤ L)
    (hGweak : ∀ z, Tendsto (fun n => inner ℝ (Gseq n) z) atTop (𝓝 (inner ℝ G z)))
    (hweakseq : ∀ n, LinearWeakEquation B (Cseq n) (vseq n) (Gseq n))
    (hlimv : ∀ x ∈ B, Tendsto (fun n => vseq n x) atTop (𝓝 (v x)))
    (hlimC : ∀ x ∈ B,
      Tendsto (fun n => (Cseq n).a x) atTop (𝓝 (C.a x)) ∧
      Tendsto (fun n => (Cseq n).c x) atTop (𝓝 (C.c x)) ∧
      Tendsto (fun n => (Cseq n).d x) atTop (𝓝 (C.d x)) ∧
      Tendsto (fun n => (Cseq n).b x) atTop (𝓝 (C.b x)) ∧
      Tendsto (fun n => (Cseq n).q x) atTop (𝓝 (C.q x)) ∧
      Tendsto (fun n => (Cseq n).f x) atTop (𝓝 (C.f x))) :
    LinearWeakEquation B C v G := by
  haveI : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr hBbdd.measure_lt_top.ne
  have hM : 0 ≤ M := le_trans (by norm_num) hbound.2.1
  intro φ hφ hφc hφB
  have hdφ : Continuous (planarGradient φ) := SeifertSurfaces.QuasilinearLocalization.Helpers.gradient_continuous φ hφ
  have hdφc : HasCompactSupport (planarGradient φ) := hφc.mono' (by
    intro x hx
    by_contra ht
    exact hx (SeifertSurfaces.QuasilinearLocalization.Helpers.gradient_zero_off_tsupport φ ht))
  have hφLp : MemLp φ 2 (volume.restrict B) := (hφ.continuous.memLp_of_hasCompactSupport hφc (p := (2 : ENNReal))).restrict B
  have hdφLp : MemLp (planarGradient φ) 2 (volume.restrict B) := (hdφ.memLp_of_hasCompactSupport hdφc (p := (2 : ENNReal))).restrict B
  obtain ⟨K₀, hK₀⟩ := hφc.exists_bound_of_continuous hφ.continuous
  obtain ⟨K₁, hK₁⟩ := hdφc.exists_bound_of_continuous hdφ
  have hk₀ : 0 ≤ K₀ := (norm_nonneg (φ 0)).trans (hK₀ 0)
  have hk₁ : 0 ≤ K₁ := (norm_nonneg (planarGradient φ 0)).trans (hK₁ 0)
  have hA := integral_variable_clm_weak_limit (volume.restrict B) Gseq G L hGn hGweak
    (fun n => (Cseq n).a) C.a (fun n => (hmeasseq n).1) hmeas.1 M hM
    (fun n => by filter_upwards [ae_restrict_mem hB.measurableSet] with x hx; exact (hboundseq n).2.2.2 x hx |>.1)
    (by filter_upwards [ae_restrict_mem hB.measurableSet] with x hx; exact (hbound.2.2.2 x hx).1)
    (by filter_upwards [ae_restrict_mem hB.measurableSet] with x hx; exact (hlimC x hx).1)
    (planarGradient φ) hdφ.aestronglyMeasurable K₁ hk₁ (ae_of_all _ hK₁)
  have hb := integral_variable_clm_weak_limit (volume.restrict B) Gseq G L hGn hGweak
    (fun n => (Cseq n).b) C.b (fun n => (hmeasseq n).2.2.2.1) hmeas.2.2.2.1 M hM
    (fun n => by filter_upwards [ae_restrict_mem hB.measurableSet] with x hx; exact (hboundseq n).2.2.2 x hx |>.2.2.2.1)
    (by filter_upwards [ae_restrict_mem hB.measurableSet] with x hx; exact (hbound.2.2.2 x hx).2.2.2.1)
    (by filter_upwards [ae_restrict_mem hB.measurableSet] with x hx; exact (hlimC x hx).2.2.2.1)
    φ hφ.continuous.aestronglyMeasurable K₀ hk₀ (ae_of_all _ hK₀)
  let Rseq : ℕ → E2 → E2 := fun n x => vseq n x • (Cseq n).c x + (Cseq n).d x
  let R : E2 → E2 := fun x => v x • C.c x + C.d x
  let Sseq : ℕ → E2 → ℝ := fun n x => (Cseq n).q x * vseq n x + (Cseq n).f x
  let S : E2 → ℝ := fun x => C.q x * v x + C.f x
  have hR := integral_inner_bounded_limit (volume.restrict B) Rseq R
    (fun n => ((hvmseq n).aestronglyMeasurable.smul (hmeasseq n).2.1).add (hmeasseq n).2.2.1)
    (M * M + M) (fun n => by
      filter_upwards [ae_restrict_mem hB.measurableSet] with x hx
      exact (norm_add_le _ _).trans (add_le_add
        (by change ‖vseq n x • (Cseq n).c x‖ ≤ M*M; rw [norm_smul]; exact mul_le_mul (hvbseq n x hx) ((hboundseq n).2.2.2 x hx).2.1 (norm_nonneg _) hM)
        ((hboundseq n).2.2.2 x hx).2.2.1))
    (by filter_upwards [ae_restrict_mem hB.measurableSet] with x hx
        exact ((hlimv x hx).smul (hlimC x hx).2.1).add (hlimC x hx).2.2.1)
    (planarGradient φ) (hdφ.integrable_of_hasCompactSupport hdφc).integrableOn
  have hS := integral_inner_bounded_limit (volume.restrict B) Sseq S
    (fun n => ((hmeasseq n).2.2.2.2.1.mul (hvmseq n).aestronglyMeasurable).add (hmeasseq n).2.2.2.2.2)
    (M * M + M) (fun n => by
      filter_upwards [ae_restrict_mem hB.measurableSet] with x hx
      exact (norm_add_le _ _).trans (add_le_add
        (by simp only [Pi.mul_apply, norm_mul]; exact mul_le_mul ((hboundseq n).2.2.2 x hx).2.2.2.2.1 (hvbseq n x hx) (norm_nonneg _) hM)
        ((hboundseq n).2.2.2 x hx).2.2.2.2.2))
    (by filter_upwards [ae_restrict_mem hB.measurableSet] with x hx
        exact ((hlimC x hx).2.2.2.2.1.mul (hlimv x hx)).add (hlimC x hx).2.2.2.2.2)
    φ (hφ.continuous.integrable_of_hasCompactSupport hφc).integrableOn
  have hfields := linearized_fields_memLp B hB hBbdd C v G κ M hbound hmeas hvm (Lp.memLp G)
  have hFint := integrable_pairing _ _ _ hfields.1 hdφLp
  have hSint : IntegrableOn (fun x => linearizedSource C v G x * φ x) B := hfields.2.integrable_mul hφLp
  refine ⟨hFint, hSint, ?_⟩
  have hFLp : MemLp R 2 (volume.restrict B) := by
    apply MemLp.of_bound ((hvm.aestronglyMeasurable.smul hmeas.2.1).add hmeas.2.2.1) (M * M + M)
    filter_upwards [ae_restrict_mem hB.measurableSet] with x hx
    have hvb : |v x| ≤ M := le_of_tendsto (hlimv x hx).abs (Eventually.of_forall (fun n => hvbseq n x hx))
    exact (norm_add_le _ _).trans (add_le_add
      (by change ‖v x • C.c x‖ ≤ M*M; rw [norm_smul]; exact mul_le_mul hvb (hbound.2.2.2 x hx).2.1 (norm_nonneg _) hM)
      (hbound.2.2.2 x hx).2.2.1)
  have hSLp : MemLp S 2 (volume.restrict B) := by
    apply MemLp.of_bound ((hmeas.2.2.2.2.1.mul hvm.aestronglyMeasurable).add hmeas.2.2.2.2.2) (M * M + M)
    filter_upwards [ae_restrict_mem hB.measurableSet] with x hx
    have hvb : |v x| ≤ M := le_of_tendsto (hlimv x hx).abs (Eventually.of_forall (fun n => hvbseq n x hx))
    exact (norm_add_le _ _).trans (add_le_add
      (by simp only [Pi.mul_apply, norm_mul]; exact mul_le_mul (hbound.2.2.2 x hx).2.2.2.2.1 hvb (norm_nonneg _) hM)
      (hbound.2.2.2 x hx).2.2.2.2.2)
  have hRint := integrable_pairing _ R _ hFLp hdφLp
  have hS0int : IntegrableOn (fun x => S x * φ x) B := hSLp.integrable_mul hφLp
  have hAint : IntegrableOn (fun x => inner ℝ (C.a x (G x)) (planarGradient φ x)) B := by
    apply (hFint.sub hRint).congr
    exact ae_of_all _ fun x => by simp [linearizedFlux, R, inner_add_left]
  have hbint : IntegrableOn (fun x => C.b x (G x) * φ x) B := by
    apply (hSint.sub hS0int).congr
    exact ae_of_all _ fun x => by dsimp [linearizedSource, S]; ring
  have hlim := (hA.add hR).sub (hb.add hS)
  simp only [RCLike.inner_apply, conj_trivial, mul_comm (φ _)] at hlim
  have heq (n : ℕ) : (∫ x in B, inner ℝ ((Cseq n).a x (Gseq n x)) (planarGradient φ x)) +
      (∫ x in B, inner ℝ (Rseq n x) (planarGradient φ x)) -
      ((∫ x in B, (Cseq n).b x (Gseq n x) * φ x) + ∫ x in B, Sseq n x * φ x) = 0 := by
    have hfieldn := linearized_fields_memLp B hB hBbdd (Cseq n) (vseq n) (Gseq n) κ M
      (hboundseq n) (hmeasseq n) (hvmseq n) (Lp.memLp _)
    have hRn : MemLp (Rseq n) 2 (volume.restrict B) := by
      apply MemLp.of_bound (((hvmseq n).aestronglyMeasurable.smul (hmeasseq n).2.1).add (hmeasseq n).2.2.1) (M*M+M)
      filter_upwards [ae_restrict_mem hB.measurableSet] with x hx
      exact (norm_add_le _ _).trans (add_le_add
        (by change ‖vseq n x • (Cseq n).c x‖ ≤ M*M; rw [norm_smul]; exact mul_le_mul (hvbseq n x hx) ((hboundseq n).2.2.2 x hx).2.1 (norm_nonneg _) hM)
        ((hboundseq n).2.2.2 x hx).2.2.1)
    have hSn : MemLp (Sseq n) 2 (volume.restrict B) := by
      apply MemLp.of_bound (((hmeasseq n).2.2.2.2.1.mul (hvmseq n).aestronglyMeasurable).add (hmeasseq n).2.2.2.2.2) (M*M+M)
      filter_upwards [ae_restrict_mem hB.measurableSet] with x hx
      exact (norm_add_le _ _).trans (add_le_add
        (by simp only [Pi.mul_apply, norm_mul]; exact mul_le_mul ((hboundseq n).2.2.2 x hx).2.2.2.2.1 (hvbseq n x hx) (norm_nonneg _) hM)
        ((hboundseq n).2.2.2 x hx).2.2.2.2.2)
    have hRi := integrable_pairing _ _ _ hRn hdφLp
    have hSi : IntegrableOn (fun x => Sseq n x * φ x) B := hSn.integrable_mul hφLp
    have hFi := integrable_pairing _ _ _ hfieldn.1 hdφLp
    have hBi : IntegrableOn (fun x => linearizedSource (Cseq n) (vseq n) (Gseq n) x * φ x) B := hfieldn.2.integrable_mul hφLp
    have hAi : IntegrableOn (fun x => inner ℝ ((Cseq n).a x (Gseq n x)) (planarGradient φ x)) B := by
      apply (hFi.sub hRi).congr
      exact ae_of_all _ fun x => by simp [linearizedFlux, Rseq, inner_add_left]
    have hbi : IntegrableOn (fun x => (Cseq n).b x (Gseq n x) * φ x) B := by
      apply (hBi.sub hSi).congr
      exact ae_of_all _ fun x => by dsimp [linearizedSource, Sseq]; ring
    rw [← integral_add hAi hRi, ← integral_add hbi hSi]
    have hsplit := integral_sub (hAi.add hRi) (hbi.add hSi)
    simp only [Pi.add_apply] at hsplit
    rw [← hsplit]
    convert (hweakseq n φ hφ hφc hφB).2.2 using 1
    congr 1
    ext x
    simp [linearizedFlux, linearizedSource, Rseq, Sseq, inner_add_left, add_mul]
    ring
  have hzero := tendsto_nhds_unique hlim (show Tendsto (fun n => _) atTop (𝓝 (0 : ℝ)) by
    simp only [heq]; exact tendsto_const_nhds)
  rw [integral_sub hFint hSint]
  have hFsplit : (∫ x in B, inner ℝ (linearizedFlux C v G x) (planarGradient φ x)) =
      (∫ x in B, inner ℝ (C.a x (G x)) (planarGradient φ x)) +
      ∫ x in B, inner ℝ (R x) (planarGradient φ x) := by
    rw [← integral_add hAint hRint]
    congr 1
    ext x
    simp [linearizedFlux, R, inner_add_left, add_assoc]
  have hSsplit : (∫ x in B, linearizedSource C v G x * φ x) =
      (∫ x in B, C.b x (G x) * φ x) + ∫ x in B, S x * φ x := by
    rw [← integral_add hbint hS0int]
    congr 1
    ext x
    simp [linearizedSource, S, add_mul]
    ring
  rw [hFsplit, hSsplit]
  exact hzero

end SeifertSurfaces.QuasilinearProviderBridge.EnergyHelpers
