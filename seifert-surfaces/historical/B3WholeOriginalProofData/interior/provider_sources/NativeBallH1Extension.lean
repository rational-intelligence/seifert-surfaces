import NativeScalarGreen
import NativeACIntervalEnergy

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
open SeifertSurfaces.AppendixACoordinates L1Independent
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

 theorem native_ball_H1_extension
    (x : E2) (q : ℝ) (hq : 0 < q) (c : ℝ → E2)
    (hcper : Periodic c (2 * Real.pi)) (hcc : Continuous c)
    (hca : ∀ i : Fin 2, AbsolutelyContinuousOnInterval (fun t => c t i) (-Real.pi) Real.pi)
    (hcd : MemLp (deriv c) 2 (volume.restrict (Icc (-Real.pi) Real.pi))) :
    ∃ (h : E2 → E2) (dh : Fin 2 → E2 → E2),
      (∀ i, H1On (Metric.ball x q) (fun z => h z i) (dh i)) ∧
      (∫ z in Metric.ball x q, euclideanJetDensity dh z) ≤
        (((2 * Real.pi) ^ 2 + 1) / 2) * ∫ t in Icc (-Real.pi) Real.pi, ‖deriv c t‖ ^ 2 ∧
      (∀ psi : E2 → ℝ, ContDiff ℝ ∞ psi → ∀ i j : Fin 2,
        IntegrableOn (fun z => h z i * fderiv ℝ psi z (coordinateVector 2 j) +
          dh i z j * psi z) (Metric.ball x q) ∧
        IntegrableOn (fun t => c t i * psi (x + q • unitCircleParameter t) *
          unitCircleParameter t j) (Icc (-Real.pi) Real.pi) ∧
        (∫ z in Metric.ball x q,
          h z i * fderiv ℝ psi z (coordinateVector 2 j) + dh i z j * psi z) =
          q * ∫ t in Icc (-Real.pi) Real.pi,
            c t i * psi (x + q • unitCircleParameter t) * unitCircleParameter t j) := by
  classical
  let K : ℝ := ((2 * Real.pi) ^ 2 + 1) / 2
  let k (i : Fin 2) := c (-Real.pi) i
  let g (i : Fin 2) (t : ℝ) := c t i - k i
  let h (z : E2) : E2 := (EuclideanSpace.equiv (Fin 2) ℝ).symm
    (fun i => scalarCone x q (k i) (g i) z)
  let dh (i : Fin 2) := scalarConeGrad x q (g i)
  have hgc (i : Fin 2) : Continuous (g i) :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp hcc).sub continuous_const
  have hgp (i : Fin 2) : Periodic (g i) (2 * Real.pi) := by
    intro t
    dsimp [g]
    rw [hcper t]
  have hga (i : Fin 2) : AbsolutelyContinuousOnInterval (g i) (-Real.pi) Real.pi :=
    (hca i).sub (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => k i)).contDiffOn.absolutelyContinuousOnInterval
  have hae := ae_deriv_coordinate c (-Real.pi) Real.pi (by linarith [Real.pi_pos]) hca
  have heq (i : Fin 2) : deriv (g i) =ᵐ[volume.restrict (Icc (-Real.pi) Real.pi)]
      (fun t => deriv c t i) := by
    filter_upwards [hae] with t ht
    simpa only [g, deriv_sub_const] using ht.2 i
  have hgd (i : Fin 2) : MemLp (deriv (g i)) 2 (volume.restrict (Icc (-Real.pi) Real.pi)) :=
    (hcd.continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) i)).ae_eq (heq i).symm
  have h1 (i : Fin 2) : H1On (Metric.ball x q) (fun z => h z i) (dh i) :=
    scalarCone_H1 x q (k i) hq (g i) (hgp i) (hgc i) (hga i) (hgd i)
  refine ⟨h, dh, h1, ?_, ?_⟩
  · have henergy (i : Fin 2) :
        (∫ z in Metric.ball x q, ‖dh i z‖ ^ 2) ≤
          K * ∫ t in Icc (-Real.pi) Real.pi, deriv (g i) t ^ 2 := by
      have he := (scalarConeGrad_energy x q hq (g i) (hgp i) (hgc i) (hgd i)).2
      have hpi := ac_interval_poincare (-Real.pi) Real.pi (by linarith [Real.pi_pos])
        (g i) (hga i) (hgd i)
      have hz : g i (-Real.pi) = 0 := sub_self _
      simp only [hz, sub_zero] at hpi
      have hgi : IntegrableOn (fun t => g i t ^ 2) (Icc (-Real.pi) Real.pi) :=
        ((hgc i).pow 2).integrableOn_Icc
      rw [integral_add hgi (hgd i).integrable_sq] at he
      change _ ≤ K * _
      change (∫ z in Metric.ball x q, ‖scalarConeGrad x q (g i) z‖ ^ 2) ≤ _
      rw [he]
      dsimp [K]
      nlinarith [hpi]
    have hnormi (i : Fin 2) : IntegrableOn (fun z => ‖dh i z‖ ^ 2) (Metric.ball x q) :=
      (h1 i).2.2.norm.integrable_sq
    have hde : (∫ t in Icc (-Real.pi) Real.pi, ∑ i : Fin 2, deriv (g i) t ^ 2) =
        ∫ t in Icc (-Real.pi) Real.pi, ‖deriv c t‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [ae_all_iff.mpr heq] with t ht
      simp_rw [ht]
      exact (EuclideanSpace.real_norm_sq_eq _).symm
    unfold euclideanJetDensity
    rw [integral_finsetSum _ (fun i _ => hnormi i)]
    calc
      _ ≤ ∑ i : Fin 2, K * ∫ t in Icc (-Real.pi) Real.pi, deriv (g i) t ^ 2 :=
        Finset.sum_le_sum (fun i _ => henergy i)
      _ = K * (∫ t in Icc (-Real.pi) Real.pi, ∑ i : Fin 2, deriv (g i) t ^ 2) := by
        rw [integral_finsetSum _ (fun i _ => (hgd i).integrable_sq), Finset.mul_sum]
      _ = _ := by rw [hde]
  · intro psi hs i j
    have hh := scalarCone_green x q (k i) hq (g i) (hgp i) (hgc i) (hga i) psi hs j
    have hgval (t : ℝ) : k i + g i t = c t i := by dsimp [g]; ring
    have hval (z : E2) : h z i = scalarCone x q (k i) (g i) z := rfl
    simpa only [hval, dh, hgval] using hh

 theorem uniform_ball_H1_extension :
    ∃ C : ℝ, 0 < C ∧
    ∀ (x : E2) (q : ℝ), 0 < q → q ≤ 1 / 2 →
      ∀ c : ℝ → E2,
        Periodic c (2 * Real.pi) → Continuous c →
        (∀ i : Fin 2, AbsolutelyContinuousOnInterval (fun t => c t i) (-Real.pi) Real.pi) →
        MemLp (deriv c) 2 (volume.restrict (Icc (-Real.pi) Real.pi)) →
        ∃ (h : E2 → E2) (dh : Fin 2 → E2 → E2),
          (∀ i, H1On (Metric.ball x q) (fun z => h z i) (dh i)) ∧
          (∫ z in Metric.ball x q, euclideanJetDensity dh z) ≤
            C * ∫ t in Icc (-Real.pi) Real.pi, ‖deriv c t‖ ^ 2 ∧
          (∀ psi : E2 → ℝ, ContDiff ℝ ∞ psi → ∀ i j : Fin 2,
            IntegrableOn (fun z => h z i * fderiv ℝ psi z (coordinateVector 2 j) +
              dh i z j * psi z) (Metric.ball x q) ∧
            IntegrableOn (fun t => c t i * psi (x + q • unitCircleParameter t) *
              unitCircleParameter t j) (Icc (-Real.pi) Real.pi) ∧
            (∫ z in Metric.ball x q,
              h z i * fderiv ℝ psi z (coordinateVector 2 j) + dh i z j * psi z) =
              q * ∫ t in Icc (-Real.pi) Real.pi,
                c t i * psi (x + q • unitCircleParameter t) * unitCircleParameter t j) := by
  refine ⟨((2 * Real.pi) ^ 2 + 1) / 2, by positivity, ?_⟩
  intro x q hq _ c hcper hcc hca hcd
  exact native_ball_H1_extension x q hq c hcper hcc hca hcd

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
