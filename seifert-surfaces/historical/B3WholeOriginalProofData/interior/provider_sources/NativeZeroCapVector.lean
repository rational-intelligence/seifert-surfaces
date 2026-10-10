import NativeZeroCapScalar
import NativeH1Sum

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
open SeifertSurfaces.AppendixACoordinates L1Independent
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem native_zero_trace_cap_extension (s q : ℝ) (hq : 0 < q) (hqhalf : q ≤ 1 / 2) :
    let e := Real.arcsin (q / 2)
    let aa := s + Real.pi / 2 + e
    let bb := s + 3 * Real.pi / 2 - e
    ∀ c : ℝ → E2,
      (∀ i : Fin 2, AbsolutelyContinuousOnInterval (fun t => c t i) aa bb) →
      c aa = 0 → c bb = 0 → MemLp (deriv c) 2 (volume.restrict (Icc aa bb)) →
      ∃ (h : E2 → E2) (dh : Fin 2 → E2 → E2),
        (∀ i, H1On (planarCap (unitCircleParameter s) q) (fun z => h z i) (dh i)) ∧
        (∫ z in planarCap (unitCircleParameter s) q, euclideanJetDensity dh z) ≤
          (((2 * Real.pi) ^ 2 + 1) / 2) * ∫ t in Icc aa bb, ‖deriv c t‖ ^ 2 ∧
        (∀ psi : E2 → ℝ, ContDiff ℝ ∞ psi → ∀ i j : Fin 2,
          IntegrableOn (fun z => h z i * fderiv ℝ psi z (coordinateVector 2 j) + dh i z j * psi z)
            (planarCap (unitCircleParameter s) q) ∧
          IntegrableOn (fun t => c t i * psi (unitCircleParameter s + q • unitCircleParameter t) *
            unitCircleParameter t j) (Icc aa bb) ∧
          (∫ z in planarCap (unitCircleParameter s) q,
            h z i * fderiv ℝ psi z (coordinateVector 2 j) + dh i z j * psi z) =
            q * ∫ t in Icc aa bb, c t i * psi (unitCircleParameter s + q • unitCircleParameter t) *
              unitCircleParameter t j) := by
  classical
  dsimp only
  intro c hca hcl hcr hcd
  let e := Real.arcsin (q / 2)
  let aa := s + Real.pi / 2 + e
  let bb := s + 3 * Real.pi / 2 - e
  let K := ((2 * Real.pi) ^ 2 + 1) / 2
  have hab : aa ≤ bb := by
    have he := (cap_sector_angles q hq hqhalf).2.1
    dsimp [aa, bb, e]
    linarith
  have hae := ae_deriv_coordinate c aa bb hab hca
  have hdc (i : Fin 2) : MemLp (deriv (fun t => c t i)) 2 (volume.restrict (Icc aa bb)) := by
    apply (hcd.continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) i)).ae_eq
    filter_upwards [hae] with t ht
    exact (ht.2 i).symm
  have hscalar (i : Fin 2) := scalar_actual_zero_cap_extension s q hq hqhalf
    (fun t => c t i) (hca i)
    (by rw [hcl]; rfl) (by rw [hcr]; rfl) (hdc i)
  choose hs ds hH hE hG using hscalar
  let h : E2 → E2 := fun z => (EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i => hs i z)
  refine ⟨h, ds, hH, ?_, ?_⟩
  · have hni (i : Fin 2) : IntegrableOn (fun z => ‖ds i z‖ ^ 2)
        (planarCap (unitCircleParameter s) q) := (hH i).2.2.norm.integrable_sq
    have hsum : (∫ t in Icc aa bb, ∑ i : Fin 2, deriv (fun t => c t i) t ^ 2) =
        ∫ t in Icc aa bb, ‖deriv c t‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [hae] with t ht
      simp_rw [ht.2]
      exact (EuclideanSpace.real_norm_sq_eq _).symm
    unfold euclideanJetDensity
    rw [integral_finsetSum _ (fun i _ => hni i)]
    calc
      _ ≤ ∑ i : Fin 2, K * ∫ t in Icc aa bb, deriv (fun t => c t i) t ^ 2 :=
        Finset.sum_le_sum (fun i _ => hE i)
      _ = K * (∫ t in Icc aa bb, ∑ i : Fin 2, deriv (fun t => c t i) t ^ 2) := by
        rw [integral_finsetSum _ (fun i _ => (hdc i).integrable_sq), Finset.mul_sum]
      _ = _ := by rw [hsum]
  · intro psi hpsi i j
    exact hG i psi hpsi j

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
