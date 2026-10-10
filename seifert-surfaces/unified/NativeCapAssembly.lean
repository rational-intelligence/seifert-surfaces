import NativeACResidualEnergy

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
open SeifertSurfaces.AppendixACoordinates L1Independent
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

theorem native_cap_assemble (s q K E : ℝ) (hq : 0 < q) (hqhalf : q ≤ 1 / 2)
    (hK : 0 < K) (hE : 0 ≤ E) :
    let e := Real.arcsin (q / 2)
    let aa := s + Real.pi / 2 + e
    let bb := s + 3 * Real.pi / 2 - e
    ∀ (c B cBase : ℝ → E2) (hBase : E2 → E2) (dBase : Fin 2 → E2 → E2),
      (∀ i : Fin 2, AbsolutelyContinuousOnInterval (fun t => c t i) aa bb) →
      MemLp (deriv c) 2 (volume.restrict (Icc aa bb)) →
      (∀ i : Fin 2, AbsolutelyContinuousOnInterval (fun t => cBase t i) aa bb) →
      MemLp (deriv cBase) 2 (volume.restrict (Icc aa bb)) →
      c aa = cBase aa → c bb = cBase bb →
      (∀ i, H1On (planarCap (unitCircleParameter s) q) (fun z => hBase z i) (dBase i)) →
      ((∫ z in planarCap (unitCircleParameter s) q, euclideanJetDensity dBase z) +
        ∫ t in Icc aa bb, ‖deriv cBase t‖ ^ 2) ≤ K * q * E →
      (∀ psi : E2 → ℝ, ContDiff ℝ ∞ psi → ∀ i j : Fin 2,
        IntegrableOn (fun z => hBase z i * fderiv ℝ psi z (coordinateVector 2 j) + dBase i z j * psi z)
          (planarCap (unitCircleParameter s) q) ∧
        IntegrableOn (fun t => cBase t i * psi (unitCircleParameter s + q • unitCircleParameter t) *
          unitCircleParameter t j) (Icc aa bb) ∧
        IntegrableOn (fun t => B t i * psi (unitCircleParameter t) * unitCircleParameter t j)
          (circlePatch (unitCircleParameter s) q) ∧
        (∫ z in planarCap (unitCircleParameter s) q,
          hBase z i * fderiv ℝ psi z (coordinateVector 2 j) + dBase i z j * psi z) =
          q * (∫ t in Icc aa bb, cBase t i * psi (unitCircleParameter s + q • unitCircleParameter t) *
            unitCircleParameter t j) +
          ∫ t in circlePatch (unitCircleParameter s) q,
            B t i * psi (unitCircleParameter t) * unitCircleParameter t j) →
      ∃ (h : E2 → E2) (dh : Fin 2 → E2 → E2),
        (∀ i, H1On (planarCap (unitCircleParameter s) q) (fun z => h z i) (dh i)) ∧
        (∫ z in planarCap (unitCircleParameter s) q, euclideanJetDensity dh z) ≤
          (2 + 4 * (((2 * Real.pi) ^ 2 + 1) / 2)) * (K + 1) *
            ((∫ t in Icc aa bb, ‖deriv c t‖ ^ 2) + q * E) ∧
        (∀ psi : E2 → ℝ, ContDiff ℝ ∞ psi → ∀ i j : Fin 2,
          IntegrableOn (fun z => h z i * fderiv ℝ psi z (coordinateVector 2 j) + dh i z j * psi z)
            (planarCap (unitCircleParameter s) q) ∧
          IntegrableOn (fun t => c t i * psi (unitCircleParameter s + q • unitCircleParameter t) *
            unitCircleParameter t j) (Icc aa bb) ∧
          IntegrableOn (fun t => B t i * psi (unitCircleParameter t) * unitCircleParameter t j)
            (circlePatch (unitCircleParameter s) q) ∧
          (∫ z in planarCap (unitCircleParameter s) q,
            h z i * fderiv ℝ psi z (coordinateVector 2 j) + dh i z j * psi z) =
            q * (∫ t in Icc aa bb, c t i * psi (unitCircleParameter s + q • unitCircleParameter t) *
              unitCircleParameter t j) +
            ∫ t in circlePatch (unitCircleParameter s) q,
              B t i * psi (unitCircleParameter t) * unitCircleParameter t j) := by
  classical
  dsimp only
  intro c B cBase hBase dBase hca hcd hba hbd hleft hright hBH hBE hBG
  let e := Real.arcsin (q / 2)
  let aa := s + Real.pi / 2 + e
  let bb := s + 3 * Real.pi / 2 - e
  let U := planarCap (unitCircleParameter s) q
  let K0 : ℝ := ((2 * Real.pi) ^ 2 + 1) / 2
  have hK0 : 0 < K0 := by dsimp [K0]; positivity
  have hab : aa ≤ bb := by
    have ha := (cap_sector_angles q hq hqhalf).2.1
    dsimp [aa, bb, e]
    linarith
  let w : ℝ → E2 := fun t => c t - cBase t
  obtain ⟨hwa, hwd, hWE⟩ := ac_vector_residual_energy aa bb hab c cBase hca hba hcd hbd
  obtain ⟨hR, dR, hRH, hRE, hRG⟩ := native_zero_trace_cap_extension s q hq hqhalf w hwa
    (by dsimp [w]; rw [hleft, sub_self]) (by dsimp [w]; rw [hright, sub_self]) hwd
  let h : E2 → E2 := fun z => hBase z + hR z
  let dh : Fin 2 → E2 → E2 := fun i z => dBase i z + dR i z
  have hH (i : Fin 2) : H1On U (fun z => h z i) (dh i) :=
    native_H1_sum U (fun z => hBase z i) (fun z => hR z i) (dBase i) (dR i) (hBH i) (hRH i)
  refine ⟨h, dh, hH, ?_, ?_⟩
  · let A := ∫ z in U, euclideanJetDensity dBase z
    let D := ∫ t in Icc aa bb, ‖deriv cBase t‖ ^ 2
    let F := ∫ t in Icc aa bb, ‖deriv c t‖ ^ 2
    have hA : 0 ≤ A := integral_nonneg (fun z => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    have hD : 0 ≤ D := integral_nonneg (fun _ => sq_nonneg _)
    have hF : 0 ≤ F := integral_nonneg (fun _ => sq_nonneg _)
    have hAD : A + D ≤ K * q * E := hBE
    have hRR : (∫ z in U, euclideanJetDensity dR z) ≤ K0 * (2 * (F + D)) :=
      hRE.trans (mul_le_mul_of_nonneg_left hWE hK0.le)
    have hsum := native_rows_sum_energy U dBase dR (fun i => (hBH i).2.2) (fun i => (hRH i).2.2)
    change (∫ z in U, euclideanJetDensity dh z) ≤ (2 + 4 * K0) * (K + 1) * (F + q * E)
    calc
      _ ≤ 2 * (A + ∫ z in U, euclideanJetDensity dR z) := hsum
      _ ≤ 2 * (A + K0 * (2 * (F + D))) := by linarith
      _ ≤ 4 * K0 * F + (2 + 4 * K0) * (A + D) := by
        nlinarith [mul_nonneg hK0.le hA]
      _ ≤ 4 * K0 * F + (2 + 4 * K0) * (K * q * E) := by
        gcongr
      _ ≤ _ := by
        have hco : 4 * K0 ≤ (2 + 4 * K0) * (K + 1) := by
          nlinarith [mul_pos hK0 hK]
        have hco' : (2 + 4 * K0) * K ≤ (2 + 4 * K0) * (K + 1) := by nlinarith
        have hf := mul_le_mul_of_nonneg_right hco hF
        have he := mul_le_mul_of_nonneg_right hco' (mul_nonneg hq.le hE)
        nlinarith
  · intro psi hs i j
    obtain ⟨hbi, hbt, hbB, hbG⟩ := hBG psi hs i j
    obtain ⟨hri, hrt, hrG⟩ := hRG psi hs i j
    let BB (z : E2) := hBase z i * fderiv ℝ psi z (coordinateVector 2 j) + dBase i z j * psi z
    let RR (z : E2) := hR z i * fderiv ℝ psi z (coordinateVector 2 j) + dR i z j * psi z
    let BT (t : ℝ) := cBase t i * psi (unitCircleParameter s + q • unitCircleParameter t) * unitCircleParameter t j
    let RT (t : ℝ) := w t i * psi (unitCircleParameter s + q • unitCircleParameter t) * unitCircleParameter t j
    have hbulk : (fun z => h z i * fderiv ℝ psi z (coordinateVector 2 j) + dh i z j * psi z) =
        (fun z => BB z + RR z) := by
      funext z
      simp only [h, dh, PiLp.add_apply, BB, RR]
      ring
    have hbound : (fun t => c t i * psi (unitCircleParameter s + q • unitCircleParameter t) * unitCircleParameter t j) =
        (fun t => BT t + RT t) := by
      funext t
      simp only [BT, RT, w, PiLp.sub_apply]
      ring
    rw [hbulk, hbound]
    refine ⟨hbi.add hri, hbt.add hrt, hbB, ?_⟩
    rw [integral_add hbi hri, integral_add hbt hrt]
    change (∫ z in U, BB z) + (∫ z in U, RR z) = _
    dsimp only [BB, RR, BT, RT]
    rw [hbG, hrG]
    ring

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
