import NativeZeroSectorCap
import NativeACTranslate

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
open SeifertSurfaces.AppendixACoordinates L1Independent
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem scalar_actual_zero_cap_extension (s q : ℝ) (hq : 0 < q) (hqhalf : q ≤ 1 / 2) :
    let e := Real.arcsin (q / 2)
    let aa := s + Real.pi / 2 + e
    let bb := s + 3 * Real.pi / 2 - e
    ∀ f : ℝ → ℝ,
      AbsolutelyContinuousOnInterval f aa bb → f aa = 0 → f bb = 0 →
      MemLp (deriv f) 2 (volume.restrict (Icc aa bb)) →
      ∃ (h : E2 → ℝ) (d : E2 → E2),
        H1On (planarCap (unitCircleParameter s) q) h d ∧
        (∫ z in planarCap (unitCircleParameter s) q, ‖d z‖ ^ 2) ≤
          (((2 * Real.pi) ^ 2 + 1) / 2) * ∫ t in Icc aa bb, deriv f t ^ 2 ∧
        (∀ psi : E2 → ℝ, ContDiff ℝ ∞ psi → ∀ j : Fin 2,
          IntegrableOn (fun z => h z * fderiv ℝ psi z (coordinateVector 2 j) + d z j * psi z)
            (planarCap (unitCircleParameter s) q) ∧
          IntegrableOn (fun t => f t * psi (unitCircleParameter s + q • unitCircleParameter t) *
            unitCircleParameter t j) (Icc aa bb) ∧
          (∫ z in planarCap (unitCircleParameter s) q,
            h z * fderiv ℝ psi z (coordinateVector 2 j) + d z j * psi z) =
            q * ∫ t in Icc aa bb, f t * psi (unitCircleParameter s + q • unitCircleParameter t) *
              unitCircleParameter t j) := by
  dsimp only
  intro f hf hfl hfr hfd
  let e := Real.arcsin (q / 2)
  let a := e - Real.pi / 2
  let b := Real.pi / 2 - e
  let d := s + Real.pi
  have ha : d + a = s + Real.pi / 2 + e := by dsimp [d, a]; ring
  have hb : d + b = s + 3 * Real.pi / 2 - e := by dsimp [d, b]; ring
  have hab : a < b := (cap_sector_angles q hq hqhalf).2.1
  let F : ℝ → ℝ := fun t => f (d + t)
  have hF : AbsolutelyContinuousOnInterval F a b :=
    ac_translate a b d hab.le f (by simpa only [ha, hb] using hf)
  have hFd : deriv F = fun t => deriv f (d + t) := by
    funext t
    exact deriv_comp_const_add f d t
  have hFp : MemLp (deriv F) 2 (volume.restrict (Icc a b)) := by
    rw [hFd]
    have hp : MemLp (deriv f) 2 (volume.restrict (Icc (d + a) (d + b))) := by
      simpa only [ha, hb] using hfd
    exact hp.comp_measurePreserving (translate_restrict_interval a b d)
  have hFE : (∫ t in Icc a b, deriv F t ^ 2) =
      ∫ t in Icc (s + Real.pi / 2 + e) (s + 3 * Real.pi / 2 - e), deriv f t ^ 2 := by
    rw [hFd]
    exact (integral_Icc_translate a b d (fun t => deriv f t ^ 2)).trans (by rw [ha, hb])
  obtain ⟨h, dh, hh, hE, hG⟩ := scalar_zero_cap_extension s q hq hqhalf F hF
    (by change f (d + a) = 0; rw [ha]; exact hfl)
    (by change f (d + b) = 0; rw [hb]; exact hfr) hFp
  refine ⟨h, dh, hh, ?_, ?_⟩
  · exact hE.trans_eq (congrArg (fun z : ℝ => (((2 * Real.pi) ^ 2 + 1) / 2) * z) hFE)
  · intro psi hs j
    have hgg := hG psi hs j
    have hab' : s + Real.pi / 2 + e ≤ s + 3 * Real.pi / 2 - e := by
      have hh' : d + a ≤ d + b := by linarith
      simpa only [ha, hb] using hh'
    have hfc : ContinuousOn f (Icc (s + Real.pi / 2 + e) (s + 3 * Real.pi / 2 - e)) := by
      have hh : AbsolutelyContinuousOnInterval f (s + Real.pi / 2 + e) (s + 3 * Real.pi / 2 - e) := hf
      simpa only [uIcc_of_le hab'] using hh.continuousOn
    have hbnd : IntegrableOn (fun t => f t * psi (unitCircleParameter s + q • unitCircleParameter t) *
        unitCircleParameter t j) (Icc (s + Real.pi / 2 + e) (s + 3 * Real.pi / 2 - e)) := by
      apply ContinuousOn.integrableOn_compact isCompact_Icc
      have hcp : Continuous (fun t => psi (unitCircleParameter s + q • unitCircleParameter t)) :=
        hs.continuous.comp (continuous_const.add
          ((continuous_const : Continuous (fun _ : ℝ => q)).smul circle_contDiff.continuous))
      exact hfc.mul hcp.continuousOn |>.mul
        ((EuclideanSpace.proj (𝕜 := ℝ) j).continuous.comp circle_contDiff.continuous).continuousOn
    refine ⟨hgg.1, hbnd, hgg.2.2.trans ?_⟩
    congr 1
    exact (integral_Icc_translate a b d (fun t => f t *
      psi (unitCircleParameter s + q • unitCircleParameter t) * unitCircleParameter t j)).trans
      (by rw [ha, hb])

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
