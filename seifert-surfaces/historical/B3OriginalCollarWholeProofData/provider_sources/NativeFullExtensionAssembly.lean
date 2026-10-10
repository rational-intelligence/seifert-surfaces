import NativeCapAssembly

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
open SeifertSurfaces.AppendixACoordinates L1Independent
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/- This closed implication is an assembly lemma. Its smooth-base premise is
exactly the separately reviewed support contract, still owned by a distinct
agent. It is not the original closed extension theorem. -/
theorem full_extension_of_smooth_cap_base
    (hbase : ∃ K : ℝ, 0 < K ∧
    ∀ s q : ℝ, 0 < q → q ≤ 1 / 2 →
      let e : ℝ := Real.arcsin (q / 2)
      let aa : ℝ := s + Real.pi / 2 + e
      let bb : ℝ := s + 3 * Real.pi / 2 - e
      ∀ (B bLocal : ℝ → E2),
        Continuous B → Periodic B (2 * Real.pi) → ContDiff ℝ ∞ bLocal →
        (∀ t ∈ Icc (s - 2 * e) (s + 2 * e), B t = bLocal t) →
        ∃ (cBase : ℝ → E2) (h : E2 → E2) (dh : Fin 2 → E2 → E2),
          ContinuousOn cBase (Icc aa bb) ∧
          (∀ i : Fin 2, AbsolutelyContinuousOnInterval (fun t => cBase t i) aa bb) ∧
          MemLp (deriv cBase) 2 (volume.restrict (Icc aa bb)) ∧
          cBase aa = B (s + 2 * e) ∧ cBase bb = B (s - 2 * e) ∧
          (∀ i, H1On (planarCap (unitCircleParameter s) q) (fun z => h z i) (dh i)) ∧
          ((∫ z in planarCap (unitCircleParameter s) q, euclideanJetDensity dh z) +
            ∫ t in Icc aa bb, ‖deriv cBase t‖ ^ 2) ≤
              K * q * ∫ t in Icc (s - 2 * e) (s + 2 * e), ‖deriv bLocal t‖ ^ 2 ∧
          (∀ psi : E2 → ℝ, ContDiff ℝ ∞ psi → ∀ i j : Fin 2,
            IntegrableOn (fun z => h z i * fderiv ℝ psi z (coordinateVector 2 j) +
              dh i z j * psi z) (planarCap (unitCircleParameter s) q) ∧
            IntegrableOn (fun t => cBase t i *
              psi (unitCircleParameter s + q • unitCircleParameter t) *
              unitCircleParameter t j) (Icc aa bb) ∧
            IntegrableOn (fun t => B t i * psi (unitCircleParameter t) *
              unitCircleParameter t j) (circlePatch (unitCircleParameter s) q) ∧
            (∫ z in planarCap (unitCircleParameter s) q,
              h z i * fderiv ℝ psi z (coordinateVector 2 j) + dh i z j * psi z) =
              q * (∫ t in Icc aa bb,
                cBase t i * psi (unitCircleParameter s + q • unitCircleParameter t) *
                  unitCircleParameter t j) +
              ∫ t in circlePatch (unitCircleParameter s) q,
                B t i * psi (unitCircleParameter t) * unitCircleParameter t j)) :
    ∃ C : ℝ, 0 < C ∧
    (∀ (x : E2) (q : ℝ), 0 < q → q ≤ 1 / 2 →
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
                c t i * psi (x + q • unitCircleParameter t) * unitCircleParameter t j)) ∧
    (∀ s q : ℝ, 0 < q → q ≤ 1 / 2 →
      let e : ℝ := Real.arcsin (q / 2)
      let aa : ℝ := s + Real.pi / 2 + e
      let bb : ℝ := s + 3 * Real.pi / 2 - e
      ∀ (c B bLocal : ℝ → E2),
        ContinuousOn c (Icc aa bb) →
        (∀ i : Fin 2, AbsolutelyContinuousOnInterval (fun t => c t i) aa bb) →
        MemLp (deriv c) 2 (volume.restrict (Icc aa bb)) →
        Continuous B → Periodic B (2 * Real.pi) →
        ContDiff ℝ ∞ bLocal →
        (∀ t ∈ Icc (s - 2 * e) (s + 2 * e), B t = bLocal t) →
        c aa = B (s + 2 * e) → c bb = B (s - 2 * e) →
        ∃ (h : E2 → E2) (dh : Fin 2 → E2 → E2),
          (∀ i, H1On (planarCap (unitCircleParameter s) q) (fun z => h z i) (dh i)) ∧
          (∫ z in planarCap (unitCircleParameter s) q, euclideanJetDensity dh z) ≤
            C * ((∫ t in Icc aa bb, ‖deriv c t‖ ^ 2) +
              q * ∫ t in Icc (s - 2 * e) (s + 2 * e), ‖deriv bLocal t‖ ^ 2) ∧
          (∀ psi : E2 → ℝ, ContDiff ℝ ∞ psi → ∀ i j : Fin 2,
            IntegrableOn (fun z => h z i * fderiv ℝ psi z (coordinateVector 2 j) +
              dh i z j * psi z) (planarCap (unitCircleParameter s) q) ∧
            IntegrableOn (fun t => c t i *
              psi (unitCircleParameter s + q • unitCircleParameter t) *
              unitCircleParameter t j) (Icc aa bb) ∧
            IntegrableOn (fun t => B t i * psi (unitCircleParameter t) *
              unitCircleParameter t j) (circlePatch (unitCircleParameter s) q) ∧
            (∫ z in planarCap (unitCircleParameter s) q,
              h z i * fderiv ℝ psi z (coordinateVector 2 j) + dh i z j * psi z) =
              q * (∫ t in Icc aa bb,
                c t i * psi (unitCircleParameter s + q • unitCircleParameter t) *
                  unitCircleParameter t j) +
              ∫ t in circlePatch (unitCircleParameter s) q,
                B t i * psi (unitCircleParameter t) * unitCircleParameter t j)) := by
  classical
  obtain ⟨K, hK, hbase⟩ := hbase
  let K0 : ℝ := ((2 * Real.pi) ^ 2 + 1) / 2
  let C : ℝ := (2 + 4 * K0) * (K + 1)
  have hK0 : 0 < K0 := by dsimp [K0]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hK0C : K0 ≤ C := by
    dsimp [C]
    nlinarith [mul_pos hK0 hK]
  refine ⟨C, hC, ?_, ?_⟩
  · intro x q hq hqhalf c hcper hcc hca hcd
    obtain ⟨h, dh, hH, hE, hG⟩ := native_ball_H1_extension x q hq c hcper hcc hca hcd
    refine ⟨h, dh, hH, hE.trans ?_, hG⟩
    exact mul_le_mul_of_nonneg_right hK0C (integral_nonneg (fun _ => sq_nonneg _))
  · intro s q hq hqhalf
    dsimp only
    intro c B bLocal hcc hca hcd hBc hBp hbs hBeq hl hr
    obtain ⟨cBase, hBase, dBase, hcBase, haBase, hdBase, hlBase, hrBase, hBH, hBE, hBG⟩ :=
      hbase s q hq hqhalf B bLocal hBc hBp hbs hBeq
    exact native_cap_assemble s q K
      (∫ t in Icc (s - 2 * Real.arcsin (q / 2)) (s + 2 * Real.arcsin (q / 2)),
        ‖deriv bLocal t‖ ^ 2) hq hqhalf hK (integral_nonneg (fun _ => sq_nonneg _))
      c B cBase hBase dBase hca hcd haBase hdBase
      (hl.trans hlBase.symm) (hr.trans hrBase.symm) hBH hBE hBG

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
