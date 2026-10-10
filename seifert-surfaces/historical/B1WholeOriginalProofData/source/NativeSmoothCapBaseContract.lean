import NativeBallH1Extension
import CapBaseH1

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
open SeifertSurfaces.AppendixACoordinates L1Independent

/- Optional independent support contract for parent routing. This file is an
unpaid scaffold, not a provider. The intended extension is bLocal composed with
s + arcsin of the tangent coordinate relative to unitCircleParameter s.
The parent target and rough zero-trace sector correction remain with this owner. -/
theorem smooth_native_cap_base_extension :
    ∃ K : ℝ, 0 < K ∧
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
                B t i * psi (unitCircleParameter t) * unitCircleParameter t j) := by
  refine ⟨4, by norm_num, ?_⟩
  intro s q hq hq1
  dsimp only
  intro B bLocal hB hBp hb hagree
  have hc := cap_artificial_trace_native_properties s q hq hq1 B bLocal hb hagree
  dsimp only at hc
  refine ⟨fun t => bLocal (capArtificialAngle s q t), capBaseMap s bLocal,
    capBaseJet s bLocal, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1,
    (fun i => cap_base_H1 s q hq hq1 B bLocal hB hBp hb hagree i),
    cap_native_energy_total s q hq hq1 bLocal hb, ?_⟩
  intro psi hpsi i j
  exact cap_native_Green s q hq hq1 B bLocal hB hBp hb hagree psi hpsi i j

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
