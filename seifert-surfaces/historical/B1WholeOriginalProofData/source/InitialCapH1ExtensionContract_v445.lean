import InitialActualArcPath_v411
import NativeFullExtensionAssembly
import NativeSmoothCapBaseContract

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal

namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates L1Independent

/- REVIEW REQUEST ONLY. One independent extension package. It neither asserts
an original minimizer theorem nor imports a replacement/seam hypothesis into
that theorem. The caller will supply these one-dimensional data from the
checked original radius/primitive/lift producers. The seam to the original
f/d, admissibility, minimum comparison, and decay remain parent-owned. -/
private theorem uniform_ball_and_boundary_cap_H1_extension_v445 :
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
  exact NativeBallCapExtension.full_extension_of_smooth_cap_base
    NativeBallCapExtension.smooth_native_cap_base_extension

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
