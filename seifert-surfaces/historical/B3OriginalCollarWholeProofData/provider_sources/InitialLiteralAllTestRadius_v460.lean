import InitialLiteralArcTraceAE_v460
import InitialLocalAllTestGreen_v460
import InitialPositiveTraceUniqueness_v457

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
set_option maxHeartbeats 1000000
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates L1Independent

local macro "paid_all_green" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialLocalAllTestGreen_v460 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.original_local_cap_green_all_tests_ae_v460)⟩

local macro "paid_literal_extra" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialLiteralArcTraceAE_v460 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.original_literal_cap_arc_trace_with_ae_v460)⟩

private theorem original_literal_cap_arc_trace_all_tests_v460
    {R : ℝ} {Ω : SmoothFlatJordanDomain R} {M : E2 → Mat2}
    {f : E2 → E2} {d : Fin 2 → E2 → E2}
    (minimum : SimultaneousMetricMinimum Ω M f d)
    (theta : ℝ → ℝ) (sigma : ℝ)
    (lift : WeakMonotoneBoundaryLift Ω theta sigma)
    (trace : HasGreenBoundaryTrace f d (liftedBoundaryValue Ω theta))
    (s r : ℝ) (hr : 0 < r) (hrhalf : r ≤ 1 / 2)
 :
    let f0 : E2 → E2 := (disc 1).indicator f
    let d0 : Fin 2 → E2 → E2 := fun i => (disc 1).indicator (d i)
    let angles : Set ℝ := Ioo (-Real.pi) Real.pi
    let J : E2 → E2 := fun v =>
      (EuclideanSpace.equiv (Fin 2) ℝ).symm ![-v 1, v 0]
    let shell : ℝ :=
      (∫ z in planarCap (unitCircleParameter s) r, euclideanJetDensity d z) -
        (∫ z in planarCap (unitCircleParameter s) (r / 2), euclideanJetDensity d z)
    ∃ q ∈ Ioo (r / 2) r,
      (∀ psi : E2 → ℝ,ContDiff ℝ ∞ psi → ∀ i j : Fin 2,
        (∫ x in planarCap (unitCircleParameter s) q,
          f x i*fderiv ℝ psi x (coordinateVector 2 j)+d i x j*psi x)=
          (q*∫ t in angles,
            (disc 1).indicator (fun x=>f x i*psi x)
              (unitCircleParameter s+q•unitCircleParameter t)*unitCircleParameter t j)+
          ∫ t in circlePatch (unitCircleParameter s) q,
            liftedBoundaryValue Ω theta t i*psi (unitCircleParameter t)*unitCircleParameter t j) ∧
      MemLp (fun t => f0 (unitCircleParameter s + q • unitCircleParameter t)) 2
        (volume.restrict angles) ∧
      (∀ i, MemLp (fun t => d0 i (unitCircleParameter s + q • unitCircleParameter t)) 2
        (volume.restrict angles)) ∧
      let e : ℝ := Real.arcsin (q / 2)
      let aa : ℝ := s + Real.pi / 2 + e
      let bb : ℝ := s + 3 * Real.pi / 2 - e
      let a : ℝ → E2 := fun t =>
        (EuclideanSpace.equiv (Fin 2) ℝ).symm
          (fun i => q * inner ℝ (d0 i (unitCircleParameter s + q • unitCircleParameter t))
            (J (unitCircleParameter t)))
      let c : ℝ → E2 := fun t =>
        liftedBoundaryValue Ω theta (s + 2 * e) + ∫ x in aa..t, a x
      aa < bb ∧ bb - aa ≤ Real.pi ∧
      ContinuousOn c (Icc aa bb) ∧
      c aa = liftedBoundaryValue Ω theta (s + 2 * e) ∧
      c bb = liftedBoundaryValue Ω theta (s - 2 * e) ∧
      (∀ i : Fin 2, AbsolutelyContinuousOnInterval (fun t => c t i) aa bb) ∧
      (∀ᵐ t ∂volume.restrict (Icc aa bb), HasDerivAt c (a t) t) ∧
      MemLp (deriv c) 2 (volume.restrict (Icc aa bb)) ∧
      (∫ t in Icc aa bb, ‖deriv c t‖ ^ 2) ≤ 2 * shell ∧
      (∀ psi : ℝ → ℝ, ContDiff ℝ ∞ psi → ∀ i : Fin 2,
        (∫ t in Icc aa bb, a t i * psi t + c t i * deriv psi t) =
          liftedBoundaryValue Ω theta (s - 2 * e) i * psi bb -
            liftedBoundaryValue Ω theta (s + 2 * e) i * psi aa) ∧
      let phi : ℕ → Fin 2 → E2 → ℝ := fun n k z =>
        ![((((z 0 - unitCircleParameter s 0 : ℝ) : ℂ) +
            ((z 1 - unitCircleParameter s 1 : ℝ) : ℂ) * Complex.I) ^ n).re,
          ((((z 0 - unitCircleParameter s 0 : ℝ) : ℂ) +
            ((z 1 - unitCircleParameter s 1 : ℝ) : ℂ) * Complex.I) ^ n).im] k
      (∀ (n : ℕ) (k i : Fin 2),
        (∫ t in angles,
          a t i * phi n k (unitCircleParameter s + q • unitCircleParameter t) +
          f0 (unitCircleParameter s + q • unitCircleParameter t) i *
            deriv (fun u => phi n k (unitCircleParameter s + q • unitCircleParameter u)) t) =
          liftedBoundaryValue Ω theta (s - 2 * e) i *
            phi n k (unitCircleParameter s + q • unitCircleParameter bb) -
          liftedBoundaryValue Ω theta (s + 2 * e) i *
            phi n k (unitCircleParameter s + q • unitCircleParameter aa)) ∧
      (fun t => f0 (unitCircleParameter s + q • unitCircleParameter t))
        =ᵐ[volume.restrict (Icc aa bb)] c := by
  classical
  let Extra : ℝ → Prop := fun q=>∀ psi : E2 → ℝ,ContDiff ℝ ∞ psi → ∀ i j : Fin 2,
    (∫ x in planarCap (unitCircleParameter s) q,
      f x i*fderiv ℝ psi x (coordinateVector 2 j)+d i x j*psi x)=
      (q*∫ t in Ioo (-Real.pi) Real.pi,
        (disc 1).indicator (fun x=>f x i*psi x)
          (unitCircleParameter s+q•unitCircleParameter t)*unitCircleParameter t j)+
      ∫ t in circlePatch (unitCircleParameter s) q,
        liftedBoundaryValue Ω theta t i*psi (unitCircleParameter t)*unitCircleParameter t j
  have hExtra : ∀ᵐ q ∂volume.restrict (Ioo (r/2) r),Extra q :=
    paid_all_green f d (liftedBoundaryValue Ω theta) minimum.admissible.1 trace
      (Ω.boundary.smooth.continuous.comp lift.2.1) (unitCircleParameter s) (r/2) r
      (by positivity) (by linarith) (by linarith)
  exact paid_literal_extra minimum theta sigma lift trace s r hr hrhalf Extra hExtra

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
