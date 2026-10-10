import B1MetricVariationalInterfaces

noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.VM03Requests
open SeifertSurfaces.AppendixACoordinates

/- Proposed lower obligations only. These statements require fresh F-Reviewer approval
before proof ownership. Every body is explicitly unpaid. No statement below replaces
the original same_minimizer_regular_representative or adds an input to that theorem. -/

/-- Source pp21--22: closed forward C1, original exponent, for the supplied minimizer. -/
theorem same_minimizer_forward_regular (R : ℝ) (A : E2 → Mat2)
    (G : InverseMetricData R A) (Ω : SmoothFlatJordanDomain R) (M : E2 → Mat2)
    (agreement : ∀ x ∈ closure Ω.domain, M x = inverseMetric A x)
    (symmetric : SymmetricOn M univ) (elliptic : UniformEllipticOn M univ)
    (holder : ∀ i j, ∃ C : ℝ≥0, HolderWith C G.alpha (fun x => M x i j))
    (identity_at_infinity : ∃ L : ℝ, 0 < L ∧ ∀ x : E2, L ≤ ‖x‖ → M x = 1)
    (f : E2 → E2) (d : Fin 2 → E2 → E2)
    (minimum : SimultaneousMetricMinimum Ω M f d) :
    ∃ u : E2 → E2, u =ᵐ[volume.restrict (disc 1)] f ∧
      ContDiffOn ℝ 1 u (closedDisc 1) ∧
      (∀ i j, ∃ C : ℝ≥0,
        HolderOnWith C G.alpha (fun z => jacobianWithin u (closedDisc 1) z i j)
          (closedDisc 1)) := by sorry

/-- Source (4.16)--(4.18): no branches including boundary, degree and area imply
closed homeomorphism for THAT supplied regular representative.
The final three inputs are outputs of the preceding owed theorem, not public VM03 hypotheses. -/
theorem same_regular_minimizer_no_branches (R : ℝ) (A : E2 → Mat2)
    (G : InverseMetricData R A) (Ω : SmoothFlatJordanDomain R) (M : E2 → Mat2)
    (agreement : ∀ x ∈ closure Ω.domain, M x = inverseMetric A x)
    (symmetric : SymmetricOn M univ) (elliptic : UniformEllipticOn M univ)
    (holder : ∀ i j, ∃ C : ℝ≥0, HolderWith C G.alpha (fun x => M x i j))
    (identity_at_infinity : ∃ L : ℝ, 0 < L ∧ ∀ x : E2, L ≤ ‖x‖ → M x = 1)
    (f : E2 → E2) (d : Fin 2 → E2 → E2)
    (minimum : SimultaneousMetricMinimum Ω M f d)
    (u : E2 → E2) (same_map : u =ᵐ[volume.restrict (disc 1)] f)
    (forward_C1 : ContDiffOn ℝ 1 u (closedDisc 1))
    (forward_holder : ∀ i j, ∃ C : ℝ≥0,
      HolderOnWith C G.alpha (fun z => jacobianWithin u (closedDisc 1) z i j) (closedDisc 1)) :
    ∃ tau : PartialHomeomorph E2 E2,
      tau.source = closedDisc 1 ∧ tau.target = closure Ω.domain ∧
      tau '' disc 1 = Ω.domain ∧
      tau '' Metric.sphere (0 : E2) 1 = frontier Ω.domain ∧
      EqOn tau u (closedDisc 1) ∧
      (∀ z ∈ closedDisc 1, Matrix.det (jacobianWithin tau (closedDisc 1) z) ≠ 0) := by sorry

/-- Source p22 joint inverse estimate: retain the original exponent on the same
closed inverse. The chart and forward conclusions below are intermediate results,
not new hypotheses on the original VM03 minimizer. -/
theorem inverse_regular_of_closed_forward
    (R : ℝ) (A : E2 → Mat2) (G : InverseMetricData R A) (Ω : SmoothFlatJordanDomain R)
    (tau : PartialHomeomorph E2 E2)
    (source_eq : tau.source = closedDisc 1) (target_eq : tau.target = closure Ω.domain)
    (interior_image : tau '' disc 1 = Ω.domain)
    (boundary_image : tau '' Metric.sphere (0 : E2) 1 = frontier Ω.domain)
    (forward_C1 : ContDiffOn ℝ 1 tau (closedDisc 1))
    (forward_det : ∀ z ∈ closedDisc 1, Matrix.det (jacobianWithin tau (closedDisc 1) z) ≠ 0)
    (forward_holder : ∀ i j, ∃ C : ℝ≥0,
      HolderOnWith C G.alpha (fun z => jacobianWithin tau (closedDisc 1) z i j) (closedDisc 1)) :
    ContDiffOn ℝ 1 tau.symm (closure Ω.domain) ∧
    (∀ x ∈ closure Ω.domain,
      Matrix.det (jacobianWithin tau.symm (closure Ω.domain) x) ≠ 0) ∧
    (∀ i j, ∃ C : ℝ≥0,
      HolderOnWith C G.alpha
        (fun x => jacobianWithin tau.symm (closure Ω.domain) x i j) (closure Ω.domain)) := by sorry

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.VM03Requests
