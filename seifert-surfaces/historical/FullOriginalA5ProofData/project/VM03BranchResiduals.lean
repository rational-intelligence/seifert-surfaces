import VM03OwedRequests
import VM03WeakJets
import Mathlib.Topology.PartialHomeomorph.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Count
noncomputable section
open Set Topology Function MeasureTheory
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.VM03BranchResiduals
open SeifertSurfaces.AppendixACoordinates
set_option maxHeartbeats 0

theorem native_weighted_count_budget (R : ℝ) (A : E2 → Mat2)
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
    AEMeasurable (fun x => (fun x : E2 => ENNReal.ofReal (Real.sqrt (Matrix.det (M x)))) x * (fun x : E2 => Measure.count {z | z ∈ disc 1 ∧ u z = x}) x) volume ∧
      (∀ᵐ x ∂volume, (Ω.domain.indicator (fun _ => (1 : ℝ≥0∞))) x ≤ (fun x : E2 => Measure.count {z | z ∈ disc 1 ∧ u z = x}) x) ∧
      (∫⁻ x, (fun x : E2 => ENNReal.ofReal (Real.sqrt (Matrix.det (M x)))) x * (fun x : E2 => Measure.count {z | z ∈ disc 1 ∧ u z = x}) x) ≤ ∫⁻ x, (fun x : E2 => ENNReal.ofReal (Real.sqrt (Matrix.det (M x)))) x * (Ω.domain.indicator (fun _ => (1 : ℝ≥0∞))) x := by sorry

theorem boundary_branch_open_excess (R : ℝ) (A : E2 → Mat2)
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
    ∀ z ∈ closedDisc 1,
      Matrix.det (jacobianWithin u (closedDisc 1) z) = 0 →
      ∃ V : Set E2, IsOpen V ∧ V.Nonempty ∧ ∀ x ∈ V, (Ω.domain.indicator (fun _ => (1 : ℝ≥0∞))) x < (fun x : E2 => Measure.count {z | z ∈ disc 1 ∧ u z = x}) x := by sorry

theorem closed_image_topology_after_nonbranching (R : ℝ) (A : E2 → Mat2)
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
    (∀ z ∈ closedDisc 1, Matrix.det (jacobianWithin u (closedDisc 1) z) ≠ 0) →
      ((fun x : E2 => Measure.count {z | z ∈ disc 1 ∧ u z = x}) =ᵐ[volume] (Ω.domain.indicator (fun _ => (1 : ℝ≥0∞)))) →
      InjOn u (closedDisc 1) ∧ u '' disc 1 = Ω.domain := by sorry

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.VM03BranchResiduals
