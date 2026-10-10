import InitialPaidComparison_v460
import InitialActualCapSeam_v460
import InitialOriginalBoundaryComparisonData_v460

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
set_option maxHeartbeats 800000
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates L1Independent

local macro "paid_paste" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialPaidComparison_v460 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.L1Independent.paid_boundary_cap_paste_v460)⟩

local macro "paid_local_energy" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialPaidComparison_v460 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.L1Independent.paid_same_minimizer_local_energy_v460)⟩

private theorem original_minimizer_actual_cap_comparison_v460
    (R : ℝ) (A : E2 → Mat2) (G : InverseMetricData R A)
    (Ω : SmoothFlatJordanDomain R) (M : E2 → Mat2)
    (agreement : ∀ x∈closure Ω.domain,M x=inverseMetric A x)
    (symmetric : SymmetricOn M univ) (elliptic : UniformEllipticOn M univ)
    (holder : ∀ i j,∃ C:ℝ≥0,HolderWith C G.alpha (fun x=>M x i j))
    (identity_at_infinity : ∃ L:ℝ,0 < L ∧ ∀ x:E2,L ≤ ‖x‖ → M x=1)
    (f : E2 → E2) (d : Fin 2 → E2 → E2)
    (minimum : SimultaneousMetricMinimum Ω M f d)
    (theta theta' : ℝ → ℝ) (sigma : ℝ)
    (lift : WeakMonotoneBoundaryLift Ω theta sigma)
    (trace : HasGreenBoundaryTrace f d (liftedBoundaryValue Ω theta))
    (new_lift : WeakMonotoneBoundaryLift Ω theta' sigma)
    (x:E2) (hx:x∈closedDisc 1) (q:ℝ) (hq:0 < q)
    (h:E2→E2) (dh:Fin 2→E2→E2)
    (local_H1 : ∀ i,H1On (planarCap x q) (fun z=>h z i) (dh i))
    (unchanged : ∀ t∈Icc 0 (2*Real.pi),unitCircleParameter t∉Metric.ball x q →
      liftedBoundaryValue Ω theta' t=liftedBoundaryValue Ω theta t)
    (seam : RelativeCapGreen x q f h d dh
      (liftedBoundaryValue Ω theta) (liftedBoundaryValue Ω theta'))
    (ell Lambda : ℝ) (hell:0 < ell) (hLambda:0 < Lambda)
    (bounds : ∀ y:E2,∀ p:E2,
      ell*‖p‖^2 ≤ inner ℝ p (matrixAction (M y) p) ∧
      inner ℝ p (matrixAction (M y) p) ≤ Lambda*‖p‖^2) :
    (∀ i,H1On (disc 1) (fun z=>pastedMap (planarCap x q) f h z i)
      (pastedJets (planarCap x q) d dh i)) ∧
    HasGreenBoundaryTrace (pastedMap (planarCap x q) f h)
      (pastedJets (planarCap x q) d dh) (liftedBoundaryValue Ω theta') ∧
    MetricAdmissible Ω (pastedMap (planarCap x q) f h) (pastedJets (planarCap x q) d dh) ∧
    (∫ z in planarCap x q,euclideanJetDensity d z) ≤
      (Lambda/ell)*∫ z in planarCap x q,euclideanJetDensity dh z := by
  obtain ⟨hpH,hpG,hpAdm⟩ := paid_paste Ω f h d dh minimum.admissible.1
    theta theta' sigma lift trace new_lift x hx q hq local_H1 unchanged seam
  have henergy := paid_local_energy R A G Ω M agreement symmetric elliptic holder
    identity_at_infinity f d minimum (planarCap x q)
    (measurableSet_ball.inter measurableSet_ball) inter_subset_left h dh hpAdm
    ell Lambda hell hLambda bounds
  exact ⟨hpH,hpG,hpAdm,henergy.2.2.2.2.2.2⟩

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
