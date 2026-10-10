import IsothermalPDEData
import NativeH10DirichletD3D5D6
import NormalizedMetricDirichletCorollary
import LaxMilgramRelease
noncomputable section
open Set Topology MeasureTheory
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower
open SeifertSurfaces.AppendixACoordinates

/-- A1.4(a): affine H1 Dirichlet solvability for the literal normalized metric. -/
theorem affine_dirichlet_weak_solution (R : ℝ) (A : E2 → Mat2)
    (G : InverseMetricData R A) (M : E2 → Mat2) (y : E2) (r : ℝ)
    (hr : 0 < r) (symmetric : SymmetricOn M (Metric.ball y r))
    (elliptic : UniformEllipticOn M (Metric.ball y r))
    (holder : ∀ i j, ∃ C : ℝ≥0,
      HolderOnWith C G.alpha (fun x => M x i j) (Metric.ball y r)) :
    ∀ rho : ℝ, 0 < rho → rho < r →
      ∃ a : E2 → ℝ, ∃ da : E2 → E2,
        Metric.closedBall y rho ⊆ Metric.ball y r ∧ AffineWeakSolution M y rho a da := by
  classical
  obtain ⟨hN, lam, K, hlam, hK, hbounds⟩ :=
    MetricNormalization.normalizedInverse_dirichlet_bounds R A G M y r hr
      symmetric elliptic holder
  obtain ⟨P, hP, hPall⟩ := NativeDirichlet.nativeH10_pair_poincare
  intro rho hrho hrhor
  have hsub : Metric.ball y rho ⊆ Metric.ball y r :=
    Metric.ball_subset_ball hrhor.le
  obtain ⟨B, ell, hB, hell, hint, hcoercive⟩ :=
    NativeDirichlet.nativeH10_affine_form_data y rho hrho (normalizedInverse M)
      lam K P hlam hK hP.le
      (fun i j => (hN i j).mono_measure (Measure.restrict_mono hsub le_rfl))
      (fun x hx v => hbounds x (hsub hx) v) (hPall y rho hrho)
  obtain ⟨p, hp, _⟩ := SeifertSurfaces.WeakSchauder.real_lax_milgram
    (fun pq => B pq.1 pq.2) B.isBoundedBilinearMap
    (lam / (1 + P * rho ^ 2)) (by positivity) hcoercive ell
  refine ⟨fun x => NativeDirichlet.val (Metric.ball y rho) p x + affineDatum y x,
    fun x => NativeDirichlet.grad (Metric.ball y rho) p x + coordinateVector 2 0,
    Metric.closedBall_subset_ball hrhor, ?_⟩
  apply NativeDirichlet.native_affine_solution_of_variational M y rho hrho p hint
  intro q
  rw [← hB, ← hell]
  exact hp q

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower
