import ClassicalBootstrap

noncomputable section
open Set MeasureTheory Function
open scoped Topology BigOperators ContDiff
namespace SeifertSurfaces.AppendixACoordinates

theorem smooth_of_C1_weak_uniformlyElliptic
    (Ω : Set E2) (hΩ : IsOpen Ω) (J : Set Jet) (hJ : IsOpen J)
    (Q : SmoothQuasilinearOperator J) (helliptic : UniformlyEllipticOn J Q.flux)
    (u : E2 → ℝ) (hC1 : ContDiffOn ℝ 1 u Ω)
    (hjets : ∀ x ∈ Ω, (x, u x, planarGradient u x) ∈ J)
    (hweak : IsWeakDivergenceSolutionOn Ω Q.flux Q.lowerOrder u) :
    ContDiffOn ℝ ∞ u Ω := by
  apply contDiffOn_infty.mpr
  intro n
  apply contDiffOn_of_locally_contDiffOn
  intro x hx
  obtain ⟨r, α, K, hr, _, _, _, hu⟩ :=
    SeifertSurfaces.QuasilinearBootstrap.R6_local_finite_orders
      Ω hΩ J hJ Q helliptic u hC1 hjets hweak x hx (max n 2) (le_max_right _ _)
  have hn : ContDiffOn ℝ (n : ℕ∞ω) u (Metric.ball x (2 * r)) :=
    hu.1.of_le (by exact_mod_cast (le_max_left n 2))
  exact ⟨Metric.ball x (2 * r), Metric.isOpen_ball, Metric.mem_ball_self (by positivity),
    hn.mono Set.inter_subset_right⟩

end SeifertSurfaces.AppendixACoordinates
