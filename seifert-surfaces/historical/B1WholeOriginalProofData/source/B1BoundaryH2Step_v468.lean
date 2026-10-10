import B1BoundaryLowerSourceTower_v468
import B1BoundaryMixedWeak_v468
import DifferentialGeometry.Analysis.Calculus.Cutoff.Compact
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open SeifertSurfaces.QuasilinearProviderBridge
set_option maxHeartbeats 800000

/-- A reusable native boundary estimate, with all test and quotient witnesses
constructed. Its zero extension also pays the next tangential trace. -/
theorem native_boundary_tangential_step_v468
    (R : ℝ) (hR : 0<R) (u : E2 → ℝ)
    (h0 : H10On (halfDisc R) u (planarGradient u))
    (B : SmoothEllipticBilinearForm 2 univ) (S : E2 → ℝ)
    (hF : MemLp (fun x => matrixAction (B.a x) (planarGradient u x)) 2
      (volume.restrict (halfDisc R)))
    (hS : MemLp S 2 (volume.restrict (halfDisc R)))
    (hweak : ∀ phi : E2 → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ halfDisc R →
      (∫ x in halfDisc R, inner ℝ (matrixAction (B.a x) (planarGradient u x))
        (planarGradient phi x)-S x*phi x)=0) :
    ∀ i : Fin 2, ∃ w : E2 → ℝ,
      MemLp w 2 (volume.restrict (Metric.ball (0:E2) (R/4))) ∧
      DeGiorgi.HasWeakPartialDeriv 0 w
        (fun y => (halfDisc R).indicator (planarGradient u) y i)
        (Metric.ball (0:E2) (R/4)) := by
  have hUm : MeasurableSet (halfDisc R) := (Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)).measurableSet
  have hcut : Metric.closedBall (0:E2) (R/4) ⊆ Metric.ball (0:E2) (R/2) := by
    intro x hx
    exact Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hx) (by linarith))
  obtain ⟨eta,hetas,hetac,hetaone,hetasub,hetarange,N,hN,hder⟩ :=
    DifferentialGeometry.Analysis.exists_bump_compact_with_fderiv_bound
      (isCompact_closedBall (0:E2) (R/4)) Metric.isOpen_ball hcut
  obtain ⟨M,hM,hbound⟩ := native_boundary_tangential_uniform_v468 R (R/2) (R/4)
    (by linarith) (by linarith) eta hetas hetac hetasub hetarange N hN hder
    (Metric.ball (0:E2) (R/4)) measurableSet_ball
    (fun x hx => hetaone.self_of_nhdsSet (Metric.ball_subset_closedBall hx)) u
    (planarGradient u) h0 _ S hF hS hweak B (fun x hx => rfl)
  have hd0 : MemLp ((halfDisc R).indicator (planarGradient u)) 2 volume :=
    (memLp_indicator_iff_restrict hUm.nullMeasurableSet).mpr h0.1.2.2
  have hVc : IsCompact (closure (Metric.ball (0:E2) (R/4))) :=
    (isCompact_closedBall (0:E2) (R/4)).of_isClosed_subset isClosed_closure
      (closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall)
  exact native_tangential_weakDerivative_of_uniform_v468 _ hd0 _ Metric.isOpen_ball hVc
    (R/4) (by linarith) M hM hbound

end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.native_boundary_tangential_step_v468
