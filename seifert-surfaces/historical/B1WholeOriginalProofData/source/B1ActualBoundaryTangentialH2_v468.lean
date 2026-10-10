import B1BoundaryTangentialWeakDerivative_v468
import B1ActualBoundaryTangentialEnergy_v468
import DifferentialGeometry.Analysis.Calculus.Cutoff.Compact
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open ChartMetricProvider.Variational.DirectWeak.BoundaryContinuation
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
set_option maxHeartbeats 800000

/-- The original positive solution has actual native L2 tangential derivatives
of every component of its zero-extended gradient on a ball crossing the flat edge.
All coefficients, cutoffs, bounds, and derivative witnesses are constructed. -/
theorem actual_positive_boundary_tangential_H2_v468
    (D : B1OriginalData (g := g) J) (s : Circle) (W : CollarWindow D s) :
    ∃ R : ℝ, 0<R ∧ R<W.R ∧ ∃ h : E2 → ℝ,
      ContinuousOn h (closedHalfDisc R) ∧
      (∀ x ∈ frontier (halfDisc R), h x=1) ∧
      (∀ x ∈ closedHalfDisc R, (1/2 : ℝ)≤h x) ∧
      ContDiffOn ℝ ∞ h (halfDisc R) ∧
      H1On (halfDisc R) h (planarGradient h) ∧
      H10On (halfDisc R) (fun x => h x-1) (planarGradient h) ∧
      WeakLinearEquationOn (halfDisc R) W.a W.b W.c h (planarGradient h) ∧
      (∀ x ∈ halfDisc R, classicalL W.a W.b W.c h x=0) ∧
      ∀ i : Fin 2, ∃ w : E2 → ℝ,
        MemLp w 2 (volume.restrict (Metric.ball (0:E2) (R/4))) ∧
        DeGiorgi.HasWeakPartialDeriv 0 w
          (fun y => (halfDisc R).indicator (planarGradient h) y i)
          (Metric.ball (0:E2) (R/4)) := by
  obtain ⟨R,hR,hRW,h,hhc,hfront,hpos,hs,h1,h0,heq,hcl⟩ :=
    actual_halfdisc_native_closed_classical_positive_v468 D s W
  have hP : IsCompact (closedHalfDisc R) := (isCompact_closedBall (0:E2) R).inter_right
    (isClosed_le continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)
  have hPW : closedHalfDisc R ⊆ closedHalfDisc W.R :=
    fun x hx => ⟨Metric.closedBall_subset_closedBall hRW.le hx.1,hx.2⟩
  obtain ⟨B,hBa⟩ := actual_closed_halfdisc_smooth_elliptic_extension_v468 D s W
    (closedHalfDisc R) hP hPW
  obtain ⟨hF,hS⟩ := actual_halfdisc_flux_source_L2_v468 D s W R hRW h (planarGradient h) h1
  have hcut : Metric.closedBall (0:E2) (R/4) ⊆ Metric.ball (0:E2) (R/2) := by
    intro x hx
    exact Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hx) (by linarith))
  obtain ⟨eta,hetas,hetac,hetaone,hetasub,hetarange,N,hN,hder⟩ :=
    DifferentialGeometry.Analysis.exists_bump_compact_with_fderiv_bound
      (isCompact_closedBall (0:E2) (R/4)) Metric.isOpen_ball hcut
  have heone : ∀ x∈Metric.ball (0:E2) (R/4), eta x=1 :=
    fun x hx => hetaone.self_of_nhdsSet (Metric.ball_subset_closedBall hx)
  obtain ⟨M,hM,hbound⟩ := native_boundary_tangential_uniform_v468 R (R/2) (R/4)
    (by linarith) (by linarith) eta hetas hetac hetasub hetarange N hN hder
    (Metric.ball (0:E2) (R/4)) measurableSet_ball heone
    (fun y => h y-1) (planarGradient h) h0
    (fun y => matrixAction (W.a y) (planarGradient h y))
    (fun y => inner ℝ (W.b y) (planarGradient h y)+W.c y*h y) hF hS
    (fun phi hphi hphic hphis => (heq.2 phi hphi hphic hphis).2) B
    (fun x hx => by rw [hBa x ⟨Metric.ball_subset_closedBall hx.1,hx.2.le⟩])
  have hUm : MeasurableSet (halfDisc R) := (Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)).measurableSet
  have hd0 : MemLp ((halfDisc R).indicator (planarGradient h)) 2 volume :=
    (memLp_indicator_iff_restrict hUm.nullMeasurableSet).mpr h1.2.2
  have hVc : IsCompact (closure (Metric.ball (0:E2) (R/4))) :=
    (isCompact_closedBall (0:E2) (R/4)).of_isClosed_subset isClosed_closure
      (closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall)
  refine ⟨R,hR,hRW,h,hhc,hfront,hpos,hs,h1,h0,heq,hcl,?_⟩
  exact native_tangential_weakDerivative_of_uniform_v468 _ hd0 _ Metric.isOpen_ball hVc
    (R/4) (by linarith) M hM hbound
end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.actual_positive_boundary_tangential_H2_v468
