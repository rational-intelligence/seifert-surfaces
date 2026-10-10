import B1ActualBoundaryDifferentiated_v468
import B1BoundaryH2Step_v468
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open ChartMetricProvider.Variational.DirectWeak
open BoundaryContinuation
set_option maxHeartbeats 800000

/-- Native boundary H2 and every compact tangential zero-trace localization
belong to one and the same positive solution constructed from D,s,W. -/
theorem actual_positive_boundary_combined_input_v468
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
      ∀ q : ℝ, 0<q → q<R/4 →
        MemWkp 2 2 h (halfDisc q) ∧
        ∀ chi : E2 → ℝ, ContDiff ℝ ∞ chi → HasCompactSupport chi →
          tsupport chi ⊆ Metric.ball (0:E2) q →
          H10On (halfDisc q) (fun x => chi x*planarGradient h x 0)
            (cutoffGradient chi (fun x => planarGradient h x 0)
              (planarGradient (fun x => planarGradient h x 0))) := by
  obtain ⟨R,hR,hRW,h,hhc,hfront,hpos,hs,h1,h0,heq,hcl,hH2⟩ :=
    actual_positive_boundary_full_H2_v468 D s W
  have hRo : IsOpen (halfDisc R) := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)
  have hP : IsCompact (closedHalfDisc R) := (isCompact_closedBall (0:E2) R).inter_right
    (isClosed_le continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)
  have hPW : closedHalfDisc R ⊆ closedHalfDisc W.R :=
    fun x hx => ⟨Metric.closedBall_subset_closedBall hRW.le hx.1,hx.2⟩
  obtain ⟨B,hBa⟩ := actual_closed_halfdisc_smooth_elliptic_extension_v468 D s W
    (closedHalfDisc R) hP hPW
  obtain ⟨hF,hS⟩ := actual_halfdisc_flux_source_L2_v468 D s W R hRW h (planarGradient h) h1
  have hdsub : planarGradient (fun x => h x-1)=planarGradient h := by
    ext x i
    simp only [QuasilinearLocalization.Helpers.gradient_apply,fderiv_sub_const]
  have hF' : MemLp (fun x => matrixAction (B.a x) (planarGradient (fun y => h y-1) x))
      2 (volume.restrict (halfDisc R)) := by
    apply hF.ae_eq
    filter_upwards [ae_restrict_mem hRo.measurableSet] with x hx
    rw [hdsub,hBa x ⟨Metric.ball_subset_closedBall hx.1,hx.2.le⟩]
  have h0' : H10On (halfDisc R) (fun x => h x-1) (planarGradient (fun x => h x-1)) := by
    rw [hdsub]
    exact h0
  have ht := native_boundary_tangential_step_v468 R hR (fun x => h x-1) h0' B
    (fun x => inner ℝ (W.b x) (planarGradient h x)+W.c x*h x) hF' hS (by
      intro phi hp hc ht
      have hh := (heq.2 phi hp hc ht).2
      convert hh using 1
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hRo.measurableSet] with x hx
      rw [hdsub,hBa x ⟨Metric.ball_subset_closedBall hx.1,hx.2.le⟩])
  rw [hdsub] at ht
  obtain ⟨w0,hw0,hd0⟩ := ht 0
  obtain ⟨w1,hw1,hd1⟩ := ht 1
  have hf := native_zero_extended_tangent_H1_v468 R (R/4) (by linarith)
    (fun x => h x-1) (planarGradient h) h0 w0 w1 hw0 hw1 hd0 hd1
  refine ⟨R,hR,hRW,h,hhc,hfront,hpos,hs,h1,h0,heq,hcl,?_⟩
  intro q hq hqR
  refine ⟨(hH2 q hq hqR).1,?_⟩
  intro chi hc hcc hct
  have hfq := h1_restrict_subset (Metric.ball 0 (R/4)) (Metric.ball 0 q)
    (Metric.ball_subset_ball hqR.le) _ _ hf
  exact native_tangent_local_zero_trace_v468 R q hq (by linarith) h hs _ hfq chi hc hcc hct
end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.actual_positive_boundary_combined_input_v468
