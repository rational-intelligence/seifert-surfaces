import B1ActualBoundaryCombinedInput_v468
import B1BoundaryCutoffH2_v468
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open ChartMetricProvider.Variational.DirectWeak.BoundaryContinuation
set_option maxHeartbeats 1000000

/-- The actual positive solution from the original data gains boundary H2 on
its compactly localized tangential derivative, while retaining its literal
Dirichlet datum and native weak equation. -/
theorem actual_positive_boundary_tangent_cutoff_H2_v468
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
      (∀ q : ℝ, 0<q → q<R/4 → MemWkp 2 2 h (halfDisc q)) ∧
      ∀ q : ℝ, 0<q → q<R/4 →
        ∀ chi : E2 → ℝ, ContDiff ℝ ∞ chi → HasCompactSupport chi →
          tsupport chi ⊆ Metric.ball (0:E2) q →
          ∀ t : ℝ, 0<t → t<q/4 →
            MemWkp 2 2 (fun x => chi x*planarGradient h x 0) (halfDisc t) := by
  obtain ⟨R,hR,hRW,h,hhc,hfront,hpos,hs,h1,h0,heq,hcl,hH2⟩ :=
    actual_positive_boundary_combined_input_v468 D s W
  have hP : IsCompact (closedHalfDisc R) := (isCompact_closedBall (0:E2) R).inter_right
    (isClosed_le continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)
  have hPW : closedHalfDisc R ⊆ closedHalfDisc W.R :=
    fun x hx => ⟨Metric.closedBall_subset_closedBall hRW.le hx.1,hx.2⟩
  obtain ⟨B,hBa⟩ := actual_closed_halfdisc_smooth_elliptic_extension_v468 D s W
    (closedHalfDisc R) hP hPW
  refine ⟨R,hR,hRW,h,hhc,hfront,hpos,hs,h1,h0,heq,hcl,?_⟩
  refine ⟨fun q hq hqR => (hH2 q hq hqR).1,?_⟩
  intro q hq hqR chi hc hcc hct
  have hqR' : q<R := by linarith
  have hsub : halfDisc q ⊆ halfDisc R :=
    fun x hx => ⟨Metric.ball_subset_ball hqR'.le hx.1,hx.2⟩
  have hU : IsOpen (halfDisc q) := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)
  have hclosed : IsClosed (closedHalfDisc q) := Metric.isClosed_closedBall.inter
    (isClosed_le continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)
  have hclsub : closure (halfDisc q) ⊆ closedHalfDisc q := closure_minimal
    (fun x hx => ⟨Metric.ball_subset_closedBall hx.1,hx.2.le⟩) hclosed
  have hUc : IsCompact (closure (halfDisc q)) :=
    ((isCompact_closedBall (0:E2) q).inter_right
      (isClosed_le continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)).of_isClosed_subset
        isClosed_closure hclsub
  have hUW : closure (halfDisc q) ⊆ closedHalfDisc W.R :=
    hclsub.trans (fun x hx => ⟨Metric.closedBall_subset_closedBall (hqR'.trans hRW).le hx.1,hx.2⟩)
  have hf := actual_halfdisc_boundary_lower_source_tower_v468 D s W R hRW h
    (planarGradient h) h1 (halfDisc q) hU hUc hsub hUW 1 (hH2 q hq hqR).1
  have h1q := h1_restrict_subset _ _ hsub h (planarGradient h) h1
  have heqq := native_full_linear_restrict_v468 _ _ hsub W.a W.b W.c h (planarGradient h) h1 heq
  obtain ⟨A,hAa⟩ := actual_halfdisc_elliptic_coeff_v468 D s W q (hqR'.trans hRW)
  obtain ⟨f,hflp,hgrad,hweak⟩ := native_boundary_differentiated_equation_v468
    (halfDisc q) hU hUc h (planarGradient h) h1q (hs.mono hsub) (fun x hx => rfl)
    W.a W.b W.c heqq A hAa B
    (fun x hx => (hAa x hx).trans (hBa x
      ⟨Metric.ball_subset_closedBall (hsub hx).1,(hsub hx).2.le⟩).symm)
    (hH2 q hq hqR).1 hf.memW1p 0
  have hgs : ContDiffOn ℝ ∞ (fun x => planarGradient h x 0) (halfDisc q) := by
    have he : (fun x => planarGradient h x 0)=fun x => fderiv ℝ h x (coordinateVector 2 0) := by
      funext x
      exact QuasilinearLocalization.Helpers.gradient_apply h x 0
    rw [he]
    exact ((hs.fderiv_of_isOpen
      (Metric.isOpen_ball.inter (isOpen_lt continuous_const
        (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)) (m:=∞) (by simp)).clm_apply
          contDiffOn_const).mono hsub
  exact native_boundary_cutoff_H2_v468 q hq _ hgs hgrad B f hflp (by
    intro phi hp hpc hpt
    have hh := (hweak phi hp hpc hpt).2
    convert hh using 1
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    rw [hBa x ⟨Metric.ball_subset_closedBall (hsub hx).1,(hsub hx).2.le⟩])
    chi hc ((hH2 q hq hqR).2 chi hc hcc hct)
end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.actual_positive_boundary_tangent_cutoff_H2_v468
