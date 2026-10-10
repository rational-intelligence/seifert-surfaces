import B1BoundaryDifferentiatedEquation_v468
import B1NativeLinearRestriction_v468
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open ChartMetricProvider.Variational.DirectWeak.BoundaryContinuation
set_option maxHeartbeats 800000

/-- The same original positive Dirichlet solution has an actual differentiated
native equation on every smaller half-disc, including the flat edge. -/
theorem actual_positive_boundary_differentiated_v468
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
      ∀ q : ℝ, 0<q → q<R/4 → ∀ l : Fin 2,
        ∃ f : E2 → ℝ, MemLp f 2 (volume.restrict (halfDisc q)) ∧
          H1On (halfDisc q) (fun x => planarGradient h x l)
            (planarGradient (fun x => planarGradient h x l)) ∧
          ∀ phi : E2 → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
            tsupport phi ⊆ halfDisc q →
            IntegrableOn (fun x => inner ℝ (matrixAction (W.a x)
              (planarGradient (fun y => planarGradient h y l) x)) (planarGradient phi x)-f x*phi x)
              (halfDisc q) ∧
            (∫ x in halfDisc q, inner ℝ (matrixAction (W.a x)
              (planarGradient (fun y => planarGradient h y l) x)) (planarGradient phi x)-f x*phi x)=0 := by
  obtain ⟨R,hR,hRW,h,hhc,hfront,hpos,hs,h1,h0,heq,hcl,hH2⟩ :=
    actual_positive_boundary_full_H2_v468 D s W
  have hP : IsCompact (closedHalfDisc R) := (isCompact_closedBall (0:E2) R).inter_right
    (isClosed_le continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)
  have hPW : closedHalfDisc R ⊆ closedHalfDisc W.R :=
    fun x hx => ⟨Metric.closedBall_subset_closedBall hRW.le hx.1,hx.2⟩
  obtain ⟨B,hBa⟩ := actual_closed_halfdisc_smooth_elliptic_extension_v468 D s W
    (closedHalfDisc R) hP hPW
  refine ⟨R,hR,hRW,h,hhc,hfront,hpos,hs,h1,h0,heq,hcl,?_⟩
  intro q hq hqR l
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
  exact native_boundary_differentiated_equation_v468 (halfDisc q) hU hUc h
    (planarGradient h) h1q (hs.mono hsub) (fun x hx => rfl) W.a W.b W.c heqq A hAa B
    (fun x hx => (hAa x hx).trans (hBa x
      ⟨Metric.ball_subset_closedBall (hsub hx).1,(hsub hx).2.le⟩).symm)
    (hH2 q hq hqR).1 hf.memW1p l
end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.actual_positive_boundary_differentiated_v468
