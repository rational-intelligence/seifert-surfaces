import B1ActualBoundaryTangentialClassical_v468
import B1BoundaryNormalL2Recovery_v468
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolev
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open SeifertSurfaces.QuasilinearProviderBridge
set_option maxHeartbeats 800000

/-- Genuine native boundary H2 for the same original positive Dirichlet
solution. The smaller patch reaches the flat edge. Both Hessian rows are paid
from the original equation, not from a boundary differentiability assumption. -/
theorem actual_positive_boundary_full_H2_v468
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
        ∀ i : Fin 2, DeGiorgi.MemW1p 2 (fun y => planarGradient h y i) (halfDisc q) := by
  obtain ⟨R,hR,hRW,h,hhc,hfront,hpos,hs,h1,h0,heq,hcl,htan⟩ :=
    actual_positive_boundary_tangential_classical_L2_v468 D s W
  have hP : IsCompact (closedHalfDisc R) := (isCompact_closedBall (0:E2) R).inter_right
    (isClosed_le continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)
  have hPW : closedHalfDisc R ⊆ closedHalfDisc W.R :=
    fun x hx => ⟨Metric.closedBall_subset_closedBall hRW.le hx.1,hx.2⟩
  obtain ⟨B,hBa⟩ := actual_closed_halfdisc_smooth_elliptic_extension_v468 D s W
    (closedHalfDisc R) hP hPW
  obtain ⟨hF,hS⟩ := actual_halfdisc_flux_source_L2_v468 D s W R hRW h (planarGradient h) h1
  have hRo : IsOpen (halfDisc R) := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)
  refine ⟨R,hR,hRW,h,hhc,hfront,hpos,hs,h1,h0,heq,hcl,?_⟩
  intro q hq hqR
  have hqR' : q<R := by linarith
  have hqsub : halfDisc q ⊆ halfDisc R :=
    fun x hx => ⟨Metric.ball_subset_ball hqR'.le hx.1,hx.2⟩
  have hU : IsOpen (halfDisc q) := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)
  have hG := h1.2.2.mono_measure (Measure.restrict_mono_set _ hqsub)
  have hg := native_boundary_normal_L2_recovery_v468 q h (hs.mono hqsub) hG B
    (fun x => inner ℝ (W.b x) (planarGradient h x)+W.c x*h x)
    (hS.mono_measure (Measure.restrict_mono_set _ hqsub)) (by
      intro x hx
      have he (i : Fin 2) :
          (fun y => matrixAction (B.a y) (planarGradient h y) i) =ᶠ[𝓝 x]
          (fun y => matrixAction (W.a y) (planarGradient h y) i) := by
        filter_upwards [hRo.mem_nhds (hqsub hx)] with y hy
        rw [hBa y ⟨Metric.ball_subset_closedBall hy.1,hy.2.le⟩]
      have hde (i : Fin 2) := congrArg (fun T : E2 →L[ℝ] ℝ => T (coordinateVector 2 i)) (he i).fderiv_eq
      have hd : (∑ i : Fin 2, fderiv ℝ (fun y => matrixAction (B.a y) (planarGradient h y) i) x
          (coordinateVector 2 i))=
        ∑ i : Fin 2, fderiv ℝ (fun y => matrixAction (W.a y) (planarGradient h y) i) x
          (coordinateVector 2 i) := Finset.sum_congr rfl (fun i _ => hde i)
      rw [hd]
      simpa only [classicalL,add_assoc] using hcl x (hqsub hx)) (htan q hq hqR)
  refine ⟨?_,hg⟩
  let hw : DeGiorgi.MemW1pWitness 2 h (halfDisc q) :=
    { memLp := h1.2.1.mono_measure (Measure.restrict_mono_set _ hqsub)
      weakGrad := planarGradient h
      weakGrad_component_memLp := hG.eval_piLp
      isWeakGrad := Helpers.C1_hasWeakGrad _ hU h ((hs.mono hqsub).of_le (by simp)) }
  exact MemWkp.of_weakGrad_memWkp (by norm_num) hU hw
    (fun i => MemWkp.one_iff_memW1p.mpr (hg i))
end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.actual_positive_boundary_full_H2_v468
