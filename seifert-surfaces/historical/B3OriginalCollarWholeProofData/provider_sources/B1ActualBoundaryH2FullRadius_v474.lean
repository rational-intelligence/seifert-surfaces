import B1ActualBoundaryTower_v474
import B1BoundaryH2RadiusIteration_v474
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open DifferentialGeometry.Analysis.Sobolev.Euclidean
set_option maxHeartbeats 500000
set_option maxRecDepth 1500
set_option backward.isDefEq.respectTransparency false

theorem actual_positive_boundary_H2_full_radius_v474
    (D : B1OriginalData (g:=g) J) (s : Circle) (W : CollarWindow D s) :
    ∃ R : ℝ, 0<R ∧ R<W.R ∧ ∃ h : E2 → ℝ,
      ContinuousOn h (closedHalfDisc R) ∧
      (∀ x ∈ frontier (halfDisc R), h x=1) ∧
      (∀ x ∈ closedHalfDisc R, (1/2 : ℝ)≤h x) ∧
      ContDiffOn ℝ ∞ h (halfDisc R) ∧
      H1On (halfDisc R) h (planarGradient h) ∧
      H10On (halfDisc R) (fun x => h x-1) (planarGradient h) ∧
      WeakLinearEquationOn (halfDisc R) W.a W.b W.c h (planarGradient h) ∧
      (∀ x ∈ halfDisc R, classicalL W.a W.b W.c h x=0) ∧
      ∀ q : ℝ, 0<q → q<R → MemWkp 2 2 h (halfDisc q) := by
  obtain ⟨R,hR,hRW,h,hhc,hfront,hpos,hs,h1,h0,heq,hcl⟩ :=
    actual_halfdisc_native_closed_classical_positive_v468 D s W
  have hP : IsCompact (closedHalfDisc R) := (isCompact_closedBall (0:E2) R).inter_right
    (isClosed_le continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)
  obtain ⟨B,hBa⟩ := actual_closed_halfdisc_smooth_elliptic_extension_v468 D s W
    (closedHalfDisc R) hP (fun x hx => ⟨Metric.closedBall_subset_closedBall hRW.le hx.1,hx.2⟩)
  have hU : IsOpen (halfDisc R) := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)
  have hBactual (x : E2) (hx : x∈halfDisc R) : B.a x=W.a x :=
    hBa x ⟨Metric.ball_subset_closedBall hx.1,hx.2.le⟩
  obtain ⟨hF,hS⟩ := actual_halfdisc_flux_source_L2_v468 D s W R hRW h _ h1
  let u : E2 → ℝ := fun x => h x-1
  have hus : ContDiffOn ℝ ∞ u (halfDisc R) := hs.sub contDiffOn_const
  have hdsub : planarGradient u=planarGradient h := by
    ext x i
    simp only [u,QuasilinearLocalization.Helpers.gradient_apply,fderiv_sub_const]
  have hu0 : H10On (halfDisc R) u (planarGradient u) := by rw [hdsub]; exact h0
  have hFB : MemLp (fun x => matrixAction (B.a x) (planarGradient u x)) 2
      (volume.restrict (halfDisc R)) := by
    apply hF.ae_eq
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    rw [hdsub,hBactual x hx]
  have hweak : ∀ phi : E2 → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ halfDisc R →
      (∫ x in halfDisc R, inner ℝ (matrixAction (B.a x) (planarGradient u x))
        (planarGradient phi x)-(inner ℝ (W.b x) (planarGradient h x)+W.c x*h x)*phi x)=0 := by
    intro phi hp hc ht
    convert (heq.2 phi hp hc ht).2 using 1
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    rw [hdsub,hBactual x hx]
  refine ⟨R,hR,hRW,h,hhc,hfront,hpos,hs,h1,h0,heq,hcl,?_⟩
  intro q hq hqR
  have hv := (native_boundary_H2_radius_v474 R q hq hqR u hus hu0 B _ hFB hS hweak).2.1
  have hQ : IsOpen (halfDisc q) := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)
  have hh := MemWkp.add (by norm_num) hQ hv (native_halfdisc_constant_Wkp_v474 q 2 1)
  convert hh using 1
  funext x
  dsimp [u]
  ring

end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.actual_positive_boundary_H2_full_radius_v474
