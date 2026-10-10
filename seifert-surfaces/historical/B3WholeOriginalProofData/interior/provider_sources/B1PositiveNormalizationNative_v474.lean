import B1ActualBoundaryTowerFullRadius_v474
import B1FlatAmbientExtension_v474
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open DifferentialGeometry.Analysis.Sobolev.Euclidean
set_option maxHeartbeats 700000
set_option maxRecDepth 1500
set_option backward.isDefEq.respectTransparency false

theorem actual_positive_normalization_native_v474
    (D : B1OriginalData (g:=g) J) (s : Circle) (W : CollarWindow D s) :
    Nonempty (PositiveNormalization W) := by
  classical
  obtain ⟨R,hR,hRW,h,hhc,hfront,hpos,hs,h1,h0,heq,hcl,htower⟩ :=
    actual_positive_boundary_sobolev_full_radius_v474 D s W
  have hR78 : 0<7*R/8 := by positivity
  have hR78R : 7*R/8<R := by linarith
  have hR34 : 0<3*R/4 := by positivity
  have hR34R78 : 3*R/4<7*R/8 := by linarith
  have hsub : halfDisc (7*R/8) ⊆ halfDisc R :=
    fun x hx => ⟨Metric.ball_subset_ball hR78R.le hx.1,hx.2⟩
  have hcsub : closedHalfDisc (7*R/8) ⊆ closedHalfDisc R :=
    fun x hx => ⟨Metric.closedBall_subset_closedBall hR78R.le hx.1,hx.2⟩
  have hclosed := native_halfdisc_smooth_closure_radius_v474 (7*R/8) (3*R/4)
    hR34 hR34R78 h (hs.mono hsub) (hhc.mono hcsub)
    (fun m => htower m (7*R/8) hR78 hR78R)
  obtain ⟨G,hG,hGeq⟩ := native_halfdisc_ambient_extension_v474 (3*R/4) (2*R/3)
    (by linarith) h hclosed
  let f : E2 → ℝ := fun x => if 0≤x 1 then h x else G x
  have hfclosed : EqOn f h (closedHalfDisc R) := fun x hx => by
    dsimp only [f]
    exact if_pos hx.2
  have hfopen : EqOn f h (halfDisc R) := fun x hx => by
    dsimp only [f]
    exact if_pos hx.2.le
  have hU : IsOpen (halfDisc R) := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)
  have hgrad : ∀ x∈halfDisc R, planarGradient h x=planarGradient f x := by
    intro x hx
    have he := hfopen.eventuallyEq_of_mem (hU.mem_nhds hx)
    simp only [planarGradient,he.fderiv_eq]
  have hae : h=ᵐ[volume.restrict (halfDisc R)] f := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    exact (hfopen hx).symm
  have hga : planarGradient h=ᵐ[volume.restrict (halfDisc R)] planarGradient f := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    exact hgrad x hx
  have hf1 := native_h1_congr_ae_v468 _ h f _ _ h1 hae hga
  have hf0 := native_h10_congr_ae_v468 _ (fun x => h x-1) (fun x => f x-1) _ _ h0
    (hae.mono fun x hx => by dsimp only; rw [hx]) hga
  have hfeq := native_linear_congr_ae_v468 _ W.a W.b W.c h f _ _ h1 heq hae hga
  have hfs : ContDiffOn ℝ ∞ f (halfDisc R) := hs.congr hfopen
  have hfclass := actual_halfdisc_native_weak_classical_at_radius_v468 D s W R hRW f hfs hfeq
  refine ⟨{
    R:=R
    R_pos:=hR
    R_inside:=hRW
    h:=f
    h_continuous:=hhc.congr hfclosed
    h_boundary_one:=?_
    h_lower_bound:=?_
    dh:=planarGradient f
    h_H1:=hf1
    h_minus_one_H10:=hf0
    h_weak:=hfeq
    N:=Metric.ball 0 (2*R/3)
    N_open:=Metric.isOpen_ball
    N_contains:=?_
    h_smooth_near_base:=?_
    h_smooth_interior:=hfs
    dh_exact:=fun _ _ => rfl
    h_classical:=hfclass }⟩
  · intro x hx
    have hxcl : x∈closedHalfDisc R := by
      rw [←native_halfdisc_closure_v474 R hR]
      exact frontier_subset_closure hx
    rw [hfclosed hxcl]
    exact hfront x hx
  · intro x hx
    rw [hfclosed hx]
    exact hpos x hx
  · intro x hx
    exact Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hx.1) (by linarith))
  · apply hG.contDiffOn.congr
    intro x hx
    dsimp only [f]
    split_ifs with hp
    · exact (hGeq ⟨Metric.ball_subset_closedBall hx,hp⟩).symm
    · rfl

end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.actual_positive_normalization_native_v474
