import B1CollarWindow_v468
noncomputable section
open Set Topology Function
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
universe v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}
set_option maxHeartbeats 300000

theorem actual_halfdisc_radial_membership_v474
    (D : B1OriginalData (g:=g) J) (s : Circle) (W : CollarWindow D s)
    (x : E2) (hx : x∈halfDisc W.R) : x 1∈Ioo (0:ℝ) D.r0 := by
  refine ⟨hx.2,?_⟩
  have hb : ‖x‖<W.R := by simpa only [disc,Metric.mem_ball,dist_zero_right] using hx.1
  have hc : |x 1|≤‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x 1
  exact ((le_abs_self _).trans hc).trans_lt (hb.trans W.R_radial)

theorem actual_halfdisc_graph_membership_v474
    (D : B1OriginalData (g:=g) J) (s : Circle) (W : CollarWindow D s)
    (x : E2) (hx : x∈halfDisc W.R) :
    D.collar (localCircle D s (x 0),x 1,localHeight D s x)∈D.A.1.image ∧
    D.collar (localCircle D s (x 0),x 1,0)∈D.B.1.image ∧
    D.collar (localCircle D s (x 0),x 1,localHeight D s x)∉(𝓡∂ 3).boundary E.Carrier ∧
    D.collar (localCircle D s (x 0),x 1,0)∉(𝓡∂ 3).boundary E.Carrier := by
  have hr := actual_halfdisc_radial_membership_v474 D s W x hx
  have hrc : x 1∈Icc (0:ℝ) D.r0 := ⟨hr.1.le,hr.2.le⟩
  have hfa : (localCircle D s (x 0),x 1,localHeight D s x)∈halfCylinder D.r0 D.eta :=
    ⟨hrc,D.graph_inside _ _ hrc⟩
  have hfb : (localCircle D s (x 0),x 1,0)∈halfCylinder D.r0 D.eta :=
    ⟨hrc,by simpa using D.eta_pos⟩
  have ha : D.collar (localCircle D s (x 0),x 1,localHeight D s x)∈D.A.1.image := by
    have hpoint : D.collar (localCircle D s (x 0),x 1,localHeight D s x)∈
        D.A.1.image ∩ (D.collar '' halfCylinder D.r0 D.eta) := by
      rw [D.A_graph_exact]
      exact ⟨(localCircle D s (x 0),x 1),hrc,rfl⟩
    exact hpoint.1
  have hb : D.collar (localCircle D s (x 0),x 1,0)∈D.B.1.image := by
    have hpoint : D.collar (localCircle D s (x 0),x 1,0)∈
        D.B.1.image ∩ (D.collar '' halfCylinder D.r0 D.eta) := by
      rw [D.B_graph_exact]
      exact ⟨(localCircle D s (x 0),x 1),hrc,rfl⟩
    exact hpoint.1
  exact ⟨ha,hb,fun hp => hr.1.ne' ((D.collar_boundary _ hfa).mp hp),
    fun hp => hr.1.ne' ((D.collar_boundary _ hfb).mp hp)⟩

theorem actual_local_zero_common_patch_v474
    (D : B1OriginalData (g:=g) J) (s : Circle) (W : CollarWindow D s)
    (hzero : ∃ U : Set E2, IsOpen U ∧ U.Nonempty ∧ U⊆halfDisc W.R ∧
      ∀ x∈U, localHeight D s x=0) :
    ∃ U : Set E2, IsOpen U ∧ U.Nonempty ∧ U⊆halfDisc W.R ∧
      ∀ x∈U, D.collar (localCircle D s (x 0),x 1,0)∈D.A.1.image∩D.B.1.image ∧
        D.collar (localCircle D s (x 0),x 1,0)∉(𝓡∂ 3).boundary E.Carrier := by
  obtain ⟨U,hU,hUne,hsub,hzero⟩ := hzero
  refine ⟨U,hU,hUne,hsub,?_⟩
  intro x hx
  obtain ⟨ha,hb,haint,hbint⟩ := actual_halfdisc_graph_membership_v474 D s W x (hsub hx)
  rw [hzero x hx] at ha
  exact ⟨⟨ha,hb⟩,hbint⟩

end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.actual_local_zero_common_patch_v474
