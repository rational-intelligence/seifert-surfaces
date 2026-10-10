import B1ActualFieldGraphSupport_v475
import B1ActualGraphParameters_v475

noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
universe v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

theorem actual_collar_graph_height_unique_v475
    (D : B1OriginalData g J) (s : Circle) (W : CollarWindow D s) :
    (∀ y ∈ collarDomain D W.R, localCollar D s y ∈ D.A.1.image →
      y 2 = localHeight D s (native_collar_base_v475 y)) ∧
    (∀ y ∈ collarDomain D W.R, localCollar D s y ∈ D.B.1.image → y 2 = 0) := by
  constructor
  · intro y hy hp
    have ha : localCollar D s y ∈ D.A.1.image ∩ (D.collar '' halfCylinder D.r0 D.eta) :=
      ⟨hp,⟨(localCircle D s (y 0),y 1,y 2),⟨hy.2.1,hy.2.2⟩,rfl⟩⟩
    rw [D.A_graph_exact] at ha
    obtain ⟨z,hz,hzeq⟩ := ha
    have hpre : (z.1,z.2,D.f z.1 z.2) = (localCircle D s (y 0),y 1,y 2) := by
      exact congrArg Subtype.val (D.collar_embedding.injective
        (a₁ := ⟨(z.1,z.2,D.f z.1 z.2),⟨hz,D.graph_inside _ _ hz⟩⟩)
        (a₂ := ⟨(localCircle D s (y 0),y 1,y 2),⟨hy.2.1,hy.2.2⟩⟩) hzeq)
    have hs := congrArg Prod.fst hpre
    have hr := congrArg (fun q : Circle × (ℝ × ℝ) => q.2.1) hpre
    have hf := congrArg (fun q : Circle × (ℝ × ℝ) => q.2.2) hpre
    have hsy : z.1 = localCircle D s (y 0) := by simpa using hs
    have hry : z.2 = y 1 := by simpa using hr
    have hfy : D.f z.1 z.2 = y 2 := by simpa using hf
    rw [← hfy,hsy,hry]
    rfl
  · intro y hy hp
    have hb : localCollar D s y ∈ D.B.1.image ∩ (D.collar '' halfCylinder D.r0 D.eta) :=
      ⟨hp,⟨(localCircle D s (y 0),y 1,y 2),⟨hy.2.1,hy.2.2⟩,rfl⟩⟩
    rw [D.B_graph_exact] at hb
    obtain ⟨z,hz,hzeq⟩ := hb
    have hpre : (z.1,z.2,(0 : ℝ)) = (localCircle D s (y 0),y 1,y 2) := by
      exact congrArg Subtype.val (D.collar_embedding.injective
        (a₁ := ⟨(z.1,z.2,(0 : ℝ)),⟨hz,by simpa using D.eta_pos⟩⟩)
        (a₂ := ⟨(localCircle D s (y 0),y 1,y 2),⟨hy.2.1,hy.2.2⟩⟩) hzeq)
    exact (congrArg (fun q : Circle × (ℝ × ℝ) => q.2.2) hpre).symm

/-- The recovered graph source parameter is injective because both collar
coordinates and the original surface embedding are injective. -/
theorem actual_graph_parameter_injOn_v475
    (D : B1OriginalData g J) (s : Circle) (W : CollarWindow D s)
    {S : CompactOrientedSurface} (f : ProperSmoothEmbedding S E.Carrier)
    (u : E2 → ℝ) (q : E2 → S)
    (hheight : ∀ x ∈ halfDisc W.R, |u x| < D.eta)
    (hq : ∀ x ∈ halfDisc W.R, f.toFun (q x) = localCollar D s (jetPoint (x,u x,0))) :
    InjOn q (halfDisc W.R) := by
  have hc (x : E2) (hx : x ∈ halfDisc W.R) : jetPoint (x,u x,0) ∈ collarDomain D W.R := by
    have hn : ‖x‖ < W.R := by simpa only [disc,Metric.mem_ball,dist_zero_right] using hx.1
    have ha : |x 0| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x 0
    have hr := actual_halfdisc_radial_membership_v474 D s W x hx
    simpa [jetPoint,collarDomain] using And.intro (show |x 0| < 2*W.R by linarith [W.R_pos])
      (And.intro (And.intro hr.1.le hr.2.le) (hheight x hx))
  intro x hx y hy hxy
  have hf : localCollar D s (jetPoint (x,u x,0)) = localCollar D s (jetPoint (y,u y,0)) := by
    rw [← hq x hx,← hq y hy,hxy]
  have hj := actual_localCollar_injective_v475 D s W (hc x hx) (hc y hy) hf
  ext i
  fin_cases i
  · simpa [jetPoint] using congrArg (fun y : E3 => y 0) hj
  · simpa [jetPoint] using congrArg (fun y : E3 => y 1) hj

#print axioms actual_collar_graph_height_unique_v475
#print axioms actual_graph_parameter_injOn_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
