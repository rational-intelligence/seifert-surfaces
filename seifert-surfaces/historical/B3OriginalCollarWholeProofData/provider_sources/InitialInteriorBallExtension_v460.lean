import InitialInteriorBallGreen_v460
import NativeBallH1Extension

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates L1Independent

local macro "paid_ball_green" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialInteriorBallGreen_v460 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.original_interior_same_radius_ball_green_v460)⟩

local macro "paid_ball_geometry" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialInteriorBallGreen_v460 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.original_contained_ball_geometry_v460)⟩

private theorem original_interior_ball_native_extension_v460
    {R : ℝ} {Ω : SmoothFlatJordanDomain R} {M : E2 → Mat2}
    {f : E2 → E2} {d : Fin 2 → E2 → E2}
    (minimum : SimultaneousMetricMinimum Ω M f d)
    (theta : ℝ → ℝ) (sigma : ℝ)
    (lift : WeakMonotoneBoundaryLift Ω theta sigma)
    (trace : HasGreenBoundaryTrace f d (liftedBoundaryValue Ω theta))
    (x:E2) (r:ℝ) (hr:0 < r) (hrhalf:r ≤ 1/2)
    (inside:Metric.closedBall x r⊆disc 1) :
    ∃ q∈Ioo (r/2) r, ∃ c:ℝ→E2, ∃ h:E2→E2, ∃ dh:Fin 2→E2→E2,
      Continuous c ∧ Periodic c (2*Real.pi) ∧
      (∀ i:Fin 2,AbsolutelyContinuousOnInterval (fun t=>c t i) (-Real.pi) Real.pi) ∧
      MemLp (deriv c) 2 (volume.restrict (Icc (-Real.pi) Real.pi)) ∧
      (∫ t in Icc (-Real.pi) Real.pi,‖deriv c t‖^2) ≤
        2*((∫ y in planarCap x r,euclideanJetDensity d y)-
          (∫ y in planarCap x (r/2),euclideanJetDensity d y)) ∧
      (fun t=>f (x+q•unitCircleParameter t))=ᵐ[volume.restrict (Icc (-Real.pi) Real.pi)] c ∧
      (∀ i,H1On (Metric.ball x q) (fun z=>h z i) (dh i)) ∧
      (∫ z in Metric.ball x q,euclideanJetDensity dh z) ≤
        (((2*Real.pi)^2+1)/2) * ∫ t in Icc (-Real.pi) Real.pi,‖deriv c t‖^2 ∧
      (∀ psi:E2→ℝ,ContDiff ℝ ∞ psi → ∀ i j:Fin 2,
        IntegrableOn (fun z=>h z i*fderiv ℝ psi z (coordinateVector 2 j)+dh i z j*psi z)
          (Metric.ball x q) ∧
        IntegrableOn (fun t=>c t i*psi (x+q•unitCircleParameter t)*unitCircleParameter t j)
          (Icc (-Real.pi) Real.pi) ∧
        (∫ z in Metric.ball x q,
          h z i*fderiv ℝ psi z (coordinateVector 2 j)+dh i z j*psi z) =
          q*∫ t in Icc (-Real.pi) Real.pi,
            c t i*psi (x+q•unitCircleParameter t)*unitCircleParameter t j) ∧
      RelativeCapGreen x q f h d dh (liftedBoundaryValue Ω theta) (liftedBoundaryValue Ω theta) := by
  obtain ⟨q,hq,c,hcc,hcp,hca,hcd,hce,htrace,hlocal⟩ :=
    paid_ball_green minimum theta sigma lift trace x r hr hrhalf inside
  have hqpos : 0 < q := lt_trans (by positivity) hq.1
  obtain ⟨h,dh,hh1,henergy,hgreen⟩ :=
    NativeBallCapExtension.native_ball_H1_extension x q hqpos c hcp hcc hca hcd
  obtain ⟨hcap,hpatch,hslice,hx⟩ := paid_ball_geometry x r q hr hqpos hq.2.le inside
  refine ⟨q,hq,c,h,dh,hcc,hcp,hca,hcd,hce,htrace,hh1,henergy,hgreen,?_⟩
  intro psi hpsi i j
  obtain ⟨holdI,holdB,holdEq⟩ := hlocal psi hpsi i j
  obtain ⟨hnewI,hnewB,hnewEq⟩ := hgreen psi hpsi i j
  have hdelta : (fun z=>(h z i-f z i)*fderiv ℝ psi z (coordinateVector 2 j)+
      (dh i z j-d i z j)*psi z) =
      (fun z=>(h z i*fderiv ℝ psi z (coordinateVector 2 j)+dh i z j*psi z)-
        (f z i*fderiv ℝ psi z (coordinateVector 2 j)+d i z j*psi z)) := by
    funext z
    ring
  simp only [sub_self,zero_mul,MeasureTheory.integrableOn_zero,MeasureTheory.integral_zero,
    hcap,hdelta]
  refine ⟨hnewI.sub holdI,?_⟩
  rw [integral_sub hnewI holdI,hnewEq,holdEq,sub_self]
  simp

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
