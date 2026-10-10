import InitialActualCapSeam_v460
import InitialActualBoundaryLift_v411
import InitialPrimitiveOscillation_v411

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates L1Independent

local macro "paid_all_radius" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialLiteralAllTestRadius_v460 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.original_literal_cap_arc_trace_all_tests_v460)⟩

local macro "paid_boundary_replace" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialActualBoundaryLift_v411 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.original_actual_boundary_lift_replacement_v411)⟩

local macro "paid_integral_sq" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialPrimitiveOscillation_v411 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.finite_L2_vector_integral_sq_v411)⟩

local macro "paid_actual_cap_geometry" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialArtificialCircleGeometry_v411 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.actual_boundary_cap_circle_geometry_v411)⟩

private theorem original_boundary_same_radius_comparison_data_v460
    {R : ℝ} {Ω : SmoothFlatJordanDomain R} {M : E2 → Mat2}
    {f : E2 → E2} {d : Fin 2 → E2 → E2}
    (minimum : SimultaneousMetricMinimum Ω M f d)
    (theta : ℝ → ℝ) (sigma : ℝ)
    (lift : WeakMonotoneBoundaryLift Ω theta sigma)
    (trace : HasGreenBoundaryTrace f d (liftedBoundaryValue Ω theta)) :
    ∃ K rho : ℝ,0 < K ∧ 0 < rho ∧ rho ≤ 1/2 ∧
      ∀ s r : ℝ,0 < r → r ≤ rho →
      ∃ q ∈ Ioo (r/2) r,∃ (theta' eta : ℝ → ℝ) (c : ℝ → E2),
        WeakMonotoneBoundaryLift Ω theta' sigma ∧
        (∀ t : ℝ,unitCircleParameter t ∉ Metric.ball (unitCircleParameter s) q →
          liftedBoundaryValue Ω theta' t=liftedBoundaryValue Ω theta t) ∧
        ContDiff ℝ ∞ eta ∧ ContDiff ℝ ∞ (fun t=>Ω.boundary.gamma (eta t)) ∧
        (∀ t∈Icc (s-2*Real.arcsin (q/2)) (s+2*Real.arcsin (q/2)),
          liftedBoundaryValue Ω theta' t=Ω.boundary.gamma (eta t)) ∧
        (∀ psi : E2 → ℝ,ContDiff ℝ ∞ psi → ∀ i j : Fin 2,
          (∫ x in planarCap (unitCircleParameter s) q,
            f x i*fderiv ℝ psi x (coordinateVector 2 j)+d i x j*psi x)=
            (q*∫ t in Ioo (-Real.pi) Real.pi,
              (disc 1).indicator (fun x=>f x i*psi x)
                (unitCircleParameter s+q•unitCircleParameter t)*unitCircleParameter t j)+
            ∫ t in circlePatch (unitCircleParameter s) q,
              liftedBoundaryValue Ω theta t i*psi (unitCircleParameter t)*unitCircleParameter t j) ∧
        let e := Real.arcsin (q/2)
        let aa := s+Real.pi/2+e
        let bb := s+3*Real.pi/2-e
        aa < bb ∧ ContinuousOn c (Icc aa bb) ∧
        c aa=liftedBoundaryValue Ω theta' (s+2*e) ∧
        c bb=liftedBoundaryValue Ω theta' (s-2*e) ∧
        (∀ i : Fin 2,AbsolutelyContinuousOnInterval (fun t=>c t i) aa bb) ∧
        MemLp (deriv c) 2 (volume.restrict (Icc aa bb)) ∧
        ((fun t=>(disc 1).indicator f (unitCircleParameter s+q•unitCircleParameter t))
          =ᵐ[volume.restrict (Icc aa bb)] c) ∧
        (∫ t in Icc aa bb,‖deriv c t‖^2)+
          q*(∫ t in Icc (s-2*e) (s+2*e),‖deriv (fun t=>Ω.boundary.gamma (eta t)) t‖^2) ≤
          K*((∫ x in planarCap (unitCircleParameter s) r,euclideanJetDensity d x)-
            (∫ x in planarCap (unitCircleParameter s) (r/2),euclideanJetDensity d x)) := by
  classical
  obtain ⟨C,rho,hC,hrho,hrhohalf,hboundary⟩ := paid_boundary_replace Ω theta sigma lift
  let K : ℝ := 2*(1+C*Real.pi)
  have hK : 0 < K := by dsimp [K];positivity
  refine ⟨K,rho,hK,hrho,hrhohalf,?_⟩
  intro s r hr hrr
  obtain ⟨q,hq,hlocal,hqf,hqd,hpath⟩ :=
    paid_all_radius minimum theta sigma lift trace s r hr (hrr.trans hrhohalf)
  dsimp only at hpath
  let e := Real.arcsin (q/2)
  let aa := s+Real.pi/2+e
  let bb := s+3*Real.pi/2-e
  let d0 : Fin 2 → E2 → E2 := fun i=>(disc 1).indicator (d i)
  let J : E2 → E2 := fun v=>(EuclideanSpace.equiv (Fin 2) ℝ).symm ![-v 1,v 0]
  let a : ℝ → E2 := fun t=>(EuclideanSpace.equiv (Fin 2) ℝ).symm
    (fun i=>q*inner ℝ (d0 i (unitCircleParameter s+q•unitCircleParameter t)) (J (unitCircleParameter t)))
  let c : ℝ → E2 := fun t=>liftedBoundaryValue Ω theta (s+2*e)+∫ x in aa..t,a x
  let D : ℝ := ∫ t in Icc aa bb,‖deriv c t‖^2
  let shell : ℝ := (∫ x in planarCap (unitCircleParameter s) r,euclideanJetDensity d x)-
    (∫ x in planarCap (unitCircleParameter s) (r/2),euclideanJetDensity d x)
  rcases hpath with ⟨haa,hwidth,hcc,hca,hcb,hac,hder,hL2,hD,_,_,htrace⟩
  change c aa=liftedBoundaryValue Ω theta (s+2*e) at hca
  change c bb=liftedBoundaryValue Ω theta (s-2*e) at hcb
  change MemLp (deriv c) 2 (volume.restrict (Icc aa bb)) at hL2
  change D ≤ 2*shell at hD
  have hqpos : 0 < q := lt_trans (by positivity) hq.1
  have hqrho : q ≤ rho := hq.2.le.trans hrr
  have hqhalf : q ≤ 1/2 := hqrho.trans hrhohalf
  obtain ⟨theta',eta,hnewlift,hnewarc,hoff,heta,hcurve,henergy⟩ := hboundary s q hqpos hqrho
  have hcircleNorm (t:ℝ) : ‖unitCircleParameter t‖=1 := by
    have hs : ‖unitCircleParameter t‖^2=1 := by
      rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two]
      exact Real.cos_sq_add_sin_sq t
    nlinarith [norm_nonneg (unitCircleParameter t)]
  have hg := paid_actual_cap_geometry s q hqpos hqhalf
  dsimp only at hg
  have hleftNot : unitCircleParameter (s+2*e) ∉ Metric.ball (unitCircleParameter s) q := by
    have heq : dist (unitCircleParameter (s+2*e)) (unitCircleParameter s)=q := by
      rw [←hg.2.2.2.1,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_of_nonneg hqpos.le,hcircleNorm,mul_one]
    simp only [Metric.mem_ball,heq,lt_self_iff_false,not_false_eq_true]
  have hrightNot : unitCircleParameter (s-2*e) ∉ Metric.ball (unitCircleParameter s) q := by
    have heq : dist (unitCircleParameter (s-2*e)) (unitCircleParameter s)=q := by
      rw [←hg.2.2.2.2.1,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_of_nonneg hqpos.le,hcircleNorm,mul_one]
    simp only [Metric.mem_ball,heq,lt_self_iff_false,not_false_eq_true]
  have haeq : deriv c=ᵐ[volume.restrict (Icc aa bb)] a := hder.mono fun t ht=>ht.deriv
  have haL2 : MemLp a 2 (volume.restrict (Icc aa bb)) := hL2.ae_eq haeq
  let : IsFiniteMeasure (volume.restrict (Icc aa bb)) := isFiniteMeasure_restrict.mpr measure_Icc_lt_top.ne
  have hsq := paid_integral_sq (volume.restrict (Icc aa bb)) a haL2
  have hvolume : ((volume.restrict (Icc aa bb)) univ).toReal=bb-aa := by
    rw [Measure.restrict_apply_univ,Real.volume_Icc,ENNReal.toReal_ofReal (sub_nonneg.mpr haa.le)]
  have hnormIntegral : (∫ t in Icc aa bb,‖a t‖^2)=D := by
    apply integral_congr_ae
    filter_upwards [haeq] with t ht
    rw [ht]
  have hinc : c bb-c aa=∫ t in Icc aa bb,a t := by
    dsimp only [c]
    rw [intervalIntegral.integral_same,add_zero,add_sub_cancel_left,
      intervalIntegral.integral_of_le haa.le,←integral_Icc_eq_integral_Ioc]
  rw [hvolume,hnormIntegral,←hinc] at hsq
  have hchord : dist (liftedBoundaryValue Ω theta (s-2*e))
      (liftedBoundaryValue Ω theta (s+2*e))^2 ≤ Real.pi*D := by
    rw [dist_eq_norm,←hca,←hcb]
    exact hsq.trans (mul_le_mul_of_nonneg_right hwidth (integral_nonneg fun t=>sq_nonneg _))
  refine ⟨q,hq,theta',eta,c,hnewlift,hoff,heta,hcurve,?_,hlocal,haa,hcc,?_,?_,hac,hL2,htrace,?_⟩
  · intro t ht
    change Ω.boundary.gamma (theta' t)=_
    rw [hnewarc t ht]
  · exact hca.trans (hoff _ hleftNot).symm
  · exact hcb.trans (hoff _ hrightNot).symm
  · change D+q*(∫ t in Icc (s-2*e) (s+2*e),‖deriv (fun t=>Ω.boundary.gamma (eta t)) t‖^2) ≤ K*shell
    have hE := henergy.trans (mul_le_mul_of_nonneg_left hchord hC.le)
    calc
      _ ≤ (1+C*Real.pi)*D := by nlinarith only [hE]
      _ ≤ (1+C*Real.pi)*(2*shell) := mul_le_mul_of_nonneg_left hD (by positivity)
      _ = K*shell := by dsimp [K];ring

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
