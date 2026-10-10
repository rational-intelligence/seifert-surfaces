import InitialInteriorLiteralTrace_v460

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
set_option maxHeartbeats 800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates L1Independent

local macro "paid_interior_trace" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialInteriorLiteralTrace_v460 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.original_interior_literal_circle_trace_v460)⟩

private theorem original_contained_ball_geometry_v460
    (x:E2) (r q:ℝ) (hr:0 < r) (hq:0 < q) (hqr:q ≤ r)
    (inside:Metric.closedBall x r⊆disc 1) :
    planarCap x q=Metric.ball x q ∧ circlePatch x q=∅ ∧
      (∀ t:ℝ,x+q•unitCircleParameter t∈disc 1) ∧ x∈closedDisc 1 := by
  classical
  have hcircleNorm (t:ℝ) : ‖unitCircleParameter t‖=1 := by
    have hs : ‖unitCircleParameter t‖^2=1 := by
      rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two]
      exact Real.cos_sq_add_sin_sq t
    nlinarith [norm_nonneg (unitCircleParameter t)]
  have hball : Metric.ball x q⊆disc 1 :=
    (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall hqr)).trans inside
  have hcap : planarCap x q=Metric.ball x q := inter_eq_right.mpr hball
  have hpatch : circlePatch x q=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro t ht
    have hin := hball ht.2
    have hlt : ‖unitCircleParameter t‖ < 1 := by simpa only [disc,Metric.mem_ball,dist_zero_right] using hin
    rw [hcircleNorm] at hlt
    exact lt_irrefl 1 hlt
  refine ⟨hcap,hpatch,?_,?_⟩
  · intro t
    apply inside
    change dist (x+q•unitCircleParameter t) x ≤ r
    rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_of_nonneg hq.le,hcircleNorm,mul_one]
    exact hqr
  · exact Metric.ball_subset_closedBall (inside (Metric.mem_closedBall_self hr.le))

private theorem original_interior_same_radius_ball_green_v460
    {R : ℝ} {Ω : SmoothFlatJordanDomain R} {M : E2 → Mat2}
    {f : E2 → E2} {d : Fin 2 → E2 → E2}
    (minimum : SimultaneousMetricMinimum Ω M f d)
    (theta : ℝ → ℝ) (sigma : ℝ)
    (lift : WeakMonotoneBoundaryLift Ω theta sigma)
    (trace : HasGreenBoundaryTrace f d (liftedBoundaryValue Ω theta))
    (x:E2) (r:ℝ) (hr:0 < r) (hrhalf:r ≤ 1/2)
    (inside:Metric.closedBall x r⊆disc 1) :
    ∃ q∈Ioo (r/2) r,∃ c:ℝ→E2,
      Continuous c ∧ Periodic c (2*Real.pi) ∧
      (∀ i:Fin 2,AbsolutelyContinuousOnInterval (fun t=>c t i) (-Real.pi) Real.pi) ∧
      MemLp (deriv c) 2 (volume.restrict (Icc (-Real.pi) Real.pi)) ∧
      (∫ t in Icc (-Real.pi) Real.pi,‖deriv c t‖^2) ≤
        2*((∫ y in planarCap x r,euclideanJetDensity d y)-
          (∫ y in planarCap x (r/2),euclideanJetDensity d y)) ∧
      (fun t=>f (x+q•unitCircleParameter t))=ᵐ[volume.restrict (Icc (-Real.pi) Real.pi)] c ∧
      (∀ psi:E2→ℝ,ContDiff ℝ ∞ psi → ∀ i j:Fin 2,
        IntegrableOn (fun y=>f y i*fderiv ℝ psi y (coordinateVector 2 j)+d i y j*psi y) (Metric.ball x q) ∧
        IntegrableOn (fun t=>c t i*psi (x+q•unitCircleParameter t)*unitCircleParameter t j)
          (Icc (-Real.pi) Real.pi) ∧
        (∫ y in Metric.ball x q,f y i*fderiv ℝ psi y (coordinateVector 2 j)+d i y j*psi y)=
          q*∫ t in Icc (-Real.pi) Real.pi,c t i*psi (x+q•unitCircleParameter t)*unitCircleParameter t j) := by
  classical
  obtain ⟨q,hq,c,hlocal,hcc,hcp,hca,hcd,hce,htrace⟩ :=
    paid_interior_trace minimum theta sigma lift trace x r hr hrhalf inside
  have hqpos : 0 < q := lt_trans (by positivity) hq.1
  obtain ⟨hcap,hpatch,hslice,hx⟩ := original_contained_ball_geometry_v460 x r q hr hqpos hq.2.le inside
  have htraceF : (fun t=>f (x+q•unitCircleParameter t))=ᵐ[volume.restrict (Icc (-Real.pi) Real.pi)] c := by
    filter_upwards [htrace] with t ht
    rwa [indicator_of_mem (hslice t)] at ht
  refine ⟨q,hq,c,hcc,hcp,hca,hcd,hce,htraceF,?_⟩
  intro psi hpsi i j
  have hbulk := (trace psi hpsi i j).1.mono_set
    (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall hq.2.le) |>.trans inside)
  have hcCircle : Continuous unitCircleParameter := by
    change Continuous (fun t:ℝ=>WithLp.toLp 2 ![Real.cos t,Real.sin t])
    fun_prop
  have hsliceCont : Continuous (fun t:ℝ=>x+q•unitCircleParameter t) := continuous_const.add (hcCircle.const_smul q)
  have hci : Continuous (fun t=>c t i) := (EuclideanSpace.proj (𝕜:=ℝ) i).continuous.comp hcc
  have hct : Continuous (fun t=>unitCircleParameter t j) := (EuclideanSpace.proj (𝕜:=ℝ) j).continuous.comp hcCircle
  have hbound : IntegrableOn (fun t=>c t i*psi (x+q•unitCircleParameter t)*unitCircleParameter t j)
      (Icc (-Real.pi) Real.pi) := (hci.mul (hpsi.continuous.comp hsliceCont) |>.mul hct).integrableOn_Icc
  refine ⟨hbulk,hbound,?_⟩
  have hG := hlocal psi hpsi i j
  rw [hcap,hpatch] at hG
  simp only [MeasureTheory.setIntegral_empty, add_zero] at hG
  have hflux : (∫ t in Ioo (-Real.pi) Real.pi,(disc 1).indicator (fun y=>f y i*psi y)
      (x+q•unitCircleParameter t)*unitCircleParameter t j)=
      ∫ t in Icc (-Real.pi) Real.pi,c t i*psi (x+q•unitCircleParameter t)*unitCircleParameter t j := by
    rw [←integral_Icc_eq_integral_Ioo]
    apply integral_congr_ae
    filter_upwards [htraceF] with t ht
    rw [indicator_of_mem (hslice t),ht]
  rw [hflux] at hG
  exact hG

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
