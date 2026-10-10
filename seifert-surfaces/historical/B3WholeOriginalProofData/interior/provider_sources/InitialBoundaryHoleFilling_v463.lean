import InitialInteriorHoleFilling_v460
import InitialCapH1ExtensionContract_v445

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates L1Independent

local macro "paid_full_extension" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialCapH1ExtensionContract_v445 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.uniform_ball_and_boundary_cap_H1_extension_v445)⟩
local macro "paid_data" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialOriginalBoundaryComparisonData_v460 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.original_boundary_same_radius_comparison_data_v460)⟩
local macro "paid_seam" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialActualCapSeam_v460 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.actual_cap_green_relative_seam_v460)⟩
local macro "paid_comparison" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialActualCapMinimality_v460 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.original_minimizer_actual_cap_comparison_v460)⟩

private theorem original_minimizer_boundary_cap_hole_filling_v463
    (R : ℝ) (A : E2 → Mat2) (G : InverseMetricData R A)
    (Ω : SmoothFlatJordanDomain R) (M : E2 → Mat2)
    (agreement : ∀ x∈closure Ω.domain,M x=inverseMetric A x)
    (symmetric : SymmetricOn M univ) (elliptic : UniformEllipticOn M univ)
    (holder : ∀ i j,∃ C:ℝ≥0,HolderWith C G.alpha (fun x=>M x i j))
    (identity_at_infinity : ∃ L:ℝ,0 < L ∧ ∀ x:E2,L ≤ ‖x‖ → M x=1)
    (f : E2 → E2) (d : Fin 2 → E2 → E2)
    (minimum : SimultaneousMetricMinimum Ω M f d) :
    ∃ K rho : ℝ, 0 < K ∧ 0 < rho ∧ rho ≤ 1/2 ∧
      ∀ s r : ℝ,0 < r → r ≤ rho →
        (∫ z in planarCap (unitCircleParameter s) (r/2),euclideanJetDensity d z) ≤
          K*((∫ z in planarCap (unitCircleParameter s) r,euclideanJetDensity d z)-
            (∫ z in planarCap (unitCircleParameter s) (r/2),euclideanJetDensity d z)) := by
  classical
  obtain ⟨ell,Lambda,hell,hLambda,hEll⟩ := elliptic
  obtain ⟨C,hC,hball,hcapExtension⟩ := paid_full_extension
  obtain ⟨theta,sigma,lift,trace⟩ := minimum.admissible.2
  obtain ⟨B,rho,hB,hrho,hrhohalf,hdata⟩ := paid_data minimum theta sigma lift trace
  let K : ℝ := (Lambda/ell)*C*B
  have hratio : 0 < Lambda/ell := div_pos hLambda hell
  refine ⟨K,rho,by dsimp [K];positivity,hrho,hrhohalf,?_⟩
  intro s r hr hrr
  obtain ⟨q,hq,theta',eta,c,hnewlift,hoff,heta,hcurve,htrue,hlocal,hpath⟩ := hdata s r hr hrr
  dsimp only at hpath
  rcases hpath with ⟨haa,hcc,hca,hcb,hac,hL2,htrace,hbudget⟩
  have hqpos : 0 < q := lt_trans (by positivity) hq.1
  have hqhalf : q ≤ 1/2 := (hq.2.le.trans hrr).trans hrhohalf
  have hnewC : Continuous (liftedBoundaryValue Ω theta') :=
    Ω.boundary.smooth.continuous.comp hnewlift.2.1
  have hnewP : Periodic (liftedBoundaryValue Ω theta') (2*Real.pi) := by
    intro t
    change Ω.boundary.gamma (theta' (t+2*Real.pi))=Ω.boundary.gamma (theta' t)
    rw [hnewlift.2.2.2]
    rcases hnewlift.1 with hsig | hsig
    · simpa only [hsig,one_mul] using Ω.boundary.periodic (theta' t)
    · simpa only [hsig,neg_one_mul,sub_eq_add_neg] using Ω.boundary.periodic.sub_eq (theta' t)
  obtain ⟨h,dh,hh1,henergy,hgreen⟩ :=
    hcapExtension s q hqpos hqhalf c (liftedBoundaryValue Ω theta')
      (fun t=>Ω.boundary.gamma (eta t)) hcc hac hL2 hnewC hnewP hcurve htrue hca hcb
  have hseam := paid_seam f h d dh (liftedBoundaryValue Ω theta)
    (liftedBoundaryValue Ω theta') c trace s q hqpos hqhalf htrace hlocal hgreen
  have hcenter : unitCircleParameter s∈closedDisc 1 := by
    have hn : ‖unitCircleParameter s‖^2=1 := by
      rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two]
      exact Real.cos_sq_add_sin_sq s
    have he : ‖unitCircleParameter s‖=1 := by nlinarith [norm_nonneg (unitCircleParameter s)]
    simpa only [closedDisc,Metric.mem_closedBall,dist_zero_right,he] using (le_refl (1:ℝ))
  obtain ⟨hpH,hpG,hpA,hcompare⟩ := paid_comparison R A G Ω M agreement symmetric
    ⟨ell,Lambda,hell,hLambda,hEll⟩ holder identity_at_infinity f d minimum
    theta theta' sigma lift trace hnewlift (unitCircleParameter s) hcenter q hqpos h dh hh1
    (fun t ht hout=>hoff t hout) hseam ell Lambda hell hLambda
    (fun y p=>hEll y (mem_univ _) p)
  have hi : IntegrableOn (euclideanJetDensity d) (disc 1) := by
    apply integrable_finsetSum
    intro i _
    exact (minimum.admissible.1 i).2.2.norm.integrable_sq
  have hmono : (∫ z in planarCap (unitCircleParameter s) (r/2),euclideanJetDensity d z) ≤
      ∫ z in planarCap (unitCircleParameter s) q,euclideanJetDensity d z := by
    apply setIntegral_mono_set (hi.mono_set inter_subset_left)
      (Eventually.of_forall fun z=>Finset.sum_nonneg fun i _=>sq_nonneg _)
    exact Eventually.of_forall fun z hz=>⟨hz.1,Metric.ball_subset_ball hq.1.le hz.2⟩
  calc
    _ ≤ ∫ z in planarCap (unitCircleParameter s) q,euclideanJetDensity d z := hmono
    _ ≤ (Lambda/ell)*∫ z in planarCap (unitCircleParameter s) q,euclideanJetDensity dh z := hcompare
    _ ≤ (Lambda/ell)*(C*((∫ t in Icc (s+Real.pi/2+Real.arcsin (q/2))
        (s+3*Real.pi/2-Real.arcsin (q/2)),‖deriv c t‖^2)+
        q*∫ t in Icc (s-2*Real.arcsin (q/2)) (s+2*Real.arcsin (q/2)),
          ‖deriv (fun t=>Ω.boundary.gamma (eta t)) t‖^2)) :=
      mul_le_mul_of_nonneg_left henergy hratio.le
    _ ≤ (Lambda/ell)*(C*(B*((∫ z in planarCap (unitCircleParameter s) r,euclideanJetDensity d z)-
        (∫ z in planarCap (unitCircleParameter s) (r/2),euclideanJetDensity d z)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbudget hC.le) hratio.le
    _ = _ := by dsimp [K];ring

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
