import InitialInteriorBallExtension_v460
import InitialActualCapMinimality_v460

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates L1Independent

local macro "paid_extension" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialInteriorBallExtension_v460 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.original_interior_ball_native_extension_v460)⟩

local macro "paid_comparison" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialActualCapMinimality_v460 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.original_minimizer_actual_cap_comparison_v460)⟩

local macro "paid_geometry" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialInteriorBallGreen_v460 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.original_contained_ball_geometry_v460)⟩

private theorem original_minimizer_contained_ball_hole_filling_v460
    (R : ℝ) (A : E2 → Mat2) (G : InverseMetricData R A)
    (Ω : SmoothFlatJordanDomain R) (M : E2 → Mat2)
    (agreement : ∀ x∈closure Ω.domain,M x=inverseMetric A x)
    (symmetric : SymmetricOn M univ) (elliptic : UniformEllipticOn M univ)
    (holder : ∀ i j,∃ C:ℝ≥0,HolderWith C G.alpha (fun x=>M x i j))
    (identity_at_infinity : ∃ L:ℝ,0 < L ∧ ∀ x:E2,L ≤ ‖x‖ → M x=1)
    (f : E2 → E2) (d : Fin 2 → E2 → E2)
    (minimum : SimultaneousMetricMinimum Ω M f d) :
    ∃ K : ℝ, 0 < K ∧
      ∀ x∈closedDisc 1,∀ r:ℝ,0 < r → r ≤ 1/2 →
        Metric.closedBall x r⊆disc 1 →
        (∫ z in planarCap x (r/2),euclideanJetDensity d z) ≤
          K*((∫ z in planarCap x r,euclideanJetDensity d z)-
            (∫ z in planarCap x (r/2),euclideanJetDensity d z)) := by
  classical
  obtain ⟨ell,Lambda,hell,hLambda,hEll⟩ := elliptic
  let C : ℝ := ((2*Real.pi)^2+1)/2
  let K : ℝ := (Lambda/ell)*C*2
  have hC : 0 < C := by dsimp [C]; positivity
  have hratio : 0 < Lambda/ell := div_pos hLambda hell
  refine ⟨K,by dsimp [K];positivity,?_⟩
  intro x hx r hr hrhalf inside
  obtain ⟨theta,sigma,lift,trace⟩ := minimum.admissible.2
  obtain ⟨q,hq,c,h,dh,hcc,hcp,hca,hcd,hce,htrace,hh1,henergy,hgreen,hseam⟩ :=
    paid_extension minimum theta sigma lift trace x r hr hrhalf inside
  have hqpos : 0 < q := lt_trans (by positivity) hq.1
  obtain ⟨hcap,hpatch,hslice,hx'⟩ := paid_geometry x r q hr hqpos hq.2.le inside
  have hhcap : ∀ i,H1On (planarCap x q) (fun z=>h z i) (dh i) := by
    simpa only [hcap] using hh1
  obtain ⟨hpH,hpG,hpA,hcompare⟩ := paid_comparison R A G Ω M agreement symmetric
    ⟨ell,Lambda,hell,hLambda,hEll⟩ holder identity_at_infinity f d minimum
    theta theta sigma lift trace lift x hx q hqpos h dh hhcap
    (by intro t ht hout; rfl) hseam ell Lambda hell hLambda
    (fun y p=>hEll y (mem_univ _) p)
  have hi : IntegrableOn (euclideanJetDensity d) (disc 1) := by
    apply integrable_finsetSum
    intro i _
    exact (minimum.admissible.1 i).2.2.norm.integrable_sq
  have hmono : (∫ z in planarCap x (r/2),euclideanJetDensity d z) ≤
      ∫ z in planarCap x q,euclideanJetDensity d z := by
    apply setIntegral_mono_set (hi.mono_set inter_subset_left)
      (Eventually.of_forall fun z=>Finset.sum_nonneg fun i _=>sq_nonneg _)
    exact Eventually.of_forall fun z hz=>
      ⟨hz.1,Metric.ball_subset_ball hq.1.le hz.2⟩
  rw [hcap] at hcompare
  calc
    _ ≤ ∫ z in Metric.ball x q,euclideanJetDensity d z := by simpa only [hcap] using hmono
    _ ≤ (Lambda/ell)*∫ z in Metric.ball x q,euclideanJetDensity dh z := hcompare
    _ ≤ (Lambda/ell)*(C*∫ t in Icc (-Real.pi) Real.pi,‖deriv c t‖^2) :=
      mul_le_mul_of_nonneg_left henergy hratio.le
    _ ≤ (Lambda/ell)*(C*(2*((∫ z in planarCap x r,euclideanJetDensity d z)-
        (∫ z in planarCap x (r/2),euclideanJetDensity d z)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hce hC.le) hratio.le
    _ = _ := by dsimp [K]; ring

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
