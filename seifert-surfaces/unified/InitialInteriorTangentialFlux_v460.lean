import InitialWeightedTrace_v411

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates L1Independent
open DirectMethod.CourantAnnularBoundaryA

local macro "paid_product_rows" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialGreenProduct_v411 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.native_H1_smooth_product_rows_L2_v411)⟩

local macro "paid_product_green" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialGreenProduct_v411 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.native_green_smooth_product_v411)⟩

private theorem original_interior_weighted_tangential_flux_ae_v460
    (f : E2 → E2) (d : Fin 2 → E2 → E2) (b : ℝ → E2)
    (H1 : ∀ i,H1On (disc 1) (fun x=>f x i) (d i))
    (green : HasGreenBoundaryTrace f d b)
    (x:E2) (a z:ℝ) (ha:0 < a) (haz:a < z) (hz:z < 1)
    (inside : Metric.closedBall x z ⊆ disc 1)
    (phi:E2→ℝ) (hphi:ContDiff ℝ ∞ phi) :
    let grad : E2 → E2 := fun y=>(EuclideanSpace.equiv (Fin 2) ℝ).symm
      (fun j=>fderiv ℝ phi y (coordinateVector 2 j))
    let dp : Fin 2 → E2 → E2 := fun i y=>phi y•d i y+f y i•grad y
    let J : E2 → E2 := fun v=>(EuclideanSpace.equiv (Fin 2) ℝ).symm ![-v 1,v 0]
    ∀ᵐ q ∂volume.restrict (Ioo a z),∀ i : Fin 2,
      q*(∫ t in Ioo (-Real.pi) Real.pi,
        inner ℝ ((disc 1).indicator (dp i) (x+q•unitCircleParameter t)) (J (unitCircleParameter t)))=0 := by
  classical
  dsimp only
  let grad : E2 → E2 := fun y=>(EuclideanSpace.equiv (Fin 2) ℝ).symm
    (fun j=>fderiv ℝ phi y (coordinateVector 2 j))
  let dp : Fin 2 → E2 → E2 := fun i y=>phi y•d i y+f y i•grad y
  let bp : ℝ → E2 := fun t=>phi (unitCircleParameter t)•b t
  let J : E2 → E2 := fun v=>(EuclideanSpace.equiv (Fin 2) ℝ).symm ![-v 1,v 0]
  let F : Fin 2 → ℝ → ℝ := fun i q=>q*(∫ t in Ioo (-Real.pi) Real.pi,
    inner ℝ ((disc 1).indicator (dp i) (x+q•unitCircleParameter t)) (J (unitCircleParameter t)))
  have hrows : ∀ i,MemLp (dp i) 2 (volume.restrict (disc 1)) :=
    paid_product_rows f d H1 phi hphi
  have hgreen : HasGreenBoundaryTrace (fun y=>phi y•f y) dp bp :=
    paid_product_green f d b green phi hphi
  obtain ⟨_,_,_,_,_,_,_,hF,htests⟩ := CourantAnalyticB.native_translated_polar_rows dp
    (fun i=>(hrows i).aestronglyMeasurable) hrows x a z ha haz hz
  dsimp only at hF htests
  apply ae_all_iff.mpr
  intro i
  have hv : LocallyIntegrableOn (F i) (Ioo a z) volume := (hF i).2.locallyIntegrableOn
  apply (CourantAnalyticB.annular_square_radius_tests_detect a z ha haz (F i) hv).2
  intro h hh hhc hhs
  let rho2 : E2 → ℝ := fun y=>(y 0-x 0)^2+(y 1-x 1)^2
  let chi : Fin 2 → E2 → ℝ := fun j y=>![-(y 1-x 1)*h (rho2 y),(y 0-x 0)*h (rho2 y)] j
  have hfield := smooth_squared_radius_rotation_field x h hh
  have hpair := native_green_divergence_free_pairing (fun y=>phi y•f y) dp bp
    hgreen chi hfield.1 hfield.2.1 i
  have hcircleOutside (t:ℝ) : z < ‖unitCircleParameter t-x‖ := by
    apply lt_of_not_ge
    intro hle
    have hin := inside (show unitCircleParameter t∈Metric.closedBall x z from by
      simpa only [Metric.mem_closedBall,dist_eq_norm] using hle)
    have hnorm : ‖unitCircleParameter t‖^2=1 := by
      rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two]
      exact Real.cos_sq_add_sin_sq t
    have hlt : ‖unitCircleParameter t‖ < 1 := by
      simpa only [disc,Metric.mem_ball,dist_zero_right] using hin
    nlinarith [norm_nonneg (unitCircleParameter t)]
  have hchiZero (t:ℝ) (j:Fin 2) : chi j (unitCircleParameter t)=0 := by
    have hout : rho2 (unitCircleParameter t)∉tsupport h := by
      intro hin
      have hs := hhs hin
      have he : rho2 (unitCircleParameter t)=‖unitCircleParameter t-x‖^2 := hfield.2.2.1 _
      rw [he] at hs
      nlinarith only [hs.2,hcircleOutside t,lt_trans ha haz,norm_nonneg (unitCircleParameter t-x)]
    have hzero := image_eq_zero_of_notMem_tsupport hout
    fin_cases j <;> simp [chi,hzero]
  have hbzero : (∫ t in Icc 0 (2*Real.pi),bp t i*
      (chi 0 (unitCircleParameter t)*unitCircleParameter t 0+
        chi 1 (unitCircleParameter t)*unitCircleParameter t 1))=0 := by
    simp only [hchiZero,zero_mul,zero_add,mul_zero,integral_zero]
  have hbulk := htests h hh hhc hhs i
  change (∫ q in Ioo a z,q*h (q^2)*F i q)=0
  rw [←hbulk.2.2]
  change (∫ y in disc 1,dp i y 0*chi 0 y+dp i y 1*chi 1 y)=0
  exact hpair.2.2.trans hbzero

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
