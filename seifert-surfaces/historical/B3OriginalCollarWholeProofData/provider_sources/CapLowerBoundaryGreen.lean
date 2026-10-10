import CapArtificialRange
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
open SeifertSurfaces.AppendixACoordinates L1Independent
set_option maxHeartbeats 0
set_option maxRecDepth 10000

def capLowerFlux (s q : ℝ) (b : ℝ→E2) (psi : E2→ℝ) (i j : Fin 2) (y : ℝ) : ℝ :=
  b (s+Real.arcsin y) i * psi (capCoordinateEquiv s (capLensLower q y,y)) *
    (unitCircleParameter s j-deriv (capLensLower q) y * rotateQuarter (unitCircleParameter s) j)

theorem cap_lower_flux_continuousOn (s q : ℝ) (hq : 0<q) (hq1 : q≤1/2)
    (b : ℝ→E2) (hb : Continuous b) (psi : E2→ℝ) (hpsi : Continuous psi) (i j : Fin 2) :
    ContinuousOn (capLowerFlux s q b psi i j) (Icc (-capLensReach q) (capLensReach q)) := by
  have hβ : Continuous (fun y:ℝ => b (s+Real.arcsin y) i) :=
    (EuclideanSpace.proj (𝕜:=ℝ) i).continuous.comp (hb.comp (continuous_const.add Real.continuous_arcsin))
  have hL : Continuous (capLensLower q) := continuous_const.sub (continuous_const.sub (continuous_id.pow 2)).sqrt
  have hcurve : Continuous (fun y:ℝ => capCoordinateEquiv s (capLensLower q y,y)) :=
    (hL.smul continuous_const).add (continuous_id.smul continuous_const)
  have hfrac : ContinuousOn (fun y:ℝ => y/Real.sqrt (q^2-y^2)) (Icc (-capLensReach q) (capLensReach q)) := by
    apply continuousOn_id.div (continuous_const.sub (continuous_id.pow 2)).sqrt.continuousOn
    intro y hy
    exact ne_of_gt (Real.sqrt_pos.mpr (cap_lens_lower_radicand_pos q y hq hq1 hy))
  have hfac : ContinuousOn (fun y:ℝ => unitCircleParameter s j-y/Real.sqrt (q^2-y^2)*rotateQuarter (unitCircleParameter s) j)
      (Icc (-capLensReach q) (capLensReach q)) := continuousOn_const.sub (hfrac.mul continuousOn_const)
  apply ((hβ.mul (hpsi.comp hcurve)).continuousOn.mul hfac).congr
  intro y hy
  unfold capLowerFlux
  rw [(cap_lens_lower_deriv q y hq hq1 hy).deriv]
  rfl

theorem cap_lower_flux_pullback (s q t : ℝ) (hq : 0<q) (hq1 : q≤1/2)
    (ht : t∈Icc (s+Real.pi/2+Real.arcsin (q/2)) (s+3*Real.pi/2-Real.arcsin (q/2)))
    (b : ℝ→E2) (psi : E2→ℝ) (i j : Fin 2) :
    capLowerFlux s q b psi i j (q*Real.sin (t-s)) * (q*Real.cos (t-s)) =
      q*(b (capArtificialAngle s q t) i * psi (unitCircleParameter s+q • unitCircleParameter t) * unitCircleParameter t j) := by
  have hf := cap_lower_flux_coordinate s q t hq hq1 ht j
  unfold capLowerFlux
  rw [cap_lower_curve s q t hq ht]
  unfold capArtificialAngle
  linear_combination b (s+Real.arcsin (q*Real.sin (t-s))) i * psi (unitCircleParameter s+q • unitCircleParameter t) * hf

theorem cap_artificial_boundary_to_lower (s q : ℝ) (hq : 0<q) (hq1 : q≤1/2)
    (b : ℝ→E2) (hb : Continuous b) (psi : E2→ℝ) (hpsi : Continuous psi) (i j : Fin 2) :
    q*(∫ t in Icc (s+Real.pi/2+Real.arcsin (q/2)) (s+3*Real.pi/2-Real.arcsin (q/2)),
      b (capArtificialAngle s q t) i * psi (unitCircleParameter s+q • unitCircleParameter t) * unitCircleParameter t j) =
      -(∫ y in Icc (-capLensReach q) (capLensReach q), capLowerFlux s q b psi i j y) := by
  let a := s+Real.pi/2+Real.arcsin (q/2)
  let d := s+3*Real.pi/2-Real.arcsin (q/2)
  let y := fun t:ℝ => q*Real.sin (t-s)
  let y' := fun t:ℝ => q*Real.cos (t-s)
  have he := cap_arcsin_bounds q hq hq1
  have had : a≤d := by dsimp [a,d];linarith [he.2.1,Real.pi_pos]
  have hdd (t:ℝ) (_ht : t∈uIcc a d) : HasDerivAt y (y' t) t := by
    simpa [y,y',Function.comp_def] using
      (((Real.hasDerivAt_sin (t-s)).comp t ((hasDerivAt_id t).sub_const s)).const_mul q)
  have hdp : Continuous y' := continuous_const.mul (Real.continuous_cos.comp (continuous_id.sub continuous_const))
  have hfc := cap_lower_flux_continuousOn s q hq hq1 b hb psi hpsi i j
  have himage : y '' uIcc a d ⊆ Icc (-capLensReach q) (capLensReach q) := by
    rintro _ ⟨t,ht,rfl⟩
    rw [uIcc_of_le had] at ht
    exact cap_artificial_transverse_range s q t hq hq1 ht
  have hsub := intervalIntegral.integral_comp_mul_deriv' hdd hdp.continuousOn (hfc.mono himage)
  have hend := cap_artificial_transverse_endpoints s q hq hq1
  have hya : y a=capLensReach q := hend.1
  have hyd : y d= -capLensReach q := hend.2
  have hV : -capLensReach q≤capLensReach q := by linarith [cap_lens_reach q hq hq1 |>.1]
  rw [intervalIntegral.integral_of_le had,← integral_Icc_eq_integral_Ioc,hya,hyd,
    intervalIntegral.integral_symm,intervalIntegral.integral_of_le hV,← integral_Icc_eq_integral_Ioc] at hsub
  calc
    _ = ∫ t in Icc a d, q*(b (capArtificialAngle s q t) i * psi (unitCircleParameter s+q • unitCircleParameter t) * unitCircleParameter t j) := (integral_const_mul q _).symm
    _ = ∫ t in Icc a d, capLowerFlux s q b psi i j (y t)*y' t := setIntegral_congr_fun measurableSet_Icc
      (fun t ht => (cap_lower_flux_pullback s q t hq hq1 ht b psi i j).symm)
    _ = _ := hsub

theorem cap_artificial_boundary_integrable (s q : ℝ) (hq : 0<q) (hq1 : q≤1/2)
    (b : ℝ→E2) (hb : Continuous b) (psi : E2→ℝ) (hpsi : Continuous psi) (i j : Fin 2) :
    IntegrableOn (fun t => b (capArtificialAngle s q t) i * psi (unitCircleParameter s+q • unitCircleParameter t) * unitCircleParameter t j)
      (Icc (s+Real.pi/2+Real.arcsin (q/2)) (s+3*Real.pi/2-Real.arcsin (q/2))) := by
  apply Continuous.integrableOn_Icc
  have hcurve : Continuous (fun t:ℝ => unitCircleParameter s+q • unitCircleParameter t) :=
    continuous_const.add (circle_contDiff.continuous.const_smul q)
  exact (((EuclideanSpace.proj (𝕜:=ℝ) i).continuous.comp (hb.comp (cap_artificial_angle_smooth s q hq hq1).continuous)).mul
    (hpsi.comp hcurve)).mul
      ((EuclideanSpace.proj (𝕜:=ℝ) j).continuous.comp circle_contDiff.continuous)

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
