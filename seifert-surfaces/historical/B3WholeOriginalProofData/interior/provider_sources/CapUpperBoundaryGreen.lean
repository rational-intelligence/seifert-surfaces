import CapTrueArcIntegral
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
open SeifertSurfaces.AppendixACoordinates L1Independent
set_option maxHeartbeats 0
set_option maxRecDepth 10000

def capUpperFlux (s : ℝ) (b : ℝ→E2) (psi : E2→ℝ) (i j : Fin 2) (y : ℝ) : ℝ :=
  b (s+Real.arcsin y) i * psi (capCoordinateEquiv s (capLensUpper y,y)) *
    (unitCircleParameter s j-deriv capLensUpper y * rotateQuarter (unitCircleParameter s) j)

theorem cap_upper_flux_as_substitution (s q y : ℝ) (hq : 0<q) (hq1 : q≤1/2)
    (hy : y∈Icc (-capLensReach q) (capLensReach q)) (b : ℝ→E2) (psi : E2→ℝ) (i j : Fin 2) :
    capUpperFlux s b psi i j y =
      (b (s+Real.arcsin y) i * psi (unitCircleParameter (s+Real.arcsin y)) *
        unitCircleParameter (s+Real.arcsin y) j) * (1/Real.sqrt (1-y^2)) := by
  have hf := cap_upper_flux_coordinate s q y hq hq1 hy j
  have hs : Real.sqrt (1-y^2)≠0 := ne_of_gt (Real.sqrt_pos.mpr (cap_transverse_interval_bounds q y hq hq1 hy).2.1)
  unfold capUpperFlux
  rw [cap_upper_curve s q y hq hq1 hy]
  rw [← hf]
  field_simp

theorem cap_upper_flux_continuousOn (s q : ℝ) (hq : 0<q) (hq1 : q≤1/2)
    (b : ℝ→E2) (hb : Continuous b) (psi : E2→ℝ) (hpsi : Continuous psi) (i j : Fin 2) :
    ContinuousOn (capUpperFlux s b psi i j) (Icc (-capLensReach q) (capLensReach q)) := by
  have hc : Continuous (fun t => b t i * psi (unitCircleParameter t) * unitCircleParameter t j) :=
    (((EuclideanSpace.proj (𝕜:=ℝ) i).continuous.comp hb).mul (hpsi.comp circle_contDiff.continuous)).mul
      ((EuclideanSpace.proj (𝕜:=ℝ) j).continuous.comp circle_contDiff.continuous)
  have hp : ContinuousOn (fun y:ℝ => 1/Real.sqrt (1-y^2)) (Icc (-capLensReach q) (capLensReach q)) := by
    apply continuousOn_const.div (continuous_const.sub (continuous_id.pow 2)).sqrt.continuousOn
    intro y hy
    exact ne_of_gt (Real.sqrt_pos.mpr (cap_transverse_interval_bounds q y hq hq1 hy).2.1)
  have hθ : Continuous (fun y:ℝ => s+Real.arcsin y) := continuous_const.add Real.continuous_arcsin
  apply ((hc.comp hθ).continuousOn.mul hp).congr
  intro y hy
  exact cap_upper_flux_as_substitution s q y hq hq1 hy b psi i j

theorem cap_upper_flux_integral (s q : ℝ) (hq : 0<q) (hq1 : q≤1/2)
    (b : ℝ→E2) (hb : Continuous b) (psi : E2→ℝ) (hpsi : Continuous psi) (i j : Fin 2) :
    (∫ y in Icc (-capLensReach q) (capLensReach q), capUpperFlux s b psi i j y) =
      ∫ t in Icc (s-2*Real.arcsin (q/2)) (s+2*Real.arcsin (q/2)),
        b t i * psi (unitCircleParameter t) * unitCircleParameter t j := by
  let V := capLensReach q
  let θ := fun y : ℝ => s+Real.arcsin y
  let θ' := fun y : ℝ => 1/Real.sqrt (1-y^2)
  let g := fun t => b t i * psi (unitCircleParameter t) * unitCircleParameter t j
  have hV := cap_lens_reach q hq hq1
  have hab : -V≤V := by dsimp [V];linarith [hV.1]
  have hp : ContinuousOn θ' (Icc (-V) V) := by
    apply continuousOn_const.div (continuous_const.sub (continuous_id.pow 2)).sqrt.continuousOn
    intro y hy
    exact ne_of_gt (Real.sqrt_pos.mpr (cap_transverse_interval_bounds q y hq hq1 hy).2.1)
  have hd (y : ℝ) (hy : y∈uIcc (-V) V) : HasDerivAt θ (θ' y) y := by
    rw [uIcc_of_le hab] at hy
    have h1 := (cap_transverse_interval_bounds q y hq hq1 hy).1
    exact (Real.hasDerivAt_arcsin (ne_of_gt (abs_lt.mp h1).1) (ne_of_lt (abs_lt.mp h1).2)).const_add s
  have hg : Continuous g :=
    (((EuclideanSpace.proj (𝕜:=ℝ) i).continuous.comp hb).mul (hpsi.comp circle_contDiff.continuous)).mul
      ((EuclideanSpace.proj (𝕜:=ℝ) j).continuous.comp circle_contDiff.continuous)
  have hsub := intervalIntegral.integral_comp_mul_deriv hd (by rwa [uIcc_of_le hab]) hg
  have hend : Real.arcsin V=2*Real.arcsin (q/2) := cap_arcsin_tangent_endpoint q hq hq1
  have he := cap_arcsin_bounds q hq hq1
  have hθa : θ (-V)=s-2*Real.arcsin (q/2) := by dsimp [θ];rw [Real.arcsin_neg,hend];ring
  have hθb : θ V=s+2*Real.arcsin (q/2) := by dsimp [θ];rw [hend]
  rw [intervalIntegral.integral_of_le hab,← integral_Icc_eq_integral_Ioc,hθa,hθb,
    intervalIntegral.integral_of_le (by linarith [he.1]),← integral_Icc_eq_integral_Ioc] at hsub
  calc
    _ = ∫ y in Icc (-V) V, (g (θ y))*θ' y := setIntegral_congr_fun measurableSet_Icc
      (fun y hy => cap_upper_flux_as_substitution s q y hq hq1 hy b psi i j)
    _ = _ := hsub

theorem cap_true_boundary_to_upper (s q : ℝ) (hq : 0<q) (hq1 : q≤1/2)
    (B b : ℝ→E2) (hBp : Periodic B (2*Real.pi)) (hb : Continuous b)
    (hagree : ∀t∈Icc (s-2*Real.arcsin (q/2)) (s+2*Real.arcsin (q/2)), B t=b t)
    (psi : E2→ℝ) (hpsi : Continuous psi) (i j : Fin 2) :
    (∫ t in circlePatch (unitCircleParameter s) q, B t i * psi (unitCircleParameter t) * unitCircleParameter t j) =
      ∫ y in Icc (-capLensReach q) (capLensReach q), capUpperFlux s b psi i j y := by
  have hp : Periodic (fun t => B t i * psi (unitCircleParameter t) * unitCircleParameter t j) (2*Real.pi) := by
    intro t
    dsimp only
    rw [hBp t,cap_circle_periodic t]
  rw [cap_circlePatch_integral s q hq hq1 _ hp,cap_upper_flux_integral s q hq hq1 b hb psi hpsi i j]
  exact setIntegral_congr_fun measurableSet_Icc (fun t ht => by rw [hagree t ht])

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
