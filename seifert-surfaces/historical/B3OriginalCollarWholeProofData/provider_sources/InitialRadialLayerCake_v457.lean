import InitialRadialNormalGreen_v457
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates L1Independent

/- Finite signed layer-cake identity. This is the Fubini step for cap bulk and
true-boundary terms; no positivity of the radial test is required. -/
private theorem radial_signed_layer_cake_v457
    {X : Type*} [MeasurableSpace X] (mu : Measure X) [SFinite mu]
    (nu : Measure ℝ) [SFinite nu]
    (rho : X → ℝ) (hrho : Measurable rho)
    (g : X → ℝ) (hg : Integrable g mu)
    (w : ℝ → ℝ) (hw : Integrable w nu) :
    Integrable (fun x => g x*(∫ r in Ioi (rho x),w r ∂nu)) mu ∧
    Integrable (fun r => w r*(∫ x in {x | rho x<r},g x ∂mu)) nu ∧
    (∫ x,g x*(∫ r in Ioi (rho x),w r ∂nu) ∂mu)=
      ∫ r,w r*(∫ x in {x | rho x<r},g x ∂mu) ∂nu := by
  classical
  let S : Set (X×ℝ) := {p | rho p.1<p.2}
  let K : X → ℝ → ℝ := fun x r=>S.indicator (fun p:X×ℝ=>g p.1*w p.2) (x,r)
  have hS : MeasurableSet S := measurableSet_lt (hrho.comp measurable_fst) measurable_snd
  have hK : Integrable (uncurry K) (mu.prod nu) := (hg.mul_prod hw).indicator hS
  have hright (x : X) : (∫ r,K x r ∂nu)=g x*(∫ r in Ioi (rho x),w r ∂nu) := by
    have he : K x=(fun r=>g x*(Ioi (rho x)).indicator w r) := by
      funext r
      by_cases h:rho x<r <;> simp [K,S,h]
    rw [he,integral_const_mul,integral_indicator measurableSet_Ioi]
  have hleft (r : ℝ) : (∫ x,K x r ∂mu)=w r*(∫ x in {x | rho x<r},g x ∂mu) := by
    have he : (fun x=>K x r)=(fun x=>({x | rho x<r}).indicator g x*w r) := by
      funext x
      by_cases h:rho x<r <;> simp [K,S,h]
    rw [he,integral_mul_const,integral_indicator (measurableSet_lt hrho measurable_const),mul_comm]
  have hI := hK.integral_prod_left
  have hJ := hK.integral_prod_right
  change Integrable (fun x=>∫ r,K x r ∂nu) mu at hI
  change Integrable (fun r=>∫ x,K x r ∂mu) nu at hJ
  have hI' : Integrable (fun x=>g x*(∫ r in Ioi (rho x),w r ∂nu)) mu := by
    simpa only [hright] using hI
  have hJ' : Integrable (fun r=>w r*(∫ x in {x | rho x<r},g x ∂mu)) nu := by
    simpa only [hleft] using hJ
  refine ⟨hI',hJ',?_⟩
  simp only [←hright,←hleft]
  exact integral_integral_swap hK

private theorem smooth_radial_tail_v457
    (h : ℝ → ℝ) (hh : ContDiff ℝ ∞ h) (z : ℝ) :
    ContDiff ℝ ∞ (fun s=>∫ r in s..z,h r) ∧
      ∀ s,deriv (fun x=>∫ r in x..z,h r) s = -h s := by
  have hD (s : ℝ) : HasDerivAt (fun x=>∫ r in x..z,h r) (-h s) s :=
    intervalIntegral.integral_hasDerivAt_left (hh.continuous.intervalIntegrable _ _)
      hh.continuous.stronglyMeasurable.stronglyMeasurableAtFilter
      hh.continuous.continuousAt
  have he : deriv (fun x=>∫ r in x..z,h r) = -h := funext (fun s=>(hD s).deriv)
  refine ⟨contDiff_infty_iff_deriv.mpr ⟨fun s=>(hD s).differentiableAt,?_⟩,fun s=>(hD s).deriv⟩
  rw [he]
  exact hh.neg

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
