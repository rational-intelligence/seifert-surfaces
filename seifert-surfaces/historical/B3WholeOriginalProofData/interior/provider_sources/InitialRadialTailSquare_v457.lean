import InitialRadialLayerCake_v457
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates L1Independent

private theorem annular_square_tail_as_radial_indicator_v457
    (h : ℝ → ℝ) (hh : ContDiff ℝ ∞ h)
    (a z : ℝ) (ha : 0<a) (haz : a<z)
    (hhs : tsupport h ⊆ Ioo (a^2) (z^2))
    (y : ℝ) (hy : 0≤y) :
    (∫ t in y^2..z^2,h t)=
      ∫ r in Ioi y,2*r*h (r^2) ∂(volume.restrict (Ioo a z)) := by
  classical
  let w : ℝ → ℝ := fun r=>2*r*h (r^2)
  have hwzero (r : ℝ) (hr : 0≤r) (hout : r∉Ioo a z) : w r=0 := by
    have hhzero : h (r^2)=0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hm
      have hs := hhs hm
      have har : a<r := (sq_lt_sq₀ ha.le hr).mp hs.1
      have hrz : r<z := (sq_lt_sq₀ hr (ha.trans haz).le).mp hs.2
      exact hout ⟨har,hrz⟩
    simp only [w,hhzero,mul_zero]
  have hsub : (∫ r in y..z,w r)=∫ t in y^2..z^2,h t := by
    have hs := intervalIntegral.integral_comp_mul_deriv (a:=y) (b:=z)
      (f:=fun r:ℝ=>r^2) (f':=fun r:ℝ=>2*r) (g:=h)
      (fun r _=>by simpa using hasDerivAt_pow 2 r)
      (by fun_prop) hh.continuous
    simpa only [w,Function.comp_apply,mul_comm] using hs
  rw [←hsub]
  rw [Measure.restrict_restrict measurableSet_Ioi]
  have hset : Ioi y ∩ Ioo a z=Ioo (max a y) z := by
    ext r
    simp only [mem_inter_iff,mem_Ioi,mem_Ioo,max_lt_iff]
    tauto
  rw [hset]
  by_cases hyz : y≤z
  · rw [intervalIntegral.integral_of_le hyz,integral_Ioc_eq_integral_Ioo]
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioo
      (fun r hr=>⟨lt_of_le_of_lt (le_max_right a y) hr.1,hr.2⟩)
    intro r hr
    have hra : r≤a := by
      by_contra hn
      exact hr.2 ⟨max_lt (lt_of_not_ge hn) hr.1.1,hr.1.2⟩
    exact hwzero r (hy.trans hr.1.1.le) (fun hi=>not_lt_of_ge hra hi.1)
  · have hzy : z≤y := le_of_lt (lt_of_not_ge hyz)
    rw [intervalIntegral.integral_of_ge hzy]
    have he : Ioo (max a y) z=∅ := Ioo_eq_empty_of_le (hzy.trans (le_max_right a y))
    rw [he,setIntegral_empty]
    have hz : (∫ r in Ioc z y,w r)=0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro r hr
      exact hwzero r ((ha.trans haz).le.trans hr.1.le) (fun hi=>not_lt_of_ge hr.1.le hi.2)
    rw [hz,neg_zero]

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
