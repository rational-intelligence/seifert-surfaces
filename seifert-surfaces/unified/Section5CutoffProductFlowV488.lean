import Section5CommonLeafDataV488
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
open Set Topology Function
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
open SeifertSurfaces.Foundations
noncomputable section

def longitudeRadialCutoff : ContDiffBump (0 : ℝ) where
  rIn := 1/4
  rOut := 1/2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

theorem longitude_radial_cutoff_zero (r : ℝ) (hr : 1/2 ≤ r) :
    longitudeRadialCutoff r = 0 := by
  apply longitudeRadialCutoff.zero_of_le_dist
  change (1/2:ℝ) ≤ dist r 0
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (by linarith)]
  exact hr

theorem longitude_radial_cutoff_one : longitudeRadialCutoff (0 : ℝ) = 1 := by
  apply longitudeRadialCutoff.one_of_mem_closedBall
  exact Metric.mem_closedBall_self longitudeRadialCutoff.rIn_pos.le

def longitudeProductFlow : Flow ℝ ((Circle × Circle) × Time) where
  toFun t p := ((longitudeLabelFlow (longitudeRadialCutoff (p.2 : ℝ) * t) p.1.1,p.1.2),p.2)
  cont' := ((longitudeLabelFlow.continuous
    (((longitudeRadialCutoff.contDiff (n:=(⊤ : ℕ∞))).continuous.comp
      (continuous_subtype_val.comp continuous_snd.snd)).mul continuous_fst)
    continuous_snd.fst.fst).prodMk continuous_snd.fst.snd).prodMk continuous_snd.snd
  map_add' t u p := by
    simp only [mul_add,Flow.map_add]
  map_zero' p := by
    simp only [mul_zero,Flow.map_zero_apply]

theorem longitude_product_flow_radial (t : ℝ) (p : (Circle × Circle) × Time) :
    (longitudeProductFlow t p).2 = p.2 := rfl

theorem longitude_product_flow_boundary (t : ℝ) (p : Circle × Circle) :
    longitudeProductFlow t (p,0) = ((longitudeLabelFlow t p.1,p.2),0) := by
  change ((longitudeLabelFlow (longitudeRadialCutoff 0*t) p.1,p.2),0) = _
  rw [longitude_radial_cutoff_one,one_mul]

theorem longitude_product_flow_fixed (t : ℝ) (p : (Circle × Circle) × Time)
    (hp : 1/2 ≤ (p.2 : ℝ)) : longitudeProductFlow t p = p := by
  change ((longitudeLabelFlow (longitudeRadialCutoff (p.2 : ℝ)*t) p.1.1,p.1.2),p.2) = p
  rw [longitude_radial_cutoff_zero _ hp,zero_mul,Flow.map_zero_apply]

theorem longitude_product_flow_smooth :
    ContMDiff (𝓘(ℝ).prod (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)))
      (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) ∞
      (fun p : ℝ × ((Circle × Circle) × Time) => longitudeProductFlow p.1 p.2) := by
  have hr : ContMDiff (𝓘(ℝ).prod (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1))) 𝓘(ℝ) ∞
      (fun p : ℝ × ((Circle × Circle) × Time) => (p.2.2 : ℝ)) :=
    contMDiff_subtypeVal_Icc.comp (contMDiff_snd.comp contMDiff_snd)
  have ht := (longitudeRadialCutoff.contDiff.contMDiff.comp hr).mul contMDiff_fst
  exact ((longitude_label_flow_smooth.comp (ht.prodMk
      (contMDiff_fst.comp (contMDiff_fst.comp contMDiff_snd)))).prodMk
    (contMDiff_snd.comp (contMDiff_fst.comp contMDiff_snd))).prodMk
      (contMDiff_snd.comp contMDiff_snd)

#print axioms longitude_product_flow_smooth
end
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
