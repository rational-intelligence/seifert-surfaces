import ActualRelativeRadialSqueezeV765

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Topology Metric
open CompressionActualPlanarWholeDiskExtensionV756
open CompressionActualRelativeRadialSqueezeV765
noncomputable section
namespace CompressionActualRelativeRadialSqueezeHomeomorphV891

lemma squeeze_comp (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (x : Plane) :
    squeeze a (squeeze b x) = squeeze (a*b) x := by
  by_cases hx : ‖x‖ ≤ 1
  · rw [squeeze_fixed b x hx,squeeze_fixed a x hx,squeeze_fixed (a*b) x hx]
  · have hx' : 1 < ‖x‖ := lt_of_not_ge hx
    have hnb : ‖squeeze b x‖ = 1+b*(‖x‖-1) := squeeze_norm_outer b hb x hx'.le
    have hbout : 1 ≤ ‖squeeze b x‖ := by rw [hnb]; nlinarith
    have hn : ‖x‖ ≠ 0 := ne_of_gt ((by norm_num : (0:ℝ)<1).trans hx')
    have hn' : 1+b*(‖x‖-1) ≠ 0 := by nlinarith
    change (a+(1-a)/max 1 ‖squeeze b x‖) • squeeze b x =
      (a*b+(1-a*b)/max 1 ‖x‖) • x
    rw [max_eq_right hbout,max_eq_right hx'.le,hnb]
    dsimp only [squeeze]
    rw [max_eq_right hx'.le,smul_smul]
    congr 1
    field_simp
    ring

/-- The actual radial squeeze is a global homeomorphism with explicit
    inverse, so confined annular embedding stages retain global maps. -/
def squeezeHomeomorph (a : ℝ) (ha : 0 < a) : Plane ≃ₜ Plane where
  toFun := squeeze a
  invFun := squeeze (1/a)
  left_inv := by
    intro x
    rw [squeeze_comp (1/a) a (by positivity) ha,one_div_mul_cancel ha.ne',squeeze_one]
  right_inv := by
    intro x
    rw [squeeze_comp a (1/a) ha (by positivity),mul_one_div_cancel ha.ne',squeeze_one]
  continuous_toFun := squeeze_joint_continuous.comp (continuous_const.prodMk continuous_id)
  continuous_invFun := squeeze_joint_continuous.comp (continuous_const.prodMk continuous_id)

#print axioms squeeze_comp
#print axioms squeezeHomeomorph
end CompressionActualRelativeRadialSqueezeHomeomorphV891
