import ActualPlanarWholeEmbeddingExtensionV759
import ActualDiskFixedPlanarIsotopyV757

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Topology Metric
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
open CompressionCapRadialSupport CompressionActualPlanarWholeDiskExtensionV756
noncomputable section
namespace CompressionActualPlanarPolarCoordinatesV761

/-- Polar angle with a harmless value at the origin; it is used only away from zero. -/
def angle (x : Plane) : Circle :=
  if hx : x = 0 then 1 else
    ⟨‖x‖⁻¹ • asComplex x,by
      apply mem_sphere_zero_iff_norm.mpr
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),
        asComplex_norm,inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]⟩

lemma angle_val (x : Plane) (hx : x ≠ 0) :
    (angle x : ℂ) = ‖x‖⁻¹ • asComplex x := by
  simp only [angle,dite_eq_right hx]

lemma polar_reconstruction (x : Plane) (hx : x ≠ 0) :
    ‖x‖ • circleVector (angle x) = x := by
  apply asComplex_injective
  have hs (r : ℝ) (v : Plane) : asComplex (r • v) = r • asComplex v := by
    apply Complex.ext <;> simp [asComplex,PiLp.smul_apply]
  rw [hs,asComplex_circleVector,angle_val x hx,smul_smul,
    mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx),one_smul]

lemma angle_circleVector (z : Circle) : angle (circleVector z) = z := by
  apply Circle.ext
  have hx : circleVector z ≠ 0 := by
    intro hx
    have hn := circleVector_norm z
    rw [hx,norm_zero] at hn
    norm_num at hn
  rw [angle_val _ hx,circleVector_norm,inv_one,one_smul,asComplex_circleVector]

lemma angle_positive_smul (r : ℝ) (hr : 0 < r) (x : Plane) (hx : x ≠ 0) :
    angle (r • x) = angle x := by
  apply Circle.ext
  have hrne : r ≠ 0 := hr.ne'
  have hx' : r • x ≠ 0 := smul_ne_zero hrne hx
  rw [angle_val _ hx',angle_val _ hx,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
  have hs : asComplex (r • x) = r • asComplex x := by apply Complex.ext <;> simp [asComplex,PiLp.smul_apply]
  rw [hs,smul_smul]
  congr 1
  field_simp

lemma angle_continuousOn : ContinuousOn angle (Set.singleton (0 : Plane))ᶜ := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  apply Continuous.subtype_mk
  let c : ↥((Set.singleton (0 : Plane))ᶜ) → ℂ := fun x => asComplex x.val
  have hc : Continuous c := by
    have hh : asComplex = fun v : Plane => (v 0 : ℂ) + (v 1 : ℂ) * Complex.I := by
      funext v
      apply Complex.ext <;> simp [asComplex]
    change Continuous (asComplex ∘ Subtype.val)
    rw [hh]
    exact ((Complex.continuous_ofReal.comp (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0)).add
      ((Complex.continuous_ofReal.comp (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1)).mul continuous_const)).comp continuous_subtype_val
  have hn : Continuous (fun x : ↥((Set.singleton (0 : Plane))ᶜ) => ‖x.val‖⁻¹) :=
    continuous_subtype_val.norm.inv₀ (fun x => norm_ne_zero_iff.mpr
      (show x.val ≠ 0 from x.property))
  have h := hn.smul hc
  exact h.congr (fun x => (angle_val x.val (show x.val ≠ 0 from x.property)).symm)

end CompressionActualPlanarPolarCoordinatesV761
