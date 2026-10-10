import Section5CommonLeafClockV488

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations

/-- The exact transverse translation on longitude labels. -/
def longitudeLabelFlow : Flow ℝ Circle where
  toFun t a := Circle.exp t * a
  cont' := Circle.exp.continuous.comp continuous_fst |>.mul continuous_snd
  map_add' t u a := by simp [Circle.exp_add,mul_assoc]
  map_zero' a := by simp

theorem longitude_label_flow_smooth :
    ContMDiff (𝓘(ℝ).prod (𝓡 1)) (𝓡 1) ∞
      (fun p : ℝ × Circle => longitudeLabelFlow p.1 p.2) :=
  (contMDiff_circleExp.comp contMDiff_fst).mul contMDiff_snd

theorem longitude_label_flow_transverse (a : Circle) :
    mfderiv 𝓘(ℝ) (𝓡 1) (fun t : ℝ => longitudeLabelFlow t a) 0
      ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1) ≠ 0 := by
  let R : Circle → Circle := fun z => z * a
  have hR : ContMDiff (𝓡 1) (𝓡 1) ∞ R := contMDiff_id.mul contMDiff_const
  have hRi : ContMDiff (𝓡 1) (𝓡 1) ∞ (fun z : Circle => z * a⁻¹) :=
    contMDiff_id.mul contMDiff_const
  have hleft : (fun z : Circle => R z * a⁻¹) = id := by
    funext z
    simp [R,mul_assoc]
  have hder (z : Circle) : Injective (mfderiv (𝓡 1) (𝓡 1) R z) := by
    have he := mfderiv_comp z (hRi.mdifferentiableAt (by simp))
      (hR.mdifferentiableAt (by simp))
    have hc : (fun z : Circle => z * a⁻¹) ∘ R = id := hleft
    rw [hc,mfderiv_id] at he
    apply Injective.of_comp (f := mfderiv (𝓡 1) (𝓡 1) (fun z : Circle => z*a⁻¹) (R z))
    change Injective ((mfderiv (𝓡 1) (𝓡 1) (fun z : Circle => z*a⁻¹) (R z)).comp
      (mfderiv (𝓡 1) (𝓡 1) R z))
    rw [← he]
    exact fun _ _ h => h
  have hi : Injective (mfderiv 𝓘(ℝ) (𝓡 1) (fun t : ℝ => longitudeLabelFlow t a) 0) := by
    change Injective (mfderiv 𝓘(ℝ) (𝓡 1) (R ∘ Circle.exp) 0)
    rw [mfderiv_comp 0 (hR.mdifferentiableAt (by simp))
      ((contMDiff_circleExp (m := ∞)).mdifferentiableAt (by simp))]
    exact (hder _).comp (circle_clock_differential_injective 0)
  intro hz
  have h10 := hi (hz.trans (map_zero _).symm)
  change (1 : ℝ) = 0 at h10
  exact one_ne_zero h10

#print axioms longitude_label_flow_transverse
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
