import ActualAnnulusHalfWholeExtensionV762

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Topology Metric
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
open CompressionActualPlanarWholeDiskExtensionV756
open CompressionActualPlanarPolarCoordinatesV761
noncomputable section
namespace CompressionActualAnnulusHalfPolarModelV768

/-- The prescribed radial model of one annulus half. -/
def polar (p : Circle × Time) : Plane := (1+(p.2:ℝ)) • circleVector p.1

lemma polar_norm (p : Circle × Time) : ‖polar p‖ = 1+(p.2:ℝ) := by
  rw [polar,norm_smul,Real.norm_eq_abs,abs_of_pos (by linarith [p.2.property.1]),
    circleVector_norm,mul_one]

lemma polar_ne_zero (p : Circle × Time) : polar p ≠ 0 := by
  intro he
  have hn := polar_norm p
  rw [he,norm_zero] at hn
  linarith [p.2.property.1]

lemma polar_angle (p : Circle × Time) : angle (polar p) = p.1 := by
  have hz : circleVector p.1 ≠ 0 := by
    intro he
    have hn := circleVector_norm p.1
    rw [he,norm_zero] at hn
    norm_num at hn
  rw [polar,angle_positive_smul _ (by linarith [p.2.property.1]) _ hz,angle_circleVector]

lemma polar_continuous : Continuous polar := by
  have hc : Continuous circleVector := by
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro i
    change Continuous (fun z : Circle => circleVector z i)
    have hcoe : Continuous (fun z : Circle => (z : ℂ)) := continuous_subtype_val
    fin_cases i
    · simpa [circleVector,PiLp.single_apply,Function.comp_def] using
        Complex.continuous_re.comp hcoe
    · simpa [circleVector,PiLp.single_apply,Function.comp_def] using
        Complex.continuous_im.comp hcoe
  exact (continuous_const.add continuous_snd.subtype_val).smul
    (hc.comp continuous_fst)

lemma polar_injective : Function.Injective polar := by
  intro p q he
  apply Prod.ext
  · have h := congrArg angle he
    simpa only [polar_angle] using h
  · apply Subtype.ext
    have h := congrArg norm he
    rw [polar_norm,polar_norm] at h
    linarith

lemma polar_embedding : IsEmbedding polar :=
  (polar_continuous.isClosedEmbedding polar_injective).isEmbedding

/-- Coordinates on the closed planar annulus with literal radial parameter. -/
def coord (x : Plane) (hlo : 1 ≤ ‖x‖) (hhi : ‖x‖ ≤ 2) : Circle × Time :=
  (angle x,⟨‖x‖-1,by constructor <;> linarith⟩)

lemma polar_coord (x : Plane) (hlo : 1 ≤ ‖x‖) (hhi : ‖x‖ ≤ 2) :
    polar (coord x hlo hhi) = x := by
  have hx : x ≠ 0 := by
    intro he
    rw [he,norm_zero] at hlo
    norm_num at hlo
  dsimp only [polar,coord]
  rw [show (1:ℝ)+(‖x‖-1)=‖x‖ by ring]
  exact polar_reconstruction x hx

lemma coord_polar (p : Circle × Time) :
    coord (polar p) (by rw [polar_norm]; linarith [p.2.property.1])
      (by rw [polar_norm]; linarith [p.2.property.2]) = p := by
  apply Prod.ext
  · exact polar_angle p
  · apply Subtype.ext
    dsimp only [coord]
    rw [polar_norm]
    ring

end CompressionActualAnnulusHalfPolarModelV768
