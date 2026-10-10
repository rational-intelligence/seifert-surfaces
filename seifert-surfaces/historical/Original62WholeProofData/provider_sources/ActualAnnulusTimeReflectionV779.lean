import ActualAnnulusHalfCoordinatesV772

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Topology
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
open CompressionActualAnnulusHalfCoordinatesV772
noncomputable section
namespace CompressionActualAnnulusTimeReflectionV779

def reverseTime (t : Time) : Time := ⟨1-(t:ℝ),by
  constructor <;> linarith [t.property.1,t.property.2]⟩

lemma reverseTime_continuous : Continuous reverseTime :=
  (continuous_const.sub continuous_subtype_val).subtype_mk _

lemma reverseTime_reverse (t : Time) : reverseTime (reverseTime t) = t := by
  apply Subtype.ext
  dsimp [reverseTime]
  ring

def reverseTimeHomeomorph : Time ≃ₜ Time where
  toFun := reverseTime
  invFun := reverseTime
  left_inv := reverseTime_reverse
  right_inv := reverseTime_reverse
  continuous_toFun := reverseTime_continuous
  continuous_invFun := reverseTime_continuous

def reflection : Circle × Time ≃ₜ Circle × Time :=
  (Homeomorph.refl Circle).prodCongr reverseTimeHomeomorph

lemma reflection_core (z : Circle) : reflection (z,middleTime) = (z,middleTime) := by
  refine Prod.ext (by rfl) ?_
  apply Subtype.ext
  dsimp [reflection,reverseTimeHomeomorph,reverseTime,middleTime]
  norm_num

lemma reflection_half_zero (p : Circle × Time) : reflection (half 0 p) = half 1 p := by
  refine Prod.ext (by rfl) ?_
  apply Subtype.ext
  dsimp [reflection,reverseTimeHomeomorph,reverseTime,half,halfTime]
  ring

lemma reflection_half_one (p : Circle × Time) : reflection (half 1 p) = half 0 p := by
  refine Prod.ext (by rfl) ?_
  apply Subtype.ext
  dsimp [reflection,reverseTimeHomeomorph,reverseTime,half,halfTime]
  ring

end CompressionActualAnnulusTimeReflectionV779
