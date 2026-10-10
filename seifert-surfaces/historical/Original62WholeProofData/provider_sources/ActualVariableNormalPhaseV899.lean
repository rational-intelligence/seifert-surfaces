import ActualVariableNormalFamilyStraighteningV895

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology
open SeifertSurfaces.Foundations
noncomputable section
namespace CompressionActualVariableNormalPhaseV899

def phase (ρ : ℝ) (n : ℝ) : Time := Set.projIcc 0 1 zero_le_one (1-|n|/ρ)

lemma phase_continuous (ρ : ℝ) : Continuous (phase ρ) := by
  apply continuous_projIcc.comp
  exact continuous_const.sub (continuous_abs.div_const ρ)

lemma phase_zero (ρ : ℝ) : phase ρ 0 = 1 := by
  apply Subtype.ext
  simp [phase]

lemma phase_off (ρ : ℝ) (hρ : 0 < ρ) (n : ℝ) (hn : n ∉ Ioo (-ρ) ρ) : phase ρ n = 0 := by
  have hab : ρ ≤ |n| := le_of_not_gt (fun h => hn (abs_lt.mp h))
  have hdiv : 1 ≤ |n|/ρ := (le_div_iff₀ hρ).mpr (by simpa using hab)
  apply Subtype.ext
  simp only [phase,Set.projIcc,Set.projIcc]
  simp [min_eq_right (by linarith : 1-|n|/ρ ≤ 1),max_eq_left (by linarith : 1-|n|/ρ ≤ 0)]

lemma phase_signed_collar (σ b r s : ℝ) (hσ : |σ| = 1) (hb : 0 < b)
    (hr : 0 < r) (hs : 0 ≤ s) :
    phase (b*r) (σ*b*s) = Set.projIcc 0 1 zero_le_one (1-s/r) := by
  have he : |σ*b*s| = b*s := by
    rw [abs_mul,abs_mul,hσ,abs_of_pos hb,abs_of_nonneg hs,one_mul]
  unfold phase
  rw [he]
  congr 1
  field_simp

#print axioms phase_off
#print axioms phase_signed_collar
end CompressionActualVariableNormalPhaseV899
