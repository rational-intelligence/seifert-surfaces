import ArcClockProbe

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set Topology Filter
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal

/-- An exact positive affine native arc clock is an embedding onto an open
subinterval of Time. This applies equally after any subsequent shrinking. -/
theorem positive_affine_native_arc_clock_topology
    (s : Time) (r : ℝ) (hr : 0 < r)
    (parameter : Ioo (-1 : ℝ) 1 → Time)
    (hformula : ∀ t, (parameter t : ℝ) = (s : ℝ) + r * (t : ℝ)) :
    IsEmbedding parameter ∧ IsOpen (range parameter) ∧
      parameter ⟨0, neg_one_lt_zero, zero_lt_one⟩ = s := by
  let A : ℝ ≃ₜ ℝ := (Homeomorph.mulLeft₀ r hr.ne').trans (Homeomorph.addLeft (s : ℝ))
  have hreal : (fun t => (parameter t : ℝ)) = (fun t : Ioo (-1 : ℝ) 1 => A t) := by
    funext t
    exact hformula t
  have hrealemb : IsEmbedding (fun t => (parameter t : ℝ)) := by
    rw [hreal]
    exact A.isEmbedding.comp IsEmbedding.subtypeVal
  have hparam : Continuous parameter :=
    Continuous.subtype_mk hrealemb.continuous (fun t => (parameter t).property)
  have hemb : IsEmbedding parameter := IsEmbedding.of_comp hparam continuous_subtype_val hrealemb
  have hrange : range parameter =
      (Subtype.val : Time → ℝ) ⁻¹' Ioo ((s : ℝ) - r) ((s : ℝ) + r) := by
    ext t
    constructor
    · rintro ⟨z, rfl⟩
      change (parameter z : ℝ) ∈ Ioo ((s : ℝ) - r) ((s : ℝ) + r)
      rw [hformula]
      constructor <;> nlinarith [mul_lt_mul_of_pos_left z.property.1 hr,
        mul_lt_mul_of_pos_left z.property.2 hr]
    · intro ht
      let z := ((t : ℝ) - (s : ℝ)) / r
      have hz : z ∈ Ioo (-1 : ℝ) 1 := by
        change -1 < ((t : ℝ) - (s : ℝ)) / r ∧ ((t : ℝ) - (s : ℝ)) / r < 1
        rw [lt_div_iff₀ hr, div_lt_iff₀ hr]
        constructor <;> linarith [ht.1, ht.2]
      refine ⟨⟨z, hz⟩, Subtype.ext ?_⟩
      rw [hformula]
      dsimp [z]
      field_simp
      ring
  refine ⟨hemb, ?_, Subtype.ext ?_⟩
  · rw [hrange]
    exact isOpen_Ioo.preimage continuous_subtype_val
  · simpa using hformula ⟨0, neg_one_lt_zero, zero_lt_one⟩

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
