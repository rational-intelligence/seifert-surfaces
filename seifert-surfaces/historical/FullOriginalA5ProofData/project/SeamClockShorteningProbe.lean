import A2NativeSeamDefinitionsV468
import CoreClockClosureProbe

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set Topology Filter
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal

theorem positive_seam_scale_maps (d : ℝ) (hd : 0 < d) (hd1 : d < 1) :
    MapsTo (fun t : ℝ => d * t) (Ioo (-1 : ℝ) 1) (Ioo (-1 : ℝ) 1) := by
  intro t ht
  constructor <;> nlinarith [mul_lt_mul_of_pos_left ht.1 hd,
    mul_lt_mul_of_pos_left ht.2 hd]

def seamScale (d : ℝ) (hd : 0 < d) (hd1 : d < 1) : SeamLocalTime → SeamLocalTime :=
  fun t => ⟨d * (t : ℝ), positive_seam_scale_maps d hd hd1 t.property⟩

theorem seamScale_embedding (d : ℝ) (hd : 0 < d) (hd1 : d < 1) :
    IsEmbedding (seamScale d hd hd1) := by
  let D := Homeomorph.mulLeft₀ d hd.ne'
  exact (D.isEmbedding.comp IsEmbedding.subtypeVal).codRestrict _ _

theorem seamScale_open_range (d : ℝ) (hd : 0 < d) (hd1 : d < 1) :
    IsOpen (range (seamScale d hd hd1)) := by
  have heq : range (seamScale d hd hd1) =
      (Subtype.val : SeamLocalTime → ℝ) ⁻¹' Ioo (-d) d := by
    ext t
    constructor
    · rintro ⟨u, rfl⟩
      change -d < d * (u : ℝ) ∧ d * (u : ℝ) < d
      constructor <;> nlinarith [mul_lt_mul_of_pos_left u.property.1 hd,
        mul_lt_mul_of_pos_left u.property.2 hd]
    · intro ht
      refine ⟨⟨(t : ℝ) / d, ?_⟩, ?_⟩
      · constructor
        · apply (lt_div_iff₀ hd).mpr
          simpa using ht.1
        · apply (div_lt_iff₀ hd).mpr
          simpa using ht.2
      · apply Subtype.ext
        change d * ((t : ℝ) / d) = (t : ℝ)
        field_simp
  rw [heq]
  exact isOpen_Ioo.preimage continuous_subtype_val

theorem shortened_seam_parameter_topology
    {P : Type*} [TopologicalSpace P]
    (p : SeamLocalTime → P) (hp : IsEmbedding p) (hpr : IsOpen (range p))
    (d : ℝ) (hd : 0 < d) (hd1 : d < 1) :
    IsEmbedding (p ∘ seamScale d hd hd1) ∧
      IsOpen (range (p ∘ seamScale d hd hd1)) := by
  refine ⟨hp.comp (seamScale_embedding d hd hd1), ?_⟩
  rw [range_comp]
  exact (hp.isInducing.isOpenMap hpr) _ (seamScale_open_range d hd hd1)

theorem shortened_native_edge_smooth_regular
    (γ : ℝ → ThreeSphere)
    (hγ : ContMDiffOn 𝓘(ℝ) (𝓡 3) ∞ γ (Ioo (-1 : ℝ) 1))
    (hr : ∀ t : SeamLocalTime, mfderiv 𝓘(ℝ) (𝓡 3) γ (t : ℝ) 1 ≠ 0)
    (d : ℝ) (hd : 0 < d) (hd1 : d < 1) :
    ContMDiffOn 𝓘(ℝ) (𝓡 3) ∞ (fun t => γ (d * t)) (Ioo (-1 : ℝ) 1) ∧
      ∀ t : SeamLocalTime,
        mfderiv 𝓘(ℝ) (𝓡 3) (fun t => γ (d * t)) (t : ℝ) 1 ≠ 0 := by
  let c : ℝ → ℝ := fun t => d * t
  have hc : ContDiff ℝ ∞ c := contDiff_const.mul contDiff_id
  have hm := positive_seam_scale_maps d hd hd1
  refine ⟨hγ.comp hc.contMDiff.contMDiffOn hm, ?_⟩
  intro t
  have hct : c t ∈ Ioo (-1 : ℝ) 1 := hm t.property
  have hdc : HasDerivAt c d (t : ℝ) := by
    convert! (hasDerivAt_id (t : ℝ)).const_mul d using 1 <;> simp [c]
  have hc1 : mfderiv 𝓘(ℝ) 𝓘(ℝ) c (t : ℝ) 1 = d := by
    rw [mfderiv_eq_fderiv]
    change fderiv ℝ c (t : ℝ) 1 = d
    simpa using congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) hdc.hasFDerivAt.fderiv
  rw [show (fun t => γ (d * t)) = γ ∘ c from rfl,
    mfderiv_comp _ ((hγ _ hct).contMDiffAt (isOpen_Ioo.mem_nhds hct)
      |>.mdifferentiableAt (by simp)) (hc.contMDiff.mdifferentiable (by simp) _)]
  change mfderiv 𝓘(ℝ) (𝓡 3) γ (c t) (mfderiv 𝓘(ℝ) 𝓘(ℝ) c (t : ℝ) 1) ≠ 0
  rw [hc1]
  have he : mfderiv 𝓘(ℝ) (𝓡 3) γ (c t) d = d • mfderiv 𝓘(ℝ) (𝓡 3) γ (c t) 1 := by
    simpa only [smul_eq_mul, mul_one] using
      (mfderiv 𝓘(ℝ) (𝓡 3) γ (c t)).map_smul d (1 : ℝ)
  rw [he]
  exact smul_ne_zero hd.ne' (hr ⟨c t, hct⟩)

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
