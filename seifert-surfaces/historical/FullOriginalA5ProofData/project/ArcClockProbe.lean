import OriginalA25SourceDefinitionsV464
import A5NativeSeamSector
import A5NativeLocalCover

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set Topology MeasureTheory Filter
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
noncomputable section

namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
universe u
variable {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)

theorem native_arc_projected_edge_smooth_regular
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (a : Fin F.seam.arcCount) :
    let γ := E.toSphere ∘ F.map ∘ F.seam.arc a ∘
      Set.projIcc (0 : ℝ) 1 (by norm_num : (0 : ℝ) ≤ 1)
    ContMDiffOn 𝓘(ℝ) (𝓡 3) ∞ γ (Ioo (0 : ℝ) 1) ∧
      ∀ t ∈ Ioo (0 : ℝ) 1, mfderiv 𝓘(ℝ) (𝓡 3) γ t 1 ≠ 0 := by
  dsimp only
  let f := E.toSphere ∘ F.map ∘ F.seam.arc a
  let p := Set.projIcc (0 : ℝ) 1 (by norm_num : (0 : ℝ) ≤ 1)
  have hE : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  have hf : ContMDiff (𝓡∂ 1) (𝓡 3) ∞ f :=
    hE.contMDiff.comp (F.seam.arc_smooth_image a)
  have hγ : ContMDiffOn 𝓘(ℝ) (𝓡 3) ∞ (f ∘ p) (Icc (0 : ℝ) 1) :=
    hf.comp_contMDiffOn contMDiffOn_projIcc
  refine ⟨hγ.mono Ioo_subset_Icc_self, ?_⟩
  intro t ht
  have htcc : t ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht
  have hp : p t = (⟨t, htcc⟩ : Time) := Set.projIcc_of_mem (by norm_num) htcc
  have hinc := hE.isImmersion.mfderiv_injective (by simp : (∞ : ℕ∞ω) ≠ 0)
    (F.map (F.seam.arc a ⟨t, htcc⟩))
  have hfinj : Function.Injective (mfderiv (𝓡∂ 1) (𝓡 3) f ⟨t, htcc⟩) := by
    rw [show f = E.toSphere ∘ (F.map ∘ F.seam.arc a) from rfl,
      mfderiv_comp _ (hE.contMDiff.mdifferentiable (by simp) _)
        ((F.seam.arc_smooth_image a).mdifferentiable (by simp) _)]
    exact hinc.comp (F.seam.arc_differential_injective a _)
  have h1 : (1 : TangentSpace (𝓡∂ 1) (⟨t, htcc⟩ : Time)) ≠ 0 := by
    intro he
    have h := mfderiv_subtypeVal_Icc_one (⟨t, htcc⟩ : Time)
    rw [he, map_zero] at h
    change (0 : ℝ) = 1 at h
    norm_num at h
  have hγd : mfderiv 𝓘(ℝ) (𝓡 3) (f ∘ p) t 1 =
      mfderiv (𝓡∂ 1) (𝓡 3) f ⟨t, htcc⟩ 1 := by
    have h := mfderivWithin_comp_projIcc_one (I := 𝓡 3) (f := f)
      (w := (⟨t, htcc⟩ : Time))
    rw [mfderivWithin_of_mem_nhds (I := 𝓘(ℝ)) (I' := 𝓡 3)
      (Icc_mem_nhds ht.1 ht.2)] at h
    exact h
  change mfderiv 𝓘(ℝ) (𝓡 3) (f ∘ p) t 1 ≠ 0
  rw [hγd]
  exact fun he => h1 (hfinj (he.trans (map_zero _).symm))



/-- An actual centered affine arc clock, with all radius bounds and smooth
nonzero ambient velocity proved from the original native edge. -/
theorem native_arc_affine_clock
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (a : Fin F.seam.arcCount) (s : Time)
    (hleft : 0 < (s : ℝ)) (hright : (s : ℝ) < 1) :
    ∃ radius : ℝ, 0 < radius ∧ 0 < (s : ℝ) - radius ∧ (s : ℝ) + radius < 1 ∧
      ∃ parameter : Ioo (-1 : ℝ) 1 → Time,
        (∀ t, (parameter t : ℝ) = (s : ℝ) + radius * (t : ℝ)) ∧
        Continuous parameter ∧
        ∃ edge : ℝ → ThreeSphere,
          (∀ t : Ioo (-1 : ℝ) 1,
            edge t = E.toSphere (F.map (F.seam.arc a (parameter t)))) ∧
          ContMDiffOn 𝓘(ℝ) (𝓡 3) ∞ edge (Ioo (-1 : ℝ) 1) ∧
          (∀ t : Ioo (-1 : ℝ) 1, mfderiv 𝓘(ℝ) (𝓡 3) edge (t : ℝ) 1 ≠ 0) := by
  let r := min (s : ℝ) (1 - (s : ℝ)) / 2
  have hr : 0 < r := half_pos (lt_min hleft (sub_pos.mpr hright))
  have hrleft : 0 < (s : ℝ) - r := by
    have := min_le_left (s : ℝ) (1 - (s : ℝ))
    dsimp only [r]
    linarith
  have hrright : (s : ℝ) + r < 1 := by
    have := min_le_right (s : ℝ) (1 - (s : ℝ))
    dsimp only [r]
    linarith
  let c : ℝ → ℝ := fun t => (s : ℝ) + r * t
  have hmaps : MapsTo c (Ioo (-1 : ℝ) 1) (Ioo (0 : ℝ) 1) := by
    intro t ht
    have h0 := mul_lt_mul_of_pos_left ht.1 hr
    have h1 := mul_lt_mul_of_pos_left ht.2 hr
    dsimp only [c]
    constructor <;> nlinarith
  let parameter : Ioo (-1 : ℝ) 1 → Time :=
    fun t => ⟨c t, Ioo_subset_Icc_self (hmaps t.property)⟩
  let γ := E.toSphere ∘ F.map ∘ F.seam.arc a ∘
    Set.projIcc (0 : ℝ) 1 (by norm_num : (0 : ℝ) ≤ 1)
  obtain ⟨hγ, hγreg⟩ := native_arc_projected_edge_smooth_regular E F a
  have hc : ContDiff ℝ ∞ c := contDiff_const.add (contDiff_const.mul contDiff_id)
  refine ⟨r, hr, hrleft, hrright, parameter, fun _ => rfl, ?_, γ ∘ c, ?_, ?_, ?_⟩
  · apply Continuous.subtype_mk
    exact hc.continuous.comp continuous_subtype_val
  · intro t
    dsimp only [Function.comp_def, γ]
    congr 3
    exact Set.projIcc_of_mem (by norm_num) (Ioo_subset_Icc_self (hmaps t.property))
  · exact hγ.comp hc.contMDiff.contMDiffOn hmaps
  · intro t
    have hct : c t ∈ Ioo (0 : ℝ) 1 := hmaps t.property
    have hdc : HasDerivAt c r (t : ℝ) := by
      convert!
        (hasDerivAt_const (t : ℝ) (s : ℝ)).add ((hasDerivAt_id (t : ℝ)).const_mul r)
        using 1 <;> simp [c]
    have hc1 : mfderiv 𝓘(ℝ) 𝓘(ℝ) c (t : ℝ) 1 = r := by
      rw [mfderiv_eq_fderiv]
      change fderiv ℝ c (t : ℝ) 1 = r
      simpa using congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) hdc.hasFDerivAt.fderiv
    rw [mfderiv_comp _ ((hγ _ hct).contMDiffAt (isOpen_Ioo.mem_nhds hct)
      |>.mdifferentiableAt (by simp)) (hc.contMDiff.mdifferentiable (by simp) _)]
    change mfderiv 𝓘(ℝ) (𝓡 3) γ (c t)
      (mfderiv 𝓘(ℝ) 𝓘(ℝ) c (t : ℝ) 1) ≠ 0
    rw [hc1]
    have he : mfderiv 𝓘(ℝ) (𝓡 3) γ (c t) r =
        r • mfderiv 𝓘(ℝ) (𝓡 3) γ (c t) 1 := by
      have h := (mfderiv 𝓘(ℝ) (𝓡 3) γ (c t)).map_smul r (1 : ℝ)
      change mfderiv 𝓘(ℝ) (𝓡 3) γ (c t) (r * 1) = _ at h
      simpa only [mul_one] using h
    rw [he]
    exact smul_ne_zero hr.ne' (hγreg _ hct)

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
