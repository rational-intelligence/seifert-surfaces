import OriginalA25SourceDefinitionsV464
import A5NativeSeamSector
import A5NativeLocalCover

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set Topology MeasureTheory Filter
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
noncomputable section

private theorem embedded_map_through_partial_homeomorph
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (e : PartialHomeomorph Y Z) (f : X → Y) (hf : IsEmbedding f)
    (hmaps : MapsTo f univ e.source) : IsEmbedding (e ∘ f) := by
  have h := e.isEmbedding_restrict.comp (hf.codRestrict e.source
    (fun x => hmaps (mem_univ x)))
  exact h

namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
universe u
variable {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)

/-- A local native circle clock with exact prescribed centre, open range,
embedding, smooth edge and nonzero actual ambient edge velocity. -/
theorem native_circle_centered_clock
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (a : Fin F.seam.circleCount) (s : Circle) :
    ∃ parameter : Ioo (-1 : ℝ) 1 → Circle,
      IsEmbedding parameter ∧ IsOpen (range parameter) ∧
      parameter ⟨0, neg_one_lt_zero, zero_lt_one⟩ = s ∧
      ∃ edge : ℝ → ThreeSphere,
        (∀ t : Ioo (-1 : ℝ) 1,
          edge t = E.toSphere (F.map (F.seam.circle a (parameter t)))) ∧
        ContMDiffOn 𝓘(ℝ) (𝓡 3) ∞ edge (Ioo (-1 : ℝ) 1) ∧
        (∀ t : Ioo (-1 : ℝ) 1, mfderiv 𝓘(ℝ) (𝓡 3) edge (t : ℝ) 1 ≠ 0) := by
  let c : OpenPartialHomeomorph Circle (Euc 1) := chartAt (Euc 1) s
  let L : Euc 1 ≃L[ℝ] ℝ := PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)
  let d : OpenPartialHomeomorph Circle ℝ := c.trans L.toHomeomorph.toOpenPartialHomeomorph
  have hs : s ∈ d.source := by
    exact ⟨mem_chart_source _ s, mem_univ _⟩
  have hds : d s ∈ d.target := d.map_source hs
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (d.open_target.mem_nhds hds)
  let A : ℝ ≃ₜ ℝ := (Homeomorph.mulLeft₀ r hr.ne').trans (Homeomorph.addLeft (d s))
  have hA (t : ℝ) : A t = d s + r * t := rfl
  have hmaps : MapsTo A (Ioo (-1 : ℝ) 1) d.target := by
    intro t ht
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, hA, add_sub_cancel_left, abs_mul, abs_of_pos hr]
    have habs : |t| < 1 := abs_lt.mpr ht
    simpa using mul_lt_mul_of_pos_left habs hr
  let parameter : Ioo (-1 : ℝ) 1 → Circle := fun t => d.symm (A t)
  have hpembed : IsEmbedding parameter := by
    have hAe : IsEmbedding (fun t : Ioo (-1 : ℝ) 1 => A t) :=
      A.isEmbedding.comp IsEmbedding.subtypeVal
    exact embedded_map_through_partial_homeomorph d.symm.toPartialHomeomorph
      (fun t : Ioo (-1 : ℝ) 1 => A t) hAe (fun t _ => hmaps t.property)
  have hpopen : IsOpen (range parameter) := by
    have heq : range parameter = d.symm '' (A '' Ioo (-1 : ℝ) 1) := by
      ext x
      constructor
      · rintro ⟨t, rfl⟩
        exact ⟨A t, ⟨t, t.property, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨t, ht, rfl⟩, heq⟩
        exact ⟨⟨t, ht⟩, heq⟩
    rw [heq]
    exact d.isOpen_image_symm_of_subset_target (A.isOpenMap _ isOpen_Ioo)
      (mapsTo_iff_image_subset.mp hmaps)
  have hpcentre : parameter ⟨0, neg_one_lt_zero, zero_lt_one⟩ = s := by
    change d.symm (d s + r * 0) = s
    simpa only [mul_zero, add_zero] using d.left_inv hs
  have hdi : ContMDiffOn 𝓘(ℝ) (𝓡 1) ∞ d.symm d.target := by
    change ContMDiffOn 𝓘(ℝ) (𝓡 1) ∞ (c.symm ∘ L.symm) d.target
    exact (contMDiffOn_chart_symm (I := 𝓡 1) (n := ∞)).comp
      L.symm.contDiff.contMDiff.contMDiffOn (fun _ ht => ht.2)
  have hAsmooth : ContDiff ℝ ∞ A := by
    change ContDiff ℝ ∞ (fun t => d s + r * t)
    fun_prop
  let q : ℝ → Circle := d.symm ∘ A
  have hq : ContMDiffOn 𝓘(ℝ) (𝓡 1) ∞ q (Ioo (-1 : ℝ) 1) :=
    hdi.comp hAsmooth.contMDiff.contMDiffOn hmaps
  have hd : d.MDifferentiable (𝓡 1) 𝓘(ℝ) := by
    exact (mdifferentiable_chart (I := 𝓡 1) s).trans
      ⟨L.contDiff.contMDiff.mdifferentiable (by simp : (∞ : ℕ∞ω) ≠ 0) |>.mdifferentiableOn,
       L.symm.contDiff.contMDiff.mdifferentiable (by simp : (∞ : ℕ∞ω) ≠ 0) |>.mdifferentiableOn⟩
  have hqreg (t : Ioo (-1 : ℝ) 1) : mfderiv 𝓘(ℝ) (𝓡 1) q (t : ℝ) 1 ≠ 0 := by
    have hAd : mfderiv 𝓘(ℝ) 𝓘(ℝ) A (t : ℝ) 1 = r := by
      rw [mfderiv_eq_fderiv]
      change fderiv ℝ A (t : ℝ) 1 = r
      have hder : HasDerivAt A r (t : ℝ) := by
        convert! (hasDerivAt_const (t : ℝ) (d s)).add
          ((hasDerivAt_id (t : ℝ)).const_mul r) using 1 <;> simp [hA]
      simpa using congrArg (fun f : ℝ →L[ℝ] ℝ => f 1) hder.hasFDerivAt.fderiv
    change mfderiv 𝓘(ℝ) (𝓡 1) (d.symm ∘ A) (t : ℝ) 1 ≠ 0
    rw [mfderiv_comp _ (hd.mdifferentiableAt_symm (hmaps t.property))
      (hAsmooth.contMDiff.mdifferentiable (by simp) _)]
    change mfderiv 𝓘(ℝ) (𝓡 1) d.symm (A t)
      (mfderiv 𝓘(ℝ) 𝓘(ℝ) A (t : ℝ) 1) ≠ 0
    rw [hAd]
    intro hzero
    have hzero' := hd.symm.mfderiv_injective (hmaps t.property)
      (hzero.trans (map_zero _).symm)
    exact hr.ne' hzero'
  let f := E.toSphere ∘ F.map ∘ F.seam.circle a
  have hE : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  have hf : ContMDiff (𝓡 1) (𝓡 3) ∞ f :=
    hE.contMDiff.comp (F.seam.circle_smooth_image a)
  have hfrank (z : Circle) : Function.Injective (mfderiv (𝓡 1) (𝓡 3) f z) := by
    change Function.Injective (mfderiv (𝓡 1) (𝓡 3)
      (E.toSphere ∘ (F.map ∘ F.seam.circle a)) z)
    rw [mfderiv_comp _ (hE.contMDiff.mdifferentiable (by simp) _)
      ((F.seam.circle_smooth_image a).mdifferentiable (by simp) _)]
    exact (hE.isImmersion.mfderiv_injective (by simp) _).comp
      (F.seam.circle_differential_injective a z)
  refine ⟨parameter, hpembed, hpopen, hpcentre, f ∘ q, fun _ => rfl,
    hf.comp_contMDiffOn hq, ?_⟩
  intro t
  rw [mfderiv_comp _ (hf.mdifferentiable (by simp) _)
    ((hq _ t.property).contMDiffAt (isOpen_Ioo.mem_nhds t.property)
      |>.mdifferentiableAt (by simp))]
  change mfderiv (𝓡 1) (𝓡 3) f (q t) (mfderiv 𝓘(ℝ) (𝓡 1) q (t : ℝ) 1) ≠ 0
  exact fun hzero => hqreg t ((hfrank _).eq_iff.mp (hzero.trans (map_zero _).symm))

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
