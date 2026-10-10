import MetricAreaAnalysis.InteriorTransport

open scoped Manifold ContDiff ENNReal
open Set Topology MeasureTheory Bundle

noncomputable section
namespace SeifertSurfaces.MetricFoundations.AreaAnalysis
open Foundations
universe u v

/-- H25: an ordinary Euclidean local left inverse, with no area premise. -/
theorem euclideanImmersion_local_leftInverse (F : Euc 2 → Euc 3)
    (D : Set (Euc 2)) (hD : IsOpen D) (x : Euc 2) (hx : x ∈ D)
    (hF : ContDiffOn ℝ ∞ F D) (hinj : Function.Injective (fderiv ℝ F x)) :
    Nonempty (EuclideanLocalLeftInverse F x D) := by 
  obtain ⟨P, hP⟩ :=
    ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hinj
  let G : Euc 2 → Euc 2 := P ∘ F
  have hG : ContDiffOn ℝ ∞ G D := P.contDiff.comp_contDiffOn hF
  have hGx : ContDiffAt ℝ ∞ G x := hG.contDiffAt (hD.mem_nhds hx)
  have hdGx : HasFDerivAt G
      (ContinuousLinearEquiv.refl ℝ (Euc 2) : Euc 2 →L[ℝ] Euc 2) x := by
    have hc := P.hasFDerivAt.comp x
      ((hF.contDiffAt (hD.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
    have heq : P.comp (fderiv ℝ F x) =
        (ContinuousLinearEquiv.refl ℝ (Euc 2) : Euc 2 →L[ℝ] Euc 2) := by
      apply ContinuousLinearMap.ext
      exact hP
    exact heq ▸ hc
  let e := hGx.toOpenPartialHomeomorph G hdGx (by simp)
  have hex : x ∈ e.source := hGx.mem_toOpenPartialHomeomorph_source hdGx (by simp)
  have heGx : G x ∈ e.target := hGx.image_mem_toOpenPartialHomeomorph_target hdGx (by simp)
  have hderiv : {z : Euc 2 | ∃ d : Euc 2 ≃L[ℝ] Euc 2,
      (d : Euc 2 →L[ℝ] Euc 2) = fderiv ℝ G z} ∈ 𝓝 x := by
    have hlin := (ContinuousLinearEquiv.refl ℝ (Euc 2)).nhds
    rw [← hdGx.fderiv] at hlin
    exact (hGx.continuousAt_fderiv (by simp)).preimage_mem_nhds hlin
  obtain ⟨V, hVsub, hVopen, hVx⟩ :=
    mem_nhds_iff.mp (Filter.inter_mem (hD.mem_nhds hx) hderiv)
  let W : Set (Euc 2) := e.target ∩ e.symm ⁻¹' V
  have hWopen : IsOpen W := e.isOpen_inter_preimage_symm hVopen
  have hGxW : G x ∈ W := by
    refine ⟨heGx, ?_⟩
    change e.symm (G x) ∈ V
    have he : e.symm (G x) = x := e.left_inv hex
    rw [he]
    exact hVx
  have hInv : ContDiffOn ℝ ∞ e.symm W := by
    intro y hy
    obtain ⟨hyD, d, hd⟩ := hVsub hy.2
    have hGy : ContDiffAt ℝ ∞ G (e.symm y) := hG.contDiffAt (hD.mem_nhds hyD)
    have hdGy : HasFDerivAt G (d : Euc 2 →L[ℝ] Euc 2) (e.symm y) := by
      rw [hd]
      exact (hGy.differentiableAt (by simp)).hasFDerivAt
    exact (e.contDiffAt_symm hy.1 hdGy hGy).contDiffWithinAt
  refine ⟨{
    source := e.source ∩ V
    target := P ⁻¹' W
    map := e.symm ∘ P
    open_source := e.open_source.inter hVopen
    source_mem := ⟨hex, hVx⟩
    source_subset := fun z hz => (hVsub hz.2).1
    open_target := hWopen.preimage P.continuous
    target_mem := hGxW
    smooth := hInv.comp P.contDiff.contDiffOn (fun _ hz => hz)
    mapsTo := ?_
    left_inverse := ?_
  }⟩
  · intro z hz
    refine ⟨e.map_source hz.1, ?_⟩
    change e.symm (G z) ∈ V
    have he : e.symm (G z) = z := e.left_inv hz.1
    rw [he]
    exact hz.2
  · intro z hz
    exact e.left_inv hz.1

variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]

/-- H24: equations for the single, literal range-homeomorphism construction. -/
theorem sameImage_homeomorph_matches {S R : CompactOrientedSurface.{u}}
    (f : ProperSmoothEmbedding S M) (h : ProperSmoothEmbedding R M)
    (heq : f.image = h.image) (x : R) :
    f.toFun (sameImageHomeomorph f h heq x) = h.toFun x := by 
  have he := f.embedding.toHomeomorph.apply_symm_apply
    (Homeomorph.setCongr heq.symm (h.embedding.toHomeomorph x))
  exact congrArg Subtype.val he

theorem sameImage_homeomorph_inverse_matches {S R : CompactOrientedSurface.{u}}
    (f : ProperSmoothEmbedding S M) (h : ProperSmoothEmbedding R M)
    (heq : f.image = h.image) (x : S) :
    h.toFun ((sameImageHomeomorph f h heq).symm x) = f.toFun x := by 
  have he := sameImage_homeomorph_matches f h heq ((sameImageHomeomorph f h heq).symm x)
  simpa only [Homeomorph.apply_symm_apply] using he.symm

/-- H26: actual source and ambient interior charts and their injective derivative. -/
theorem properEmbedding_interior_chart_leftInverse {S : CompactOrientedSurface.{u}}
    (f : ProperSmoothEmbedding S M) (x : S) (hx : x ∈ (S.boundary)ᶜ) :
    Nonempty (EmbeddingInteriorLocalInverse f x) := by 
  have hi : surfaceChart x x ∈ interior (surfaceChart x).target :=
    (𝓡∂ 2).isInteriorPoint_iff.mp
      (((𝓡∂ 2).isInteriorPoint_iff_not_isBoundaryPoint x).mpr hx)
  have hrange : range (𝓡∂ 2) ∈ 𝓝 (surfaceChart x x) :=
    Filter.mem_of_superset (isOpen_interior.mem_nhds hi)
      (fun z hz => extChartAt_target_subset_range x (interior_subset hz))
  have hfx : f.toFun x ∈ (((𝓡∂ 3).boundary M)ᶜ) := by
    change f.toFun x ∉ (𝓡∂ 3).boundary M
    intro h
    apply hx
    rw [← f.boundary_preimage]
    exact h
  let T := (extChartAt (𝓡∂ 3) (f.toFun x)).source ∩ (((𝓡∂ 3).boundary M)ᶜ)
  have hT : IsOpen T := (isOpen_extChartAt_source (f.toFun x)).inter
    (((𝓡∂ 3).isClosed_boundary (M := M) (n := ∞) (by simp)).isOpen_compl)
  let D := interior (surfaceChart x).target ∩
    (f.toFun ∘ (surfaceChart x).symm) ⁻¹' T
  have hD : IsOpen D :=
    ((f.embedding.continuous.comp_continuousOn
      ((continuousOn_extChartAt_symm x).mono interior_subset)).isOpen_inter_preimage
        isOpen_interior hT)
  have hxD : surfaceChart x x ∈ D := by
    refine ⟨hi, ?_⟩
    change f.toFun ((surfaceChart x).symm (surfaceChart x x)) ∈ T
    rw [(surfaceChart x).left_inv (mem_extChartAt_source x)]
    exact ⟨mem_extChartAt_source (f.toFun x), hfx⟩
  have hF : ContDiffOn ℝ ∞ (embeddingCoordinateMap f x) D := by
    have hsrc : ContMDiffOn 𝓘(ℝ, Euc 2) (𝓡∂ 2) ∞ (surfaceChart x).symm D :=
      (contMDiffOn_extChartAt_symm (I := 𝓡∂ 2) (n := ∞) x).mono
      (fun y hy => interior_subset hy.1)
    have hf := f.smooth.comp_contMDiffOn hsrc
    have htar : ContMDiffOn (𝓡∂ 3) 𝓘(ℝ, Euc 3) ∞
        (extChartAt (𝓡∂ 3) (f.toFun x))
        (extChartAt (𝓡∂ 3) (f.toFun x)).source := by
      simpa only [extChartAt_source] using
        (contMDiffOn_extChartAt (I := 𝓡∂ 3) (n := ∞) (x := f.toFun x))
    exact (htar.comp hf (fun _ hy => hy.2.1)).contDiffOn
  have hmd : MDifferentiableAt (𝓡∂ 2) (𝓡∂ 3) f.toFun x :=
    f.smooth.contMDiffAt.mdifferentiableAt (by simp)
  have hd := f.differential_injective x
  rw [hmd.mfderiv, fderivWithin_of_mem_nhds hrange] at hd
  have hinj : Function.Injective
      (fderiv ℝ (embeddingCoordinateMap f x) (surfaceChart x x)) := by
    intro v w hvw
    have h : (tangentSpaceCastModel (𝓡∂ 2) x).symm v =
        (tangentSpaceCastModel (𝓡∂ 2) x).symm w := hd (by
      simpa only [ContinuousLinearMap.comp_apply,
        ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply,
        writtenInExtChartAt, embeddingCoordinateMap] using
        congrArg (tangentSpaceCastModel (𝓡∂ 3) (f.toFun x)).symm hvw)
    exact (tangentSpaceCastModel (𝓡∂ 2) x).symm.injective h
  obtain ⟨L⟩ := euclideanImmersion_local_leftInverse (embeddingCoordinateMap f x)
    D hD (surfaceChart x x) hxD hF hinj
  exact ⟨{
    domain := D
    open_domain := hD
    base_mem := hxD
    domain_subset := fun _ hy => hy.1
    ambient_mem := fun _ hy => hy.2
    chart_smooth := hF
    derivative_injective := hinj
    inverse := L
  }⟩

/-- H27a: exact boundary preimages come from the original two embeddings. -/
theorem sameImage_homeomorph_boundary {S R : CompactOrientedSurface.{u}}
    (f : ProperSmoothEmbedding S M) (h : ProperSmoothEmbedding R M)
    (heq : f.image = h.image) :
    sameImageHomeomorph f h heq ⁻¹' S.boundary = R.boundary := by 
  ext r
  change sameImageHomeomorph f h heq r ∈ S.boundary ↔ r ∈ R.boundary
  rw [← f.boundary_preimage, ← h.boundary_preimage]
  simp only [Set.mem_preimage]
  rw [sameImage_homeomorph_matches]

/-- H27b: the local coordinate identity uses the same homeomorphism and left inverse. -/
theorem sameImage_homeomorph_local_coordinate {S R : CompactOrientedSurface.{u}}
    (f : ProperSmoothEmbedding S M) (h : ProperSmoothEmbedding R M)
    (heq : f.image = h.image) (r : R) (hr : r ∈ (R.boundary)ᶜ)
    (L : EmbeddingInteriorLocalInverse f (sameImageHomeomorph f h heq r)) :
    ∃ U : Set R, IsOpen U ∧ r ∈ U ∧ U ⊆ (R.boundary)ᶜ ∧
      MapsTo (sameImageHomeomorph f h heq) U
        (surfaceChart (sameImageHomeomorph f h heq r)).source ∧
      MapsTo (surfaceChart (sameImageHomeomorph f h heq r) ∘ sameImageHomeomorph f h heq)
        U L.inverse.source ∧
      MapsTo (extChartAt (𝓡∂ 3) (f.toFun (sameImageHomeomorph f h heq r)) ∘ h.toFun)
        U L.inverse.target ∧
      ∀ z ∈ U,
        surfaceChart (sameImageHomeomorph f h heq r) (sameImageHomeomorph f h heq z) =
          L.inverse.map (extChartAt (𝓡∂ 3)
            (f.toFun (sameImageHomeomorph f h heq r)) (h.toFun z)) := by 
  let a := sameImageHomeomorph f h heq
  let U : Set R := a ⁻¹' ((surfaceChart (a r)).source ∩
      (surfaceChart (a r)) ⁻¹' L.inverse.source) ∩ (R.boundary)ᶜ
  have hU : IsOpen U :=
    ((isOpen_extChartAt_preimage' (a r) L.inverse.open_source).preimage a.continuous).inter
      (((𝓡∂ 2).isClosed_boundary (M := R) (n := ∞) (by simp)).isOpen_compl)
  have hidentity (z : R) (hz : z ∈ U) :
      embeddingCoordinateMap f (a r) (surfaceChart (a r) (a z)) =
        extChartAt (𝓡∂ 3) (f.toFun (a r)) (h.toFun z) := by
    simp only [embeddingCoordinateMap, Function.comp_apply,
      (surfaceChart (a r)).left_inv hz.1.1]
    exact congrArg (extChartAt (𝓡∂ 3) (f.toFun (a r)))
      (sameImage_homeomorph_matches f h heq z)
  refine ⟨U, hU, ⟨⟨mem_extChartAt_source (a r), L.inverse.source_mem⟩, hr⟩,
    fun _ hz => hz.2, fun _ hz => hz.1.1, fun _ hz => hz.1.2, ?_, ?_⟩
  · intro z hz
    change extChartAt (𝓡∂ 3) (f.toFun (a r)) (h.toFun z) ∈ L.inverse.target
    rw [← hidentity z hz]
    exact L.inverse.mapsTo hz.1.2
  · intro z hz
    rw [← hidentity z hz]
    exact (L.inverse.left_inverse _ hz.1.2).symm

theorem sameImage_homeomorph_interior_smoothAt {S R : CompactOrientedSurface.{u}}
    (f : ProperSmoothEmbedding S M) (h : ProperSmoothEmbedding R M)
    (heq : f.image = h.image) (r : R) (hr : r ∈ (R.boundary)ᶜ) :
    ContMDiffAt (𝓡∂ 2) (𝓡∂ 2) ∞ (sameImageHomeomorph f h heq) r := by 
  let a := sameImageHomeomorph f h heq
  have har : a r ∈ (S.boundary)ᶜ :=
    (homeomorph_interior_iff a (sameImage_homeomorph_boundary f h heq) r).mpr hr
  obtain ⟨L⟩ := properEmbedding_interior_chart_leftInverse f (a r) har
  obtain ⟨U, hU, hrU, _, _, _, htarget, hcoord⟩ :=
    sameImage_homeomorph_local_coordinate f h heq r hr L
  have hmap : ContMDiffAt 𝓘(ℝ, Euc 3) 𝓘(ℝ, Euc 2) ∞ L.inverse.map
      (extChartAt (𝓡∂ 3) (f.toFun (a r)) (h.toFun r)) :=
    (L.inverse.smooth.contDiffAt
      (L.inverse.open_target.mem_nhds (htarget hrU))).contMDiffAt
  have hchart : ContMDiffAt (𝓡∂ 3) 𝓘(ℝ, Euc 3) ∞
      (extChartAt (𝓡∂ 3) (f.toFun (a r))) (h.toFun r) := by
    apply contMDiffAt_extChartAt'
    rw [← sameImage_homeomorph_matches f h heq r]
    exact mem_chart_source (EuclideanHalfSpace 3) (f.toFun (a r))
  have hcompose := hmap.comp r (hchart.comp r h.smooth.contMDiffAt)
  have hevent : (surfaceChart (a r) ∘ a) =ᶠ[𝓝 r]
      (L.inverse.map ∘ extChartAt (𝓡∂ 3) (f.toFun (a r)) ∘ h.toFun) := by
    filter_upwards [hU.mem_nhds hrU] with z hz
    exact hcoord z hz
  apply contMDiffAt_iff_target.mpr
  exact ⟨a.continuous.continuousAt, hcompose.congr_of_eventuallyEq hevent⟩

theorem sameImage_homeomorph_interior_smooth {S R : CompactOrientedSurface.{u}}
    (f : ProperSmoothEmbedding S M) (h : ProperSmoothEmbedding R M)
    (heq : f.image = h.image) :
    ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) ∞ (sameImageHomeomorph f h heq) ((R.boundary)ᶜ) := by 
  intro r hr
  exact (sameImage_homeomorph_interior_smoothAt f h heq r hr).contMDiffWithinAt

theorem sameImage_homeomorph_inverse_interior_smooth {S R : CompactOrientedSurface.{u}}
    (f : ProperSmoothEmbedding S M) (h : ProperSmoothEmbedding R M)
    (heq : f.image = h.image) :
    ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) ∞ (sameImageHomeomorph f h heq).symm
      ((S.boundary)ᶜ) := by 
  have he : sameImageHomeomorph h f heq.symm = (sameImageHomeomorph f h heq).symm := by
    ext x
    apply h.embedding.injective
    exact (sameImage_homeomorph_matches h f heq.symm x).trans
      (sameImage_homeomorph_inverse_matches f h heq x).symm
  rw [← he]
  exact sameImage_homeomorph_interior_smooth h f heq.symm

end SeifertSurfaces.MetricFoundations.AreaAnalysis
