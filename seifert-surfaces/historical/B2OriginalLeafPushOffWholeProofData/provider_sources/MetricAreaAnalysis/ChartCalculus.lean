import MetricAreaAnalysis.Definitions

open scoped Manifold ContDiff ENNReal
open Set Topology MeasureTheory Bundle

noncomputable section
namespace SeifertSurfaces.MetricFoundations.AreaAnalysis
open Foundations
universe u v

/-- H01: the chart is a measurable embedding only after restriction to its source. -/
theorem extChart_restricted_measurableEmbedding {S : CompactOrientedSurface.{u}} (p : S) :
    MeasurableEmbedding (fun x : ↥(surfaceChart p).source => surfaceChart p x) := by
  letI : BorelSpace S := ⟨rfl⟩
  let e : PartialHomeomorph S (Euc 2) :=
    { toPartialEquiv := surfaceChart p
      continuousOn_toFun := continuousOn_extChartAt p
      continuousOn_invFun := continuousOn_extChartAt_symm p }
  apply e.isEmbedding_restrict.measurableEmbedding
  change MeasurableSet (Set.range ((surfaceChart p).source.domRestrict (surfaceChart p)))
  rw [Set.range_domRestrict, (surfaceChart p).image_source_eq_target]
  rw [extChartAt_target, range_modelWithCornersEuclideanHalfSpace]
  exact ((chartAt (EuclideanHalfSpace 2) p).open_target.preimage
    (𝓡∂ 2).continuous_symm).measurableSet.inter
      (isClosed_le continuous_const (by fun_prop)).measurableSet

theorem extChart_target_measurable {S : CompactOrientedSurface.{u}} (p : S) :
    MeasurableSet (surfaceChart p).target := by
  rw [extChartAt_target, range_modelWithCornersEuclideanHalfSpace]
  exact ((chartAt (EuclideanHalfSpace 2) p).open_target.preimage
    (𝓡∂ 2).continuous_symm).measurableSet.inter
      (isClosed_le continuous_const (by fun_prop)).measurableSet

theorem extChart_image_measurable {S : CompactOrientedSurface.{u}} (p : S) (s : Set S)
    (hs : MeasurableSet s) (hsub : s ⊆ (surfaceChart p).source) :
    MeasurableSet ((surfaceChart p) '' s) := by
  have hm := (extChart_restricted_measurableEmbedding p).measurableSet_image.mpr
    (measurable_subtype_coe hs)
  convert hm using 1
  ext y
  simp only [mem_image, mem_preimage, Subtype.exists]
  constructor
  · rintro ⟨x, hx, hxy⟩
    exact ⟨x, hsub hx, hx, hxy⟩
  · rintro ⟨x, _, hx, hxy⟩
    exact ⟨x, hx, hxy⟩

theorem extChart_image_subset_target {S : CompactOrientedSurface.{u}} (p : S) (s : Set S)
    (hsub : s ⊆ (surfaceChart p).source) :
    (surfaceChart p) '' s ⊆ (surfaceChart p).target := by
  exact (surfaceChart p).mapsTo.mono_left hsub |>.image_subset

theorem extChart_source_preimage_measurable {S : CompactOrientedSurface.{u}} (p : S)
    (b : Set (Euc 2)) (hb : MeasurableSet b) :
    MeasurableSet ((surfaceChart p).source ∩ (surfaceChart p) ⁻¹' b) := by
  letI : BorelSpace S := ⟨rfl⟩
  have hm := (extChart_restricted_measurableEmbedding p).measurable hb
  have hsource : MeasurableSet (surfaceChart p).source :=
    (isOpen_extChartAt_source p).measurableSet
  convert (MeasurableEmbedding.subtype_coe hsource).measurableSet_image.mpr hm using 1
  ext x
  simp only [mem_inter_iff, mem_preimage, mem_image, Subtype.exists, exists_and_right]
  aesop

/-- H02: all differentiation occurs on this full overlap. -/
theorem chartOverlap_measurable {S : CompactOrientedSurface.{u}} (p q : S) :
    MeasurableSet (chartOverlap p q) := by
  letI : BorelSpace S := ⟨rfl⟩
  have heq : chartOverlap p q = (surfaceChart p) ''
      ((surfaceChart p).source ∩ (surfaceChart q).source) := by
    ext y
    constructor
    · rintro ⟨hp, hq⟩
      exact ⟨(surfaceChart p).symm y, ⟨(surfaceChart p).map_target hp, hq⟩,
        (surfaceChart p).right_inv hp⟩
    · rintro ⟨x, ⟨hp, hq⟩, rfl⟩
      exact ⟨(surfaceChart p).map_source hp, by
        simpa only [mem_preimage, (surfaceChart p).left_inv hp] using hq⟩
  rw [heq]
  exact extChart_image_measurable p _
    ((isOpen_extChartAt_source p).measurableSet.inter
      (isOpen_extChartAt_source q).measurableSet) inter_subset_left

theorem chartOverlap_uniqueDiffOn {S : CompactOrientedSurface.{u}} (p q : S) :
    UniqueDiffOn ℝ (chartOverlap p q) := by
  exact ModelWithCorners.uniqueDiffOn_extendCoordChange_source
    (I := 𝓡∂ 2) (e := chartAt (EuclideanHalfSpace 2) p)
      (e' := chartAt (EuclideanHalfSpace 2) q)

theorem chartTransition_hasFDerivWithinAt {S : CompactOrientedSurface.{u}} (p q : S)
    {y : Euc 2} (hy : y ∈ chartOverlap p q) :
    HasFDerivWithinAt (chartTransition p q) (chartTransitionDerivative p q y)
      (chartOverlap p q) y := by
  have hc : ContDiffOn ℝ ∞ (chartTransition p q) (chartOverlap p q) :=
    ModelWithCorners.contDiffOn_extendCoordChange
      (IsManifold.chart_mem_maximalAtlas p) (IsManifold.chart_mem_maximalAtlas q)
  exact (hc.differentiableOn (by simp) y hy).hasFDerivWithinAt

theorem chartTransition_injOn {S : CompactOrientedSurface.{u}} (p q : S) :
    InjOn (chartTransition p q) (chartOverlap p q) := by
  exact ((surfaceChart p).symm.trans (surfaceChart q)).injOn

theorem chartTransition_mapsTo {S : CompactOrientedSurface.{u}} (p q : S) :
    MapsTo (chartTransition p q) (chartOverlap p q) (chartOverlap q p) := by
  exact ((surfaceChart p).symm.trans (surfaceChart q)).mapsTo

theorem chartTransition_inverse {S : CompactOrientedSurface.{u}} (p q : S)
    {y : Euc 2} (hy : y ∈ chartOverlap p q) :
    chartTransition q p (chartTransition p q y) = y := by
  exact ((surfaceChart p).symm.trans (surfaceChart q)).left_inv hy

theorem chartTransition_image {S : CompactOrientedSurface.{u}} (p q : S) (s : Set S)
    (hsub : s ⊆ (surfaceChart p).source ∩ (surfaceChart q).source) :
    (surfaceChart p) '' s ⊆ chartOverlap p q ∧
      chartTransition p q '' ((surfaceChart p) '' s) = (surfaceChart q) '' s := by
  constructor
  · rintro y ⟨x, hx, rfl⟩
    exact ⟨(surfaceChart p).map_source (hsub hx).1,
      by simpa only [mem_preimage, (surfaceChart p).left_inv (hsub hx).1] using (hsub hx).2⟩
  · ext y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, by simp only [chartTransition, Function.comp_apply,
        (surfaceChart p).left_inv (hsub hx).1]⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨surfaceChart p x, ⟨x, hx, rfl⟩, by
        simp only [chartTransition, Function.comp_apply, (surfaceChart p).left_inv (hsub hx).1]⟩

variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]

/-- H03: scalar Gram entries, rather than vectors in unequal varying fibers. -/
theorem coordinateGram_entry_continuous (g : SmoothMetric M)
    {S : CompactOrientedSurface.{u}} (F : S → M)
    (hF : ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ F) (p : S) (i j : Fin 2) :
    ContinuousOn (fun y => coordinateGram g F p y i j) (surfaceChart p).target := by
  let f := F ∘ (surfaceChart p).symm
  have hf : ContMDiffOn 𝓘(ℝ, Euc 2) (𝓡∂ 3) ∞ f (surfaceChart p).target :=
    hF.comp_contMDiffOn (contMDiffOn_extChartAt_symm p)
  have hu : UniqueMDiffOn 𝓘(ℝ, Euc 2) (surfaceChart p).target :=
    fun y hy => (uniqueDiffOn_extChartAt_target p y hy).uniqueMDiffWithinAt
  have ht := hf.continuousOn_tangentMapWithin (by simp) hu
  have hv (k : Fin 2) : ContinuousOn (fun y =>
      (⟨f y, mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 3) f (surfaceChart p).target y
        ((tangentSpaceCastModel 𝓘(ℝ, Euc 2) y).symm (EuclideanSpace.single k 1))⟩ :
          TangentBundle (𝓡∂ 3) M)) (surfaceChart p).target := by
    let ins : Euc 2 → TangentBundle 𝓘(ℝ, Euc 2) (Euc 2) := fun y =>
      (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, Euc 2)).symm (y, EuclideanSpace.single k 1)
    exact ht.comp ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, Euc 2)).symm.continuous.comp
      (continuous_id.prodMk continuous_const)).continuousOn (fun y hy => hy)
  letI : RiemannianBundle (fun x : M => TangentSpace (𝓡∂ 3) x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle (Euc 3)
      (fun x : M => TangentSpace (𝓡∂ 3) x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  exact (hv i).inner_bundle (hv j)

/-- H04: continuity of sqrt is enough, including zero-density smooth maps. -/
theorem coordinateAreaDensity_continuous (g : SmoothMetric M)
    {S : CompactOrientedSurface.{u}} (F : S → M)
    (hF : ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ F) (p : S) :
    ContinuousOn (coordinateAreaDensity g F p) (surfaceChart p).target := by
  apply ContinuousOn.sqrt
  exact continuous_id.matrix_det.comp_continuousOn (continuousOn_pi.mpr
    (fun i => continuousOn_pi.mpr (fun j => coordinateGram_entry_continuous g F hF p i j)))

/-- H05a: this equality supplies the actual dependent tangent-fiber transport. -/
theorem overlap_image_point {S : CompactOrientedSurface.{u}} (F : S → M)
    (p q : S) {y : Euc 2} (hy : y ∈ chartOverlap p q) :
    F ((surfaceChart q).symm (chartTransition p q y)) = F ((surfaceChart p).symm y) := by
  change F ((surfaceChart q).symm (surfaceChart q ((surfaceChart p).symm y))) = _
  rw [(surfaceChart q).left_inv hy.2]

/-- H05b: factorization with the explicit cast between equal image-point fibers. -/
theorem coordinateDifferential_overlap {S : CompactOrientedSurface.{u}} (F : S → M)
    (hF : ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ F) (p q : S) {y : Euc 2}
    (hy : y ∈ chartOverlap p q) (w : Euc 2) :
    coordinateDifferential F p y w =
      tangentTransport (overlap_image_point F p q hy)
        (coordinateDifferential F q (chartTransition p q y)
          (chartTransitionDerivative p q y w)) := by
  have hp : MDifferentiableWithinAt 𝓘(ℝ, Euc 2) (𝓡∂ 3)
      (F ∘ (surfaceChart p).symm) (surfaceChart p).target y :=
    (hF.mdifferentiable (by simp) _).comp_mdifferentiableWithinAt y
      (mdifferentiableOn_extChartAt_symm y hy.1)
  have hqy := chartTransition_mapsTo p q hy
  have hq : MDifferentiableWithinAt 𝓘(ℝ, Euc 2) (𝓡∂ 3)
      (F ∘ (surfaceChart q).symm) (surfaceChart q).target (chartTransition p q y) :=
    (hF.mdifferentiable (by simp) _).comp_mdifferentiableWithinAt _
      (mdifferentiableOn_extChartAt_symm _ hqy.1)
  have hu := (chartOverlap_uniqueDiffOn p q y hy).uniqueMDiffWithinAt
  have hm : MapsTo (chartTransition p q) (chartOverlap p q) (surfaceChart q).target :=
    fun z hz => (chartTransition_mapsTo p q hz).1
  have hd := (chartTransition_hasFDerivWithinAt p q hy).differentiableWithinAt
    |>.mdifferentiableWithinAt
  have hc := mfderivWithin_comp y hq hd hm hu
  have heq : ∀ z ∈ chartOverlap p q,
      ((F ∘ (surfaceChart q).symm) ∘ chartTransition p q) z =
        (F ∘ (surfaceChart p).symm) z := fun z hz => overlap_image_point F p q hz
  have hg := mfderivWithin_congr_of_mem (I := 𝓘(ℝ, Euc 2)) (I' := 𝓡∂ 3) heq hy
  rw [hc, hp.mfderivWithin_mono hu inter_subset_left] at hg
  have hcast : ∀ (x z : M) (h : x = z) (v : TangentSpace (𝓡∂ 3) x),
      tangentTransport h v = (tangentSpaceCast (𝓡∂ 3) x z) v := by
    intro x z h v
    subst z
    rfl
  rw [hcast]
  have hv := congrArg (fun d => d ((tangentSpaceCastModel 𝓘(ℝ, Euc 2) y).symm w)) hg
  rw [mfderivWithin_eq_fderivWithin] at hv
  exact hv.symm

/-- H06: absolute determinant, with no orientation-preservation hypothesis. -/
theorem coordinateAreaDensity_overlap (g : SmoothMetric M)
    {S : CompactOrientedSurface.{u}} (F : S → M)
    (hF : ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ F) (p q : S) {y : Euc 2}
    (hy : y ∈ chartOverlap p q) :
    coordinateAreaDensity g F p y = |(chartTransitionDerivative p q y).det| *
      coordinateAreaDensity g F q (chartTransition p q y) := by
  letI : RiemannianBundle (fun x : M => TangentSpace (𝓡∂ 3) x) :=
    ⟨g.toRiemannianMetric⟩
  have hinner {x z : M} (h : x = z) (a b : TangentSpace (𝓡∂ 3) x) :
      g.inner z (tangentTransport h a) (tangentTransport h b) = g.inner x a b := by
    subst z
    rfl
  have hgram : coordinateGram g F p y = Matrix.gram ℝ (fun i : Fin 2 =>
      coordinateDifferential F q (chartTransition p q y)
        (chartTransitionDerivative p q y (EuclideanSpace.single i 1))) := by
    ext i j
    change g.inner (F ((surfaceChart p).symm y))
      (coordinateDifferential F p y (EuclideanSpace.single i 1))
      (coordinateDifferential F p y (EuclideanSpace.single j 1)) = _
    rw [coordinateDifferential_overlap F hF p q hy,
      coordinateDifferential_overlap F hF p q hy, hinner]
    rfl
  unfold coordinateAreaDensity
  rw [hgram]
  exact linearMapGramDensity_comp (coordinateDifferential F q (chartTransition p q y))
    (chartTransitionDerivative p q y).toLinearMap

/-- H07a: literal coordinate integrals on arbitrary measurable subordinate pieces. -/
theorem coordinateIntegral_overlap (g : SmoothMetric M) {S : CompactOrientedSurface.{u}}
    (F : S → M) (hF : ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ F) (p q : S) (s : Set S)
    (hs : MeasurableSet s) (hsub : s ⊆ (surfaceChart p).source ∩ (surfaceChart q).source) :
    coordinateIntegral g F p s = coordinateIntegral g F q s := by
  have hi := chartTransition_image p q s hsub
  have hderiv : ∀ y ∈ (surfaceChart p) '' s,
      HasFDerivWithinAt (chartTransition p q) (chartTransitionDerivative p q y)
        ((surfaceChart p) '' s) y := fun y hy =>
    (chartTransition_hasFDerivWithinAt p q (hi.1 hy)).mono hi.1
  have hcov := integral_image_eq_integral_abs_det_fderiv_smul volume
    (extChart_image_measurable p s hs (hsub.trans inter_subset_left)) hderiv
    ((chartTransition_injOn p q).mono hi.1) (coordinateAreaDensity g F q)
  unfold coordinateIntegral
  rw [hi.2] at hcov
  rw [hcov]
  apply setIntegral_congr_fun (extChart_image_measurable p s hs (hsub.trans inter_subset_left))
  intro y hy
  exact coordinateAreaDensity_overlap g F hF p q (hi.1 hy)

/-- H07b: integrability transport uses the supplied full-overlap derivative. -/
theorem coordinateIntegrable_overlap (g : SmoothMetric M) {S : CompactOrientedSurface.{u}}
    (F : S → M) (hF : ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ F) (p q : S) (s : Set S)
    (hs : MeasurableSet s) (hsub : s ⊆ (surfaceChart p).source ∩ (surfaceChart q).source) :
    IntegrableOn (coordinateAreaDensity g F p) ((surfaceChart p) '' s) ↔
      IntegrableOn (coordinateAreaDensity g F q) ((surfaceChart q) '' s) := by
  have hi := chartTransition_image p q s hsub
  have hderiv : ∀ y ∈ (surfaceChart p) '' s,
      HasFDerivWithinAt (chartTransition p q) (chartTransitionDerivative p q y)
        ((surfaceChart p) '' s) y := fun y hy =>
    (chartTransition_hasFDerivWithinAt p q (hi.1 hy)).mono hi.1
  have hcov := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    (extChart_image_measurable p s hs (hsub.trans inter_subset_left)) hderiv
    ((chartTransition_injOn p q).mono hi.1) (coordinateAreaDensity g F q)
  rw [hi.2] at hcov
  rw [hcov]
  exact integrableOn_congr_fun (fun y hy =>
    coordinateAreaDensity_overlap g F hF p q (hi.1 hy))
      (extChart_image_measurable p s hs (hsub.trans inter_subset_left))

end SeifertSurfaces.MetricFoundations.AreaAnalysis
