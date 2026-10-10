import OriginalB1
open scoped Manifold ContDiff
open Set Topology MeasureTheory
namespace SeifertSurfaces.MetricFoundations.B1Bridges
open SeifertSurfaces.Foundations
universe u v
noncomputable section
set_option autoImplicit false
variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]

def imageTransitionDomain {S R : CompactOrientedSurface.{u}}
    {F : GeometricPiecewiseSurface S M} {G : GeometricPiecewiseSurface R M}
    (a : R ≃ₜ S) (cF : SmoothImageChart S F.map) (cG : SmoothImageChart R G.map) :
    Set (Euc 2) :=
  (𝓡∂ 2) '' (cG.chart.target ∩ cG.chart.symm ⁻¹'
    (R.boundaryᶜ ∩ a ⁻¹' cF.chart.source))

def imageTransitionCoordinate {S R : CompactOrientedSurface.{u}}
    {F : GeometricPiecewiseSurface S M} {G : GeometricPiecewiseSurface R M}
    (a : R ≃ₜ S) (cF : SmoothImageChart S F.map) (cG : SmoothImageChart R G.map) :
    Euc 2 → Euc 2 :=
  (𝓡∂ 2) ∘ cF.chart ∘ a ∘ cG.chart.symm ∘ (𝓡∂ 2).symm

def imageChartAmbientMap {S : CompactOrientedSurface.{u}}
    {F : GeometricPiecewiseSurface S M} (cF : SmoothImageChart S F.map) : Euc 2 → M :=
  F.map ∘ cF.chart.symm ∘ (𝓡∂ 2).symm

def imageTangentTransport {x y : M} (h : x = y)
    (w : TangentSpace (𝓡∂ 3) x) : TangentSpace (𝓡∂ 3) y := h ▸ w

theorem same_image_chart_transition_smooth {S R : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (G : GeometricPiecewiseSurface R M)
    (a : R ≃ₜ S) (ha : ∀ x, F.map (a x) = G.map x)
    (hb : a ⁻¹' S.boundary = R.boundary)
    (cF : SmoothImageChart S F.map) (cG : SmoothImageChart R G.map) :
    ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) ∞ (cF.chart ∘ a ∘ cG.chart.symm)
      (cG.chart.target ∩ cG.chart.symm ⁻¹'
        (R.boundaryᶜ ∩ a ⁻¹' cF.chart.source)) := by
  have euclidean_cancel (g : Euc 2 → Euc 3) (f : Euc 2 → Euc 2) (x : Euc 2)
      (hg : ContDiffAt ℝ ∞ g (f x)) (hinj : Function.Injective (fderiv ℝ g (f x)))
      (hf : ContinuousAt f x) (hgf : ContDiffAt ℝ ∞ (g ∘ f) x) :
      ContDiffAt ℝ ∞ f x := by
    obtain ⟨L, hL⟩ := ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hinj
    have hder : HasFDerivAt (L ∘ g) (ContinuousLinearEquiv.refl ℝ (Euc 2) : Euc 2 →L[ℝ] Euc 2) (f x) := by
      have h := L.hasFDerivAt.comp (f x) (hg.differentiableAt (by simp)).hasFDerivAt
      have hcomp : L.comp (fderiv ℝ g (f x)) = (ContinuousLinearEquiv.refl ℝ (Euc 2) : Euc 2 →L[ℝ] Euc 2) := by
        apply ContinuousLinearMap.ext
        intro w
        exact hL w
      simpa only [hcomp] using h
    have hsm : ContDiffAt ℝ ∞ (L ∘ g) (f x) := L.contDiff.contDiffAt.comp (f x) hg
    have hsmcomp : ContDiffAt ℝ ∞ (L ∘ g ∘ f) x := L.contDiff.contDiffAt.comp x hgf
    have hinv := hsm.to_localInverse hder (by simp)
    have heq := (hsm.hasStrictFDerivAt' hder (by simp)).eventually_left_inverse
    exact (hinv.comp x hsmcomp).congr_of_eventuallyEq (Filter.EventuallyEq.symm (hf.eventually heq))
  have manifold_cancel (g : EuclideanHalfSpace 2 → M) (f : EuclideanHalfSpace 2 → EuclideanHalfSpace 2)
      (x : EuclideanHalfSpace 2)
      (hx : (𝓡∂ 2).IsInteriorPoint x) (hfx : (𝓡∂ 2).IsInteriorPoint (f x))
      (hg : ContMDiffAt (𝓡∂ 2) (𝓡∂ 3) ∞ g (f x))
      (hinj : Function.Injective (mfderiv (𝓡∂ 2) (𝓡∂ 3) g (f x)))
      (hf : ContinuousAt f x) (hgf : ContMDiffAt (𝓡∂ 2) (𝓡∂ 3) ∞ (g ∘ f) x) :
      ContMDiffAt (𝓡∂ 2) (𝓡∂ 2) ∞ f x := by
    let u : Euc 2 → Euc 3 := extChartAt (𝓡∂ 3) (g (f x)) ∘ g ∘ (𝓡∂ 2).symm
    let v : Euc 2 → Euc 2 := (𝓡∂ 2) ∘ f ∘ (𝓡∂ 2).symm
    have hxu : Set.range (𝓡∂ 2) ∈ 𝓝 ((𝓡∂ 2) x) := range_mem_nhds_isInteriorPoint hx
    have hfxu : Set.range (𝓡∂ 2) ∈ 𝓝 ((𝓡∂ 2) (f x)) := range_mem_nhds_isInteriorPoint hfx
    have hvx : v ((𝓡∂ 2) x) = (𝓡∂ 2) (f x) := by simp only [v, Function.comp_apply, ModelWithCorners.left_inv]
    have hgu : ContDiffAt ℝ ∞ u ((𝓡∂ 2) (f x)) :=
      ((contMDiffAt_iff.mp hg).2).contDiffAt hfxu
    have hdu := (hg.mdifferentiableAt (by simp)).hasMFDerivAt.2.hasFDerivAt hfxu
    change HasFDerivAt u
      ((tangentSpaceCastModel (𝓡∂ 3) (g (f x))).toContinuousLinearMap.comp
        ((mfderiv (𝓡∂ 2) (𝓡∂ 3) g (f x)).comp
          (tangentSpaceCastModel (𝓡∂ 2) (f x)).symm.toContinuousLinearMap))
      ((𝓡∂ 2) (f x)) at hdu
    have hiu : Function.Injective (fderiv ℝ u ((𝓡∂ 2) (f x))) := by
      rw [hdu.fderiv]
      exact (tangentSpaceCastModel (𝓡∂ 3) (g (f x))).injective.comp
        (hinj.comp (tangentSpaceCastModel (𝓡∂ 2) (f x)).symm.injective)
    have hv : ContinuousAt v ((𝓡∂ 2) x) := by
      apply (𝓡∂ 2).continuousAt.comp
      apply ContinuousAt.comp _ (𝓡∂ 2).continuousAt_symm
      simpa only [ModelWithCorners.left_inv] using hf
    have huv : ContDiffAt ℝ ∞ (u ∘ v) ((𝓡∂ 2) x) := by
      have hh := ((contMDiffAt_iff.mp hgf).2).contDiffAt hxu
      change ContDiffAt ℝ ∞ (extChartAt (𝓡∂ 3) (g (f x)) ∘ (g ∘ f) ∘ (𝓡∂ 2).symm) ((𝓡∂ 2) x) at hh
      simpa only [u, v, Function.comp_def, ModelWithCorners.left_inv] using hh
    have hvsm : ContDiffAt ℝ ∞ v ((𝓡∂ 2) x) := by
      apply euclidean_cancel u v ((𝓡∂ 2) x) _ _ hv huv
      · simpa only [hvx] using hgu
      · simpa only [hvx] using hiu
    exact contMDiffAt_iff.mpr ⟨hf, hvsm.contDiffWithinAt⟩
  have chart_interior {P : CompactOrientedSurface.{u}} {H : GeometricPiecewiseSurface P M}
      (c : SmoothImageChart P H.map) (z : EuclideanHalfSpace 2)
      (hz : z ∈ c.chart.target) (hn : c.chart.symm z ∉ P.boundary) :
      (𝓡∂ 2).IsInteriorPoint z := by
    apply (ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint z).mpr
    intro hbad
    have hm : z ∈ (𝓡∂ 2).boundary (EuclideanHalfSpace 2) ∩ c.chart.target := ⟨hbad, hz⟩
    rw [← c.boundary_image] at hm
    obtain ⟨w, hw, he⟩ := hm
    apply hn
    rw [← he, c.chart.left_inv hw.2]
    exact hw.1
  intro x hx
  have hG : ContinuousAt cG.chart.symm x :=
    (cG.chart.symm.continuousOn x hx.1).continuousAt (cG.target_open.mem_nhds hx.1)
  have hax : ContinuousAt (a ∘ cG.chart.symm) x := a.continuous.continuousAt.comp hG
  have hF : ContinuousAt cF.chart (a (cG.chart.symm x)) :=
    (cF.chart.continuousOn _ hx.2.2).continuousAt (cF.source_open.mem_nhds hx.2.2)
  have htx : cF.chart (a (cG.chart.symm x)) ∈ cF.chart.target := cF.chart.map_source hx.2.2
  have hnot : a (cG.chart.symm x) ∉ S.boundary := by
    intro hbad
    apply hx.2.1
    rw [← hb]
    exact hbad
  have hgsm := cF.cInfinity.contMDiffAt (cF.target_open.mem_nhds htx)
  have hginj := cF.differential_injective _ htx
  rw [mfderivWithin_of_mem_nhds (cF.target_open.mem_nhds htx)] at hginj
  have hevent : (F.map ∘ cF.chart.symm) ∘ (cF.chart ∘ a ∘ cG.chart.symm)
      =ᶠ[𝓝 x] G.map ∘ cG.chart.symm := by
    filter_upwards [hax.eventually (cF.source_open.mem_nhds hx.2.2)] with z hz
    dsimp only [Function.comp_apply] at hz ⊢
    rw [cF.chart.left_inv hz, ha]
  have hcomp := (cG.cInfinity.contMDiffAt (cG.target_open.mem_nhds hx.1)).congr_of_eventuallyEq hevent
  apply ContMDiffAt.contMDiffWithinAt
  apply manifold_cancel (F.map ∘ cF.chart.symm) (cF.chart ∘ a ∘ cG.chart.symm) x
    (chart_interior cG x hx.1 hx.2.1) _ hgsm hginj ((hF.comp (a.continuous.continuousAt)).comp hG) hcomp
  apply chart_interior cF _ htx
  simpa only [Function.comp_apply, cF.chart.left_inv hx.2.2] using hnot

theorem same_image_chart_inverse_transition_smooth {S R : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (G : GeometricPiecewiseSurface R M)
    (a : R ≃ₜ S) (ha : ∀ x, F.map (a x) = G.map x)
    (hb : a ⁻¹' S.boundary = R.boundary)
    (cF : SmoothImageChart S F.map) (cG : SmoothImageChart R G.map) :
    ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) ∞ (cG.chart ∘ a.symm ∘ cF.chart.symm)
      (cF.chart.target ∩ cF.chart.symm ⁻¹'
        (S.boundaryᶜ ∩ a.symm ⁻¹' cG.chart.source)) := by
  apply same_image_chart_transition_smooth G F a.symm
  · intro x
    exact (ha (a.symm x)).symm.trans (congrArg F.map (a.apply_symm_apply x))
  · ext x
    change a.symm x ∈ R.boundary ↔ x ∈ S.boundary
    rw [← hb]
    change a (a.symm x) ∈ S.boundary ↔ x ∈ S.boundary
    rw [a.apply_symm_apply]

theorem same_image_euclidean_transition_geometry {S R : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (G : GeometricPiecewiseSurface R M)
    (a : R ≃ₜ S) (ha : ∀ x, F.map (a x) = G.map x)
    (hb : a ⁻¹' S.boundary = R.boundary)
    (cF : SmoothImageChart S F.map) (cG : SmoothImageChart R G.map) :
    let D := imageTransitionDomain a cF cG
    let T := imageTransitionCoordinate a cF cG
    IsOpen D ∧ ContDiffOn ℝ ∞ T D ∧ InjOn T D ∧
      MapsTo T D (imageTransitionDomain a.symm cG cF) ∧
      (∀ y ∈ D, imageTransitionCoordinate a.symm cG cF (T y) = y) ∧
      (∀ y ∈ D, HasFDerivAt T (fderiv ℝ T y) y ∧
        Function.Injective (fderiv ℝ T y) ∧ (fderiv ℝ T y).det ≠ 0) := by
  have chart_interior {P : CompactOrientedSurface.{u}} {H : GeometricPiecewiseSurface P M}
      (c : SmoothImageChart P H.map) (z : EuclideanHalfSpace 2)
      (hz : z ∈ c.chart.target) (hn : c.chart.symm z ∉ P.boundary) :
      (𝓡∂ 2).IsInteriorPoint z := by
    apply (ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint z).mpr
    intro hbad
    have hm : z ∈ (𝓡∂ 2).boundary (EuclideanHalfSpace 2) ∩ c.chart.target := ⟨hbad, hz⟩
    rw [← c.boundary_image] at hm
    obtain ⟨w, hw, he⟩ := hm
    apply hn
    rw [← he, c.chart.left_inv hw.2]
    exact hw.1
  have basic {S R : CompactOrientedSurface.{u}}
      (F : GeometricPiecewiseSurface S M) (G : GeometricPiecewiseSurface R M)
      (a : R ≃ₜ S) (hb : a ⁻¹' S.boundary = R.boundary)
      (cF : SmoothImageChart S F.map) (cG : SmoothImageChart R G.map)
      (hsm : ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) ∞ (cF.chart ∘ a ∘ cG.chart.symm)
        (cG.chart.target ∩ cG.chart.symm ⁻¹' (R.boundaryᶜ ∩ a ⁻¹' cF.chart.source))) :
      IsOpen (imageTransitionDomain a cF cG) ∧
      ContDiffOn ℝ ∞ (imageTransitionCoordinate a cF cG) (imageTransitionDomain a cF cG) ∧
      MapsTo (imageTransitionCoordinate a cF cG) (imageTransitionDomain a cF cG)
        (imageTransitionDomain a.symm cG cF) ∧
      (∀ y ∈ imageTransitionDomain a cF cG,
        imageTransitionCoordinate a.symm cG cF (imageTransitionCoordinate a cF cG y) = y) := by
    let U := cG.chart.target ∩ cG.chart.symm ⁻¹' (R.boundaryᶜ ∩ a ⁻¹' cF.chart.source)
    have hopen : IsOpen U := by
      apply cG.chart.symm.continuousOn.isOpen_inter_preimage cG.target_open
      apply IsOpen.inter _ (cF.source_open.preimage a.continuous)
      exact (ModelWithCorners.isClosed_boundary (n := ∞) (by simp)).isOpen_compl
    have hnhds : ∀ x ∈ U, imageTransitionDomain a cF cG ∈ 𝓝 ((𝓡∂ 2) x) := by
      intro x hx
      have hr : Set.range (𝓡∂ 2) ∈ 𝓝 ((𝓡∂ 2) x) :=
        range_mem_nhds_isInteriorPoint (chart_interior cG x hx.1 hx.2.1)
      have hu := (𝓡∂ 2).continuousAt_symm.preimage_mem_nhds
        (show U ∈ 𝓝 ((𝓡∂ 2).symm ((𝓡∂ 2) x)) by
          simpa only [ModelWithCorners.left_inv] using hopen.mem_nhds hx)
      filter_upwards [hr, hu] with y hyr hyu
      exact ⟨(𝓡∂ 2).symm y, hyu, (𝓡∂ 2).right_inv hyr⟩
    refine ⟨isOpen_iff_mem_nhds.mpr ?_, ?_, ?_, ?_⟩
    · rintro y ⟨x, hx, rfl⟩
      exact hnhds x hx
    · rintro y ⟨x, hx, rfl⟩
      have h := hsm.contMDiffAt (hopen.mem_nhds hx)
      have hr : Set.range (𝓡∂ 2) ∈ 𝓝 ((𝓡∂ 2) x) :=
        range_mem_nhds_isInteriorPoint (chart_interior cG x hx.1 hx.2.1)
      exact ((contMDiffAt_iff.mp h).2.contDiffAt hr).contDiffWithinAt
    · rintro y ⟨x, hx, rfl⟩
      refine ⟨cF.chart (a (cG.chart.symm x)), ?_, ?_⟩
      · refine ⟨cF.chart.map_source hx.2.2, ?_, ?_⟩
        · change cF.chart.symm (cF.chart (a (cG.chart.symm x))) ∉ S.boundary
          rw [cF.chart.left_inv hx.2.2]
          intro hbad
          apply hx.2.1
          rw [← hb]
          exact hbad
        · change a.symm (cF.chart.symm (cF.chart (a (cG.chart.symm x)))) ∈ cG.chart.source
          rw [cF.chart.left_inv hx.2.2, a.symm_apply_apply]
          exact cG.chart.map_target hx.1
      · dsimp only [imageTransitionCoordinate, Function.comp_apply]
        rw [ModelWithCorners.left_inv]
    · rintro y ⟨x, hx, rfl⟩
      dsimp only [imageTransitionCoordinate, Function.comp_apply]
      rw [ModelWithCorners.left_inv, ModelWithCorners.left_inv, cF.chart.left_inv hx.2.2,
        a.symm_apply_apply, cG.chart.right_inv hx.1]
  have hforward := basic F G a hb cF cG (same_image_chart_transition_smooth F G a ha hb cF cG)
  have hbackBoundary : a.symm ⁻¹' R.boundary = S.boundary := by
    ext x
    change a.symm x ∈ R.boundary ↔ x ∈ S.boundary
    rw [← hb]
    change a (a.symm x) ∈ S.boundary ↔ x ∈ S.boundary
    rw [a.apply_symm_apply]
  have hback := basic G F a.symm hbackBoundary cG cF
    (same_image_chart_inverse_transition_smooth F G a ha hb cF cG)
  dsimp only
  refine ⟨hforward.1, hforward.2.1, ?_, hforward.2.2.1, hforward.2.2.2, ?_⟩
  · intro x hx y hy heq
    rw [← hforward.2.2.2 x hx, ← hforward.2.2.2 y hy, heq]
  · intro y hy
    have hT := (hforward.2.1.contDiffAt (hforward.1.mem_nhds hy)).differentiableAt (by simp)
    have hU := (hback.2.1.contDiffAt
      (hback.1.mem_nhds (hforward.2.2.1 hy))).differentiableAt (by simp)
    have heq : imageTransitionCoordinate a.symm cG cF ∘ imageTransitionCoordinate a cF cG
        =ᶠ[𝓝 y] id := Filter.eventuallyEq_of_mem (hforward.1.mem_nhds hy) hforward.2.2.2
    have hid := (hU.hasFDerivAt.comp y hT.hasFDerivAt).congr_of_eventuallyEq heq.symm
    have hlin := hid.unique (hasFDerivAt_id y)
    have hleft : Function.LeftInverse
        (fderiv ℝ (imageTransitionCoordinate a.symm cG cF) (imageTransitionCoordinate a cF cG y))
        (fderiv ℝ (imageTransitionCoordinate a cF cG) y) := by
      intro w
      exact congrArg (fun L : Euc 2 →L[ℝ] Euc 2 => L w) hlin
    refine ⟨hT.hasFDerivAt, hleft.injective, ?_⟩
    change (fderiv ℝ (imageTransitionCoordinate a cF cG) y).toLinearMap.det ≠ 0
    intro hz
    exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hz) (LinearMap.ker_eq_bot.mpr hleft.injective)

theorem same_image_ambient_derivative_factor {S R : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (G : GeometricPiecewiseSurface R M)
    (a : R ≃ₜ S) (ha : ∀ x, F.map (a x) = G.map x)
    (hb : a ⁻¹' S.boundary = R.boundary)
    (cF : SmoothImageChart S F.map) (cG : SmoothImageChart R G.map)
    (y : Euc 2) (hy : y ∈ imageTransitionDomain a cF cG) :
    let T := imageTransitionCoordinate a cF cG
    ∃ hpoint : imageChartAmbientMap cF (T y) = imageChartAmbientMap cG y,
      MDifferentiableAt 𝓘(ℝ, Euc 2) (𝓡∂ 3) (imageChartAmbientMap cG) y ∧
      MDifferentiableAt 𝓘(ℝ, Euc 2) (𝓡∂ 3) (imageChartAmbientMap cF) (T y) ∧
      ∀ w : Euc 2,
        mfderiv 𝓘(ℝ, Euc 2) (𝓡∂ 3) (imageChartAmbientMap cG) y
          ((tangentSpaceCastModel 𝓘(ℝ, Euc 2) y).symm w) =
        imageTangentTransport hpoint
          (mfderiv 𝓘(ℝ, Euc 2) (𝓡∂ 3) (imageChartAmbientMap cF) (T y)
            ((tangentSpaceCastModel 𝓘(ℝ, Euc 2) (T y)).symm (fderiv ℝ T y w))) := by
  have ambient_regular {P : CompactOrientedSurface.{u}} {H : GeometricPiecewiseSurface P M}
      (c : SmoothImageChart P H.map) (z : EuclideanHalfSpace 2)
      (hz : z ∈ c.chart.target) (hn : c.chart.symm z ∉ P.boundary) :
      MDifferentiableAt 𝓘(ℝ, Euc 2) (𝓡∂ 3) (imageChartAmbientMap c) ((𝓡∂ 2) z) := by
    have hi : (𝓡∂ 2).IsInteriorPoint z := by
      apply (ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint z).mpr
      intro hbad
      have hm : z ∈ (𝓡∂ 2).boundary (EuclideanHalfSpace 2) ∩ c.chart.target := ⟨hbad, hz⟩
      rw [← c.boundary_image] at hm
      obtain ⟨w, hw, he⟩ := hm
      apply hn
      rw [← he, c.chart.left_inv hw.2]
      exact hw.1
    have hmodel : ContMDiffAt 𝓘(ℝ, Euc 2) (𝓡∂ 2) ∞ (𝓡∂ 2).symm ((𝓡∂ 2) z) :=
      (𝓡∂ 2).contMDiffOn_symm.contMDiffAt (range_mem_nhds_isInteriorPoint hi)
    have hc := c.cInfinity.contMDiffAt (c.target_open.mem_nhds hz)
    have hc' : ContMDiffAt (𝓡∂ 2) (𝓡∂ 3) ∞ (H.map ∘ c.chart.symm)
        ((𝓡∂ 2).symm ((𝓡∂ 2) z)) := by
      simpa only [ModelWithCorners.left_inv] using hc
    exact (hc'.comp ((𝓡∂ 2) z) hmodel).mdifferentiableAt (by simp)
  have hgeo := same_image_euclidean_transition_geometry F G a ha hb cF cG
  have hpointwise : ∀ z ∈ imageTransitionDomain a cF cG,
      imageChartAmbientMap cF (imageTransitionCoordinate a cF cG z) = imageChartAmbientMap cG z := by
    rintro z ⟨x, hx, rfl⟩
    dsimp only [imageChartAmbientMap, imageTransitionCoordinate, Function.comp_apply]
    rw [ModelWithCorners.left_inv, ModelWithCorners.left_inv, cF.chart.left_inv hx.2.2, ha]
  have hpoint := hpointwise y hy
  refine ⟨hpoint, ?_, ?_, ?_⟩
  · obtain ⟨z, hz, rfl⟩ := hy
    exact ambient_regular cG z hz.1 hz.2.1
  · obtain ⟨z, hz, heq⟩ := hgeo.2.2.2.1 hy
    rw [← heq]
    exact ambient_regular cF z hz.1 hz.2.1
  · intro w
    have hFreg : MDifferentiableAt 𝓘(ℝ, Euc 2) (𝓡∂ 3) (imageChartAmbientMap cF)
        (imageTransitionCoordinate a cF cG y) := by
      obtain ⟨z, hz, heq⟩ := hgeo.2.2.2.1 hy
      rw [← heq]
      exact ambient_regular cF z hz.1 hz.2.1
    have hTreg := ((hgeo.2.1.contDiffAt (hgeo.1.mem_nhds hy)).contMDiffAt).mdifferentiableAt (by simp)
    have hevent : imageChartAmbientMap cF ∘ imageTransitionCoordinate a cF cG
        =ᶠ[𝓝 y] imageChartAmbientMap cG :=
      Filter.eventuallyEq_of_mem (hgeo.1.mem_nhds hy) hpointwise
    have heq := Filter.EventuallyEq.mfderiv_eq (I := 𝓘(ℝ, Euc 2)) (I' := 𝓡∂ 3) hevent.symm
    rw [mfderiv_comp y hFreg hTreg, mfderiv_eq_fderiv] at heq
    have htransport {p q : M} (h : p = q) (v : TangentSpace (𝓡∂ 3) p) :
        imageTangentTransport h v = tangentSpaceCast (𝓡∂ 3) p q v := by
      subst q
      rfl
    rw [htransport]
    exact congrArg (fun L => L ((tangentSpaceCastModel 𝓘(ℝ, Euc 2) y).symm w)) heq
end
end SeifertSurfaces.MetricFoundations.B1Bridges
