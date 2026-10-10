import MetricAreaGeometryDefinitions

set_option maxSynthPendingDepth 3
open scoped Manifold ContDiff
open Set Topology MeasureTheory Bundle
namespace SeifertSurfaces.MetricFoundations.AreaCertificates
open Foundations AreaAnalysis
universe u v
noncomputable section
variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]

theorem geometricSameImageHomeomorph_properties {S R : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (G : GeometricPiecewiseSurface R M)
    (heq : F.image = G.image) :
    (∀ x, F.map (geometricSameImageHomeomorph F G heq x) = G.map x) ∧
    (geometricSameImageHomeomorph F G heq) ⁻¹' S.boundary = R.boundary ∧
    (geometricSameImageHomeomorph F G heq).symm = geometricSameImageHomeomorph G F heq.symm := by
  have hmatch (x : R) : F.map (geometricSameImageHomeomorph F G heq x) = G.map x := by
    have he := F.embedding.toHomeomorph.apply_symm_apply
      (Homeomorph.setCongr heq.symm (G.embedding.toHomeomorph x))
    exact congrArg Subtype.val he
  refine ⟨hmatch, ?_, ?_⟩
  · ext x
    change geometricSameImageHomeomorph F G heq x ∈ S.boundary ↔ x ∈ R.boundary
    rw [← F.boundary_preimage, ← G.boundary_preimage]
    simp only [Set.mem_preimage, hmatch]
  · ext x
    apply G.embedding.injective
    have hi := hmatch ((geometricSameImageHomeomorph F G heq).symm x)
    have he := G.embedding.toHomeomorph.apply_symm_apply
      (Homeomorph.setCongr heq (F.embedding.toHomeomorph x))
    have hi' : F.map x = G.map ((geometricSameImageHomeomorph F G heq).symm x) := by
      simpa only [Homeomorph.apply_symm_apply] using hi
    exact hi'.symm.trans
      (congrArg Subtype.val he).symm

theorem smoothImage_local_inverse {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (c : SmoothImageChart S F.map)
    (y₀ : EuclideanHalfSpace 2) (hy : y₀ ∈ c.chart.target)
    (hinterior : y₀ ∉ (𝓡∂ 2).boundary (EuclideanHalfSpace 2)) :
    Nonempty (SmoothImageLocalInverse F c y₀) := by
  have hi : (𝓡∂ 2) y₀ ∈ interior (Set.range (𝓡∂ 2)) := by
    have he := (𝓡∂ 2).isInteriorPoint_iff.mp
      (((𝓡∂ 2).isInteriorPoint_iff_not_isBoundaryPoint y₀).mpr hinterior)
    simpa [mfld_simps] using he
  have hrange : Set.range (𝓡∂ 2) ∈ 𝓝 ((𝓡∂ 2) y₀) :=
    Filter.mem_of_superset (isOpen_interior.mem_nhds hi) interior_subset
  have hbase : (𝓡∂ 2) y₀ ∈ interior (imageChartEuclideanTarget c) := by
    apply mem_interior_iff_mem_nhds.mpr
    rw [← nhdsWithin_eq_nhds.2 hrange]
    exact (𝓡∂ 2).image_mem_nhdsWithin (c.target_open.mem_nhds hy)
  have htarget {z : Euc 2} (hz : z ∈ interior (imageChartEuclideanTarget c)) :
      (𝓡∂ 2).symm z ∈ c.chart.target := by
    rcases interior_subset hz with ⟨w, hw, rfl⟩
    simpa only [ModelWithCorners.left_inv] using hw
  have hzrange {z : Euc 2} (hz : z ∈ interior (imageChartEuclideanTarget c)) :
      z ∈ Set.range (𝓡∂ 2) := by
    rcases interior_subset hz with ⟨w, hw, rfl⟩
    exact Set.mem_range_self _
  have hx : c.chart.symm y₀ ∉ S.boundary := by
    intro hs
    have he : y₀ ∈ c.chart '' (S.boundary ∩ c.chart.source) :=
      ⟨c.chart.symm y₀, ⟨hs, c.chart.map_target hy⟩, c.chart.right_inv hy⟩
    rw [c.boundary_image] at he
    exact hinterior he.1
  have hfx : F.map (c.chart.symm y₀) ∉ (𝓡∂ 3).boundary M := by
    intro h
    apply hx
    rw [← F.boundary_preimage]
    exact h
  let T := (extChartAt (𝓡∂ 3) (F.map (c.chart.symm y₀))).source ∩
    ((𝓡∂ 3).boundary M)ᶜ
  have hT : IsOpen T := (isOpen_extChartAt_source _).inter
    (((𝓡∂ 3).isClosed_boundary (M := M) (n := ∞) (by simp)).isOpen_compl)
  let D := interior (imageChartEuclideanTarget c) ∩
    (F.map ∘ c.chart.symm ∘ (𝓡∂ 2).symm) ⁻¹' T
  have hcont : ContinuousOn (F.map ∘ c.chart.symm ∘ (𝓡∂ 2).symm)
      (interior (imageChartEuclideanTarget c)) :=
    F.map.continuous.comp_continuousOn
      (c.chart.symm.continuousOn.comp (𝓡∂ 2).continuous_symm.continuousOn
        (fun _ hz => htarget hz))
  have hD : IsOpen D := hcont.isOpen_inter_preimage isOpen_interior hT
  have hyD : (𝓡∂ 2) y₀ ∈ D := by
    refine ⟨hbase, ?_⟩
    change F.map (c.chart.symm ((𝓡∂ 2).symm ((𝓡∂ 2) y₀))) ∈ T
    simpa only [ModelWithCorners.left_inv] using
      (show F.map (c.chart.symm y₀) ∈ T from ⟨mem_extChartAt_source _, hfx⟩)
  have hF : ContDiffOn ℝ ∞ (imageChartAmbientCoordinates F c y₀) D := by
    have hsrc : ContMDiffOn 𝓘(ℝ, Euc 2) (𝓡∂ 2) ∞ (𝓡∂ 2).symm D :=
      (𝓡∂ 2).contMDiffOn_symm.mono (fun _ hz => hzrange hz.1)
    have hf := c.cInfinity.comp hsrc (fun _ hz => htarget hz.1)
    have htar : ContMDiffOn (𝓡∂ 3) 𝓘(ℝ, Euc 3) ∞
        (extChartAt (𝓡∂ 3) (F.map (c.chart.symm y₀)))
        (extChartAt (𝓡∂ 3) (F.map (c.chart.symm y₀))).source := by
      simpa only [extChartAt_source] using contMDiffOn_extChartAt
        (I := 𝓡∂ 3) (n := ∞) (x := F.map (c.chart.symm y₀))
    exact (htar.comp hf (fun _ hz => hz.2.1)).contDiffOn
  have hmd : MDifferentiableAt (𝓡∂ 2) (𝓡∂ 3) (F.map ∘ c.chart.symm) y₀ :=
    (c.cInfinity.contMDiffAt (c.target_open.mem_nhds hy)).mdifferentiableAt (by simp)
  have hd := c.differential_injective y₀ hy
  rw [mfderivWithin_of_mem_nhds (c.target_open.mem_nhds hy), hmd.mfderiv] at hd
  simp only [extChartAt_self_apply, fderivWithin_of_mem_nhds hrange] at hd
  have hraw : writtenInExtChartAt (𝓡∂ 2) (𝓡∂ 3) y₀ (F.map ∘ c.chart.symm) =
      imageChartAmbientCoordinates F c y₀ := by
    funext z
    rfl
  rw [hraw] at hd
  simp only [Function.comp_apply] at hd
  have hinj : Function.Injective
      (fderiv ℝ (imageChartAmbientCoordinates F c y₀) ((𝓡∂ 2) y₀)) := by
    intro v w hvw
    have he : (tangentSpaceCastModel (𝓡∂ 2) y₀).symm v =
        (tangentSpaceCastModel (𝓡∂ 2) y₀).symm w := hd (by
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.apply_symm_apply] using
        congrArg (tangentSpaceCastModel (𝓡∂ 3) (F.map (c.chart.symm y₀))).symm hvw)
    exact (tangentSpaceCastModel (𝓡∂ 2) y₀).symm.injective he
  obtain ⟨L⟩ := euclideanImmersion_local_leftInverse
    (imageChartAmbientCoordinates F c y₀) D hD ((𝓡∂ 2) y₀) hyD hF hinj
  exact ⟨⟨D, hD, hyD, fun _ hz => hz.1, fun _ hz => hz.2, hF, hinj, L⟩⟩

def sameImageCoordinateHomeomorph {S R : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (G : GeometricPiecewiseSurface R M)
    (heq : F.image = G.image) (cF : SmoothImageChart S F.map)
    (cG : SmoothImageChart R G.map) :
    OpenPartialHomeomorph (EuclideanHalfSpace 2) (EuclideanHalfSpace 2) where
  toFun := imageCoordinateTransition (geometricSameImageHomeomorph F G heq) cF cG
  invFun := imageCoordinateTransition (geometricSameImageHomeomorph F G heq).symm cG cF
  source := imageInteriorCoordinateDomain (geometricSameImageHomeomorph F G heq) cF cG
  target := imageInteriorCoordinateDomain (geometricSameImageHomeomorph F G heq).symm cG cF
  map_source' := by
    intro y hy
    change y ∈ cG.chart.target ∧ cG.chart.symm y ∈ R.boundaryᶜ ∧
      geometricSameImageHomeomorph F G heq (cG.chart.symm y) ∈ cF.chart.source at hy
    change cF.chart (geometricSameImageHomeomorph F G heq (cG.chart.symm y)) ∈ cF.chart.target ∧
      cF.chart.symm (cF.chart (geometricSameImageHomeomorph F G heq (cG.chart.symm y))) ∈ S.boundaryᶜ ∧
      (geometricSameImageHomeomorph F G heq).symm
        (cF.chart.symm (cF.chart (geometricSameImageHomeomorph F G heq (cG.chart.symm y)))) ∈ cG.chart.source
    rw [cF.chart.left_inv hy.2.2]
    refine ⟨cF.chart.map_source hy.2.2, ?_, ?_⟩
    · intro hs
      apply hy.2.1
      rw [← (geometricSameImageHomeomorph_properties F G heq).2.1]
      exact hs
    · simpa only [Homeomorph.symm_apply_apply] using cG.chart.map_target hy.1
  map_target' := by
    intro y hy
    change y ∈ cF.chart.target ∧ cF.chart.symm y ∈ S.boundaryᶜ ∧
      (geometricSameImageHomeomorph F G heq).symm (cF.chart.symm y) ∈ cG.chart.source at hy
    change cG.chart ((geometricSameImageHomeomorph F G heq).symm (cF.chart.symm y)) ∈ cG.chart.target ∧
      cG.chart.symm (cG.chart ((geometricSameImageHomeomorph F G heq).symm (cF.chart.symm y))) ∈ R.boundaryᶜ ∧
      geometricSameImageHomeomorph F G heq
        (cG.chart.symm (cG.chart ((geometricSameImageHomeomorph F G heq).symm (cF.chart.symm y)))) ∈ cF.chart.source
    rw [cG.chart.left_inv hy.2.2]
    refine ⟨cG.chart.map_source hy.2.2, ?_, ?_⟩
    · intro hr
      apply hy.2.1
      have hs : geometricSameImageHomeomorph F G heq
          ((geometricSameImageHomeomorph F G heq).symm (cF.chart.symm y)) ∈ S.boundary := by
        rw [← (geometricSameImageHomeomorph_properties F G heq).2.1] at hr
        exact hr
      simpa only [Homeomorph.apply_symm_apply] using hs
    · simpa only [Homeomorph.apply_symm_apply] using cF.chart.map_target hy.1
  left_inv' := by
    intro y hy
    simp only [imageInteriorCoordinateDomain, Set.mem_inter_iff, Set.mem_preimage] at hy
    simp only [imageCoordinateTransition, Function.comp_apply,
      cF.chart.left_inv hy.2.2, Homeomorph.symm_apply_apply, cG.chart.right_inv hy.1]
  right_inv' := by
    intro y hy
    simp only [imageInteriorCoordinateDomain, Set.mem_inter_iff, Set.mem_preimage] at hy
    simp only [imageCoordinateTransition, Function.comp_apply,
      cG.chart.left_inv hy.2.2, Homeomorph.apply_symm_apply, cF.chart.right_inv hy.1]
  continuousOn_toFun := by
    apply cF.chart.continuousOn.comp
      ((geometricSameImageHomeomorph F G heq).continuous.comp_continuousOn
        (cG.chart.symm.continuousOn.mono inter_subset_left))
    exact fun _ hy => hy.2.2
  continuousOn_invFun := by
    apply cG.chart.continuousOn.comp
      ((geometricSameImageHomeomorph F G heq).symm.continuous.comp_continuousOn
        (cF.chart.symm.continuousOn.mono inter_subset_left))
    exact fun _ hy => hy.2.2
  open_source := by
    apply cG.chart.symm.continuousOn.isOpen_inter_preimage cG.target_open
    exact ((𝓡∂ 2).isClosed_boundary (M := R) (n := ∞) (by simp)).isOpen_compl.inter
      (cF.source_open.preimage (geometricSameImageHomeomorph F G heq).continuous)
  open_target := by
    apply cF.chart.symm.continuousOn.isOpen_inter_preimage cF.target_open
    exact ((𝓡∂ 2).isClosed_boundary (M := S) (n := ∞) (by simp)).isOpen_compl.inter
      (cG.source_open.preimage (geometricSameImageHomeomorph F G heq).symm.continuous)

theorem sameImageCoordinateHomeomorph_smooth {S R : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (G : GeometricPiecewiseSurface R M)
    (heq : F.image = G.image) (cF : SmoothImageChart S F.map)
    (cG : SmoothImageChart R G.map) :
    ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) ∞ (sameImageCoordinateHomeomorph F G heq cF cG)
      (sameImageCoordinateHomeomorph F G heq cF cG).source ∧
    ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) ∞ (sameImageCoordinateHomeomorph F G heq cF cG).symm
      (sameImageCoordinateHomeomorph F G heq cF cG).target ∧
    (∀ y ∈ (sameImageCoordinateHomeomorph F G heq cF cG).source, Function.Injective
      (mfderivWithin (𝓡∂ 2) (𝓡∂ 2) (sameImageCoordinateHomeomorph F G heq cF cG)
        (sameImageCoordinateHomeomorph F G heq cF cG).source y)) := by
  have hsmooth : ∀ {S R : CompactOrientedSurface.{u}}
      (F : GeometricPiecewiseSurface S M) (G : GeometricPiecewiseSurface R M)
      (heq : F.image = G.image) (cF : SmoothImageChart S F.map)
      (cG : SmoothImageChart R G.map),
      ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) ∞
        (sameImageCoordinateHomeomorph F G heq cF cG)
        (sameImageCoordinateHomeomorph F G heq cF cG).source := by
    intro S R F G heq cF cG y hy
    let C := sameImageCoordinateHomeomorph F G heq cF cG
    have hyF : C y ∈ cF.chart.target := (C.map_source hy).1
    have hinterior : C y ∉ (𝓡∂ 2).boundary (EuclideanHalfSpace 2) := by
      intro hb
      have hbc : C y ∈ cF.chart '' (S.boundary ∩ cF.chart.source) := by
        rw [cF.boundary_image]
        exact ⟨hb, hyF⟩
      rcases hbc with ⟨x, ⟨hx, hxs⟩, hxy⟩
      have ha : geometricSameImageHomeomorph F G heq (cG.chart.symm y) = x := by
        apply cF.chart.injOn hy.2.2 hxs
        exact hxy.symm
      apply hy.2.1
      rw [← (geometricSameImageHomeomorph_properties F G heq).2.1]
      change geometricSameImageHomeomorph F G heq (cG.chart.symm y) ∈ S.boundary
      rw [ha]
      exact hx
    obtain ⟨L⟩ := smoothImage_local_inverse F cF (C y) hyF hinterior
    let U := C.source ∩ ((𝓡∂ 2) ∘ C) ⁻¹' L.inverse.source
    have hU : IsOpen U :=
      ((𝓡∂ 2).continuous.comp_continuousOn C.continuousOn).isOpen_inter_preimage
        C.open_source L.inverse.open_source
    have hyU : y ∈ U := ⟨hy, L.inverse.source_mem⟩
    have hidentity (z : EuclideanHalfSpace 2) (hz : z ∈ U) :
        imageChartAmbientCoordinates F cF (C y) ((𝓡∂ 2) (C z)) =
          extChartAt (𝓡∂ 3) (F.map (cF.chart.symm (C y))) (G.map (cG.chart.symm z)) := by
      simp only [imageChartAmbientCoordinates, Function.comp_apply, ModelWithCorners.left_inv]
      change extChartAt (𝓡∂ 3) _ (F.map (cF.chart.symm
        (cF.chart (geometricSameImageHomeomorph F G heq (cG.chart.symm z))))) = _
      rw [cF.chart.left_inv hz.1.2.2,
        (geometricSameImageHomeomorph_properties F G heq).1]
    have htarget (z : EuclideanHalfSpace 2) (hz : z ∈ U) :
        extChartAt (𝓡∂ 3) (F.map (cF.chart.symm (C y))) (G.map (cG.chart.symm z))
          ∈ L.inverse.target := by
      rw [← hidentity z hz]
      exact L.inverse.mapsTo hz.2
    have hcoord (z : EuclideanHalfSpace 2) (hz : z ∈ U) :
        (𝓡∂ 2) (C z) = L.inverse.map
          (extChartAt (𝓡∂ 3) (F.map (cF.chart.symm (C y))) (G.map (cG.chart.symm z))) := by
      rw [← hidentity z hz]
      exact (L.inverse.left_inverse _ hz.2).symm
    have hpoint : F.map (cF.chart.symm (C y)) = G.map (cG.chart.symm y) := by
      change F.map (cF.chart.symm (cF.chart
        (geometricSameImageHomeomorph F G heq (cG.chart.symm y)))) = _
      rw [cF.chart.left_inv hy.2.2,
        (geometricSameImageHomeomorph_properties F G heq).1]
    have hmap : ContMDiffAt 𝓘(ℝ, Euc 3) 𝓘(ℝ, Euc 2) ∞ L.inverse.map
        (extChartAt (𝓡∂ 3) (F.map (cF.chart.symm (C y))) (G.map (cG.chart.symm y))) :=
      (L.inverse.smooth.contDiffAt
        (L.inverse.open_target.mem_nhds (htarget y hyU))).contMDiffAt
    have hchart : ContMDiffAt (𝓡∂ 3) 𝓘(ℝ, Euc 3) ∞
        (extChartAt (𝓡∂ 3) (F.map (cF.chart.symm (C y)))) (G.map (cG.chart.symm y)) := by
      rw [← hpoint]
      exact contMDiffAt_extChartAt
    have hg := cG.cInfinity.contMDiffAt (cG.target_open.mem_nhds hy.1)
    have hcompose := hmap.comp y (hchart.comp y hg)
    have hevent : ((𝓡∂ 2) ∘ C) =ᶠ[𝓝 y]
        (L.inverse.map ∘ extChartAt (𝓡∂ 3) (F.map (cF.chart.symm (C y))) ∘
          (G.map ∘ cG.chart.symm)) := by
      filter_upwards [hU.mem_nhds hyU] with z hz
      exact hcoord z hz
    have hC : ContMDiffAt (𝓡∂ 2) (𝓡∂ 2) ∞ C y := by
      apply contMDiffAt_iff_target.mpr
      exact ⟨C.continuousOn.continuousAt (C.open_source.mem_nhds hy),
        hcompose.congr_of_eventuallyEq hevent⟩
    exact hC.contMDiffWithinAt
  let C := sameImageCoordinateHomeomorph F G heq cF cG
  have hfor := hsmooth F G heq cF cG
  have hinv : ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) ∞ C.symm C.target := by
    have h := hsmooth G F heq.symm cG cF
    change ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) ∞
      (imageCoordinateTransition (geometricSameImageHomeomorph G F heq.symm) cG cF)
      (imageInteriorCoordinateDomain (geometricSameImageHomeomorph G F heq.symm) cG cF) at h
    change ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) ∞
      (imageCoordinateTransition (geometricSameImageHomeomorph F G heq).symm cG cF)
      (imageInteriorCoordinateDomain (geometricSameImageHomeomorph F G heq).symm cG cF)
    rw [(geometricSameImageHomeomorph_properties F G heq).2.2]
    exact h
  refine ⟨hfor, hinv, ?_⟩
  intro y hy
  have hdfor := (hfor y hy).mdifferentiableWithinAt (by simp)
  have hdinv := (hinv (C y) (C.map_source hy)).mdifferentiableWithinAt (by simp)
  have hchain := mfderivWithin_comp y hdinv hdfor C.mapsTo (C.open_source.uniqueMDiffOn y hy)
  have heq : (C.symm ∘ C) =ᶠ[𝓝[C.source] y] id := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact C.left_inv hz
  have hd := heq.mfderivWithin_eq_of_mem hy (I := 𝓡∂ 2) (I' := 𝓡∂ 2)
  rw [hd, mfderivWithin_id] at hchain
  · intro v w hvw
    have hv := congrArg (fun L : TangentSpace (𝓡∂ 2) y →L[ℝ] TangentSpace (𝓡∂ 2) y => L v) hchain
    have hw := congrArg (fun L : TangentSpace (𝓡∂ 2) y →L[ℝ] TangentSpace (𝓡∂ 2) y => L w) hchain
    have hmid : (mfderivWithin (𝓡∂ 2) (𝓡∂ 2) C.symm C.target (C y))
        ((mfderivWithin (𝓡∂ 2) (𝓡∂ 2) C C.source y) v) =
        (mfderivWithin (𝓡∂ 2) (𝓡∂ 2) C.symm C.target (C y))
        ((mfderivWithin (𝓡∂ 2) (𝓡∂ 2) C C.source y) w) := congrArg _ hvw
    apply (tangentSpaceCast (𝓡∂ 2) (id y) ((C.symm ∘ C) y)).injective
    exact hv.trans (hmid.trans hw.symm)
  · exact C.open_source.uniqueMDiffOn y hy

theorem sameImage_local_coordinate_identity {S R : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (G : GeometricPiecewiseSurface R M)
    (heq : F.image = G.image) (cF : SmoothImageChart S F.map)
    (cG : SmoothImageChart R G.map) (y₀ : EuclideanHalfSpace 2)
    (hy : y₀ ∈ imageInteriorCoordinateDomain (geometricSameImageHomeomorph F G heq) cF cG)
    (L : SmoothImageLocalInverse F cF
      (imageCoordinateTransition (geometricSameImageHomeomorph F G heq) cF cG y₀)) :
    ∃ U : Set (EuclideanHalfSpace 2), IsOpen U ∧ y₀ ∈ U ∧
      U ⊆ imageInteriorCoordinateDomain (geometricSameImageHomeomorph F G heq) cF cG ∧
      (∀ z ∈ U, (𝓡∂ 2)
          (imageCoordinateTransition (geometricSameImageHomeomorph F G heq) cF cG z)
        ∈ L.inverse.source) ∧
      (∀ z ∈ U, extChartAt (𝓡∂ 3)
          (F.map (cF.chart.symm
            (imageCoordinateTransition (geometricSameImageHomeomorph F G heq) cF cG y₀)))
          (G.map (cG.chart.symm z)) ∈ L.inverse.target) ∧
      ∀ z ∈ U, (𝓡∂ 2)
          (imageCoordinateTransition (geometricSameImageHomeomorph F G heq) cF cG z) =
        L.inverse.map (extChartAt (𝓡∂ 3)
          (F.map (cF.chart.symm
            (imageCoordinateTransition (geometricSameImageHomeomorph F G heq) cF cG y₀)))
          (G.map (cG.chart.symm z))) := by
  let C := sameImageCoordinateHomeomorph F G heq cF cG
  let U : Set (EuclideanHalfSpace 2) := C.source ∩
    ((𝓡∂ 2) ∘ C) ⁻¹' L.inverse.source
  have hU : IsOpen U :=
    ((𝓡∂ 2).continuous.comp_continuousOn C.continuousOn).isOpen_inter_preimage
      C.open_source L.inverse.open_source
  have hyU : y₀ ∈ U := ⟨hy, L.inverse.source_mem⟩
  have hidentity (z : EuclideanHalfSpace 2) (hz : z ∈ U) :
      imageChartAmbientCoordinates F cF
          (imageCoordinateTransition (geometricSameImageHomeomorph F G heq) cF cG y₀)
          ((𝓡∂ 2) (C z)) =
        extChartAt (𝓡∂ 3)
          (F.map (cF.chart.symm
            (imageCoordinateTransition (geometricSameImageHomeomorph F G heq) cF cG y₀)))
          (G.map (cG.chart.symm z)) := by
    change z ∈ imageInteriorCoordinateDomain (geometricSameImageHomeomorph F G heq) cF cG ∧
      _ at hz
    simp only [imageChartAmbientCoordinates, Function.comp_apply, ModelWithCorners.left_inv]
    change extChartAt (𝓡∂ 3) _
      (F.map (cF.chart.symm (cF.chart (geometricSameImageHomeomorph F G heq
        (cG.chart.symm z))))) = _
    rw [cF.chart.left_inv hz.1.2.2,
      (geometricSameImageHomeomorph_properties F G heq).1]
  refine ⟨U, hU, hyU, fun _ hz => hz.1, fun _ hz => hz.2, ?_, ?_⟩
  · intro z hz
    rw [← hidentity z hz]
    exact L.inverse.mapsTo hz.2
  · intro z hz
    rw [← hidentity z hz]
    exact (L.inverse.left_inverse _ hz.2).symm

end
end SeifertSurfaces.MetricFoundations.AreaCertificates
