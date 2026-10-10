import AreaSectorInteriorSupport
import GeometricSameImageCoordinates

set_option maxSynthPendingDepth 3
set_option autoImplicit false
open scoped Manifold ContDiff ENNReal
open Set Topology MeasureTheory Bundle
namespace SeifertSurfaces.MetricFoundations.AreaCertificates
open Foundations AreaAnalysis
universe u v
noncomputable section
variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]

def sectorPieceSourcePoint {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (i : Fin F.pieceCount)
    (j : Fin (F.domain i).count) (y : Euc 2) : S :=
  F.parametrization i (((F.domain i).chart j).map.symm y)

def sectorPieceAmbientCoordinates {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (i : Fin F.pieceCount)
    (j : Fin (F.domain i).count) (y₀ : Euc 2) : Euc 2 → Euc 3 :=
  extChartAt (𝓡∂ 3) (F.map (sectorPieceSourcePoint F i j y₀)) ∘
    sectorCoordinateMap (F.map ∘ F.parametrization i) j

/-- A left inverse of the actual ambient immersion of the supplied piece. -/
structure SectorPieceLocalInverse {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (i : Fin F.pieceCount)
    (j : Fin (F.domain i).count) (y₀ : Euc 2) where
  domain : Set (Euc 2)
  domain_open : IsOpen domain
  base_mem : y₀ ∈ domain
  domain_subset : domain ⊆ interior ((F.domain i).chart j).map.target
  ambient_mem : MapsTo (sectorCoordinateMap (F.map ∘ F.parametrization i) j) domain
    ((extChartAt (𝓡∂ 3) (F.map (sectorPieceSourcePoint F i j y₀))).source ∩
      ((𝓡∂ 3).boundary M)ᶜ)
  chart_smooth : ContDiffOn ℝ ∞ (sectorPieceAmbientCoordinates F i j y₀) domain
  derivative_injective : Function.Injective
    (fderiv ℝ (sectorPieceAmbientCoordinates F i j y₀) y₀)
  inverse : EuclideanLocalLeftInverse (sectorPieceAmbientCoordinates F i j y₀) y₀ domain

theorem sector_piece_local_immersion_inverse {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (i : Fin F.pieceCount)
    (j : Fin (F.domain i).count) (y₀ : Euc 2)
    (hy₀ : y₀ ∈ interior ((F.domain i).chart j).map.target) :
    Nonempty (SectorPieceLocalInverse F i j y₀) := by
  let x := sectorPieceSourcePoint F i j y₀
  have hfx : F.map x ∉ (𝓡∂ 3).boundary M := by
    intro hb
    have hx := sector_source_point_avoids_boundary F i j hy₀
    apply hx
    rw [← F.boundary_preimage]
    exact hb
  let T := (extChartAt (𝓡∂ 3) (F.map x)).source ∩ ((𝓡∂ 3).boundary M)ᶜ
  have hT : IsOpen T := (isOpen_extChartAt_source _).inter
    (((𝓡∂ 3).isClosed_boundary (M := M) (n := ∞) (by simp)).isOpen_compl)
  let D := interior ((F.domain i).chart j).map.target ∩
    sectorCoordinateMap (F.map ∘ F.parametrization i) j ⁻¹' T
  have hc : ContinuousOn (sectorCoordinateMap (F.map ∘ F.parametrization i) j)
      (interior ((F.domain i).chart j).map.target) :=
    (F.piece_smooth_interior i j).continuousOn
  have hD : IsOpen D := hc.isOpen_inter_preimage isOpen_interior hT
  have hyD : y₀ ∈ D := ⟨hy₀, mem_extChartAt_source _, hfx⟩
  have htar : ContMDiffOn (𝓡∂ 3) 𝓘(ℝ, Euc 3) ∞
      (extChartAt (𝓡∂ 3) (F.map x)) (extChartAt (𝓡∂ 3) (F.map x)).source := by
    simpa only [extChartAt_source] using
      contMDiffOn_extChartAt (I := 𝓡∂ 3) (n := ∞) (x := F.map x)
  have hF : ContDiffOn ℝ ∞ (sectorPieceAmbientCoordinates F i j y₀) D :=
    (htar.comp ((F.piece_smooth_interior i j).mono inter_subset_left)
      (fun _ hz => hz.2.1)).contDiffOn
  have hn : ((F.domain i).chart j).map.target ∈ 𝓝 y₀ := mem_interior_iff_mem_nhds.mp hy₀
  have hmd : MDifferentiableAt 𝓘(ℝ, Euc 2) (𝓡∂ 3)
      (sectorCoordinateMap (F.map ∘ F.parametrization i) j) y₀ :=
    ((F.piece_c1 i j).contMDiffAt hn).mdifferentiableAt (by simp)
  have hd := F.piece_differential_injective i j y₀ (interior_subset hy₀)
  rw [mfderivWithin_of_mem_nhds hn, hmd.mfderiv] at hd
  have hraw : writtenInExtChartAt 𝓘(ℝ, Euc 2) (𝓡∂ 3) y₀
      (sectorCoordinateMap (F.map ∘ F.parametrization i) j) =
      sectorPieceAmbientCoordinates F i j y₀ := by
    funext z
    simp [writtenInExtChartAt, sectorPieceAmbientCoordinates, sectorPieceSourcePoint,
      sectorCoordinateMap, mfld_simps]
  rw [hraw] at hd
  simp only [extChartAt_self_apply, mfld_simps, fderivWithin_univ] at hd
  have hinj : Function.Injective
      (fderiv ℝ (sectorPieceAmbientCoordinates F i j y₀) y₀) := by
    intro v w hvw
    have he : (tangentSpaceCastModel 𝓘(ℝ, Euc 2) y₀).symm v =
        (tangentSpaceCastModel 𝓘(ℝ, Euc 2) y₀).symm w := hd (by
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.apply_symm_apply, writtenInExtChartAt,
        sectorPieceAmbientCoordinates, sectorPieceSourcePoint] using
        congrArg (tangentSpaceCastModel (𝓡∂ 3)
          (sectorCoordinateMap (F.map ∘ F.parametrization i) j y₀)).symm hvw)
    exact (tangentSpaceCastModel 𝓘(ℝ, Euc 2) y₀).symm.injective he
  obtain ⟨L⟩ := euclideanImmersion_local_leftInverse
    (sectorPieceAmbientCoordinates F i j y₀) D hD y₀ hyD hF hinj
  exact ⟨⟨D, hD, hyD, fun _ hz => hz.1, fun _ hz => hz.2, hF, hinj, L⟩⟩

/-- Local expression through the actual proper-embedding interior inverse. -/
theorem sector_source_local_inverse_identity {S : CompactOrientedSurface.{u}}
    (f : ProperSmoothEmbedding S M) (F : GeometricPiecewiseSurface S M)
    (heq : F.map = f.continuousMap) (i : Fin F.pieceCount)
    (j : Fin (F.domain i).count) (p : S) (y₀ : Euc 2)
    (hy₀ : y₀ ∈ sectorToSourceDomain F i j p)
    (L : EmbeddingInteriorLocalInverse f (sectorPieceSourcePoint F i j y₀)) :
    ∃ V : Set (Euc 2), IsOpen V ∧ y₀ ∈ V ∧ V ⊆ sectorToSourceDomain F i j p ∧
      MapsTo (sectorPieceSourcePoint F i j) V
        ((surfaceChart (sectorPieceSourcePoint F i j y₀)).source ∩
          (surfaceChart p).source) ∧
      MapsTo (surfaceChart (sectorPieceSourcePoint F i j y₀) ∘ sectorPieceSourcePoint F i j)
        V L.inverse.source ∧
      MapsTo (sectorPieceAmbientCoordinates F i j y₀) V L.inverse.target ∧
      (∀ y ∈ V, surfaceChart (sectorPieceSourcePoint F i j y₀)
        (sectorPieceSourcePoint F i j y) =
          L.inverse.map (sectorPieceAmbientCoordinates F i j y₀ y)) := by
  let q := sectorPieceSourcePoint F i j
  let x := q y₀
  have hq : ContinuousAt q y₀ :=
    ((F.parametrization i).continuous.comp_continuousOn
      (((F.domain i).chart j).map.symm.continuousOn.mono interior_subset)).continuousAt
      (isOpen_interior.mem_nhds hy₀.1)
  have hbase : ContinuousAt (surfaceChart x ∘ q) y₀ :=
    (ContinuousAt.comp (f := q) ((continuousOn_extChartAt x).continuousAt
      ((isOpen_extChartAt_source x).mem_nhds (mem_extChartAt_source x))) hq)
  have hamb : ContinuousAt (sectorPieceAmbientCoordinates F i j y₀) y₀ := by
    have hs := (F.piece_smooth_interior i j).contMDiffAt
      (isOpen_interior.mem_nhds hy₀.1)
    exact ContinuousAt.comp
      (f := sectorCoordinateMap (F.map ∘ F.parametrization i) j)
      ((continuousOn_extChartAt (F.map x)).continuousAt
        ((isOpen_extChartAt_source _).mem_nhds (mem_extChartAt_source _))) hs.continuousAt
  have hDom : IsOpen (sectorToSourceDomain F i j p) :=
    ((F.parametrization i).continuous.comp_continuousOn
      (((F.domain i).chart j).map.symm.continuousOn.mono interior_subset)).isOpen_inter_preimage
      isOpen_interior (isOpen_extChartAt_source p)
  have hqmem : q y₀ ∈ (surfaceChart x).source ∩ (surfaceChart p).source :=
    ⟨mem_extChartAt_source x, hy₀.2⟩
  have htarget : sectorPieceAmbientCoordinates F i j y₀ y₀ ∈ L.inverse.target := by
    have h := L.inverse.target_mem
    change extChartAt (𝓡∂ 3) (f.toFun x)
      (f.toFun ((surfaceChart x).symm (surfaceChart x x))) ∈ L.inverse.target at h
    rw [(surfaceChart x).left_inv (mem_extChartAt_source x)] at h
    change extChartAt (𝓡∂ 3) (F.map x) (F.map x) ∈ L.inverse.target
    have hm : F.map x = f.toFun x := congrFun (congrArg DFunLike.coe heq) x
    rwa [hm]
  have hset : {y | y ∈ sectorToSourceDomain F i j p ∧
      q y ∈ (surfaceChart x).source ∩ (surfaceChart p).source ∧
      surfaceChart x (q y) ∈ L.inverse.source ∧
      sectorPieceAmbientCoordinates F i j y₀ y ∈ L.inverse.target} ∈ 𝓝 y₀ := by
    apply Filter.inter_mem (hDom.mem_nhds hy₀)
    apply Filter.inter_mem
      (hq.preimage_mem_nhds (((isOpen_extChartAt_source x).inter
        (isOpen_extChartAt_source p)).mem_nhds hqmem))
    exact Filter.inter_mem
      (hbase.preimage_mem_nhds (L.inverse.open_source.mem_nhds L.inverse.source_mem))
      (hamb.preimage_mem_nhds (L.inverse.open_target.mem_nhds htarget))
  obtain ⟨V, hV, hVo, hyV⟩ := mem_nhds_iff.mp hset
  refine ⟨V, hVo, hyV, fun y hy => (hV hy).1, fun y hy => (hV hy).2.1,
    fun y hy => (hV hy).2.2.1, fun y hy => (hV hy).2.2.2, ?_⟩
  intro y hy
  have hs := (hV hy).2.1.1
  have he : embeddingCoordinateMap f x (surfaceChart x (q y)) =
      sectorPieceAmbientCoordinates F i j y₀ y := by
    change extChartAt (𝓡∂ 3) (f.toFun x)
      (f.toFun ((surfaceChart x).symm (surfaceChart x (q y)))) =
      extChartAt (𝓡∂ 3) (F.map x) (F.map (q y))
    rw [(surfaceChart x).left_inv hs]
    have hm (z : S) : F.map z = f.toFun z := congrFun (congrArg DFunLike.coe heq) z
    rw [hm x, hm (q y)]
  exact (L.inverse.left_inverse _ (hV hy).2.2.1).symm.trans (congrArg L.inverse.map he)

theorem sector_source_coordinate_smooth_at {S : CompactOrientedSurface.{u}}
    (f : ProperSmoothEmbedding S M) (F : GeometricPiecewiseSurface S M)
    (heq : F.map = f.continuousMap) (i : Fin F.pieceCount)
    (j : Fin (F.domain i).count) (p : S) {y : Euc 2}
    (hy : y ∈ sectorToSourceDomain F i j p) :
    ContDiffAt ℝ ∞ (sectorToSourceCoordinates F i j p) y := by
  let x := sectorPieceSourcePoint F i j y
  obtain ⟨L⟩ := properEmbedding_interior_chart_leftInverse f x
    (sector_source_point_avoids_boundary F i j hy.1)
  obtain ⟨V, hVo, hyV, hVD, hVs, hVsrc, hVtar, hVid⟩ :=
    sector_source_local_inverse_identity f F heq i j p y hy L
  have hamb : ContDiffAt ℝ ∞ (sectorPieceAmbientCoordinates F i j y) y := by
    have hs := (F.piece_smooth_interior i j).contMDiffAt
      (isOpen_interior.mem_nhds hy.1)
    exact (contMDiffAt_extChartAt.comp y hs).contDiffAt
  have hb := (L.inverse.smooth.contDiffAt
    (L.inverse.open_target.mem_nhds (hVtar hyV))).comp y hamb
  have hB : ContDiffAt ℝ ∞ (surfaceChart x ∘ sectorPieceSourcePoint F i j) y := by
    apply hb.congr_of_eventuallyEq
    filter_upwards [hVo.mem_nhds hyV] with z hz
    exact hVid z hz
  have hi : surfaceChart x x ∈ interior (surfaceChart x).target := by
    exact (𝓡∂ 2).isInteriorPoint_iff.mp
      (((𝓡∂ 2).isInteriorPoint_iff_not_isBoundaryPoint x).mpr
        (sector_source_point_avoids_boundary F i j hy.1))
  have hrange : range (𝓡∂ 2) ∈ 𝓝 (surfaceChart x x) :=
    Filter.mem_of_superset (isOpen_interior.mem_nhds hi)
      (fun z hz => extChartAt_target_subset_range x (interior_subset hz))
  have hchange : ContDiffAt ℝ ∞ (surfaceChart p ∘ (surfaceChart x).symm)
      (surfaceChart x x) := by
    apply (contDiffWithinAt_ext_coord_change p x (I := 𝓡∂ 2) (n := ∞) ?_).contDiffAt hrange
    exact ⟨(surfaceChart x).map_source (mem_extChartAt_source x), by
      change (surfaceChart x).symm (surfaceChart x x) ∈ (surfaceChart p).source
      rw [(surfaceChart x).left_inv (mem_extChartAt_source x)]
      exact hy.2⟩
  apply (hchange.comp y hB).congr_of_eventuallyEq
  filter_upwards [hVo.mem_nhds hyV] with z hz
  change surfaceChart p (sectorPieceSourcePoint F i j z) =
    surfaceChart p ((surfaceChart x).symm (surfaceChart x (sectorPieceSourcePoint F i j z)))
  rw [(surfaceChart x).left_inv (hVs hz).1]

theorem sector_source_ambient_derivative_factorization {S : CompactOrientedSurface.{u}}
    (f : ProperSmoothEmbedding S M) (F : GeometricPiecewiseSurface S M)
    (heq : F.map = f.continuousMap) (i : Fin F.pieceCount)
    (j : Fin (F.domain i).count) (p : S) {y : Euc 2}
    (hy : y ∈ sectorToSourceDomain F i j p) :
    (fderiv ℝ (extChartAt (𝓡∂ 3) (F.map (sectorPieceSourcePoint F i j y)) ∘
      f.toFun ∘ (surfaceChart p).symm) (sectorToSourceCoordinates F i j p y)).comp
        (sectorToSourceDerivative F i j p y) =
      fderiv ℝ (sectorPieceAmbientCoordinates F i j y) y := by
  let x := sectorPieceSourcePoint F i j y
  let C := sectorToSourceCoordinates F i j p
  let A := extChartAt (𝓡∂ 3) (F.map x)
  have hi : (𝓡∂ 2).IsInteriorPoint x :=
    ((𝓡∂ 2).isInteriorPoint_iff_not_isBoundaryPoint x).mpr
      (sector_source_point_avoids_boundary F i j hy.1)
  have hs : x ∈ (chartAt (EuclideanHalfSpace 2) p).source := by
    have h : x ∈ (surfaceChart p).source := hy.2
    simpa only [surfaceChart, extChartAt_source] using h
  have hz : C y ∈ interior (surfaceChart p).target :=
    ((𝓡∂ 2).isInteriorPoint_iff_of_mem_atlas (n := ∞) (by simp)
      (chart_mem_atlas (EuclideanHalfSpace 2) p) hs).mp hi
  let D := interior (surfaceChart p).target ∩
    (f.toFun ∘ (surfaceChart p).symm) ⁻¹' A.source
  have hD : IsOpen D :=
    (f.embedding.continuous.comp_continuousOn
      ((continuousOn_extChartAt_symm p).mono interior_subset)).isOpen_inter_preimage
      isOpen_interior (isOpen_extChartAt_source _)
  have hzD : C y ∈ D := by
    refine ⟨hz, ?_⟩
    change f.toFun ((surfaceChart p).symm (surfaceChart p x)) ∈ A.source
    have hp : x ∈ (surfaceChart p).source := hy.2
    rw [(surfaceChart p).left_inv hp]
    have hm : F.map x = f.toFun x := congrFun (congrArg DFunLike.coe heq) x
    rw [← hm]
    exact mem_extChartAt_source _
  have hraw : DifferentiableAt ℝ (A ∘ f.toFun ∘ (surfaceChart p).symm) (C y) := by
    have hsrc := (contMDiffOn_extChartAt_symm (I := 𝓡∂ 2) (n := ∞) p).mono
      (fun z (hz : z ∈ D) => interior_subset hz.1)
    have hf := f.smooth.comp_contMDiffOn hsrc
    have htar : ContMDiffOn (𝓡∂ 3) 𝓘(ℝ, Euc 3) ∞ A A.source := by
      simpa only [A, extChartAt_source] using
        contMDiffOn_extChartAt (I := 𝓡∂ 3) (n := ∞) (x := F.map x)
    exact ((htar.comp hf (fun z hz => hz.2)).contDiffOn.contDiffAt
      (hD.mem_nhds hzD)).differentiableAt (by simp)
  have hC := (sector_source_coordinate_smooth_at f F heq i j p hy).differentiableAt
    (by simp)
  have hDom : IsOpen (sectorToSourceDomain F i j p) :=
    ((F.parametrization i).continuous.comp_continuousOn
      (((F.domain i).chart j).map.symm.continuousOn.mono interior_subset)).isOpen_inter_preimage
      isOpen_interior (isOpen_extChartAt_source p)
  have hevent : (A ∘ f.toFun ∘ (surfaceChart p).symm) ∘ C =ᶠ[𝓝 y]
      sectorPieceAmbientCoordinates F i j y := by
    filter_upwards [hDom.mem_nhds hy] with z hz
    change A (f.toFun ((surfaceChart p).symm
      (surfaceChart p (sectorPieceSourcePoint F i j z)))) =
      A (F.map (sectorPieceSourcePoint F i j z))
    have hp : sectorPieceSourcePoint F i j z ∈ (surfaceChart p).source := hz.2
    rw [(surfaceChart p).left_inv hp]
    have hm := congrFun (congrArg DFunLike.coe heq) (sectorPieceSourcePoint F i j z)
    rw [hm]
    rfl
  rw [sectorToSourceDerivative, fderivWithin_of_mem_nhds (hDom.mem_nhds hy)]
  exact (fderiv_comp y hraw hC).symm.trans hevent.fderiv_eq

theorem sector_source_coordinate_derivative_bijective {S : CompactOrientedSurface.{u}}
    (f : ProperSmoothEmbedding S M) (F : GeometricPiecewiseSurface S M)
    (heq : F.map = f.continuousMap) (i : Fin F.pieceCount)
    (j : Fin (F.domain i).count) (p : S) {y : Euc 2}
    (hy : y ∈ sectorToSourceDomain F i j p) :
    Function.Bijective (sectorToSourceDerivative F i j p y) := by
  obtain ⟨L⟩ := sector_piece_local_immersion_inverse F i j y hy.1
  have hinj : Function.Injective (sectorToSourceDerivative F i j p y) := by
    intro v w hvw
    apply L.derivative_injective
    have h := sector_source_ambient_derivative_factorization f F heq i j p hy
    rw [← h]
    simpa only [ContinuousLinearMap.comp_apply] using congrArg
      (fderiv ℝ (extChartAt (𝓡∂ 3) (F.map (sectorPieceSourcePoint F i j y)) ∘
        f.toFun ∘ (surfaceChart p).symm) (sectorToSourceCoordinates F i j p y)) hvw
  exact ⟨hinj, (LinearMap.injective_iff_surjective
    (f := (sectorToSourceDerivative F i j p y).toLinearMap)).mp hinj⟩

theorem source_sector_coordinate_smooth_at {S : CompactOrientedSurface.{u}}
    (f : ProperSmoothEmbedding S M) (F : GeometricPiecewiseSurface S M)
    (heq : F.map = f.continuousMap) (i : Fin F.pieceCount)
    (j : Fin (F.domain i).count) (p : S) {y : Euc 2}
    (hy : y ∈ sectorToSourceCoordinates F i j p '' sectorToSourceDomain F i j p) :
    ContDiffAt ℝ ∞ (sourceToSectorCoordinates F i j p) y := by
  let C : OpenPartialHomeomorph (Euc 2) (Euc 2) := {
    toFun := sectorToSourceCoordinates F i j p
    invFun := sourceToSectorCoordinates F i j p
    source := sectorToSourceDomain F i j p
    target := sectorToSourceCoordinates F i j p '' sectorToSourceDomain F i j p
    map_source' := by
      intro y hy
      exact ⟨y, hy, rfl⟩
    map_target' := by
      rintro y ⟨z, hz, rfl⟩
      have hx : F.parametrization i (((F.domain i).chart j).map.symm z) ∈
          (surfaceChart p).source := hz.2
      have hpoint : (surfaceChart p).symm (sectorToSourceCoordinates F i j p z) =
          F.parametrization i (((F.domain i).chart j).map.symm z) :=
        (surfaceChart p).left_inv hx
      have hr : (surfaceChart p).symm (sectorToSourceCoordinates F i j p z) ∈
          Set.range (F.parametrization i) := by
        rw [hpoint]
        exact ⟨_, rfl⟩
      have hid : sourceToSectorCoordinates F i j p (sectorToSourceCoordinates F i j p z) = z := by
        unfold sourceToSectorCoordinates
        rw [dite_eq_left hr]
        have he := (F.parametrization_embedding i).toHomeomorph.apply_symm_apply
          ⟨(surfaceChart p).symm (sectorToSourceCoordinates F i j p z), hr⟩
        have hparam : (F.parametrization_embedding i).toHomeomorph.symm
            ⟨(surfaceChart p).symm (sectorToSourceCoordinates F i j p z), hr⟩ =
            ((F.domain i).chart j).map.symm z :=
          (F.parametrization_embedding i).injective ((congrArg Subtype.val he).trans hpoint)
        rw [hparam]
        exact ((F.domain i).chart j).map.right_inv (interior_subset hz.1)
      simpa only [hid] using hz
    left_inv' := by
      intro y hy
      have hx := hy.2
      change F.parametrization i (((F.domain i).chart j).map.symm y) ∈
        (surfaceChart p).source at hx
      have hpoint : (surfaceChart p).symm (sectorToSourceCoordinates F i j p y) =
          F.parametrization i (((F.domain i).chart j).map.symm y) :=
        (surfaceChart p).left_inv hx
      have hr : (surfaceChart p).symm (sectorToSourceCoordinates F i j p y) ∈
          Set.range (F.parametrization i) := by
        rw [hpoint]
        exact ⟨_, rfl⟩
      unfold sourceToSectorCoordinates
      rw [dite_eq_left hr]
      have he := (F.parametrization_embedding i).toHomeomorph.apply_symm_apply
        ⟨(surfaceChart p).symm (sectorToSourceCoordinates F i j p y), hr⟩
      have hparam : (F.parametrization_embedding i).toHomeomorph.symm
          ⟨(surfaceChart p).symm (sectorToSourceCoordinates F i j p y), hr⟩ =
          ((F.domain i).chart j).map.symm y :=
        (F.parametrization_embedding i).injective ((congrArg Subtype.val he).trans hpoint)
      rw [hparam]
      exact ((F.domain i).chart j).map.right_inv (interior_subset hy.1)
    right_inv' := by
      rintro y ⟨z, hz, rfl⟩
      have hx : F.parametrization i (((F.domain i).chart j).map.symm z) ∈
          (surfaceChart p).source := hz.2
      have hpoint : (surfaceChart p).symm (sectorToSourceCoordinates F i j p z) =
          F.parametrization i (((F.domain i).chart j).map.symm z) :=
        (surfaceChart p).left_inv hx
      have hr : (surfaceChart p).symm (sectorToSourceCoordinates F i j p z) ∈
          Set.range (F.parametrization i) := by
        rw [hpoint]
        exact ⟨_, rfl⟩
      have hid : sourceToSectorCoordinates F i j p (sectorToSourceCoordinates F i j p z) = z := by
        unfold sourceToSectorCoordinates
        rw [dite_eq_left hr]
        have he := (F.parametrization_embedding i).toHomeomorph.apply_symm_apply
          ⟨(surfaceChart p).symm (sectorToSourceCoordinates F i j p z), hr⟩
        have hparam : (F.parametrization_embedding i).toHomeomorph.symm
            ⟨(surfaceChart p).symm (sectorToSourceCoordinates F i j p z), hr⟩ =
            ((F.domain i).chart j).map.symm z :=
          (F.parametrization_embedding i).injective ((congrArg Subtype.val he).trans hpoint)
        rw [hparam]
        exact ((F.domain i).chart j).map.right_inv (interior_subset hz.1)
      rw [hid]
    continuousOn_toFun := by
      apply (continuousOn_extChartAt p).comp
        ((F.parametrization i).continuous.comp_continuousOn
          (((F.domain i).chart j).map.symm.continuousOn.mono
            (inter_subset_left.trans interior_subset)))
      exact fun _ hy => hy.2
    continuousOn_invFun := by
      let T := sectorToSourceCoordinates F i j p '' sectorToSourceDomain F i j p
      have ht (y : T) : (y : Euc 2) ∈ (surfaceChart p).target := by
        rcases y.property with ⟨z, hz, he⟩
        rw [← he]
        exact (surfaceChart p).map_source hz.2
      have hr (y : T) : (surfaceChart p).symm (y : Euc 2) ∈
          Set.range (F.parametrization i) := by
        rcases y.property with ⟨z, hz, he⟩
        rw [← he]
        change (surfaceChart p).symm ((surfaceChart p)
          (F.parametrization i (((F.domain i).chart j).map.symm z))) ∈ _
        rw [(surfaceChart p).left_inv hz.2]
        exact ⟨_, rfl⟩
      let L : T → Set.range (F.parametrization i) :=
        fun y => ⟨(surfaceChart p).symm (y : Euc 2), hr y⟩
      have hL : Continuous L := by
        apply Continuous.subtype_mk
        exact (continuousOn_extChartAt_symm p).comp_continuous continuous_subtype_val ht
      have hm (y : T) : (F.parametrization_embedding i).toHomeomorph.symm (L y) ∈
          ((F.domain i).chart j).map.source := by
        rcases y.property with ⟨z, hz, he⟩
        have hpoint : (surfaceChart p).symm (y : Euc 2) =
            F.parametrization i (((F.domain i).chart j).map.symm z) := by
          rw [← he]
          exact (surfaceChart p).left_inv hz.2
        have hparam : (F.parametrization_embedding i).toHomeomorph.symm (L y) =
            ((F.domain i).chart j).map.symm z := by
          apply (F.parametrization_embedding i).injective
          exact (congrArg Subtype.val
            ((F.parametrization_embedding i).toHomeomorph.apply_symm_apply (L y))).trans hpoint
        rw [hparam]
        exact ((F.domain i).chart j).map.map_target (interior_subset hz.1)
      apply continuousOn_iff_continuous_domRestrict.mpr
      have hc := ((F.domain i).chart j).map.continuousOn.comp_continuous
        ((F.parametrization_embedding i).toHomeomorph.symm.continuous.comp hL) hm
      convert hc using 1
      funext y
      exact dite_eq_left (hr y)
    open_source := by
      apply (((F.parametrization i).continuous.comp_continuousOn
        (((F.domain i).chart j).map.symm.continuousOn.mono interior_subset))).isOpen_inter_preimage
        isOpen_interior
      exact isOpen_extChartAt_source p
    open_target := sector_source_coordinate_target_open F i j p
  }
  have hz : C.symm y ∈ sectorToSourceDomain F i j p := C.map_target hy
  have hb := sector_source_coordinate_derivative_bijective f F heq i j p hz
  let e := ContinuousLinearEquiv.ofBijective (sectorToSourceDerivative F i j p (C.symm y))
    (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2)
  have hs := sector_source_coordinate_smooth_at f F heq i j p hz
  have hDom : IsOpen (sectorToSourceDomain F i j p) := C.open_source
  have hd : HasFDerivAt C (e : Euc 2 →L[ℝ] Euc 2) (C.symm y) := by
    have h := hs.differentiableAt (by simp)
    change HasFDerivAt (sectorToSourceCoordinates F i j p)
      (e : Euc 2 →L[ℝ] Euc 2) (C.symm y)
    simpa only [e, ContinuousLinearEquiv.coe_ofBijective, sectorToSourceDerivative,
      fderivWithin_of_mem_nhds (hDom.mem_nhds hz)] using h.hasFDerivAt
  exact C.contDiffAt_symm hy hd hs

theorem sector_source_coordinates_in_surface_chart_interior {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (i : Fin F.pieceCount)
    (j : Fin (F.domain i).count) (p : S) :
    MapsTo (sectorToSourceCoordinates F i j p) (sectorToSourceDomain F i j p)
      (interior (surfaceChart p).target) := by
  intro y hy
  have hi : (𝓡∂ 2).IsInteriorPoint (sectorPieceSourcePoint F i j y) :=
    ((𝓡∂ 2).isInteriorPoint_iff_not_isBoundaryPoint _).mpr
      (sector_source_point_avoids_boundary F i j hy.1)
  have hs : sectorPieceSourcePoint F i j y ∈ (chartAt (EuclideanHalfSpace 2) p).source := by
    have hp : sectorPieceSourcePoint F i j y ∈ (surfaceChart p).source := hy.2
    simpa only [surfaceChart, extChartAt_source] using hp
  exact ((𝓡∂ 2).isInteriorPoint_iff_of_mem_atlas (n := ∞) (by simp)
    (chart_mem_atlas (EuclideanHalfSpace 2) p) hs).mp hi

end
end SeifertSurfaces.MetricFoundations.AreaCertificates
