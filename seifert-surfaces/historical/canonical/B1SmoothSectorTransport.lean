import OriginalB1
import B1NativeRegularRecovery
import AreaSectorInteriorSupport
import MetricAreaAnalysis.CompactIntegrability
open scoped Manifold ContDiff ENNReal
open Set Topology MeasureTheory
namespace SeifertSurfaces.MetricFoundations.B1Bridges
open SeifertSurfaces.Foundations
universe u v
noncomputable section
set_option autoImplicit false
variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]

def nativeSectorParameter {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (i : Fin F.pieceCount)
    (j : Fin (F.domain i).count) : Euc 2 → S :=
  F.parametrization i ∘ ((F.domain i).chart j).map.symm

def nativeSectorInteriorDomain {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (i : Fin F.pieceCount)
    (j : Fin (F.domain i).count) : Set (Euc 2) :=
  interior ((F.domain i).chart j).map.target ∩ nativeSectorParameter F i j ⁻¹' S.boundaryᶜ

def nativeSectorChartDomain {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (i : Fin F.pieceCount)
    (j : Fin (F.domain i).count) (p : S) : Set (Euc 2) :=
  interior ((F.domain i).chart j).map.target ∩ nativeSectorParameter F i j ⁻¹'
    (S.boundaryᶜ ∩ (extChartAt (𝓡∂ 2) p).source)

def nativeSectorChartMap {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (i : Fin F.pieceCount)
    (j : Fin (F.domain i).count) (p : S) : Euc 2 → Euc 2 :=
  extChartAt (𝓡∂ 2) p ∘ nativeSectorParameter F i j

theorem native_sector_parameter_regular {S : CompactOrientedSurface.{u}}
    (f : ProperSmoothEmbedding S M) (F : GeometricPiecewiseSurface S M)
    (h : F.map = f.continuousMap) (i : Fin F.pieceCount)
    (j : Fin (F.domain i).count) :
    ContMDiffOn 𝓘(ℝ, Euc 2) (𝓡∂ 2) ∞ (nativeSectorParameter F i j)
      (nativeSectorInteriorDomain F i j) ∧
    (∀ y ∈ nativeSectorInteriorDomain F i j, Function.Injective
      (mfderiv 𝓘(ℝ, Euc 2) (𝓡∂ 2) (nativeSectorParameter F i j) y)) := by
  have hsmooth : ContMDiffOn 𝓘(ℝ, Euc 2) (𝓡∂ 2) ∞ (nativeSectorParameter F i j)
      (nativeSectorInteriorDomain F i j) := by
    intro y hy
    have hparameterContinuous : ContinuousAt (nativeSectorParameter F i j) y := by
      change ContinuousAt (F.parametrization i ∘ ((F.domain i).chart j).map.symm) y
      exact (F.parametrization i).continuous.continuousAt.comp
        ((((F.domain i).chart j).map.symm.continuousOn y (interior_subset hy.1)).continuousAt
          (Filter.mem_of_superset (isOpen_interior.mem_nhds hy.1) interior_subset))
    have hcomp : ContMDiffAt 𝓘(ℝ, Euc 2) (𝓡∂ 3) ∞
        (f.toFun ∘ nativeSectorParameter F i j) y := by
      have hf := (F.piece_smooth_interior i j y hy.1).contMDiffAt
        (isOpen_interior.mem_nhds hy.1)
      rw [h] at hf
      exact hf
    exact (proper_smooth_embedding_interior_parameter_smooth f
      (nativeSectorParameter F i j) y hparameterContinuous hy.2 hcomp).contMDiffWithinAt
  refine ⟨hsmooth, ?_⟩
  intro y hy
  have hiy : y ∈ interior ((F.domain i).chart j).map.target := hy.1
  have hparameterContinuous : ContinuousAt (nativeSectorParameter F i j) y := by
    change ContinuousAt (F.parametrization i ∘ ((F.domain i).chart j).map.symm) y
    exact (F.parametrization i).continuous.continuousAt.comp
      ((((F.domain i).chart j).map.symm.continuousOn y (interior_subset hiy)).continuousAt
        (Filter.mem_of_superset (isOpen_interior.mem_nhds hiy) interior_subset))
  have hdomain : nativeSectorInteriorDomain F i j ∈ 𝓝 y := by
    exact Filter.inter_mem (isOpen_interior.mem_nhds hiy)
      (hparameterContinuous.preimage_mem_nhds
        (((𝓡∂ 2).isClosed_boundary (M := S) (n := ∞) (by simp)).isOpen_compl.mem_nhds hy.2))
  have hdparameter := (hsmooth y hy).mdifferentiableWithinAt (by simp)
    |>.mdifferentiableAt hdomain
  have hcomp := mfderiv_comp y (f.smooth.mdifferentiableAt (by simp)) hdparameter
  have hambient := F.piece_differential_injective i j y (interior_subset hiy)
  rw [mfderivWithin_of_mem_nhds
    (Filter.mem_of_superset (isOpen_interior.mem_nhds hiy) interior_subset)] at hambient
  have hfactor : mfderiv 𝓘(ℝ, Euc 2) (𝓡∂ 3)
      (sectorCoordinateMap (F.map ∘ F.parametrization i) j) y =
      (mfderiv (𝓡∂ 2) (𝓡∂ 3) f.toFun (nativeSectorParameter F i j y)).comp
        (mfderiv 𝓘(ℝ, Euc 2) (𝓡∂ 2) (nativeSectorParameter F i j) y) := by
    rw [h]
    exact hcomp
  intro v w hvw
  apply hambient
  rw [hfactor]
  exact congrArg (mfderiv (𝓡∂ 2) (𝓡∂ 3) f.toFun (nativeSectorParameter F i j y)) hvw

theorem native_sector_chart_geometry {S : CompactOrientedSurface.{u}}
    (f : ProperSmoothEmbedding S M) (F : GeometricPiecewiseSurface S M)
    (h : F.map = f.continuousMap) (i : Fin F.pieceCount)
    (j : Fin (F.domain i).count) (p : S) :
    let D := nativeSectorChartDomain F i j p
    let c := nativeSectorChartMap F i j p
    IsOpen D ∧ ContDiffOn ℝ ∞ c D ∧ InjOn c D ∧
      MapsTo c D (interior (extChartAt (𝓡∂ 2) p).target) ∧
      (∀ y ∈ D, HasFDerivAt c (fderiv ℝ c y) y ∧
        Function.Injective (fderiv ℝ c y) ∧ (fderiv ℝ c y).det ≠ 0) := by
  let D := nativeSectorChartDomain F i j p
  let c := nativeSectorChartMap F i j p
  have hcontinuous : ContinuousOn (nativeSectorParameter F i j)
      (interior ((F.domain i).chart j).map.target) := by
    change ContinuousOn (F.parametrization i ∘ ((F.domain i).chart j).map.symm) _
    exact (F.parametrization i).continuous.comp_continuousOn
      (((F.domain i).chart j).map.symm.continuousOn.mono interior_subset)
  have hopen : IsOpen D := by
    exact hcontinuous.isOpen_inter_preimage isOpen_interior
      ((((𝓡∂ 2).isClosed_boundary (M := S) (n := ∞) (by simp)).isOpen_compl).inter
        (isOpen_extChartAt_source (I := 𝓡∂ 2) p))
  have hsub : D ⊆ nativeSectorInteriorDomain F i j := fun y hy => ⟨hy.1, hy.2.1⟩
  have hregular := native_sector_parameter_regular f F h i j
  have hsmooth : ContDiffOn ℝ ∞ c D := by
    change ContDiffOn ℝ ∞ (extChartAt (𝓡∂ 2) p ∘ nativeSectorParameter F i j) D
    exact ((contMDiffOn_extChartAt (I := 𝓡∂ 2) (x := p)).comp
      (hregular.1.mono hsub) (fun y hy => by
        change nativeSectorParameter F i j y ∈ (chartAt (EuclideanHalfSpace 2) p).source
        simpa only [extChartAt_source] using hy.2.2)).contDiffOn
  have hinjective : InjOn c D := by
    intro x hx y hy hxy
    have hq := (extChartAt (𝓡∂ 2) p).injOn hx.2.2 hy.2.2 hxy
    have hparam := (F.parametrization_embedding i).injective hq
    exact ((F.domain i).chart j).map.symm.injOn
      (interior_subset hx.1) (interior_subset hy.1) hparam
  have hmaps : MapsTo c D (interior (extChartAt (𝓡∂ 2) p).target) := by
    intro y hy
    have hinterior : (𝓡∂ 2).IsInteriorPoint (nativeSectorParameter F i j y) :=
      ((𝓡∂ 2).isInteriorPoint_iff_not_isBoundaryPoint _).2 hy.2.1
    exact ((𝓡∂ 2).isInteriorPoint_iff_of_mem_atlas (n := ∞) (by simp)
      (chart_mem_atlas (EuclideanHalfSpace 2) p)
        (by simpa only [extChartAt_source] using hy.2.2)).1 hinterior
  refine ⟨hopen, hsmooth, hinjective, hmaps, ?_⟩
  intro y hy
  have hd := (hsmooth.contDiffAt (hopen.mem_nhds hy)).differentiableAt (by simp)
  refine ⟨hd.hasFDerivAt, ?_⟩
  have hdparameter := (((hregular.1.mono hsub) y hy).contMDiffAt
    (hopen.mem_nhds hy)).mdifferentiableAt (by simp)
  have hdfactor := mfderiv_comp y
    (mdifferentiableAt_extChartAt (I := 𝓡∂ 2)
      (by simpa only [extChartAt_source] using hy.2.2)) hdparameter
  have hmfinjective : Function.Injective (mfderiv 𝓘(ℝ, Euc 2) 𝓘(ℝ, Euc 2) c y) := by
    change Function.Injective (mfderiv 𝓘(ℝ, Euc 2) 𝓘(ℝ, Euc 2)
      (extChartAt (𝓡∂ 2) p ∘ nativeSectorParameter F i j) y)
    rw [hdfactor]
    exact ((isInvertible_mfderiv_extChartAt hy.2.2).injective).comp
      (hregular.2 y (hsub hy))
  have hinj : Function.Injective (fderiv ℝ c y) := by
    intro v w hvw
    apply hmfinjective
    rw [mfderiv_eq_fderiv]
    exact hvw
  refine ⟨hinj, ?_⟩
  intro hzero
  have hbot := LinearMap.bot_lt_ker_of_det_eq_zero (f := (fderiv ℝ c y).toLinearMap) hzero
  rw [LinearMap.ker_eq_bot.2 hinj] at hbot
  exact lt_irrefl _ hbot

theorem native_sector_ambient_chain_rule {S : CompactOrientedSurface.{u}}
    (f : ProperSmoothEmbedding S M) (F : GeometricPiecewiseSurface S M)
    (h : F.map = f.continuousMap) (i : Fin F.pieceCount)
    (j : Fin (F.domain i).count) (y : Euc 2)
    (hy : y ∈ nativeSectorInteriorDomain F i j) :
    mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 3)
      (sectorCoordinateMap (f.continuousMap ∘ F.parametrization i) j)
      ((F.domain i).chart j).map.target y =
      (mfderiv (𝓡∂ 2) (𝓡∂ 3) f.toFun (nativeSectorParameter F i j y)).comp
        (mfderiv 𝓘(ℝ, Euc 2) (𝓡∂ 2) (nativeSectorParameter F i j) y) := by
  have hiy : y ∈ interior ((F.domain i).chart j).map.target := hy.1
  have hregular := (native_sector_parameter_regular f F h i j).1
  have hdparameter : MDifferentiableAt 𝓘(ℝ, Euc 2) (𝓡∂ 2)
      (nativeSectorParameter F i j) y := by
    have hdwithin := (hregular y hy).mdifferentiableWithinAt (by simp)
    have hparameterContinuous : ContinuousAt (nativeSectorParameter F i j) y := by
      change ContinuousAt (F.parametrization i ∘ ((F.domain i).chart j).map.symm) y
      exact (F.parametrization i).continuous.continuousAt.comp
        ((((F.domain i).chart j).map.symm.continuousOn y (interior_subset hiy)).continuousAt
          (Filter.mem_of_superset (isOpen_interior.mem_nhds hiy) interior_subset))
    have hd : nativeSectorInteriorDomain F i j ∈ 𝓝 y := by
      change interior ((F.domain i).chart j).map.target ∩
        nativeSectorParameter F i j ⁻¹' S.boundaryᶜ ∈ 𝓝 y
      exact Filter.inter_mem (isOpen_interior.mem_nhds hiy)
        (hparameterContinuous.preimage_mem_nhds
          (((𝓡∂ 2).isClosed_boundary (M := S) (n := ∞) (by simp)).isOpen_compl.mem_nhds hy.2))
    exact hdwithin.mdifferentiableAt hd
  rw [mfderivWithin_of_mem_nhds
    (Filter.mem_of_superset (isOpen_interior.mem_nhds hiy) interior_subset)]
  change mfderiv 𝓘(ℝ, Euc 2) (𝓡∂ 3) (f.toFun ∘ nativeSectorParameter F i j) y = _
  exact mfderiv_comp y (f.smooth.mdifferentiableAt (by simp)) hdparameter

theorem native_sector_density_covariance {S : CompactOrientedSurface.{u}}
    (g : SmoothMetric M) (f : ProperSmoothEmbedding S M)
    (F : GeometricPiecewiseSurface S M) (h : F.map = f.continuousMap)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count) (p : S)
    (y : Euc 2) (hy : y ∈ nativeSectorChartDomain F i j p) :
    sectorCoordinateDensity g (F.map ∘ F.parametrization i) j y =
      |(fderiv ℝ (nativeSectorChartMap F i j p) y).det| *
        coordinateAreaDensity g f.toFun p (nativeSectorChartMap F i j p y) := by
  open Bundle in
  let D := nativeSectorChartDomain F i j p
  let c := nativeSectorChartMap F i j p
  let fG := sectorCoordinateMap (F.map ∘ F.parametrization i) j
  let fF := f.toFun ∘ (extChartAt (𝓡∂ 2) p).symm
  obtain ⟨hopen, hsmooth, _, hmaps, _⟩ := native_sector_chart_geometry f F h i j p
  have hiy : y ∈ interior ((F.domain i).chart j).map.target := hy.1
  have hcy : c y ∈ interior (extChartAt (𝓡∂ 2) p).target := hmaps hy
  have hmatch : ∀ z ∈ D, fF (c z) = fG z := by
    intro z hz
    change f.toFun ((extChartAt (𝓡∂ 2) p).symm
      ((extChartAt (𝓡∂ 2) p) (nativeSectorParameter F i j z))) =
        F.map (nativeSectorParameter F i j z)
    rw [(extChartAt (𝓡∂ 2) p).left_inv hz.2.2, h]
    rfl
  have heq : fG =ᶠ[𝓝 y] fF ∘ c := by
    filter_upwards [hopen.mem_nhds hy] with z hz
    exact (hmatch z hz).symm
  have hdF : MDifferentiableAt 𝓘(ℝ, Euc 2) (𝓡∂ 3) fF (c y) := by
    exact (f.smooth.mdifferentiableAt (by simp)).comp (c y)
      ((mdifferentiableOn_extChartAt_symm (I := 𝓡∂ 2) (x := p) _
        (interior_subset hcy)).mdifferentiableAt
          (Filter.mem_of_superset (isOpen_interior.mem_nhds hcy) interior_subset))
  have hdC : MDifferentiableAt 𝓘(ℝ, Euc 2) 𝓘(ℝ, Euc 2) c y :=
    (hsmooth.contDiffAt (hopen.mem_nhds hy)).differentiableAt (by simp) |>.mdifferentiableAt
  have hder : ∀ w : Euc 2,
      @Eq (Euc 3)
        (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 3) fG ((F.domain i).chart j).map.target y w)
        (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 3) fF (extChartAt (𝓡∂ 2) p).target
          (c y) (fderiv ℝ c y w)) := by
    intro w
    have hder := heq.mfderiv_eq (I := 𝓘(ℝ, Euc 2)) (I' := 𝓡∂ 3)
    have hcomp := mfderiv_comp y hdF hdC
    rw [mfderivWithin_of_mem_nhds (Filter.mem_of_superset (isOpen_interior.mem_nhds hiy)
      interior_subset), mfderivWithin_of_mem_nhds
      (Filter.mem_of_superset (isOpen_interior.mem_nhds hcy) interior_subset)]
    have happ := congrArg (fun L : Euc 2 →L[ℝ] Euc 3 => L w) hder
    rw [hcomp, mfderiv_eq_fderiv] at happ
    exact happ
  letI : RiemannianBundle (fun x : M => TangentSpace (𝓡∂ 3) x) := ⟨g.toRiemannianMetric⟩
  let dG := (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 3) fG
    ((F.domain i).chart j).map.target y).toLinearMap.comp
      (tangentSpaceCastModel 𝓘(ℝ, Euc 2) y).symm.toLinearMap
  let dF := (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 3) fF
    (extChartAt (𝓡∂ 2) p).target (c y)).toLinearMap.comp
      (tangentSpaceCastModel 𝓘(ℝ, Euc 2) (c y)).symm.toLinearMap
  have density {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
      (d : Euc 2 →ₗ[ℝ] V) :
      Real.sqrt (Matrix.gram ℝ (fun k : Fin 2 => d (EuclideanSpace.single k 1))).det =
        (d.normDet : ℝ) := by
    have hd := d.normDet_sq_eq_det_gram (EuclideanSpace.basisFun (Fin 2) ℝ)
    simp only [EuclideanSpace.basisFun_apply] at hd
    rw [← hd]
    exact Real.sqrt_sq (by exact d.normDet_nonneg)
  change Real.sqrt (Matrix.gram ℝ (fun k : Fin 2 => dG (EuclideanSpace.single k 1))).det =
    |(fderiv ℝ c y).det| *
      Real.sqrt (Matrix.gram ℝ (fun k : Fin 2 => dF (EuclideanSpace.single k 1))).det
  have hdensityG := density (V := TangentSpace (𝓡∂ 3) (fG y)) dG
  have hdensityF := density (V := TangentSpace (𝓡∂ 3) (fF (c y))) dF
  rw [hdensityG, hdensityF]
  have factor : ∀ (x z : M) (hp : x = z)
      (dG : Euc 2 →ₗ[ℝ] TangentSpace (𝓡∂ 3) z)
      (dF : Euc 2 →ₗ[ℝ] TangentSpace (𝓡∂ 3) x)
      (A : Euc 2 →ₗ[ℝ] Euc 2),
      (∀ w, @Eq (Euc 3) (dG w) (dF (A w))) →
      (dG.normDet : ℝ) = |A.det| * (dF.normDet : ℝ) := by
    intro x z hp
    cases hp
    intro dG dF A hd
    have hm : dG = dF.comp A := by
      ext w
      exact hd w
    rw [hm, LinearMap.normDet_comp_of_finrank_eq A dF rfl,
      LinearMap.normDet_eq_abs_det]
    simp only [mul_comm]
  exact factor _ _ (hmatch y hy) dG dF (fderiv ℝ c y).toLinearMap hder

theorem native_sector_subordinate_integral_transport {S : CompactOrientedSurface.{u}}
    (g : SmoothMetric M) (f : ProperSmoothEmbedding S M)
    (F : GeometricPiecewiseSurface S M) (h : F.map = f.continuousMap)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count) (p : S)
    (s : Set (F.domain i)) (hs : MeasurableSet s)
    (hsub : s ⊆ ((F.domain i).chart j).map.source ∩ (F.domain i).interior ∩
      (F.parametrization i) ⁻¹' (S.boundaryᶜ ∩ (extChartAt (𝓡∂ 2) p).source)) :
    IntegrableOn (sectorCoordinateDensity g (F.map ∘ F.parametrization i) j)
      (((F.domain i).chart j).map '' s) ∧
    IntegrableOn (coordinateAreaDensity g f.toFun p)
      ((extChartAt (𝓡∂ 2) p) '' ((F.parametrization i) '' s)) ∧
    (∫ y in ((F.domain i).chart j).map '' s,
      sectorCoordinateDensity g (F.map ∘ F.parametrization i) j y) =
    (∫ y in (extChartAt (𝓡∂ 2) p) '' ((F.parametrization i) '' s),
      coordinateAreaDensity g f.toFun p y) := by
  let a := ((F.domain i).chart j).map
  let c := nativeSectorChartMap F i j p
  let u := a '' s
  let v := (extChartAt (𝓡∂ 2) p) '' ((F.parametrization i) '' s)
  have hsource : s ⊆ a.source := fun x hx => (hsub hx).1.1
  have hu : MeasurableSet u := by
    letI : BorelSpace (F.domain i) := ⟨rfl⟩
    letI : MetricSpace (F.domain i) := TopologicalSpace.metrizableSpaceMetric (F.domain i)
    exact hs.image_of_continuousOn_injOn (a.continuousOn.mono hsource)
      (a.injOn.mono hsource)
  have hparameter_image : MeasurableSet ((F.parametrization i) '' s) := by
    letI : BorelSpace S := ⟨rfl⟩
    letI : BorelSpace (F.domain i) := ⟨rfl⟩
    letI : MetricSpace (F.domain i) := TopologicalSpace.metrizableSpaceMetric (F.domain i)
    exact hs.image_of_continuousOn_injOn (F.parametrization i).continuous.continuousOn
      (F.parametrization_embedding i).injective.injOn
  have hparameter_source : (F.parametrization i) '' s ⊆
      (extChartAt (𝓡∂ 2) p).source := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hsub hx).2.2
  have hsubD : u ⊆ nativeSectorChartDomain F i j p := by
    rintro _ ⟨x, hx, rfl⟩
    have hint : a x ∈ interior a.target := by
      rw [← AreaCertificates.sector_chart_piece_interior (F.domain i) j]
      exact ⟨x, ⟨(hsub hx).1.2, hsource hx⟩, rfl⟩
    refine ⟨hint, ?_⟩
    change F.parametrization i (a.symm (a x)) ∈
      (S.boundaryᶜ ∩ (extChartAt (𝓡∂ 2) p).source)
    rw [a.left_inv (hsource hx)]
    exact (hsub hx).2
  have himage : c '' u = v := by
    ext z
    constructor
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨F.parametrization i x, ⟨x, hx, rfl⟩, ?_⟩
      change extChartAt (𝓡∂ 2) p (F.parametrization i x) =
        extChartAt (𝓡∂ 2) p (F.parametrization i (a.symm (a x)))
      rw [a.left_inv (hsource hx)]
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨a x, ⟨x, hx, rfl⟩, ?_⟩
      change extChartAt (𝓡∂ 2) p (F.parametrization i (a.symm (a x))) = _
      rw [a.left_inv (hsource hx)]
  have hv_integrable : IntegrableOn (coordinateAreaDensity g f.toFun p) v := by
    exact AreaAnalysis.coordinateDensity_integrable_measurableChartSubset
      g f.toFun f.smooth p ((F.parametrization i) '' s) hparameter_image hparameter_source
  obtain ⟨_, _, hinj, _, hd⟩ := native_sector_chart_geometry f F h i j p
  have hder : ∀ y ∈ u, HasFDerivWithinAt c (fderiv ℝ c y) u y :=
    fun y hy => (hd y (hsubD hy)).1.hasFDerivWithinAt
  have hweighted : IntegrableOn (fun y => |(fderiv ℝ c y).det| •
      coordinateAreaDensity g f.toFun p (c y)) u := by
    apply (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hu hder
      (hinj.mono hsubD) (coordinateAreaDensity g f.toFun p)).1
    simpa only [himage] using hv_integrable
  have hcovariance : ∀ y ∈ u,
      sectorCoordinateDensity g (F.map ∘ F.parametrization i) j y =
        |(fderiv ℝ c y).det| • coordinateAreaDensity g f.toFun p (c y) :=
    fun y hy => native_sector_density_covariance g f F h i j p y (hsubD hy)
  refine ⟨hweighted.congr_fun (fun y hy => (hcovariance y hy).symm) hu,
    hv_integrable, ?_⟩
  calc
    (∫ y in u, sectorCoordinateDensity g (F.map ∘ F.parametrization i) j y) =
        ∫ y in u, |(fderiv ℝ c y).det| • coordinateAreaDensity g f.toFun p (c y) :=
      setIntegral_congr_fun hu hcovariance
    _ = ∫ y in c '' u, coordinateAreaDensity g f.toFun p y :=
      (integral_image_eq_integral_abs_det_fderiv_smul volume hu hder
        (hinj.mono hsubD) (coordinateAreaDensity g f.toFun p)).symm
    _ = ∫ y in v, coordinateAreaDensity g f.toFun p y := by rw [himage]
end
end SeifertSurfaces.MetricFoundations.B1Bridges
