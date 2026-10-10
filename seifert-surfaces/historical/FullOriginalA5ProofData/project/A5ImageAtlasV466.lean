import A5BoundaryTransitionV466

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.GlobalSmoothSource
universe u v
variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]

private def imageChartOpen {S : CompactOrientedSurface.{u}} {F : GeometricPiecewiseSurface S M}
    (c : SmoothImageChart S F.map) : OpenPartialHomeomorph S (EuclideanHalfSpace 2) where
  toPartialHomeomorph := c.chart
  open_source := c.source_open
  open_target := c.target_open

@[instance_reducible] private def imageChartedSpace {S : CompactOrientedSurface.{u}} {F : GeometricPiecewiseSurface S M}
    (c : S → SmoothImageChart S F.map) (hc : ∀ x, x ∈ (c x).chart.source) :
    ChartedSpace (EuclideanHalfSpace 2) S where
  atlas := Set.range (fun x => imageChartOpen (c x))
  chartAt x := imageChartOpen (c x)
  mem_chart_source := hc
  chart_mem_atlas := fun x => mem_range_self x

private theorem imageChartedSpace_manifold
    {S : CompactOrientedSurface.{u}} {F : GeometricPiecewiseSurface S M}
    (c : S → SmoothImageChart S F.map) (hc : ∀ x, x ∈ (c x).chart.source) :
    letI := imageChartedSpace c hc; IsManifold (𝓡∂ 2) ∞ S := by
  letI := imageChartedSpace c hc
  apply isManifold_of_contDiffOn
  rintro e d ⟨p,rfl⟩ ⟨q,rfl⟩
  have ht := native_image_chart_transition_smooth F (c p) (c q)
  exact ((𝓡∂ 2).contMDiff.comp_contMDiffOn
    (ht.comp ((𝓡∂ 2).contMDiffOn_symm.mono inter_subset_right)
      (fun _ hz => hz.1))).contDiffOn

private theorem imageChartedSpace_map_smooth
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S M)
    (c : S → SmoothImageChart S F.map) (hc : ∀ x, x ∈ (c x).chart.source) :
    letI := imageChartedSpace c hc;
    letI := imageChartedSpace_manifold c hc;
    ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ F.map := by
  letI := imageChartedSpace c hc
  letI := imageChartedSpace_manifold c hc
  intro x
  have hx := (c x).chart.map_source (hc x)
  have hsm := (c x).cInfinity.contMDiffAt ((c x).target_open.mem_nhds hx)
  apply contMDiffAt_iff.mpr
  refine ⟨F.map.continuous.continuousAt, ?_⟩
  have hg := (contMDiffAt_iff.mp hsm).2
  have he : F.map ((c x).chart.symm ((c x).chart x)) = F.map x :=
    congrArg F.map ((c x).chart.left_inv (hc x))
  change ContDiffWithinAt ℝ ∞
    (extChartAt (𝓡∂ 3) (F.map x) ∘ F.map ∘ (c x).chart.symm ∘ (𝓡∂ 2).symm)
    (range (𝓡∂ 2)) ((𝓡∂ 2) ((c x).chart x))
  simpa only [extChartAt_coe_symm, chartAt_self_eq, OpenPartialHomeomorph.refl_symm,
    OpenPartialHomeomorph.refl_apply, extChartAt_self_apply, id_eq,
    Function.comp_apply, he, Function.comp_def] using hg

private theorem imageChartedSpace_map_rank
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S M)
    (c : S → SmoothImageChart S F.map) (hc : ∀ x, x ∈ (c x).chart.source) :
    letI := imageChartedSpace c hc;
    letI := imageChartedSpace_manifold c hc;
    ∀ x : S, Function.Injective (mfderiv (𝓡∂ 2) (𝓡∂ 3) F.map x) := by
  letI := imageChartedSpace c hc
  letI := imageChartedSpace_manifold c hc
  have hf := imageChartedSpace_map_smooth F c hc
  intro x
  have hx := (c x).chart.map_source (hc x)
  have hsm := (c x).cInfinity.contMDiffAt ((c x).target_open.mem_nhds hx)
  have hinj := (c x).differential_injective ((c x).chart x) hx
  rw [mfderivWithin_of_mem_nhds ((c x).target_open.mem_nhds hx)] at hinj
  have hm := (hsm.mdifferentiableAt (by simp)).hasMFDerivAt.2
  have hF := (hf.mdifferentiableAt (by simp) (x := x)).hasMFDerivAt.2
  have he : F.map ((c x).chart.symm ((c x).chart x)) = F.map x :=
    congrArg F.map ((c x).chart.left_inv (hc x))
  have hcoord : writtenInExtChartAt (𝓡∂ 2) (𝓡∂ 3) ((c x).chart x)
      (F.map ∘ (c x).chart.symm) = writtenInExtChartAt (𝓡∂ 2) (𝓡∂ 3) x F.map := by
    simp only [writtenInExtChartAt,extChartAt_coe_symm,chartAt_self_eq,
      OpenPartialHomeomorph.refl_symm,OpenPartialHomeomorph.refl_apply,id_eq,he,
      Function.comp_def]
    rfl
  have hxy : extChartAt (𝓡∂ 2) x x = (𝓡∂ 2) ((c x).chart x) := rfl
  have hD := ((𝓡∂ 2).uniqueDiffOn _ (mem_range_self _)).eq hm ((by simpa only [hcoord, hxy, extChartAt_self_apply] using hF) :
    HasFDerivWithinAt (writtenInExtChartAt (𝓡∂ 2) (𝓡∂ 3) ((c x).chart x)
      (F.map ∘ (c x).chart.symm))
      ((tangentSpaceCastModel (𝓡∂ 3) (F.map x)).toContinuousLinearMap.comp
        ((mfderiv (𝓡∂ 2) (𝓡∂ 3) F.map x).comp
          (tangentSpaceCastModel (𝓡∂ 2) x).symm.toContinuousLinearMap))
      (range (𝓡∂ 2)) ((𝓡∂ 2) ((c x).chart x)))
  have hi : Function.Injective
      ((tangentSpaceCastModel (𝓡∂ 3) (F.map x)).toContinuousLinearMap.comp
        ((mfderiv (𝓡∂ 2) (𝓡∂ 3) F.map x).comp
          (tangentSpaceCastModel (𝓡∂ 2) x).symm.toContinuousLinearMap)) := by
    rw [←hD]
    exact (tangentSpaceCastModel (𝓡∂ 3) _).injective.comp
      (hinj.comp (tangentSpaceCastModel (𝓡∂ 2) _).symm.injective)
  intro a b hab
  have heq := @hi (tangentSpaceCastModel (𝓡∂ 2) x a)
    (tangentSpaceCastModel (𝓡∂ 2) x b) (by simpa only [ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] using
      (congrArg (tangentSpaceCastModel (𝓡∂ 3) (F.map x)) hab))
  exact (tangentSpaceCastModel (𝓡∂ 2) x).injective heq

private theorem imageChartedSpace_boundary
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S M)
    (c : S → SmoothImageChart S F.map) (hc : ∀ x, x ∈ (c x).chart.source) :
    (letI := imageChartedSpace c hc; (𝓡∂ 2).boundary S) = S.boundary := by
  ext x
  have hb : x ∈ S.boundary ↔ (c x).chart x ∈ (𝓡∂ 2).boundary (EuclideanHalfSpace 2) := by
    constructor
    · intro hx
      have hh : (c x).chart x ∈ (c x).chart '' (S.boundary ∩ (c x).chart.source) :=
        ⟨x,⟨hx,hc x⟩,rfl⟩
      rw [(c x).boundary_image] at hh
      exact hh.1
    · intro hx
      have hh : (c x).chart x ∈ (c x).chart '' (S.boundary ∩ (c x).chart.source) := by
        rw [(c x).boundary_image]
        exact ⟨hx,(c x).chart.map_source (hc x)⟩
      obtain ⟨y,hy,he⟩ := hh
      exact (c x).chart.injOn hy.2 (hc x) he ▸ hy.1
  letI := imageChartedSpace c hc
  change (𝓡∂ 2).IsBoundaryPoint x ↔ _
  rw [hb]
  rfl

/-- The actual new smooth atlas and the original map, before choosing its orientation form. -/
structure NativeImageSmoothAtlas {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S M) where
  charted : ChartedSpace (EuclideanHalfSpace 2) S
  smooth : letI := charted; IsManifold (𝓡∂ 2) ∞ S
  map_smooth : letI := charted; letI := smooth; ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ F.map
  map_rank : letI := charted; letI := smooth;
    ∀ x : S, Function.Injective (mfderiv (𝓡∂ 2) (𝓡∂ 3) F.map x)
  boundary_eq : (letI := charted; (𝓡∂ 2).boundary S) = S.boundary

theorem native_image_smooth_atlas_exists
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S M)
    (hcover : ∀ x : S, ∃ c : SmoothImageChart S F.map, x ∈ c.chart.source) :
    Nonempty (NativeImageSmoothAtlas F) := by
  classical
  choose c hc using hcover
  exact ⟨{
    charted := imageChartedSpace c hc
    smooth := imageChartedSpace_manifold c hc
    map_smooth := imageChartedSpace_map_smooth F c hc
    map_rank := imageChartedSpace_map_rank F c hc
    boundary_eq := imageChartedSpace_boundary F c hc }⟩

#print axioms native_image_smooth_atlas_exists
end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.GlobalSmoothSource
