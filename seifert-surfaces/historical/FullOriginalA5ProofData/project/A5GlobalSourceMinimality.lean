import A5NativeSmoothImageMinimality
import A5GlobalSourceConsumer

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
universe u

/-- The paid global source reconstruction inherits genuine minimality in
the same ambient metric from its native pieces, through its literal
pointwise source homeomorphism. -/
theorem smooth_source_reconstruction_minimal_of_pieces
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    (G : A7.SourceGeometry E) {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier)
    (Q : GlobalSmoothSource.SmoothSourceReconstruction E F)
    (hpieces : ∀ i j, IsMinimalPatch G.extension
      (E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j)
      (interior ((F.domain i).chart j).map.target)) :
    MinimalEmbedding E G Q.embedding := by
  intro p
  let C : GlobalSmoothSource.A5CompactSmoothCarrier := { carrier := Q.source }
  let d := GlobalSmoothSource.a5InteriorExtendedChart C p
  let e := Q.homeomorph.symm.toOpenPartialHomeomorph.trans d
  have het : e.target = d.target := by
    simp [e]
  have he : F.map ∘ e.symm = Q.embedding.toFun ∘ d.symm := by
    funext y
    exact (Q.pointwise_same_map (d.symm y)).symm
  have hd : ContMDiffOn 𝓘(ℝ, E2) (𝓡∂ 2) ∞ d.symm d.target :=
    (contMDiffOn_extChartAt_symm p).mono interior_subset
  have hf : ContMDiffOn 𝓘(ℝ, E2) (𝓡∂ 3) ∞ (F.map ∘ e.symm) d.target := by
    rw [he]
    exact Q.embedding.smooth.comp_contMDiffOn hd
  have hr (y : E2) (hy : y ∈ d.target) :
      Function.Injective (mfderiv 𝓘(ℝ, E2) (𝓡∂ 3) (F.map ∘ e.symm) y) := by
    rw [he, mfderiv_comp y (Q.embedding.smooth.mdifferentiable (by simp) _)
      ((hd.contMDiffAt (d.open_target.mem_nhds hy)).mdifferentiableAt (by simp))]
    apply (Q.embedding.differential_injective _).comp
    have hi := isInvertible_mfderivWithin_extChartAt_symm (I := 𝓡∂ 2) (x := p)
      (interior_subset hy)
    have hn : range (𝓡∂ 2) ∈ 𝓝 y :=
      mem_of_superset (d.open_target.mem_nhds hy)
        (interior_subset.trans (extChartAt_target_subset_range p))
    rw [mfderivWithin_of_mem_nhds hn] at hi
    exact hi.injective
  have hm := native_smooth_image_chart_minimal_of_pieces E F G.extension e d.target d.open_target
    (by rw [het]) hf hr hpieces
  have hmap : E.toSphere ∘ F.map ∘ e.symm =
      E.toSphere ∘ Q.embedding.toFun ∘ (extChartAt (𝓡∂ 2) p).symm := by
    rw [he]
    rfl
  rw [hmap] at hm
  have htarget : interior (extChartAt (𝓡∂ 2) p).target =
      (extChartAt (𝓡∂ 2) p).target ∩ {y : E2 | 0 < y 0} := by
    have hB : IsOpen ((𝓡∂ 2).symm ⁻¹' (chartAt (EuclideanHalfSpace 2) p).target) :=
      (chartAt (EuclideanHalfSpace 2) p).open_target.preimage (𝓡∂ 2).continuous_symm
    rw [extChartAt_target, interior_inter, hB.interior_eq,
      interior_range_modelWithCornersEuclideanHalfSpace]
    ext y
    constructor
    · rintro ⟨hy, hp⟩
      exact ⟨⟨hy, by simpa only [range_modelWithCornersEuclideanHalfSpace, mem_ofPred_eq] using hp.le⟩, hp⟩
    · rintro ⟨⟨hy, _⟩, hp⟩
      exact ⟨hy, hp⟩
  change IsMinimalPatch G.extension _ (interior (extChartAt (𝓡∂ 2) p).target) at hm
  rwa [htarget] at hm

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
