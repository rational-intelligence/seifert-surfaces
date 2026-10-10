import Section5GeometricDefinitions
import OriginalSection4Whole
import Section4AreaSupport
import A6CompetitorNonempty

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology Function MeasureTheory
open scoped Manifold ContDiff BigOperators

namespace SeifertSurfaces.OriginalEndpoints.Section5.WholeAssemblyV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.GenusLinking SeifertSurfaces.Complexity
open SeifertSurfaces.OriginalEndpoints.Section4
open SeifertSurfaces.OriginalEndpoints.AppendixAOriginal

variable {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)

/-- The actual constant geometric cylinder gives reflexivity without adding
an isotopy premise to a minimum or infimum comparison. -/
theorem geometric_image_isotopic_refl {S : CompactOrientedSurface.{0}}
    (F : GeometricPiecewiseSurface S E.Carrier) : GeometricImageIsotopic F F := by
  obtain ⟨e, stage, hc, ht, h0, h1, _⟩ := A6Construction.fixed_boundary_image_isotopic_refl (E := E) F
  exact ⟨e, stage, hc, ht, h0, h1⟩

theorem native_infimum_le_smooth (H : SourceGeometry E) (v : Vertices E)
    (F : IncompressibleSpanningSurface.{0} E)
    (hv : SurfaceVertex E F = v) (hJ : H.foliation.BoundaryIn F.1.embedding.toFun) :
    areaInfimum E H v ≤ area H.metric F.1.embedding.toFun := by
  obtain ⟨Q, hQ, _⟩ := smooth_as_piecewise (ProperSmoothEmbedding.ofNeat F.1.embedding)
  have hJQ : H.foliation.BoundaryIn Q.map := by
    rw [hQ]
    exact hJ
  have h := area_infimum_le_competitor E H v F hv Q hQ Q hJQ
    (geometric_image_isotopic_refl E Q)
  rw [smooth_piecewise_area H.metric (ProperSmoothEmbedding.ofNeat F.1.embedding) Q hQ] at h
  exact h

theorem smooth_area_nonnegative (H : SourceGeometry E)
    (F : IncompressibleSpanningSurface.{0} E) : 0 ≤ area H.metric F.1.embedding.toFun := by
  obtain ⟨Q, hQ, _⟩ := smooth_as_piecewise (ProperSmoothEmbedding.ofNeat F.1.embedding)
  have h := geometric_area_nonnegative H.metric Q
  rw [smooth_piecewise_area H.metric (ProperSmoothEmbedding.ofNeat F.1.embedding) Q hQ] at h
  exact h

theorem smooth_class_area_values_bddBelow (H : SourceGeometry E) (v : Vertices E) :
    BddBelow {a : ℝ | ∃ F : IncompressibleSpanningSurface.{0} E,
      AppendixBOriginalV479.vertexOf F = v ∧ H.foliation.BoundaryIn F.1.embedding.toFun ∧
        a = area H.metric F.1.embedding.toFun} := by
  refine ⟨0, ?_⟩
  rintro a ⟨F, _, _, rfl⟩
  exact smooth_area_nonnegative E H F

end SeifertSurfaces.OriginalEndpoints.Section5.WholeAssemblyV480
