import A5NativeVertexFromImageCover

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC

/-- A finite set of interior image singularities is removable from an
actual native piecewise minimal surface. The pointwise theorem chooses all
projection/graph data itself; only the punctured smooth image charts enter. -/
theorem native_image_chart_cover_of_finite_interior_exceptional_set
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface} (F : GeometricPiecewiseSurface S E.Carrier)
    (h : AmbientMetric ThreeSphere)
    (A : Set S) (hA : A.Finite) (hAboundary : A ⊆ S.boundaryᶜ)
    (hpieces : ∀ i j, IsMinimalPatch h
      (E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j)
      (interior ((F.domain i).chart j).map.target))
    (hcover : ∀ x ∉ A, ∃ C : SmoothImageChart S F.map, x ∈ C.chart.source) :
    ∀ x : S, ∃ C : SmoothImageChart S F.map, x ∈ C.chart.source := by
  intro x
  by_cases hxA : x ∈ A
  · let V := S.boundaryᶜ ∩ (A \ {x})ᶜ
    have hV : IsOpen V :=
      ((𝓡∂ 2).isClosed_boundary (M := S) (n := ∞) (by simp)).isOpen_compl.inter
        (show (A \ {x}).Finite from hA.subset sdiff_subset).isClosed.isOpen_compl
    have hxV : x ∈ V := ⟨hAboundary hxA, fun hx => hx.2 (mem_singleton x)⟩
    let c : SmoothAmbientChart ThreeSphere := {
      chart := chartAt E3 (E.toSphere (F.map x))
      smooth := contMDiffOn_chart
      inverse_smooth := contMDiffOn_chart_symm }
    obtain ⟨C, hxC, _⟩ := native_interior_image_chart_of_punctured_image_cover E F h x V hV hxV
      (fun _ hy => hy.1) c (mem_chart_source E3 _) hpieces
      (fun y hy hne => hcover y (fun hyA => hy.2 ⟨hyA, hne⟩))
    exact ⟨C, hxC⟩
  · exact hcover x hxA

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
