import GeometricCategory
import A3GraphLower

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
universe u v

/-- Near any native source point, only the incident whole pieces occur, and
one actual sector chart of each incident piece suffices for its entire local
image. This is derived from compactness and the native embeddings. -/
theorem native_incident_sector_chart_neighborhood
    {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (x : S) :
    ∃ U : Set S, IsOpen U ∧ x ∈ U ∧
      (∀ i, x ∉ range (F.parametrization i) → range (F.parametrization i) ∩ U = ∅) ∧
      (∀ i, x ∈ range (F.parametrization i) → ∃ j : Fin (F.domain i).count,
        x ∈ (F.parametrization i) '' ((F.domain i).chart j).map.source ∧
        range (F.parametrization i) ∩ U =
          (F.parametrization i) '' (((F.domain i).chart j).map.source ∩
            (F.parametrization i) ⁻¹' U)) ∧
      (⋃ i, range (F.parametrization i) ∩ U) = U := by
  classical
  have local_choice (i : Fin F.pieceCount) : ∃ V : Set S, IsOpen V ∧ x ∈ V ∧
      (x ∉ range (F.parametrization i) → range (F.parametrization i) ∩ V = ∅) ∧
      (x ∈ range (F.parametrization i) → ∃ j : Fin (F.domain i).count,
        x ∈ (F.parametrization i) '' ((F.domain i).chart j).map.source ∧
        (F.parametrization i) ⁻¹' V ⊆ ((F.domain i).chart j).map.source) := by
    by_cases hi : x ∈ range (F.parametrization i)
    · obtain ⟨q, hq⟩ := hi
      have hcover : q ∈ ⋃ j, ((F.domain i).chart j).map.source := by
        rw [(F.domain i).covers]
        trivial
      obtain ⟨j, hj⟩ := mem_iUnion.mp hcover
      obtain ⟨V, hV, hqV, _, hpre, _⟩ :=
        A3GraphLower.embedding_ambient_open_source_isolation (F.parametrization i)
          (F.parametrization_embedding i) q ((F.domain i).chart j).map.source
          ((F.domain i).chart j).source_open hj univ isOpen_univ (mem_univ _)
      refine ⟨V, hV, hq ▸ hqV, ?_, fun _ => ⟨j, ⟨q, hj, hq⟩, hpre⟩⟩
      intro hnot
      exact (hnot ⟨q, hq⟩).elim
    · refine ⟨(range (F.parametrization i))ᶜ,
        (isCompact_range (F.parametrization i).continuous).isClosed.isOpen_compl,
        hi, fun _ => inter_compl_self _, fun h => (hi h).elim⟩
  choose V hV hxV havoid hchart using local_choice
  let U : Set S := ⋂ i, V i
  have hUV (i : Fin F.pieceCount) : U ⊆ V i := iInter_subset V i
  refine ⟨U, isOpen_iInter_of_finite hV, mem_iInter.mpr hxV, ?_, ?_, ?_⟩
  · intro i hi
    apply subset_empty_iff.mp
    rw [← havoid i hi]
    exact inter_subset_inter_right _ (hUV i)
  · intro i hi
    obtain ⟨j, hj, hpre⟩ := hchart i hi
    refine ⟨j, hj, ?_⟩
    ext y
    constructor
    · rintro ⟨⟨q, rfl⟩, hq⟩
      exact ⟨q, ⟨hpre (hUV i hq), hq⟩, rfl⟩
    · rintro ⟨q, ⟨_, hq⟩, rfl⟩
      exact ⟨⟨q, rfl⟩, hq⟩
  · rw [← iUnion_inter, F.covers, univ_inter]

/-- The same finite native local cover gives an exact equality of ambient
images, not just containment in a collection of charts. -/
theorem native_local_image_eq_union
    {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (U : Set S) :
    F.map '' U = ⋃ i, (F.map ∘ F.parametrization i) '' ((F.parametrization i) ⁻¹' U) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hcover : x ∈ ⋃ i, range (F.parametrization i) := by rw [F.covers]; trivial
    obtain ⟨i, q, hq⟩ := mem_iUnion.mp hcover
    exact mem_iUnion.mpr ⟨i, q, show F.parametrization i q ∈ U by rw [hq]; exact hx,
      congrArg F.map hq⟩
  · intro hz
    obtain ⟨i, q, hq, rfl⟩ := mem_iUnion.mp hz
    exact ⟨F.parametrization i q, hq, rfl⟩

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
