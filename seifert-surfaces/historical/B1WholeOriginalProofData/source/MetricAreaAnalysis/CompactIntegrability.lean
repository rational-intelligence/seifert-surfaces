import MetricAreaAnalysis.ChartCalculus

open scoped Manifold ContDiff ENNReal
open Set Topology MeasureTheory Bundle

noncomputable section
namespace SeifertSurfaces.MetricFoundations.AreaAnalysis
open Foundations
universe u v
set_option maxSynthPendingDepth 3

/- H08: includes the empty surface, for which count can be zero. -/
theorem compactChartCover_exists (S : CompactOrientedSurface.{u}) :
    Nonempty (CompactChartCover S) := by
  classical
  have hsource (x : S) : IsOpen (surfaceChart x).source := by
    rw [extChartAt_source]
    exact (chartAt (EuclideanHalfSpace 2) x).open_source
  have hlocal (x : S) : ∃ V : Set S, IsOpen V ∧ x ∈ V ∧
      closure V ⊆ (surfaceChart x).source ∧ IsCompact (closure V) := by
    obtain ⟨V, hV, hxV, hsub, hcomp⟩ :=
      exists_open_between_and_isCompact_closure isCompact_singleton (hsource x)
        (singleton_subset_iff.mpr (mem_extChartAt_source x))
    exact ⟨V, hV, hxV (mem_singleton x), hsub, hcomp⟩
  choose V hV hmem hsub hcomp using hlocal
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover V hV (by
    intro x _
    exact mem_iUnion.mpr ⟨x, hmem x⟩)
  let center : Fin t.card → S := fun i => (t.equivFin.symm i : S)
  have hcover : (⋃ i, V (center i)) = univ := by
    apply Subset.antisymm (subset_univ _)
    intro x hx
    rcases mem_iUnion.mp (ht hx) with ⟨y, hy⟩
    rcases mem_iUnion.mp hy with ⟨hyt, hxy⟩
    refine mem_iUnion.mpr ⟨t.equivFin ⟨y, hyt⟩, ?_⟩
    simpa only [center, Equiv.symm_apply_apply] using hxy
  exact ⟨⟨t.card, center, fun i => V (center i), fun i => closure (V (center i)),
    fun i => hV (center i), fun _ => subset_closure,
    fun i => hcomp (center i), fun i => hsub (center i), hcover⟩⟩

/- H09: disjointed is concrete; none of these pieces is assumed compact. -/
theorem compactChartCover_disjoint_refinement {S : CompactOrientedSurface.{u}}
    (C : CompactChartCover S) :
    (∀ k, MeasurableSet (compactCoverPiece C k)) ∧
    (∀ k, compactCoverPiece C k ⊆ C.openSet k ∧ compactCoverPiece C k ⊆ C.compactSet k) ∧
    Pairwise (fun k l => Disjoint (compactCoverPiece C k) (compactCoverPiece C l)) ∧
    (⋃ k, compactCoverPiece C k) = univ := by
  letI : BorelSpace S := ⟨rfl⟩
  refine ⟨?_, ?_, disjoint_disjointed C.openSet, ?_⟩
  · intro k
    rw [compactCoverPiece, disjointed_eq_inter_compl]
    exact (C.isOpen k).measurableSet.inter (MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun _ => (C.isOpen j).measurableSet.compl)
  · intro k
    exact ⟨disjointed_subset C.openSet k,
      (disjointed_subset C.openSet k).trans (C.open_subset k)⟩
  · simpa only [compactCoverPiece, iUnion_disjointed] using C.covers

variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]

/- H10: continuity only on the actual chart target, with compact coordinate image. -/
theorem coordinateDensity_integrable_compactChart (g : SmoothMetric M)
    {S : CompactOrientedSurface.{u}} (F : S → M)
    (hF : ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ F) (p : S) (K : Set S)
    (hK : IsCompact K) (hsub : K ⊆ (surfaceChart p).source) :
    IntegrableOn (coordinateAreaDensity g F p) ((surfaceChart p) '' K) := by
  have hcompact : IsCompact ((surfaceChart p) '' K) :=
    hK.image_of_continuousOn ((continuousOn_extChartAt (I := 𝓡∂ 2) p).mono hsub)
  exact ((coordinateAreaDensity_continuous g F hF p).mono
    (image_subset_iff.mpr (fun _ hx => (surfaceChart p).mapsTo (hsub hx)))).integrableOn_compact hcompact

/- H11: transfer from a compact cover chart into an arbitrary original chart. -/
theorem coordinateDensity_integrable_cover_intersection (g : SmoothMetric M)
    {S : CompactOrientedSurface.{u}} (F : S → M)
    (hF : ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ F) (p : S) (s : Set S)
    (hs : MeasurableSet s) (hsub : s ⊆ (surfaceChart p).source)
    (C : CompactChartCover S) (k : Fin C.count) :
    IntegrableOn (coordinateAreaDensity g F p)
      ((surfaceChart p) '' (s ∩ compactCoverPiece C k)) := by
  letI : BorelSpace S := ⟨rfl⟩
  have hpiece := compactChartCover_disjoint_refinement C
  have hmeas : MeasurableSet (s ∩ compactCoverPiece C k) := hs.inter (hpiece.1 k)
  have hcompactsub : s ∩ compactCoverPiece C k ⊆ C.compactSet k :=
    inter_subset_right.trans (hpiece.2.1 k).2
  have hover : s ∩ compactCoverPiece C k ⊆
      (surfaceChart p).source ∩ (surfaceChart (C.center k)).source :=
    fun x hx => ⟨hsub hx.1, C.subordinate k (hcompactsub hx)⟩
  apply (coordinateIntegrable_overlap g F hF p (C.center k) _ hmeas hover).mpr
  exact (coordinateDensity_integrable_compactChart g F hF (C.center k)
    (C.compactSet k) (C.isCompact k) (C.subordinate k)).mono_set
      (image_mono hcompactsub)

/- H12: the stronger smooth-map producer does not require an embedding. -/
theorem coordinateDensity_integrable_measurableChartSubset (g : SmoothMetric M)
    {S : CompactOrientedSurface.{u}} (F : S → M)
    (hF : ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ F) (p : S) (s : Set S)
    (hs : MeasurableSet s) (hsub : s ⊆ (surfaceChart p).source) :
    IntegrableOn (coordinateAreaDensity g F p) ((surfaceChart p) '' s) := by
  let C := Classical.choice (compactChartCover_exists S)
  have hcover := (compactChartCover_disjoint_refinement C).2.2.2
  have heq : s = ⋃ k, s ∩ compactCoverPiece C k := by
    apply Subset.antisymm
    · intro x hx
      have hxc : x ∈ ⋃ k, compactCoverPiece C k := by rw [hcover]; trivial
      rcases mem_iUnion.mp hxc with ⟨k, hk⟩
      exact mem_iUnion.mpr ⟨k, hx, hk⟩
    · intro x hx
      rcases mem_iUnion.mp hx with ⟨k, hk⟩
      exact hk.1
  rw [heq, image_iUnion]
  exact integrableOn_finite_iUnion.mpr
    (fun k => coordinateDensity_integrable_cover_intersection g F hF p s hs hsub C k)

end SeifertSurfaces.MetricFoundations.AreaAnalysis
