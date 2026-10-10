import B1SmoothSectorTransport
import B1SectorImageTransport
import B1SeamNullity
open scoped Manifold ContDiff ENNReal
open Set Topology MeasureTheory
namespace SeifertSurfaces.MetricFoundations.B1Bridges
open SeifertSurfaces.Foundations
universe u v
noncomputable section
set_option autoImplicit false
variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]

abbrev SectorCellIndex {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) :=
  Σ i : Fin F.pieceCount, Fin (canonicalSectorPartition (F.domain i)).count

def sectorCellSet {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (α : SectorCellIndex F) : Set (F.domain α.1) :=
  (canonicalSectorPartition (F.domain α.1)).piece α.2

def sectorCellChart {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (α : SectorCellIndex F) : Fin (F.domain α.1).count :=
  (canonicalSectorPartition (F.domain α.1)).chartIndex α.2

def sectorCellIntegral {S : CompactOrientedSurface.{u}}
    (g : SmoothMetric M) (F : GeometricPiecewiseSurface S M)
    (α : SectorCellIndex F) (s : Set (F.domain α.1)) : ℝ :=
  ∫ y in ((F.domain α.1).chart (sectorCellChart F α)).map '' s,
    sectorCoordinateDensity g (F.map ∘ F.parametrization α.1) (sectorCellChart F α) y

def smoothMixedCell {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (Q : ChartPartition S)
    (α : SectorCellIndex F) (b : Fin Q.count) : Set (F.domain α.1) :=
  sectorCellSet F α ∩ (F.domain α.1).interior ∩
    (F.parametrization α.1) ⁻¹' (Q.piece b ∩ (F.seam.carrier ∪ S.boundary)ᶜ)

def smoothMixedImage {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (Q : ChartPartition S)
    (α : SectorCellIndex F) (b : Fin Q.count) : Set S :=
  (F.parametrization α.1) '' smoothMixedCell F Q α b

def mixedSectorCell {S R : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (G : GeometricPiecewiseSurface R M)
    (a : R ≃ₜ S) (α : SectorCellIndex G) (β : SectorCellIndex F) : Set (G.domain α.1) :=
  sectorCellSet G α ∩ (G.domain α.1).interior ∩
    (G.parametrization α.1) ⁻¹'
      ((G.seam.carrier ∪ R.boundary)ᶜ ∩ a ⁻¹'
        ((F.parametrization β.1) '' (sectorCellSet F β ∩ (F.domain β.1).interior)))

theorem smooth_mixed_refinement_metadata {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (Q : ChartPartition S) :
    (∀ α b, MeasurableSet (smoothMixedCell F Q α b) ∧
      MeasurableSet (smoothMixedImage F Q α b)) ∧
    (∀ α, Pairwise (fun b c => Disjoint (smoothMixedCell F Q α b) (smoothMixedCell F Q α c))) ∧
    (∀ b, Pairwise (fun α β => Disjoint (smoothMixedImage F Q α b) (smoothMixedImage F Q β b))) ∧
    (∀ α, (⋃ b, smoothMixedCell F Q α b) = sectorCellSet F α ∩ (F.domain α.1).interior) ∧
    (∀ b, (⋃ α, smoothMixedImage F Q α b) = Q.piece b ∩ (F.seam.carrier ∪ S.boundary)ᶜ) := by
  classical
  letI : BorelSpace S := ⟨rfl⟩
  letI : ∀ i, BorelSpace (F.domain i) := fun _ => ⟨rfl⟩
  have hseam : IsClosed F.seam.carrier :=
    (isClosed_iUnion_of_finite fun i => (isCompact_range (F.seam.arc i).continuous).isClosed).union
      (isClosed_iUnion_of_finite fun i => (isCompact_range (F.seam.circle i).continuous).isClosed)
  have hboundary : IsClosed S.boundary := (𝓡∂ 2).isClosed_boundary (M := S) (n := ∞) (by decide)
  have himage (i : Fin F.pieceCount) : MeasurableSet
      ((F.parametrization i) '' (F.domain i).interior) := by
    obtain ⟨x, hx, he⟩ := F.piece_interior_component i
    rw [he, connectedComponentIn_eq_image hx]
    exact (MeasurableEmbedding.subtype_coe (hseam.union hboundary).measurableSet.compl).measurableSet_image'
      isClosed_connectedComponent.measurableSet
  have hinter (i : Fin F.pieceCount) : MeasurableSet (F.domain i).interior := by
    have := (himage i).preimage (F.parametrization i).continuous.measurable
    simpa only [Set.preimage_image_eq _ (F.parametrization_embedding i).injective] using this
  have hclean (i : Fin F.pieceCount) :
      (F.parametrization i) '' (F.domain i).interior ⊆ (F.seam.carrier ∪ S.boundary)ᶜ := by
    obtain ⟨x, hx, he⟩ := F.piece_interior_component i
    rw [he]
    exact connectedComponentIn_subset _ _
  have hcell (α : SectorCellIndex F) (b : Fin Q.count) : MeasurableSet (smoothMixedCell F Q α b) :=
    (((canonicalSectorPartition (F.domain α.1)).measurable α.2).inter (hinter α.1)).inter
      (((Q.measurable b).inter (hseam.union hboundary).measurableSet.compl).preimage
        (F.parametrization α.1).continuous.measurable)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro α b
    refine ⟨hcell α b, ?_⟩
    exact ((F.parametrization_embedding α.1).measurableEmbedding
      (isCompact_range (F.parametrization α.1).continuous).isClosed.measurableSet).measurableSet_image'
        (hcell α b)
  · intro α b c hbc
    refine Set.disjoint_left.2 ?_
    intro x hx hy
    exact Set.disjoint_left.1 (Q.disjoint hbc) hx.2.1 hy.2.1
  · intro b α β hab
    rcases α with ⟨i, j⟩
    rcases β with ⟨k, l⟩
    refine Set.disjoint_left.2 ?_
    rintro z ⟨x, hx, rfl⟩ ⟨y, hy, he⟩
    by_cases hik : i = k
    · subst k
      have hxy : y = x := (F.parametrization_embedding i).injective he
      subst y
      have hjl : j ≠ l := fun h => hab (by cases h; rfl)
      exact Set.disjoint_left.1 ((canonicalSectorPartition (F.domain i)).disjoint hjl)
        hx.1.1 hy.1.1
    · exact Set.disjoint_left.1 (F.pieces_distinct hik)
        ⟨x, hx.1.2, rfl⟩ ⟨y, hy.1.2, he⟩
  · intro α
    ext x
    constructor
    · intro hx
      obtain ⟨b, hb⟩ := Set.mem_iUnion.1 hx
      exact hb.1
    · intro hx
      have hcover : F.parametrization α.1 x ∈ ⋃ b, Q.piece b := by rw [Q.covers]; trivial
      obtain ⟨b, hb⟩ := Set.mem_iUnion.1 hcover
      exact Set.mem_iUnion.2 ⟨b, hx, hb, hclean α.1 ⟨x, hx.2, rfl⟩⟩
  · intro b
    ext z
    constructor
    · intro hz
      obtain ⟨α, x, hx, rfl⟩ := Set.mem_iUnion.1 hz
      exact hx.2
    · intro hz
      have hcover : z ∈ ⋃ i, Set.range (F.parametrization i) := by rw [F.covers]; trivial
      obtain ⟨i, x, rfl⟩ := Set.mem_iUnion.1 hcover
      have hx : x ∈ (F.domain i).interior := by
        intro hx
        exact hz.2 (F.piece_boundary i ⟨x, hx, rfl⟩)
      have hcover : x ∈ ⋃ j, (canonicalSectorPartition (F.domain i)).piece j := by
        rw [(canonicalSectorPartition (F.domain i)).covers]; trivial
      obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hcover
      exact Set.mem_iUnion.2 ⟨⟨i, j⟩, x, ⟨⟨hj, hx⟩, hz⟩, rfl⟩

theorem same_image_mixed_refinement_metadata {S R : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (G : GeometricPiecewiseSurface R M)
    (a : R ≃ₜ S) (ha : ∀ x, F.map (a x) = G.map x)
    (hb : a ⁻¹' S.boundary = R.boundary) :
    (∀ α β, MeasurableSet (mixedSectorCell F G a α β)) ∧
    (∀ α, Pairwise (fun β γ => Disjoint (mixedSectorCell F G a α β) (mixedSectorCell F G a α γ))) ∧
    (∀ α, (⋃ β, mixedSectorCell F G a α β) =
      sectorCellSet G α ∩ (G.domain α.1).interior ∩
        (G.parametrization α.1) ⁻¹' (a ⁻¹' F.seam.carrierᶜ)) ∧
    (∀ α β, a '' ((G.parametrization α.1) '' mixedSectorCell F G a α β) =
      (F.parametrization β.1) '' mixedSectorCell G F a.symm β α) := by
  classical
  letI : BorelSpace S := ⟨rfl⟩
  letI : BorelSpace R := ⟨rfl⟩
  letI : ∀ i, BorelSpace (F.domain i) := fun _ => ⟨rfl⟩
  letI : ∀ i, BorelSpace (G.domain i) := fun _ => ⟨rfl⟩
  have hseamF : IsClosed F.seam.carrier :=
    (isClosed_iUnion_of_finite fun i => (isCompact_range (F.seam.arc i).continuous).isClosed).union
      (isClosed_iUnion_of_finite fun i => (isCompact_range (F.seam.circle i).continuous).isClosed)
  have hseamG : IsClosed G.seam.carrier :=
    (isClosed_iUnion_of_finite fun i => (isCompact_range (G.seam.arc i).continuous).isClosed).union
      (isClosed_iUnion_of_finite fun i => (isCompact_range (G.seam.circle i).continuous).isClosed)
  have hboundaryS : IsClosed S.boundary := (𝓡∂ 2).isClosed_boundary (M := S) (n := ∞) (by decide)
  have hboundaryR : IsClosed R.boundary := (𝓡∂ 2).isClosed_boundary (M := R) (n := ∞) (by decide)
  have hinterF (i : Fin F.pieceCount) : MeasurableSet (F.domain i).interior := by
    obtain ⟨x, hx, he⟩ := F.piece_interior_component i
    have hi : MeasurableSet ((F.parametrization i) '' (F.domain i).interior) := by
      rw [he, connectedComponentIn_eq_image hx]
      exact (MeasurableEmbedding.subtype_coe (hseamF.union hboundaryS).measurableSet.compl).measurableSet_image'
        isClosed_connectedComponent.measurableSet
    have hp := hi.preimage (F.parametrization i).continuous.measurable
    simpa only [Set.preimage_image_eq _ (F.parametrization_embedding i).injective] using hp
  have hinterG (i : Fin G.pieceCount) : MeasurableSet (G.domain i).interior := by
    obtain ⟨x, hx, he⟩ := G.piece_interior_component i
    have hi : MeasurableSet ((G.parametrization i) '' (G.domain i).interior) := by
      rw [he, connectedComponentIn_eq_image hx]
      exact (MeasurableEmbedding.subtype_coe (hseamG.union hboundaryR).measurableSet.compl).measurableSet_image'
        isClosed_connectedComponent.measurableSet
    have hp := hi.preimage (G.parametrization i).continuous.measurable
    simpa only [Set.preimage_image_eq _ (G.parametrization_embedding i).injective] using hp
  have hcleanF (i : Fin F.pieceCount) :
      (F.parametrization i) '' (F.domain i).interior ⊆ (F.seam.carrier ∪ S.boundary)ᶜ := by
    obtain ⟨x, hx, he⟩ := F.piece_interior_component i
    rw [he]
    exact connectedComponentIn_subset _ _
  have hcleanG (i : Fin G.pieceCount) :
      (G.parametrization i) '' (G.domain i).interior ⊆ (G.seam.carrier ∪ R.boundary)ᶜ := by
    obtain ⟨x, hx, he⟩ := G.piece_interior_component i
    rw [he]
    exact connectedComponentIn_subset _ _
  have hcell (α : SectorCellIndex G) (β : SectorCellIndex F) :
      MeasurableSet (mixedSectorCell F G a α β) := by
    have hi : MeasurableSet ((F.parametrization β.1) ''
        (sectorCellSet F β ∩ (F.domain β.1).interior)) :=
      ((F.parametrization_embedding β.1).measurableEmbedding
        (isCompact_range (F.parametrization β.1).continuous).isClosed.measurableSet).measurableSet_image'
          (((canonicalSectorPartition (F.domain β.1)).measurable β.2).inter (hinterF β.1))
    exact (((canonicalSectorPartition (G.domain α.1)).measurable α.2).inter (hinterG α.1)).inter
      (((hseamG.union hboundaryR).measurableSet.compl.inter (hi.preimage a.continuous.measurable)).preimage
        (G.parametrization α.1).continuous.measurable)
  refine ⟨hcell, ?_, ?_, ?_⟩
  · intro α β γ hβγ
    refine Set.disjoint_left.2 ?_
    intro x hx hy
    rcases β with ⟨i, j⟩
    rcases γ with ⟨k, l⟩
    rcases hx.2.2 with ⟨y, hyF, he⟩
    rcases hy.2.2 with ⟨z, hzF, hez⟩
    by_cases hik : i = k
    · subst k
      have hyz : y = z := (F.parametrization_embedding i).injective (he.trans hez.symm)
      subst z
      have hjl : j ≠ l := fun h => hβγ (by cases h; rfl)
      exact Set.disjoint_left.1 ((canonicalSectorPartition (F.domain i)).disjoint hjl) hyF.1 hzF.1
    · exact Set.disjoint_left.1 (F.pieces_distinct hik)
        ⟨y, hyF.2, he⟩ ⟨z, hzF.2, hez⟩
  · intro α
    ext x
    constructor
    · intro hx
      obtain ⟨β, hβ⟩ := Set.mem_iUnion.1 hx
      have h := hβ.2.2
      rcases h with ⟨y, hy, he⟩
      exact ⟨hβ.1, fun h => (hcleanF β.1 ⟨y, hy.2, he⟩) (Or.inl h)⟩
    · rintro ⟨⟨hxcell, hxint⟩, hxpre⟩
      have hxclean := hcleanG α.1 ⟨x, hxint, rfl⟩
      have hxS : a (G.parametrization α.1 x) ∉ S.boundary := by
        intro h
        have hr : G.parametrization α.1 x ∈ R.boundary := by rw [← hb]; exact h
        exact hxclean (Or.inr hr)
      have hcover : a (G.parametrization α.1 x) ∈ ⋃ i, Set.range (F.parametrization i) := by
        rw [F.covers]; trivial
      obtain ⟨i, y, he⟩ := Set.mem_iUnion.1 hcover
      have hyint : y ∈ (F.domain i).interior := by
        intro hy
        rcases F.piece_boundary i ⟨y, hy, he⟩ with hs | hs
        · exact hxpre hs
        · exact hxS hs
      have hcover : y ∈ ⋃ j, (canonicalSectorPartition (F.domain i)).piece j := by
        rw [(canonicalSectorPartition (F.domain i)).covers]; trivial
      obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hcover
      exact Set.mem_iUnion.2 ⟨⟨i, j⟩, ⟨hxcell, hxint⟩, hxclean, y, ⟨hj, hyint⟩, he⟩
  · intro α β
    ext z
    constructor
    · rintro ⟨w, ⟨x, hx, rfl⟩, rfl⟩
      rcases hx with ⟨⟨hxcell, hxint⟩, hxclean, y, ⟨hycell, hyint⟩, he⟩
      refine ⟨y, ⟨⟨hycell, hyint⟩, hcleanF β.1 ⟨y, hyint, rfl⟩, ?_⟩, he⟩
      exact ⟨x, ⟨hxcell, hxint⟩, by rw [he, a.symm_apply_apply]⟩
    · rintro ⟨y, hy, rfl⟩
      rcases hy with ⟨⟨hycell, hyint⟩, hyclean, x, ⟨hxcell, hxint⟩, he⟩
      have he' : a (G.parametrization α.1 x) = F.parametrization β.1 y := by
        rw [he, a.apply_symm_apply]
      exact ⟨G.parametrization α.1 x,
        ⟨x, ⟨⟨hxcell, hxint⟩, hcleanG α.1 ⟨x, hxint, rfl⟩,
          y, ⟨hycell, hyint⟩, he'.symm⟩, rfl⟩, he'⟩

theorem smooth_mixed_integrability_and_row_assembly {S : CompactOrientedSurface.{u}}
    (g : SmoothMetric M) (f : ProperSmoothEmbedding S M)
    (F : GeometricPiecewiseSurface S M) (h : F.map = f.continuousMap)
    (Q : ChartPartition S) :
    (∀ α b,
      IntegrableOn (sectorCoordinateDensity g (F.map ∘ F.parametrization α.1) (sectorCellChart F α))
        (((F.domain α.1).chart (sectorCellChart F α)).map '' smoothMixedCell F Q α b) ∧
      IntegrableOn (coordinateAreaDensity g f.toFun (Q.center b))
        ((extChartAt (𝓡∂ 2) (Q.center b)) '' smoothMixedImage F Q α b)) ∧
    (∀ α, sectorCellIntegral g F α (sectorCellSet F α) =
      ∑ b : Fin Q.count, sectorCellIntegral g F α (smoothMixedCell F Q α b)) ∧
    (∀ b, (∫ y in (extChartAt (𝓡∂ 2) (Q.center b)) '' Q.piece b,
      coordinateAreaDensity g f.toFun (Q.center b) y) =
      ∑ α : SectorCellIndex F,
        ∫ y in (extChartAt (𝓡∂ 2) (Q.center b)) '' smoothMixedImage F Q α b,
          coordinateAreaDensity g f.toFun (Q.center b) y) := by
  classical
  letI : BorelSpace S := ⟨rfl⟩
  letI : ∀ i, BorelSpace (F.domain i) := fun _ => ⟨rfl⟩
  letI : ∀ i, MetricSpace (F.domain i) := fun i =>
    TopologicalSpace.metrizableSpaceMetric (F.domain i)
  obtain ⟨hm, hd, hdi, hu, hui⟩ := smooth_mixed_refinement_metadata F Q
  have hcellsub (α : SectorCellIndex F) :
      sectorCellSet F α ⊆ ((F.domain α.1).chart (sectorCellChart F α)).map.source :=
    (canonicalSectorPartition (F.domain α.1)).subordinate α.2
  have hsub (α : SectorCellIndex F) (b : Fin Q.count) :
      smoothMixedCell F Q α b ⊆
        ((F.domain α.1).chart (sectorCellChart F α)).map.source ∩
          (F.domain α.1).interior ∩ (F.parametrization α.1) ⁻¹'
            (S.boundaryᶜ ∩ (extChartAt (𝓡∂ 2) (Q.center b)).source) := by
    intro x hx
    refine ⟨⟨hcellsub α hx.1.1, hx.1.2⟩, ?_, Q.subordinate b hx.2.1⟩
    exact fun hb => hx.2.2 (Or.inr hb)
  have hi (α : SectorCellIndex F) (b : Fin Q.count) :=
    native_sector_subordinate_integral_transport g f F h α.1 (sectorCellChart F α)
      (Q.center b) (smoothMixedCell F Q α b) (hm α b).1 (hsub α b)
  refine ⟨fun α b => ⟨(hi α b).1, (hi α b).2.1⟩, ?_, ?_⟩
  · intro α
    let c := ((F.domain α.1).chart (sectorCellChart F α)).map
    have hae : c '' sectorCellSet F α =ᵐ[volume]
        c '' (sectorCellSet F α ∩ (F.domain α.1).interior) := by
      apply ae_eq_set.mpr
      constructor
      · apply measure_mono_null (t := c '' ((F.domain α.1).boundary ∩ c.source))
        · rintro y ⟨⟨x, hx, rfl⟩, hn⟩
          refine ⟨x, ⟨?_, hcellsub α hx⟩, rfl⟩
          by_contra hb
          exact hn ⟨x, ⟨hx, hb⟩, rfl⟩
        · exact (own_sector_exclusions_separately_null F α.1 (sectorCellChart F α)).1
      · exact measure_mono_null (sdiff_subset_iff.mpr
          ((image_mono inter_subset_left).trans subset_union_left)) (measure_empty)
    change (∫ y in c '' sectorCellSet F α,
      sectorCoordinateDensity g (F.map ∘ F.parametrization α.1) (sectorCellChart F α) y) = _
    rw [setIntegral_congr_set hae, ← hu α, image_iUnion]
    apply integral_iUnion_fintype
    · intro b
      exact (hm α b).1.image_of_continuousOn_injOn
        (c.continuousOn.mono fun x hx => (hsub α b hx).1.1)
        (c.injOn.mono fun x hx => (hsub α b hx).1.1)
    · intro b d hbd
      change Disjoint (c '' smoothMixedCell F Q α b) (c '' smoothMixedCell F Q α d)
      rw [Set.disjoint_left]
      rintro y ⟨x, hx, hxy⟩ ⟨z, hz, hzy⟩
      have heq := c.injOn (hsub α b hx).1.1 (hsub α d hz).1.1 (hxy.trans hzy.symm)
      subst z
      exact Set.disjoint_left.mp (hd α hbd) hx hz
    · intro b
      exact (hi α b).1
  · intro b
    let c := extChartAt (𝓡∂ 2) (Q.center b)
    have hnull : volume (c '' (F.seam.carrier ∩ c.source) ∪
        c '' (Q.piece b ∩ S.boundary)) = 0 := by
      apply measure_union_null
      · exact smooth_source_actual_seam_chart_null f F h (Q.center b)
      · exact AreaAnalysis.extChart_boundary_image_null (Q.center b) (Q.piece b)
          (Q.subordinate b)
    have hae : c '' Q.piece b =ᵐ[volume]
        c '' (Q.piece b ∩ (F.seam.carrier ∪ S.boundary)ᶜ) := by
      apply ae_eq_set.mpr
      constructor
      · apply measure_mono_null (t := c '' (F.seam.carrier ∩ c.source) ∪
          c '' (Q.piece b ∩ S.boundary)) _ hnull
        rintro y ⟨⟨x, hx, rfl⟩, hn⟩
        have hbad : x ∈ F.seam.carrier ∪ S.boundary := by
          by_contra hb
          exact hn ⟨x, ⟨hx, hb⟩, rfl⟩
        rcases hbad with hs | hb
        · exact Or.inl ⟨x, ⟨hs, Q.subordinate b hx⟩, rfl⟩
        · exact Or.inr ⟨x, ⟨hx, hb⟩, rfl⟩
      · apply measure_mono_null (t := ∅) _ measure_empty
        exact sdiff_subset_iff.mpr ((image_mono inter_subset_left).trans subset_union_left)
    change (∫ y in c '' Q.piece b, coordinateAreaDensity g f.toFun (Q.center b) y) = _
    rw [setIntegral_congr_set hae, ← hui b, image_iUnion]
    apply integral_iUnion_fintype
    · intro α
      exact AreaAnalysis.extChart_image_measurable (Q.center b) _ (hm α b).2
        (by rintro _ ⟨x, hx, rfl⟩; exact Q.subordinate b hx.2.1)
    · intro α β hab
      change Disjoint (c '' smoothMixedImage F Q α b) (c '' smoothMixedImage F Q β b)
      rw [Set.disjoint_left]
      rintro y ⟨x, hx, hxy⟩ ⟨z, hz, hzy⟩
      have hxs : x ∈ c.source := by
        obtain ⟨q, hq, rfl⟩ := hx
        exact Q.subordinate b hq.2.1
      have hzs : z ∈ c.source := by
        obtain ⟨q, hq, rfl⟩ := hz
        exact Q.subordinate b hq.2.1
      have heq := c.injOn hxs hzs (hxy.trans hzy.symm)
      subst z
      exact Set.disjoint_left.mp (hdi b hab) hx hz
    · intro α
      exact (hi α b).2.1

theorem same_image_mixed_integrability_and_row_assembly {S R : CompactOrientedSurface.{u}}
    (g : SmoothMetric M) (F : GeometricPiecewiseSurface S M)
    (G : GeometricPiecewiseSurface R M) (a : R ≃ₜ S)
    (ha : ∀ x, F.map (a x) = G.map x) (hb : a ⁻¹' S.boundary = R.boundary) :
    (∀ α β,
      IntegrableOn (sectorCoordinateDensity g (G.map ∘ G.parametrization α.1) (sectorCellChart G α))
        (((G.domain α.1).chart (sectorCellChart G α)).map '' mixedSectorCell F G a α β) ∧
      IntegrableOn (sectorCoordinateDensity g (F.map ∘ F.parametrization β.1) (sectorCellChart F β))
        (((F.domain β.1).chart (sectorCellChart F β)).map '' mixedSectorCell G F a.symm β α)) ∧
    (∀ α, sectorCellIntegral g G α (sectorCellSet G α) =
      ∑ β : SectorCellIndex F, sectorCellIntegral g G α (mixedSectorCell F G a α β)) ∧
    (∀ β, sectorCellIntegral g F β (sectorCellSet F β) =
      ∑ α : SectorCellIndex G, sectorCellIntegral g F β (mixedSectorCell G F a.symm β α)) ∧
    (∀ α β, sectorCellIntegral g G α (mixedSectorCell F G a α β) =
      sectorCellIntegral g F β (mixedSectorCell G F a.symm β α)) := by
  classical
  letI : BorelSpace S := ⟨rfl⟩
  letI : BorelSpace R := ⟨rfl⟩
  letI : ∀ i, BorelSpace (F.domain i) := fun _ => ⟨rfl⟩
  letI : ∀ i, BorelSpace (G.domain i) := fun _ => ⟨rfl⟩
  letI : ∀ i, MetricSpace (F.domain i) := fun i =>
    TopologicalSpace.metrizableSpaceMetric (F.domain i)
  letI : ∀ i, MetricSpace (G.domain i) := fun i =>
    TopologicalSpace.metrizableSpaceMetric (G.domain i)
  have has : ∀ x, G.map (a.symm x) = F.map x := by
    intro x
    exact (ha (a.symm x)).symm.trans
      (congrArg (fun y => F.map y) (a.apply_symm_apply x))
  have hbs : a.symm ⁻¹' R.boundary = S.boundary := by
    ext x
    have hx := Set.ext_iff.mp hb (a.symm x)
    change a (a.symm x) ∈ S.boundary ↔ a.symm x ∈ R.boundary at hx
    rw [a.apply_symm_apply x] at hx
    exact hx.symm
  obtain ⟨hm, hd, hu, him⟩ := same_image_mixed_refinement_metadata F G a ha hb
  obtain ⟨hms, hds, hus, hims⟩ := same_image_mixed_refinement_metadata G F a.symm has hbs
  have hcellsub {D : CompactOrientedSurface.{u}} (K : GeometricPiecewiseSurface D M)
      (α : SectorCellIndex K) :
      sectorCellSet K α ⊆ ((K.domain α.1).chart (sectorCellChart K α)).map.source :=
    (canonicalSectorPartition (K.domain α.1)).subordinate α.2
  have hsub {D E : CompactOrientedSurface.{u}}
      (A : GeometricPiecewiseSurface D M) (B : GeometricPiecewiseSurface E M)
      (e : E ≃ₜ D) (α : SectorCellIndex B) (β : SectorCellIndex A) :
      ((B.domain α.1).chart (sectorCellChart B α)).map '' mixedSectorCell A B e α β ⊆
        sectorCrossDomain A B e α.1 (sectorCellChart B α) β.1 (sectorCellChart A β) := by
    rintro _ ⟨q, hq, rfl⟩
    let c := ((B.domain α.1).chart (sectorCellChart B α)).map
    have hqs := hcellsub B α hq.1.1
    refine ⟨?_, ?_⟩
    · rw [← AreaCertificates.sector_chart_piece_interior (B.domain α.1) (sectorCellChart B α)]
      exact ⟨q, ⟨hq.1.2, hqs⟩, rfl⟩
    · change B.parametrization α.1 (c.symm (c q)) ∈
        ((B.seam.carrier ∪ E.boundary)ᶜ ∩ e ⁻¹'
          ((A.parametrization β.1) '' ((A.domain β.1).interior ∩
            ((A.domain β.1).chart (sectorCellChart A β)).map.source)))
      rw [c.left_inv hqs]
      refine ⟨hq.2.1, ?_⟩
      obtain ⟨z, hz, hze⟩ := hq.2.2
      exact ⟨z, ⟨hz.2, hcellsub A β hz.1⟩, hze⟩
  have htransport (α : SectorCellIndex G) (β : SectorCellIndex F) :
      IntegrableOn (sectorCoordinateDensity g (G.map ∘ G.parametrization α.1) (sectorCellChart G α))
        (((G.domain α.1).chart (sectorCellChart G α)).map '' mixedSectorCell F G a α β) ∧
      IntegrableOn (sectorCoordinateDensity g (F.map ∘ F.parametrization β.1) (sectorCellChart F β))
        (((F.domain β.1).chart (sectorCellChart F β)).map '' mixedSectorCell G F a.symm β α) ∧
      sectorCellIntegral g G α (mixedSectorCell F G a α β) =
        sectorCellIntegral g F β (mixedSectorCell G F a.symm β α) := by
    obtain ⟨T⟩ := sector_same_image_transition_exists F G a ha hb
      α.1 (sectorCellChart G α) β.1 (sectorCellChart F β)
    let cG := ((G.domain α.1).chart (sectorCellChart G α)).map
    let cF := ((F.domain β.1).chart (sectorCellChart F β)).map
    let s := cG '' mixedSectorCell F G a α β
    have hs : MeasurableSet s := (hm α β).image_of_continuousOn_injOn
      (cG.continuousOn.mono fun q hq => hcellsub G α hq.1.1)
      (cG.injOn.mono fun q hq => hcellsub G α hq.1.1)
    have hsT : s ⊆ T.coordinate.source := by
      rw [T.source_eq]
      exact hsub F G a α β
    have himage : T.coordinate '' s = cF '' mixedSectorCell G F a.symm β α := by
      apply Set.Subset.antisymm
      · rintro y ⟨_, ⟨q, hq, rfl⟩, rfl⟩
        have hy := hsT ⟨q, hq, rfl⟩
        have hyt := T.coordinate.map_source hy
        rw [T.target_eq] at hyt
        have hcf : T.coordinate (cG q) ∈ cF.target := interior_subset hyt.1
        have hp := T.parametrization_matches (cG q) hy
        change F.parametrization β.1 (cF.symm (T.coordinate (cG q))) =
          a (G.parametrization α.1 (cG.symm (cG q))) at hp
        rw [cG.left_inv (hcellsub G α hq.1.1)] at hp
        have hmem : a (G.parametrization α.1 q) ∈
            (F.parametrization β.1) '' mixedSectorCell G F a.symm β α := by
          rw [← him α β]
          exact ⟨G.parametrization α.1 q, ⟨q, hq, rfl⟩, rfl⟩
        obtain ⟨z, hz, hze⟩ := hmem
        have hzeq := (F.parametrization_embedding β.1).injective (hze.trans hp.symm)
        refine ⟨z, hz, ?_⟩
        rw [hzeq, cF.right_inv hcf]
      · rintro y ⟨z, hz, rfl⟩
        have hycross := hsub G F a.symm β α ⟨z, hz, rfl⟩
        have hyt : cF z ∈ T.coordinate.target := by rw [T.target_eq]; exact hycross
        have hy := T.coordinate.map_target hyt
        have hyg : T.coordinate.symm (cF z) ∈ cG.target := by
          rw [T.source_eq] at hy
          exact interior_subset hy.1
        have hp := T.parametrization_matches (T.coordinate.symm (cF z)) hy
        rw [T.coordinate.right_inv hyt] at hp
        change F.parametrization β.1 (cF.symm (cF z)) =
          a (G.parametrization α.1 (cG.symm (T.coordinate.symm (cF z)))) at hp
        rw [cF.left_inv (hcellsub F β hz.1.1)] at hp
        have hmem : F.parametrization β.1 z ∈
            a '' ((G.parametrization α.1) '' mixedSectorCell F G a α β) := by
          rw [him α β]
          exact ⟨z, hz, rfl⟩
        obtain ⟨x, ⟨q, hq, rfl⟩, hqe⟩ := hmem
        have hqe' := a.injective (hqe.trans hp)
        have hqeq := (G.parametrization_embedding α.1).injective hqe'
        refine ⟨T.coordinate.symm (cF z), ?_, T.coordinate.right_inv hyt⟩
        refine ⟨q, hq, ?_⟩
        rw [hqeq, cG.right_inv hyg]
    obtain ⟨_, hiG, hiF, hei⟩ := sector_same_image_density_integral_transport g F G a ha hb
      α.1 (sectorCellChart G α) β.1 (sectorCellChart F β) T s hs hsT
    rw [himage] at hiF hei
    exact ⟨hiG, hiF, hei⟩
  have hrow {D E : CompactOrientedSurface.{u}}
      (A : GeometricPiecewiseSurface D M) (B : GeometricPiecewiseSurface E M)
      (e : E ≃ₜ D) (he : ∀ x, A.map (e x) = B.map x)
      (hbe : e ⁻¹' D.boundary = E.boundary)
      (hm : ∀ α β, MeasurableSet (mixedSectorCell A B e α β))
      (hd : ∀ α, Pairwise (fun β γ => Disjoint (mixedSectorCell A B e α β)
        (mixedSectorCell A B e α γ)))
      (hu : ∀ α, (⋃ β, mixedSectorCell A B e α β) =
        sectorCellSet B α ∩ (B.domain α.1).interior ∩
          (B.parametrization α.1) ⁻¹' (e ⁻¹' A.seam.carrierᶜ))
      (hi : ∀ α β, IntegrableOn
        (sectorCoordinateDensity g (B.map ∘ B.parametrization α.1) (sectorCellChart B α))
        (((B.domain α.1).chart (sectorCellChart B α)).map '' mixedSectorCell A B e α β))
      (α : SectorCellIndex B) :
      sectorCellIntegral g B α (sectorCellSet B α) =
        ∑ β : SectorCellIndex A, sectorCellIntegral g B α (mixedSectorCell A B e α β) := by
    letI : BorelSpace E := ⟨rfl⟩
    letI : ∀ i, BorelSpace (B.domain i) := fun _ => ⟨rfl⟩
    letI : ∀ i, MetricSpace (B.domain i) := fun i =>
      TopologicalSpace.metrizableSpaceMetric (B.domain i)
    let c := ((B.domain α.1).chart (sectorCellChart B α)).map
    let t := sectorCellSet B α ∩ (B.domain α.1).interior ∩
      (B.parametrization α.1) ⁻¹' (e ⁻¹' A.seam.carrierᶜ)
    have hn : volume (c '' ((B.domain α.1).boundary ∩ c.source) ∪
        c '' ((B.domain α.1).interior ∩
          (B.parametrization α.1) ⁻¹' (e ⁻¹' A.seam.carrier) ∩ c.source)) = 0 :=
      measure_union_null (own_sector_exclusions_separately_null B α.1 (sectorCellChart B α)).1
        (opposite_seam_sector_chart_null A B e he hbe α.1 (sectorCellChart B α))
    have hae : c '' sectorCellSet B α =ᵐ[volume] c '' t := by
      apply ae_eq_set.mpr
      constructor
      · apply measure_mono_null (t := c '' ((B.domain α.1).boundary ∩ c.source) ∪
          c '' ((B.domain α.1).interior ∩
            (B.parametrization α.1) ⁻¹' (e ⁻¹' A.seam.carrier) ∩ c.source)) _ hn
        rintro y ⟨⟨q, hq, rfl⟩, hnt⟩
        by_cases hint : q ∈ (B.domain α.1).interior
        · apply Or.inr
          refine ⟨q, ⟨⟨hint, ?_⟩, hcellsub B α hq⟩, rfl⟩
          by_contra hbad
          exact hnt ⟨q, ⟨⟨hq, hint⟩, hbad⟩, rfl⟩
        · exact Or.inl ⟨q, ⟨Classical.not_not.mp hint, hcellsub B α hq⟩, rfl⟩
      · apply measure_mono_null (t := ∅) _ measure_empty
        apply sdiff_subset_iff.mpr
        exact (image_mono (fun q hq => hq.1.1)).trans subset_union_left
    change (∫ y in c '' sectorCellSet B α,
      sectorCoordinateDensity g (B.map ∘ B.parametrization α.1) (sectorCellChart B α) y) = _
    rw [setIntegral_congr_set hae]
    change (∫ y in c '' (sectorCellSet B α ∩ (B.domain α.1).interior ∩
      (B.parametrization α.1) ⁻¹' (e ⁻¹' A.seam.carrierᶜ)), _) = _
    rw [← hu α, image_iUnion]
    apply integral_iUnion_fintype
    · intro β
      exact (hm α β).image_of_continuousOn_injOn
        (c.continuousOn.mono fun q hq => hcellsub B α hq.1.1)
        (c.injOn.mono fun q hq => hcellsub B α hq.1.1)
    · intro β γ hbg
      change Disjoint (c '' mixedSectorCell A B e α β) (c '' mixedSectorCell A B e α γ)
      rw [Set.disjoint_left]
      rintro y ⟨q, hq, hqy⟩ ⟨z, hz, hzy⟩
      have heq := c.injOn (hcellsub B α hq.1.1) (hcellsub B α hz.1.1) (hqy.trans hzy.symm)
      subst z
      exact Set.disjoint_left.mp (hd α hbg) hq hz
    · exact hi α
  exact ⟨fun α β => ⟨(htransport α β).1, (htransport α β).2.1⟩,
    hrow F G a ha hb hm hd hu (fun α β => (htransport α β).1),
    hrow G F a.symm has hbs hms hds hus (fun β α => (htransport α β).2.1),
    fun α β => (htransport α β).2.2⟩


end
end SeifertSurfaces.MetricFoundations.B1Bridges
