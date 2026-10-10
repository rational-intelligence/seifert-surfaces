import OriginalB1
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import AreaSmoothCurveNullitySupport
open scoped Manifold ContDiff ENNReal
open Set Topology MeasureTheory
namespace SeifertSurfaces.MetricFoundations.B1Bridges
open SeifertSurfaces.Foundations
universe u v
noncomputable section
set_option autoImplicit false
variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]

def actualSeamEndpoints {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) : Set S :=
  ⋃ k, {F.seam.arc k 0, F.seam.arc k 1}

theorem opposite_seam_sector_chart_null {S R : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (G : GeometricPiecewiseSurface R M)
    (a : R ≃ₜ S) (ha : ∀ x, F.map (a x) = G.map x)
    (hb : a ⁻¹' S.boundary = R.boundary)
    (i : Fin G.pieceCount) (j : Fin (G.domain i).count) :
    volume (((G.domain i).chart j).map ''
      ((G.domain i).interior ∩ (G.parametrization i) ⁻¹' (a ⁻¹' F.seam.carrier) ∩
        ((G.domain i).chart j).map.source)) = 0 := by
  let C (A : Set S) : Set (Euc 2) := AreaCertificates.oppositePieceCoordinates G a A i j
  have hunion (A B : Set S) : C (A ∪ B) = C A ∪ C B := by
    ext y
    simp only [C, AreaCertificates.oppositePieceCoordinates,
      AreaCertificates.oppositePieceSourceSet, mem_image, mem_inter_iff,
      mem_preimage, mem_union]
    aesop
  have hiunion {α : Type} (A : α → Set S) : C (⋃ k, A k) = ⋃ k, C (A k) := by
    ext y
    simp only [C, AreaCertificates.oppositePieceCoordinates,
      AreaCertificates.oppositePieceSourceSet, mem_image, mem_inter_iff,
      mem_preimage, mem_iUnion]
    aesop
  change volume (C F.seam.carrier) = 0
  rw [SeamGraph.carrier, hunion, hiunion, hiunion]
  apply measure_union_null
  · apply measure_iUnion_null
    intro k
    simpa only [C, image_univ] using
      (AreaCertificates.opposite_ambient_smooth_arc_coordinate_nullity F G a
        (fun x => (ha x).symm) (F.seam.arc k) (F.seam.arc_smooth_image k)
        univ isOpen_univ i j).1
  · apply measure_iUnion_null
    intro k
    simpa only [C, image_univ] using
      (AreaCertificates.opposite_ambient_smooth_circle_coordinate_nullity F G a
        (fun x => (ha x).symm) (F.seam.circle k) (F.seam.circle_smooth_image k)
        univ isOpen_univ i j).1

theorem opposite_seam_inverse_sector_chart_null {S R : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (G : GeometricPiecewiseSurface R M)
    (a : R ≃ₜ S) (ha : ∀ x, F.map (a x) = G.map x)
    (hb : a ⁻¹' S.boundary = R.boundary)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count) :
    volume (((F.domain i).chart j).map ''
      ((F.domain i).interior ∩ (F.parametrization i) ⁻¹' (a.symm ⁻¹' G.seam.carrier) ∩
        ((F.domain i).chart j).map.source)) = 0 := by
  apply opposite_seam_sector_chart_null G F a.symm
  · intro x
    simpa only [Homeomorph.apply_symm_apply] using (ha (a.symm x)).symm
  · ext x
    have hx := Set.ext_iff.mp hb (a.symm x)
    simpa only [mem_preimage, Homeomorph.apply_symm_apply] using hx.symm

theorem smooth_source_actual_seam_chart_null {S : CompactOrientedSurface.{u}}
    (f : ProperSmoothEmbedding S M) (F : GeometricPiecewiseSurface S M)
    (h : F.map = f.continuousMap) (p : S) :
    volume ((extChartAt (𝓡∂ 2) p) ''
      (F.seam.carrier ∩ (extChartAt (𝓡∂ 2) p).source)) = 0 := by
  have hreflect {E' H' K : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E']
      [TopologicalSpace H'] [TopologicalSpace K] [ChartedSpace H' K]
      (I : ModelWithCorners ℝ E' H') (σ : C(K,S)) (t : K)
      (ht : σ t ∉ S.boundary)
      (hs : ContMDiffAt I (𝓡∂ 3) ∞ (f.toFun ∘ σ) t) :
      ContMDiffAt I (𝓡∂ 2) ∞ σ t := by
    let x := σ t
    obtain ⟨L⟩ := AreaAnalysis.properEmbedding_interior_chart_leftInverse f x ht
    let U : Set K := σ ⁻¹' ((extChartAt (𝓡∂ 2) x).source ∩
      (extChartAt (𝓡∂ 2) x) ⁻¹' L.inverse.source)
    have hU : IsOpen U :=
      (isOpen_extChartAt_preimage' x L.inverse.open_source).preimage σ.continuous
    have htU : t ∈ U := ⟨mem_extChartAt_source x,L.inverse.source_mem⟩
    have heq (z : K) (hz : z ∈ U) :
        extChartAt (𝓡∂ 2) x (σ z) =
          L.inverse.map (extChartAt (𝓡∂ 3) (f.toFun x) (f.toFun (σ z))) := by
      have hi : AreaAnalysis.embeddingCoordinateMap f x
          (extChartAt (𝓡∂ 2) x (σ z)) =
          extChartAt (𝓡∂ 3) (f.toFun x) (f.toFun (σ z)) := by
        simp only [AreaAnalysis.embeddingCoordinateMap, Function.comp_apply,
          (extChartAt (𝓡∂ 2) x).left_inv hz.1]
      rw [← hi]
      exact (L.inverse.left_inverse _ hz.2).symm
    have htar : extChartAt (𝓡∂ 3) (f.toFun x) (f.toFun (σ t)) ∈ L.inverse.target := by
      have hx := L.inverse.target_mem
      simpa only [AreaAnalysis.embeddingCoordinateMap, Function.comp_apply,
        (extChartAt (𝓡∂ 2) x).left_inv (mem_extChartAt_source x)] using hx
    have hl : ContMDiffAt 𝓘(ℝ,Euc 3) 𝓘(ℝ,Euc 2) ∞ L.inverse.map
        (extChartAt (𝓡∂ 3) (f.toFun x) (f.toFun (σ t))) :=
      (L.inverse.smooth.contDiffAt (L.inverse.open_target.mem_nhds htar)).contMDiffAt
    have hc := hl.comp t (contMDiffAt_extChartAt.comp t hs)
    apply contMDiffAt_iff_target.mpr
    refine ⟨σ.continuous.continuousAt,hc.congr_of_eventuallyEq ?_⟩
    filter_upwards [hU.mem_nhds htU] with z hz
    exact heq z hz
  have hboundary : IsClosed S.boundary :=
    (𝓡∂ 2).isClosed_boundary (M := S) (n := ∞) (by simp)
  let c := extChartAt (𝓡∂ 2) p
  have harc (k : Fin F.seam.arcCount) :
      volume (c '' (range (F.seam.arc k) ∩ c.source)) = 0 := by
    let σ := F.seam.arc k
    let A : Set Time := σ ⁻¹' (c.source ∩ S.boundaryᶜ)
    have hA : IsOpen A := ((isOpen_extChartAt_source p).inter hboundary.isOpen_compl).preimage
      σ.continuous
    have hs : ContMDiffOn (𝓡∂ 1) 𝓘(ℝ,Euc 2) ∞ (c ∘ σ) A := by
      intro t ht
      have hamb : ContMDiffAt (𝓡∂ 1) (𝓡∂ 3) ∞ (f.toFun ∘ σ) t := by
        have hh := F.seam.arc_smooth_image k
        change ContMDiff (𝓡∂ 1) (𝓡∂ 3) ∞ (F.map ∘ σ) at hh
        have he : (F.map ∘ σ) = f.toFun ∘ σ := by
          funext z
          exact congrArg (fun q : C(S,M) => q (σ z)) h
        rw [he] at hh
        exact hh.contMDiffAt
      have hchart : ContMDiffAt (𝓡∂ 2) 𝓘(ℝ,Euc 2) ∞ c (σ t) := by
        apply contMDiffAt_extChartAt'
        simpa only [c, extChartAt_source] using ht.1
      exact hchart.comp t
        (hreflect (𝓡∂ 1) σ t ht.2 hamb) |>.contMDiffWithinAt
    obtain ⟨C⟩ := AreaCertificates.smooth_time_coordinate_image_curve_cover (c ∘ σ) A hA hs
    have hnull := AreaCertificates.countable_lipschitz_curve_cover_volume_zero C
    apply measure_mono_null (t := (c ∘ σ) '' A ∪ {c (σ 0),c (σ 1)})
    · rintro y ⟨x,⟨⟨t,rfl⟩,hxs⟩,rfl⟩
      by_cases ht : σ t ∈ S.boundary
      · have hend := F.seam.arc_boundary k ht
        rcases hend with ht | ht
        · exact Or.inr (Or.inl (congrArg (fun t => c (σ t)) ht))
        · exact Or.inr (Or.inr (congrArg (fun t => c (σ t)) ht))
      · exact Or.inl ⟨t,⟨hxs,ht⟩,rfl⟩
    · exact measure_union_null hnull ((Set.toFinite {c (σ 0),c (σ 1)}).measure_zero volume)
  have hcircle (k : Fin F.seam.circleCount) :
      volume (c '' (range (F.seam.circle k) ∩ c.source)) = 0 := by
    let σ := F.seam.circle k
    let A : Set Circle := σ ⁻¹' c.source
    have hA : IsOpen A := (isOpen_extChartAt_source p).preimage σ.continuous
    have hs : ContMDiffOn (𝓡 1) 𝓘(ℝ,Euc 2) ∞ (c ∘ σ) A := by
      intro t ht
      have htb : σ t ∉ S.boundary := by
        intro htb
        exact Set.disjoint_left.mp (F.seam.circle_off_boundary k) ⟨t,rfl⟩ htb
      have hamb : ContMDiffAt (𝓡 1) (𝓡∂ 3) ∞ (f.toFun ∘ σ) t := by
        have hh := F.seam.circle_smooth_image k
        change ContMDiff (𝓡 1) (𝓡∂ 3) ∞ (F.map ∘ σ) at hh
        have he : (F.map ∘ σ) = f.toFun ∘ σ := by
          funext z
          exact congrArg (fun q : C(S,M) => q (σ z)) h
        rw [he] at hh
        exact hh.contMDiffAt
      have hchart : ContMDiffAt (𝓡∂ 2) 𝓘(ℝ,Euc 2) ∞ c (σ t) := by
        apply contMDiffAt_extChartAt'
        simpa only [A, mem_preimage, c, extChartAt_source] using ht
      exact hchart.comp t
        (hreflect (𝓡 1) σ t htb hamb) |>.contMDiffWithinAt
    obtain ⟨C⟩ := AreaCertificates.smooth_circle_coordinate_image_curve_cover (c ∘ σ) A hA hs
    have heq : c '' (range σ ∩ c.source) = (c ∘ σ) '' A := by
      ext y
      simp only [A, mem_image, mem_inter_iff, mem_range, mem_preimage, Function.comp_apply]
      aesop
    rw [heq]
    exact AreaCertificates.countable_lipschitz_curve_cover_volume_zero C
  change volume (c '' (F.seam.carrier ∩ c.source)) = 0
  rw [SeamGraph.carrier, union_inter_distrib_right, image_union,
    iUnion_inter, iUnion_inter, image_iUnion, image_iUnion]
  exact measure_union_null (measure_iUnion_null harc) (measure_iUnion_null hcircle)

theorem own_sector_exclusions_separately_null {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (i : Fin F.pieceCount)
    (j : Fin (F.domain i).count) :
    volume (((F.domain i).chart j).map ''
      ((F.domain i).boundary ∩ ((F.domain i).chart j).map.source)) = 0 ∧
    volume (((F.domain i).chart j).map ''
      ((F.parametrization i) ⁻¹' F.seam.carrier ∩ ((F.domain i).chart j).map.source)) = 0 ∧
    volume (((F.domain i).chart j).map ''
      ((F.parametrization i) ⁻¹' S.boundary ∩ ((F.domain i).chart j).map.source)) = 0 ∧
    volume (((F.domain i).chart j).map ''
      ((F.parametrization i) ⁻¹' actualSeamEndpoints F ∩
        ((F.domain i).chart j).map.source)) = 0 := by
  have hspan (t : ℝ) :
      volume (↑(Submodule.span ℝ {sectorUnit t}) : Set (Euc 2)) = 0 := by
    apply Measure.addHaar_submodule volume
    intro htop
    have hn : sectorUnit t ≠ 0 := by
      intro hz
      have hsq : ‖sectorUnit t‖ ^ 2 = 1 := by
        rw [EuclideanSpace.real_norm_sq_eq]
        simpa [sectorUnit, Fin.sum_univ_two, add_comm] using Real.sin_sq_add_cos_sq t
      rw [hz, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hsq
      exact zero_ne_one hsq
    have hr := finrank_span_singleton (K := ℝ) hn
    rw [htop, finrank_top] at hr
    norm_num [finrank_euclideanSpace] at hr
  have hsector (θ : ℝ) : volume (sectorBoundary θ) = 0 := by
    apply measure_mono_null (t :=
      (↑(Submodule.span ℝ {sectorUnit 0}) : Set (Euc 2)) ∪
        ↑(Submodule.span ℝ {sectorUnit θ}))
    · rintro x ⟨r,hr,hx | hx⟩
      · exact Or.inl (Submodule.mem_span_singleton.mpr ⟨r,hx.symm⟩)
      · exact Or.inr (Submodule.mem_span_singleton.mpr ⟨r,hx.symm⟩)
    · exact measure_union_null (hspan 0) (hspan θ)
  have hmodel (A : SectorModel) : volume A.boundary = 0 := by
    unfold SectorModel.boundary
    cases h : A.interiorChart
    · simpa [h] using measure_mono_null inter_subset_right (hsector A.angle)
    · simp [h]
  have hboundary : volume (((F.domain i).chart j).map ''
      ((F.domain i).boundary ∩ ((F.domain i).chart j).map.source)) = 0 := by
    rw [(F.domain i).boundary_charts j]
    exact hmodel _
  have hpre : (F.parametrization i) ⁻¹' (F.seam.carrier ∪ S.boundary) ⊆
      (F.domain i).boundary := by
    intro q hq
    by_contra hq'
    obtain ⟨x,hx,himage⟩ := F.piece_interior_component i
    have hin : F.parametrization i q ∈ connectedComponentIn
        (F.seam.carrier ∪ S.boundary)ᶜ x := himage ▸ ⟨q,hq',rfl⟩
    exact (connectedComponentIn_subset _ _ hin) hq
  have hnull (A : Set S) (hA : A ⊆ F.seam.carrier ∪ S.boundary) :
      volume (((F.domain i).chart j).map ''
        ((F.parametrization i) ⁻¹' A ∩ ((F.domain i).chart j).map.source)) = 0 := by
    apply measure_mono_null _ hboundary
    apply image_mono
    intro q hq
    exact ⟨hpre (hA hq.1),hq.2⟩
  refine ⟨hboundary,hnull _ subset_union_left,hnull _ subset_union_right,hnull _ ?_⟩
  intro q hq
  obtain ⟨k,hk⟩ := mem_iUnion.mp hq
  apply Or.inl
  apply Or.inl
  apply mem_iUnion.mpr
  refine ⟨k,?_⟩
  rcases hk with hq | hq
  · exact ⟨0,hq.symm⟩
  · exact ⟨1,hq.symm⟩
end
end SeifertSurfaces.MetricFoundations.B1Bridges
