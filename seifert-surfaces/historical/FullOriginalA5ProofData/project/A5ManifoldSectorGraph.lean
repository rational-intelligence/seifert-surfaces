import A5SectorLocalInverse
import OriginalA3
import GeometricCategory

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates

/-- Pass the literal C1/rank native sector data into actual ambient chart
coordinates, shrinking only the radius. -/
theorem manifold_sector_coordinates_C1_rank
    {N : Type*} [TopologicalSpace N] [ChartedSpace (Euc 3) N]
    [IsManifold 𝓘(ℝ, Euc 3) ∞ N]
    (θ R : ℝ) (hθ : 0 < θ) (hθπ : θ < 2 * Real.pi) (hR : 0 < R)
    (F : Euc 2 → N) (c : SmoothAmbientChart N) (hc : F 0 ∈ c.chart.source)
    (hF : ContMDiffOn 𝓘(ℝ, Euc 2) 𝓘(ℝ, Euc 3) 1 F
      (Metric.ball 0 R ∩ planarSector θ))
    (hrank : Function.Injective (mfderivWithin 𝓘(ℝ, Euc 2) 𝓘(ℝ, Euc 3) F
      (Metric.ball 0 R ∩ planarSector θ) 0)) :
    ∃ r : ℝ, 0 < r ∧ r ≤ R ∧
      MapsTo F (Metric.ball 0 r ∩ planarSector θ) c.chart.source ∧
      ContDiffOn ℝ 1 (c.chart ∘ F) (Metric.ball 0 r ∩ planarSector θ) ∧
      Function.Injective (fderivWithin ℝ (c.chart ∘ F)
        (Metric.ball 0 r ∩ planarSector θ) 0) := by
  let S := Metric.ball (0 : Euc 2) R ∩ planarSector θ
  have hz : (0 : Euc 2) ∈ S := ⟨Metric.mem_ball_self hR,
    0, le_rfl, 0, ⟨le_rfl, hθ.le⟩, by simp⟩
  have hnear : F ⁻¹' c.chart.source ∈ 𝓝[S] (0 : Euc 2) :=
    (hF.continuousOn 0 hz) (c.chart.open_source.mem_nhds hc)
  obtain ⟨δ, hδ, hδF⟩ := Metric.mem_nhdsWithin_iff.mp hnear
  let r := min δ R
  have hr : 0 < r := lt_min hδ hR
  have hrR : r ≤ R := min_le_right _ _
  let T := Metric.ball (0 : Euc 2) r ∩ planarSector θ
  have hTS : T ⊆ S := fun _ hx => ⟨Metric.ball_subset_ball hrR hx.1, hx.2⟩
  have hmaps : MapsTo F T c.chart.source := fun _ hx =>
    hδF ⟨Metric.ball_subset_ball (min_le_left δ R) hx.1, hTS hx⟩
  have hT : UniqueDiffOn ℝ T := by
    simpa only [T, inter_comm] using (planarSector_uniqueDiffOn hθ hθπ).inter
      (Metric.isOpen_ball (x := (0 : Euc 2)) (ε := r))
  have hzt : (0 : Euc 2) ∈ T := ⟨Metric.mem_ball_self hr, hz.2⟩
  have hFT := hF.mono hTS
  have hcF : ContDiffOn ℝ 1 (c.chart ∘ F) T :=
    ((c.smooth.of_le (by simp)).comp hFT hmaps).contDiffOn
  have hderiv_eq : mfderivWithin 𝓘(ℝ, Euc 2) 𝓘(ℝ, Euc 3) F T 0 =
      mfderivWithin 𝓘(ℝ, Euc 2) 𝓘(ℝ, Euc 3) F S 0 := by
    exact mfderivWithin_subset hTS (hT 0 hzt).uniqueMDiffWithinAt
      ((hF 0 hz).mdifferentiableWithinAt (by norm_num))
  have hcDiff : c.chart.MDifferentiable 𝓘(ℝ, Euc 3) 𝓘(ℝ, Euc 3) :=
    ⟨c.smooth.mdifferentiableOn (by simp), c.inverse_smooth.mdifferentiableOn (by simp)⟩
  have hcinj := hcDiff.mfderiv_injective hc
  have hcomp := mfderiv_comp_mfderivWithin (I := 𝓘(ℝ, Euc 2))
    (I' := 𝓘(ℝ, Euc 3)) (I'' := 𝓘(ℝ, Euc 3)) 0
    (((c.smooth _ hc).contMDiffAt (c.chart.open_source.mem_nhds hc)).mdifferentiableAt (by simp))
    ((hFT 0 hzt).mdifferentiableWithinAt (by norm_num)) (hT 0 hzt).uniqueMDiffWithinAt
  have hm : Function.Injective (mfderivWithin 𝓘(ℝ, Euc 2) 𝓘(ℝ, Euc 3) (c.chart ∘ F) T 0) := by
    rw [hcomp, hderiv_eq]
    exact hcinj.comp hrank
  refine ⟨r, hr, hrR, hmaps, hcF, ?_⟩
  rw [mfderivWithin_eq_fderivWithin] at hm
  intro v w hvw
  have he := hm (a₁ := (NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : Euc 2)).symm v)
    (a₂ := (NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : Euc 2)).symm w) (by simpa using hvw)
  exact (NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : Euc 2)).symm.injective he

/-- An actual manifold-valued native sector of rank two is a C1 graph over
its actual projected region in any ambient chart containing the vertex. -/
theorem manifold_sector_graph
    {N : Type*} [TopologicalSpace N] [ChartedSpace (Euc 3) N]
    [IsManifold 𝓘(ℝ, Euc 3) ∞ N]
    (θ R : ℝ) (hθ : 0 < θ) (hθπ : θ < 2 * Real.pi) (hR : 0 < R)
    (F : Euc 2 → N) (c : SmoothAmbientChart N) (hc : F 0 ∈ c.chart.source)
    (hF : ContMDiffOn 𝓘(ℝ, Euc 2) 𝓘(ℝ, Euc 3) 1 F
      (Metric.ball 0 R ∩ planarSector θ))
    (hrank : Function.Injective (mfderivWithin 𝓘(ℝ, Euc 2) 𝓘(ℝ, Euc 3) F
      (Metric.ball 0 R ∩ planarSector θ) 0)) :
    ∃ r : ℝ, 0 < r ∧ r ≤ R ∧ ∃ P : Euc 3 →L[ℝ] Euc 2,
      ∃ H : Euc 2 ≃ₜ Euc 2,
        EqOn (P ∘ c.chart ∘ F) H (Metric.ball 0 r ∩ planarSector θ) ∧
        UniqueDiffOn ℝ ((P ∘ c.chart ∘ F) '' (Metric.ball 0 r ∩ planarSector θ)) ∧
        ContMDiffOn 𝓘(ℝ, Euc 2) 𝓘(ℝ, Euc 3) 1
          (c.chart.symm ∘ c.chart ∘ F ∘ H.symm)
          ((P ∘ c.chart ∘ F) '' (Metric.ball 0 r ∩ planarSector θ)) ∧
        (c.chart.symm ∘ c.chart ∘ F ∘ H.symm) ''
          ((P ∘ c.chart ∘ F) '' (Metric.ball 0 r ∩ planarSector θ)) =
          F '' (Metric.ball 0 r ∩ planarSector θ) := by
  obtain ⟨R', hR', hR'R, hmaps, hcoord, hcoordrank⟩ :=
    manifold_sector_coordinates_C1_rank θ R hθ hθπ hR F c hc hF hrank
  obtain ⟨P, _, r, hr, hrR', H, hH, hunique, hgraph, _, hexact⟩ :=
    C1_sector_rank_projection θ R' hθ hθπ hR' (c.chart ∘ F) hcoord hcoordrank
  let T := Metric.ball (0 : Euc 2) r ∩ planarSector θ
  have hT (x : Euc 2) (hx : x ∈ T) : F x ∈ c.chart.source :=
    hmaps ⟨Metric.ball_subset_ball hrR' hx.1, hx.2⟩
  have htarget : MapsTo (c.chart ∘ F ∘ H.symm) ((P ∘ c.chart ∘ F) '' T) c.chart.target := by
    rintro y ⟨x, hx, rfl⟩
    have he : (P ∘ c.chart ∘ F) x = H x := hH hx
    change c.chart (F (H.symm ((P ∘ c.chart ∘ F) x))) ∈ c.chart.target
    rw [he, H.symm_apply_apply]
    exact c.chart.map_source (hT x hx)
  refine ⟨r, hr, hrR'.trans hR'R, P, H, hH, hunique, ?_, ?_⟩
  · exact (c.inverse_smooth.of_le (by simp)).comp hgraph.contMDiffOn htarget
  · calc
      (c.chart.symm ∘ c.chart ∘ F ∘ H.symm) '' ((P ∘ c.chart ∘ F) '' T) =
          c.chart.symm '' ((c.chart ∘ F ∘ H.symm) '' ((P ∘ c.chart ∘ F) '' T)) := image_comp _ _ _
      _ = c.chart.symm '' ((c.chart ∘ F) '' T) := by
        exact congrArg (fun A : Set (Euc 3) => c.chart.symm '' A) hexact
      _ = F '' T := by
        rw [← image_comp]
        exact image_congr fun x hx => c.chart.left_inv (hT x hx)

/-- The original whole-piece hypotheses supply C1 regularity and rank in the
two-sided sphere directly. No A2 conclusion or smooth source parametrization
is used in this coordinate adapter. -/
theorem native_piece_sphere_C1_rank
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count) :
    ContMDiffOn 𝓘(ℝ, Euc 2) (𝓡 3) 1
      (E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j)
      ((F.domain i).chart j).map.target ∧
    ∀ y ∈ ((F.domain i).chart j).map.target,
      Function.Injective (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡 3)
        (E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j)
        ((F.domain i).chart j).map.target y) := by
  let _ : ChartedSpace (EuclideanHalfSpace 3) T.Carrier := E.charted
  let _ : IsManifold (𝓡∂ 3) ∞ T.Carrier := E.smooth
  have he : ContMDiff (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion.contMDiff
  refine ⟨(he.of_le (by simp)).comp_contMDiffOn (F.piece_c1 i j), ?_⟩
  intro y hy
  have huniq : UniqueDiffOn ℝ ((F.domain i).chart j).map.target := by
    rw [((F.domain i).chart j).target_eq]
    exact ((F.domain i).chart j).model.uniqueDiffOn_domain
  rw [mfderiv_comp_mfderivWithin y (he.mdifferentiableAt (by simp))
    ((F.piece_c1 i j y hy).mdifferentiableWithinAt (by norm_num))
    (huniq y hy).uniqueMDiffWithinAt]
  exact (E.inclusion.isImmersion.mfderiv_injective (by simp) _).comp
    (F.piece_differential_injective i j y hy)

/-- Exact native whole-piece vertex graph, with no added regularity or
projection data. All graph coordinates and their C1 property are output. -/
theorem native_piece_vertex_graph
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count)
    (hsector : ((F.domain i).chart j).model.interiorChart = false)
    (c : SmoothAmbientChart ThreeSphere)
    (hc : E.toSphere (sectorCoordinateMap (F.map ∘ F.parametrization i) j 0) ∈ c.chart.source) :
    let A := ((F.domain i).chart j).model
    let g := E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j
    ∃ r : ℝ, 0 < r ∧ r ≤ A.radius ∧ ∃ P : Euc 3 →L[ℝ] Euc 2,
      ∃ H : Euc 2 ≃ₜ Euc 2,
        EqOn (P ∘ c.chart ∘ g) H (Metric.ball 0 r ∩ planarSector A.angle) ∧
        UniqueDiffOn ℝ ((P ∘ c.chart ∘ g) '' (Metric.ball 0 r ∩ planarSector A.angle)) ∧
        ContMDiffOn 𝓘(ℝ, Euc 2) (𝓡 3) 1
          (c.chart.symm ∘ c.chart ∘ g ∘ H.symm)
          ((P ∘ c.chart ∘ g) '' (Metric.ball 0 r ∩ planarSector A.angle)) ∧
        (c.chart.symm ∘ c.chart ∘ g ∘ H.symm) ''
          ((P ∘ c.chart ∘ g) '' (Metric.ball 0 r ∩ planarSector A.angle)) =
          g '' (Metric.ball 0 r ∩ planarSector A.angle) := by
  dsimp only
  let A := ((F.domain i).chart j).model
  let g := E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j
  have hdomain : ((F.domain i).chart j).map.target =
      Metric.ball (0 : Euc 2) A.radius ∩ planarSector A.angle := by
    rw [((F.domain i).chart j).target_eq]
    simp only [SectorModel.domain, hsector, Bool.false_eq_true, ↓reduceIte, A]
  obtain ⟨hC, hR⟩ := native_piece_sphere_C1_rank E F i j
  rw [hdomain] at hC hR
  exact manifold_sector_graph A.angle A.radius A.angle_positive A.angle_lt_two_pi
    A.radius_positive g c hc hC (hR 0 ⟨Metric.mem_ball_self A.radius_positive,
      0, le_rfl, 0, ⟨le_rfl, A.angle_positive.le⟩, by simp⟩)

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
