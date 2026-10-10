import A5RelativeGraph
import A5SeamTangents

set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations

/-- A native whole-piece chart in the source of an actual projection
homeomorphism gives a C1 section on its exact curved projected region.
The inverse coordinate lift and unique derivatives are constructed. -/
theorem native_piece_projection_graph
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface} (F : GeometricPiecewiseSurface S E.Carrier)
    (c : SmoothAmbientChart ThreeSphere) (P : Euc 3 →L[ℝ] Euc 2)
    (e : OpenPartialHomeomorph S (Euc 2))
    (he : ∀ x, e x = P (c.chart (E.toSphere (F.map x))))
    (hmaps : MapsTo (E.toSphere ∘ F.map) e.source c.chart.source)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count)
    (hchart : ∀ a, F.parametrization i a ∈ e.source → a ∈ ((F.domain i).chart j).map.source)
    (htrans : ∀ z ∈ ((F.domain i).chart j).map.target,
      F.parametrization i (((F.domain i).chart j).map.symm z) ∈ e.source →
      Function.Bijective (P.comp (fderivWithin ℝ
        (c.chart ∘ E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j)
        ((F.domain i).chart j).map.target z))) :
    let R := e.target ∩ e.symm ⁻¹' range (F.parametrization i)
    let f := c.chart ∘ E.toSphere ∘ F.map ∘ e.symm
    UniqueDiffOn ℝ R ∧ ContDiffOn ℝ 1 f R ∧
    ∀ z ∈ ((F.domain i).chart j).map.target,
      F.parametrization i (((F.domain i).chart j).map.symm z) ∈ e.source →
      (fderivWithin ℝ f R (P (c.chart (E.toSphere
        (sectorCoordinateMap (F.map ∘ F.parametrization i) j z))))).toLinearMap.range =
      (fderivWithin ℝ
        (c.chart ∘ E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j)
        ((F.domain i).chart j).map.target z).toLinearMap.range := by
  classical
  dsimp only
  let b := ((F.domain i).chart j).map
  let R := e.target ∩ e.symm ⁻¹' range (F.parametrization i)
  let f := c.chart ∘ E.toSphere ∘ F.map ∘ e.symm
  let H := c.chart ∘ E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j
  let Q := b.target ∩ (F.parametrization i ∘ b.symm) ⁻¹' e.source
  have hqexists (y : Euc 2) (hy : y ∈ R) :
      ∃ z ∈ b.target, sectorCoordinateMap (F.map ∘ F.parametrization i) j z = F.map (e.symm y) := by
    obtain ⟨a, ha⟩ := hy.2
    have has : a ∈ b.source := hchart a (ha ▸ e.map_target hy.1)
    refine ⟨b a, b.map_source has, ?_⟩
    change F.map (F.parametrization i (b.symm (b a))) = F.map (e.symm y)
    rw [b.left_inv has, ha]
  let q (y : Euc 2) := if hy : y ∈ R then (hqexists y hy).choose else 0
  have hq (y : Euc 2) (hy : y ∈ R) : q y ∈ b.target ∧
      sectorCoordinateMap (F.map ∘ F.parametrization i) j (q y) = F.map (e.symm y) := by
    simpa only [q, dite_eq_left hy] using (hqexists y hy).choose_spec
  have hqsource (y : Euc 2) (hy : y ∈ R) : F.parametrization i (b.symm (q y)) = e.symm y :=
    F.embedding.injective (hq y hy).2
  have hqQ : MapsTo q R Q := by
    intro y hy
    refine ⟨(hq y hy).1, ?_⟩
    change F.parametrization i (b.symm (q y)) ∈ e.source
    rw [hqsource y hy]
    exact e.map_target hy.1
  have hqC : ContinuousOn q R := continuous_coordinate_lift_of_embedded_image b
    (F.map ∘ F.parametrization i) (F.piece_topological_embedding i) R (F.map ∘ e.symm) q
    (F.map.continuous.comp_continuousOn (e.symm.continuousOn.mono inter_subset_left))
    (fun y hy => (hq y hy).1) (fun y hy => (hq y hy).2)
  have hQU : UniqueDiffOn ℝ Q := by
    have hb : UniqueDiffOn ℝ b.target := by
      rw [((F.domain i).chart j).target_eq]
      exact ((F.domain i).chart j).model.uniqueDiffOn_domain
    intro z hz
    apply (hb z hz.1).inter'
    exact ((F.parametrization i).continuous.comp_continuousOn b.symm.continuousOn z hz.1)
      (e.open_source.mem_nhds hz.2)
  have hHQ : ContDiffOn ℝ 1 H Q := by
    intro z hz
    have hc : E.toSphere (sectorCoordinateMap (F.map ∘ F.parametrization i) j z) ∈ c.chart.source :=
      hmaps hz.2
    exact (native_piece_chart_C1_rank_at E F i j z hz.1 c hc).1.mono inter_subset_left
  have hHD (z : Euc 2) (hz : z ∈ Q) : fderivWithin ℝ H Q z = fderivWithin ℝ H b.target z := by
    apply fderivWithin_subset inter_subset_left (hQU z hz)
    exact ((native_piece_chart_C1_rank_at E F i j z hz.1 c (hmaps hz.2)).1).differentiableWithinAt
      (by norm_num)
  have hproj : (P ∘ H) '' Q = R := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzs : F.parametrization i (b.symm z) ∈ e.source := hz.2
      have hez : e (F.parametrization i (b.symm z)) = P (H z) := he _
      refine ⟨?_, ?_⟩
      · change P (H z) ∈ e.target
        rw [← hez]
        exact e.map_source hzs
      change e.symm (P (H z)) ∈ range (F.parametrization i)
      rw [← hez, e.left_inv hzs]
      exact mem_range_self _
    · intro hy
      refine ⟨q y, hqQ hy, ?_⟩
      change P (c.chart (E.toSphere (sectorCoordinateMap (F.map ∘ F.parametrization i) j (q y)))) = y
      rw [(hq y hy).2, ← he, e.right_inv hy.1]
  have hinv (z : Euc 2) (hz : z ∈ Q) : q (P (H z)) = z := by
    have hzs : F.parametrization i (b.symm z) ∈ e.source := hz.2
    have hy : P (H z) ∈ R := by rw [← hproj]; exact ⟨z, hz, rfl⟩
    have hez : e (F.parametrization i (b.symm z)) = P (H z) := he _
    have heq := hqsource _ hy
    rw [← hez, e.left_inv hzs] at heq
    have hb := (F.parametrization_embedding i).injective heq
    have hh := congrArg b hb
    rwa [hez, b.right_inv (hq _ hy).1, b.right_inv hz.1] at hh
  obtain ⟨hu, hc, _, _, hr⟩ := C1_section_of_continuous_projection_inverse Q hQU H P q hHQ
    (fun z hz => by rw [hHD z hz]; exact htrans z hz.1 hz.2)
    (by rw [hproj]; exact hqC) hinv
  rw [hproj] at hu hc hr
  have hsame : EqOn (H ∘ q) f R := by
    intro y hy
    exact congrArg (c.chart ∘ E.toSphere) (hq y hy).2
  refine ⟨hu, hc.congr hsame.symm, ?_⟩
  intro z hz hzs
  have hzQ : z ∈ Q := ⟨hz, hzs⟩
  have hy : P (H z) ∈ R := by rw [← hproj]; exact ⟨z, hzQ, rfl⟩
  have hh := hr z hzQ
  rw [fderivWithin_congr' hsame hy, hHD z hzQ] at hh
  exact hh

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
