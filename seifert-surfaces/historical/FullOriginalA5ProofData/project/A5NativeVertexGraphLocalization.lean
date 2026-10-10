import A5NativeVertexC1Graph

set_option autoImplicit false
set_option maxHeartbeats 1500000
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations

/-- The literal native finite cover constructs the chart localization used
for vertex graph regularity. No incident-piece or chart-selection certificate
is needed by the caller. The projection and inverse maps are preserved. -/
theorem native_projection_graph_C1_after_restriction
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface} (F : GeometricPiecewiseSurface S E.Carrier)
    (x : S) (c : SmoothAmbientChart ThreeSphere) (P : Euc 3 →L[ℝ] Euc 2)
    (e : OpenPartialHomeomorph S (Euc 2)) (hx : x ∈ e.source)
    (he : ∀ z, e z = P (c.chart (E.toSphere (F.map z))))
    (hmaps : MapsTo (E.toSphere ∘ F.map) e.source c.chart.source)
    (htrans : ∀ i j z, z ∈ ((F.domain i).chart j).map.target →
      F.parametrization i (((F.domain i).chart j).map.symm z) ∈ e.source →
      Function.Bijective (P.comp (fderivWithin ℝ
        (c.chart ∘ E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j)
        ((F.domain i).chart j).map.target z)))
    (htangent : ∀ i j k l z w,
      z ∈ ((F.domain i).chart j).map.target → w ∈ ((F.domain k).chart l).map.target →
      F.parametrization i (((F.domain i).chart j).map.symm z) =
        F.parametrization k (((F.domain k).chart l).map.symm w) →
      F.parametrization i (((F.domain i).chart j).map.symm z) ∈ e.source →
      F.parametrization i (((F.domain i).chart j).map.symm z) ≠ x →
      (fderivWithin ℝ
        (c.chart ∘ E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j)
        ((F.domain i).chart j).map.target z).toLinearMap.range =
      (fderivWithin ℝ
        (c.chart ∘ E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization k) l)
        ((F.domain k).chart l).map.target w).toLinearMap.range) :
    ∃ e' : OpenPartialHomeomorph S (Euc 2),
      (e' : S → Euc 2) = e ∧ (e'.symm : Euc 2 → S) = e.symm ∧
      x ∈ e'.source ∧ e'.source ⊆ e.source ∧
      ContDiffOn ℝ 1 (c.chart ∘ E.toSphere ∘ F.map ∘ e'.symm) e'.target := by
  obtain ⟨U, hU, hxU, havoid, hcharts, _⟩ := native_incident_sector_chart_neighborhood F x
  let e' := e.restrOpen U hU
  have hx' : x ∈ e'.source := ⟨hx, hxU⟩
  have hsub : e'.source ⊆ e.source := inter_subset_left
  refine ⟨e', rfl, rfl, hx', hsub, ?_⟩
  apply native_projection_graph_C1_across_vertex E F x c P e' hx' he
    (fun z hz => hmaps (hsub hz))
  · intro i hi
    apply subset_empty_iff.mp
    rw [← havoid i hi]
    intro z hz
    exact ⟨hz.1, hz.2.2⟩
  · intro i hi
    obtain ⟨j, _, hcover⟩ := hcharts i hi
    refine ⟨j, ?_⟩
    intro a ha
    have hmem : F.parametrization i a ∈ range (F.parametrization i) ∩ U :=
      ⟨mem_range_self a, ha.2⟩
    rw [hcover] at hmem
    obtain ⟨b, hb, heq⟩ := hmem
    have hab := (F.parametrization_embedding i).injective heq
    exact hab ▸ hb.1
  · intro i j z hz hzs
    exact htrans i j z hz (hsub hzs)
  · intro i j k l z w hz hw heq hzs hne
    exact htangent i j k l z w hz hw heq (hsub hzs) hne

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
