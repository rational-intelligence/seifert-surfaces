import A5RegularSeamLocalChartV472

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC CurvedDivergence
universe u

theorem original_stationary_regular_circle_image_chart
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    (G : A7.SourceGeometry E) {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier)
    (hstationary : ∀ X : InteriorSmoothVectorField E, pieceDivergenceSum E G F X = 0)
    (hminimal : PiecesMinimal E G F)
    (a : Fin F.seam.circleCount) (s : Circle) :
    ∃ C : SmoothImageChart S F.map, F.seam.circle a s ∈ C.chart.source := by
  obtain ⟨d⟩ := native_adjacent_circle_producer E G F a s
  let trace := fun t => F.seam.circle a (d.parameter t)
  have htraceboundary : ∀ t : SeamLocalTime, trace t ∉ S.boundary := by
    intro t hb
    exact Set.disjoint_left.mp (F.seam.circle_off_boundary a) ⟨d.parameter t,rfl⟩ hb
  have hcenter : trace regularSeamZero = F.seam.circle a s := by
    change F.seam.circle a (d.parameter regularSeamZero) = _
    rw [show d.parameter regularSeamZero = s from d.parameter_center]
  let nu1 := fun t : SeamLocalTime => actualPieceConormal E F d.one d.chartOne
    (d.liftOne t) (d.outwardOne t) (d.edge t) (d.imageOne t)
  let nu2 := fun t : SeamLocalTime => actualPieceConormal E F d.two d.chartTwo
    (d.liftTwo t) (d.outwardTwo t) (d.edge t) (d.imageTwo t)
  have hbal := native_actual_pair_conormal_balance E G F hstationary hminimal
    d.edge d.edge_smooth d.edge_regular trace htraceboundary (fun t => (d.edge_formula t).symm)
    d.one d.two d.one_ne_two d.chartOne d.chartTwo d.incident_exact
    d.liftOne d.liftTwo d.outwardOne d.outwardTwo d.liftOne_boundary d.liftTwo_boundary
    d.imageOne d.imageTwo d.halfStripOne d.halfStripTwo
    d.outwardOne_direction d.outwardTwo_direction nu1 nu2
    (fun _ => rfl) (fun _ => rfl) d.conormalOne_continuous d.conormalTwo_continuous
    d.conormalOne_unit d.conormalTwo_unit d.conormalOne_orthogonal d.conormalTwo_orthogonal
  let i : Fin 2 → Fin F.pieceCount := ![d.one,d.two]
  let j : ∀ k, Fin (F.domain (i k)).count :=
    Fin.cases d.chartOne (fun k => Fin.cases d.chartTwo (fun k => Fin.elim0 k) k)
  let q : Fin 2 → SeamLocalTime → E2 := ![d.liftOne,d.liftTwo]
  let n : Fin 2 → SeamLocalTime → E2 := ![d.outwardOne,d.outwardTwo]
  have hqall : ∀ k t, q k t ∈ ((F.domain (i k)).chart (j k)).map.target ∩
      frontier ((F.domain (i k)).chart (j k)).map.target := by
    intro k t
    fin_cases k
    · exact d.liftOne_boundary t
    · exact d.liftTwo_boundary t
  have himall : ∀ k t, pieceSphereCoordinate E F (i k) (j k) (q k t) = d.edge t := by
    intro k t
    fin_cases k
    · exact d.imageOne t
    · exact d.imageTwo t
  have hbalanced : ∀ t, actualPieceConormal E F (i 0) (j 0) (q 0 t) (n 0 t)
      (d.edge t) (himall 0 t) + actualPieceConormal E F (i 1) (j 1) (q 1 t) (n 1 t)
      (d.edge t) (himall 1 t) = 0 := by
    intro t
    change nu1 t + nu2 t = 0
    exact hbal t
  obtain ⟨V,hV,hxV,hVboundary,hVseam⟩ := native_circle_seam_isolation F.seam a s
    (range d.parameter) d.parameter_open_range ⟨regularSeamZero,d.parameter_center⟩
  have htrace : ∀ z ∈ V, z ∈ F.seam.carrier → ∃ t, trace t = z := by
    intro z hz hs
    have hm : z ∈ (F.seam.circle a '' range d.parameter) ∩ V := hVseam ▸ ⟨hs,hz⟩
    obtain ⟨v,⟨t,ht⟩,hvz⟩ := hm.1
    exact ⟨t,by change F.seam.circle a (d.parameter t) = z; rw [ht,hvz]⟩
  refine regular_seam_chart_of_balanced_native_pair E G F (F.seam.circle a s) trace hcenter htraceboundary
    d.edge d.edge_formula d.edge_smooth d.edge_regular i j q n hqall himall ?_ ?_ ?_ hbalanced
    d.neighbourhood d.neighbourhood_open d.contains_point ?_ d.incident_exact V hV hxV hVboundary htrace
    (fun ii jj => hminimal ii jj) ?_
  · intro k
    fin_cases k
    · obtain ⟨eps,heps,hdir⟩ := d.outwardOne_direction regularSeamZero
      exact ⟨eps,heps,fun b hb => interior_subset (hdir b hb).1⟩
    · obtain ⟨eps,heps,hdir⟩ := d.outwardTwo_direction regularSeamZero
      exact ⟨eps,heps,fun b hb => interior_subset (hdir b hb).1⟩
  · intro k t
    fin_cases k
    · exact d.conormalOne_unit t
    · exact d.conormalTwo_unit t
  · intro k t
    fin_cases k
    · exact d.conormalOne_orthogonal t
    · exact d.conormalTwo_orthogonal t
  · intro z hz
    have hm := hz
    rw [d.covers_two_sheets] at hm
    rcases hm.1 with h1 | h2
    · obtain ⟨y,_,hy⟩ := h1
      exact ⟨0,y,hy⟩
    · obtain ⟨y,_,hy⟩ := h2
      exact ⟨1,y,hy⟩
  · intro c P ρ sig left right hl hr hgeom
    exact native_circle_projected_signed_zero_near E F a s d.parameter d.parameter_embedding
      d.parameter_open_range d.parameter_center d.edge d.edge_formula c P ρ sig left right hl hr hgeom

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
