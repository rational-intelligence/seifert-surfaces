import NativeSharedSeamAssemblyProbe

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open scoped Manifold ContDiff Bundle
open Set Topology Filter
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
universe u
variable {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)

theorem native_adjacent_arc_construction_v468 (G : A7.SourceGeometry E)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (a : Fin F.seam.arcCount) (s : Time)
    (hleft : 0 < (s : ℝ)) (hright : (s : ℝ) < 1) :
    Nonempty (AdjacentArcData E G F a s) := by
  obtain ⟨r, hr, hl, hu, parameter, hformula, hpemb, hpr, hp0,
    γ, hγformula, hγ, hreg, Q, hQ, hQW, h0Q, hlifts⟩ :=
    native_arc_finite_regular_boundary_lifts E F a s hleft hright
  let β : SeamLocalTime → S := F.seam.arc a ∘ parameter
  have hβ0 : β ⟨0, neg_one_lt_zero, zero_lt_one⟩ = F.seam.arc a s := by
    dsimp only [β, Function.comp_def]
    rw [hp0]
  have hγemb : IsEmbedding (fun t : SeamLocalTime => γ t) := by
    have hE : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
    have heq : (fun t : SeamLocalTime => γ t) = E.toSphere ∘ F.map ∘ F.seam.arc a ∘ parameter :=
      funext hγformula
    rw [heq]
    exact hE.isEmbedding.comp (F.embedding.comp ((F.seam.arc_embedding a).comp hpemb))
  have hxseam : β ⟨0, neg_one_lt_zero, zero_lt_one⟩ ∈ F.seam.carrier := by
    rw [hβ0]
    exact Or.inl (mem_iUnion.mpr ⟨a, s, rfl⟩)
  obtain ⟨U, hU, hsU, hUB, hcut⟩ := native_arc_isolated_source_window E F a s hleft hright
  have hxboundary : β ⟨0, neg_one_lt_zero, zero_lt_one⟩ ∉ S.boundary := by
    rw [hβ0]
    exact hUB hsU
  obtain ⟨D⟩ := native_shared_seam_geometry E G F β γ hγformula hγ hreg hγemb
    hxseam hxboundary Q hQ hQW h0Q (by simpa only [hβ0] using hlifts)
  let p : SeamLocalTime → Time := parameter ∘ seamScale D.scale D.scale_pos D.scale_lt_one
  have hrad : 0 < r * D.scale := mul_pos hr D.scale_pos
  have hradlt : r * D.scale < r := by nlinarith [D.scale_lt_one]
  refine ⟨{
    radius := r * D.scale
    radius_pos := hrad
    left_bound := by linarith
    right_bound := by linarith
    parameter := p
    parameter_formula := ?_
    contains_point := ?_
    edge := D.edge
    edge_formula := D.edge_formula
    edge_smooth := D.edge_smooth
    edge_regular := D.edge_regular
    one := D.one
    two := D.two
    chartOne := D.chartOne
    chartTwo := D.chartTwo
    liftOne := D.liftOne
    liftTwo := D.liftTwo
    liftOne_boundary := D.liftOne_boundary
    liftTwo_boundary := D.liftTwo_boundary
    imageOne := D.imageOne
    imageTwo := D.imageTwo
    outwardOne := D.outwardOne
    outwardTwo := D.outwardTwo
    outwardOne_direction := D.outwardOne_direction
    outwardTwo_direction := D.outwardTwo_direction
    conormalOne_unit := D.conormalOne_unit
    conormalTwo_unit := D.conormalTwo_unit
    conormalOne_orthogonal := D.conormalOne_orthogonal
    conormalTwo_orthogonal := D.conormalTwo_orthogonal
    neighbourhood := D.neighbourhood
    neighbourhood_open := D.neighbourhood_open
    covers_two_sheets := D.covers_two_sheets
    otherwise_disjoint := D.otherwise_disjoint
    one_ne_two := D.one_ne_two
    incident_exact := D.incident_exact
    coreRadius := D.coreRadius
    coreRadius_pos := D.coreRadius_pos
    coreRadius_lt_one := D.coreRadius_lt_one
    core_edge_closure_in_neighbourhood := D.core_edge_closure_in_neighbourhood
    halfStripOne := D.halfStripOne
    halfStripTwo := D.halfStripTwo
    outwardOne_continuous := D.outwardOne_continuous
    outwardTwo_continuous := D.outwardTwo_continuous
    conormalOne_continuous := D.conormalOne_continuous
    conormalTwo_continuous := D.conormalTwo_continuous
  }⟩
  · intro t
    change (parameter (seamScale D.scale D.scale_pos D.scale_lt_one t) : ℝ) = _
    rw [hformula]
    change (s : ℝ) + r * (D.scale * (t : ℝ)) = (s : ℝ) + (r * D.scale) * (t : ℝ)
    ring
  · have hc := D.contains_point
    rwa [hβ0] at hc

theorem native_adjacent_circle_construction_v468 (G : A7.SourceGeometry E)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (a : Fin F.seam.circleCount) (s : Circle) :
    Nonempty (AdjacentCircleData E G F a s) := by
  obtain ⟨parameter, hpemb, hpr, hp0, γ, hγformula, hγ, hreg, Q, hQ, hQW, h0Q, hlifts⟩ :=
    native_circle_finite_regular_boundary_lifts E F a s
  let β : SeamLocalTime → S := F.seam.circle a ∘ parameter
  have hβ0 : β ⟨0, neg_one_lt_zero, zero_lt_one⟩ = F.seam.circle a s := by
    dsimp only [β, Function.comp_def]
    rw [hp0]
  have hγemb : IsEmbedding (fun t : SeamLocalTime => γ t) := by
    have hE : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
    have heq : (fun t : SeamLocalTime => γ t) = E.toSphere ∘ F.map ∘ F.seam.circle a ∘ parameter :=
      funext hγformula
    rw [heq]
    exact hE.isEmbedding.comp (F.embedding.comp ((F.seam.circle_embedding a).comp hpemb))
  have hxseam : β ⟨0, neg_one_lt_zero, zero_lt_one⟩ ∈ F.seam.carrier := by
    rw [hβ0]
    exact Or.inr (mem_iUnion.mpr ⟨a, s, rfl⟩)
  have hxboundary : β ⟨0, neg_one_lt_zero, zero_lt_one⟩ ∉ S.boundary := by
    rw [hβ0]
    exact fun hb => Set.disjoint_left.mp (F.seam.circle_off_boundary a) ⟨s, rfl⟩ hb
  obtain ⟨D⟩ := native_shared_seam_geometry E G F β γ hγformula hγ hreg hγemb
    hxseam hxboundary Q hQ hQW h0Q (by simpa only [hβ0] using hlifts)
  let p : SeamLocalTime → Circle := parameter ∘ seamScale D.scale D.scale_pos D.scale_lt_one
  obtain ⟨hp, hpo⟩ := shortened_seam_parameter_topology parameter hpemb hpr D.scale D.scale_pos D.scale_lt_one
  refine ⟨{
    parameter := p
    parameter_embedding := hp
    parameter_open_range := hpo
    parameter_center := ?_
    contains_point := ?_
    edge := D.edge
    edge_formula := D.edge_formula
    edge_smooth := D.edge_smooth
    edge_regular := D.edge_regular
    one := D.one
    two := D.two
    chartOne := D.chartOne
    chartTwo := D.chartTwo
    liftOne := D.liftOne
    liftTwo := D.liftTwo
    liftOne_boundary := D.liftOne_boundary
    liftTwo_boundary := D.liftTwo_boundary
    imageOne := D.imageOne
    imageTwo := D.imageTwo
    outwardOne := D.outwardOne
    outwardTwo := D.outwardTwo
    outwardOne_direction := D.outwardOne_direction
    outwardTwo_direction := D.outwardTwo_direction
    conormalOne_unit := D.conormalOne_unit
    conormalTwo_unit := D.conormalTwo_unit
    conormalOne_orthogonal := D.conormalOne_orthogonal
    conormalTwo_orthogonal := D.conormalTwo_orthogonal
    neighbourhood := D.neighbourhood
    neighbourhood_open := D.neighbourhood_open
    covers_two_sheets := D.covers_two_sheets
    otherwise_disjoint := D.otherwise_disjoint
    one_ne_two := D.one_ne_two
    incident_exact := D.incident_exact
    coreRadius := D.coreRadius
    coreRadius_pos := D.coreRadius_pos
    coreRadius_lt_one := D.coreRadius_lt_one
    core_edge_closure_in_neighbourhood := D.core_edge_closure_in_neighbourhood
    halfStripOne := D.halfStripOne
    halfStripTwo := D.halfStripTwo
    outwardOne_continuous := D.outwardOne_continuous
    outwardTwo_continuous := D.outwardTwo_continuous
    conormalOne_continuous := D.conormalOne_continuous
    conormalTwo_continuous := D.conormalTwo_continuous
  }⟩
  · change parameter (seamScale D.scale D.scale_pos D.scale_lt_one ⟨0, neg_one_lt_zero, zero_lt_one⟩) = s
    have hz : seamScale D.scale D.scale_pos D.scale_lt_one ⟨0, neg_one_lt_zero, zero_lt_one⟩ =
        ⟨0, neg_one_lt_zero, zero_lt_one⟩ := by
      apply Subtype.ext
      exact mul_zero _
    rw [hz]
    exact hp0
  · have hc := D.contains_point
    rwa [hβ0] at hc

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
