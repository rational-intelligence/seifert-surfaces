import A5FiniteVertexMinimalSourceConsumer

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
universe u

/-- The literal finite seam graph leaves only finitely many interior arc
endpoints after ordinary seam and boundary regularity. These vertices are
removed by the native point-removal theorem, and the resulting same-image
source is minimal with the exact original boundary. -/
theorem minimizer_smooth_minimal_source_of_regular_seam_and_boundary_charts
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    (G : A7.SourceGeometry E) {S R : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier)
    (Fprime : GeometricPiecewiseSurface R E.Carrier)
    (hminimum : FixedBoundaryMinimizer E G.metric F Fprime)
    (hpieces : ∀ i j, IsMinimalPatch G.extension
      (E.toSphere ∘ sectorCoordinateMap (Fprime.map ∘ Fprime.parametrization i) j)
      (interior ((Fprime.domain i).chart j).map.target))
    (hboundary : ∀ x ∈ R.boundary, ∃ C : SmoothImageChart R Fprime.map, x ∈ C.chart.source)
    (harc : ∀ (a : Fin Fprime.seam.arcCount) (s : Time), 0 < s → s < 1 →
      ∃ C : SmoothImageChart R Fprime.map, Fprime.seam.arc a s ∈ C.chart.source)
    (hcircle : ∀ (a : Fin Fprime.seam.circleCount) (s : Circle),
      ∃ C : SmoothImageChart R Fprime.map, Fprime.seam.circle a s ∈ C.chart.source) :
    ∃ Q : GlobalSmoothSource.SmoothSourceReconstruction E Fprime,
      MinimalEmbedding E G Q.embedding ∧
      Q.embedding.toFun '' Q.source.boundary = F.map '' S.boundary ∧
      Fprime.image ∩ (𝓡∂ 3).boundary E.Carrier = F.map '' S.boundary := by
  let A : Set R := (range (fun a => Fprime.seam.arc a 0) ∪
    range (fun a => Fprime.seam.arc a 1)) \ R.boundary
  have hA : A.Finite := ((finite_range _).union (finite_range _)).subset sdiff_subset
  apply minimizer_smooth_minimal_source_after_finite_vertex_removal E G F Fprime hminimum
    A hA (fun x hx => hx.2) hpieces
  intro x hx
  by_cases hxb : x ∈ R.boundary
  · exact hboundary x hxb
  by_cases hxs : x ∈ Fprime.seam.carrier
  · rcases hxs with hxa | hxc
    · obtain ⟨a, s, rfl⟩ := mem_iUnion.mp hxa
      have hs0 : s ≠ 0 := by
        intro he
        subst s
        exact hx ⟨Or.inl (mem_range_self a), hxb⟩
      have hs1 : s ≠ 1 := by
        intro he
        subst s
        exact hx ⟨Or.inr (mem_range_self a), hxb⟩
      exact harc a s (lt_of_le_of_ne (by exact s.property.1) (Ne.symm hs0))
        (lt_of_le_of_ne (by exact s.property.2) hs1)
    · obtain ⟨a, s, rfl⟩ := mem_iUnion.mp hxc
      exact hcircle a s
  · obtain ⟨C, hxC, _⟩ := Fprime.smooth_off_seam x hxs
    exact ⟨C, hxC⟩

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
