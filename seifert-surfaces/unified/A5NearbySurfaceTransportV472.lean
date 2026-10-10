import A5GlobalSmoothSourceV466

open Set Topology Function
open scoped Manifold ContDiff

noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.NearbyDeformations.SurfaceTransport
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
universe u v w

theorem homeomorph_component_transport
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) {s : Set Y} {x : X} (hx : e x ∈ s) :
    e ⁻¹' connectedComponentIn s (e x) = connectedComponentIn (e ⁻¹' s) x := by
  have hforward := e.continuous.continuousOn.image_connectedComponentIn_subset
    (s := e ⁻¹' s) (a := x) hx
  have hbackward := e.symm.continuous.continuousOn.image_connectedComponentIn_subset
    (s := s) (a := e x) hx
  have hpre : e.symm '' s = e ⁻¹' s := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa using hz
    · intro hy
      exact ⟨e y, hy, e.symm_apply_apply y⟩
  have himage : e '' (e ⁻¹' s) = s := e.surjective.image_preimage s
  rw [hpre, e.symm_apply_apply] at hbackward
  rw [himage] at hforward
  ext y
  constructor
  · intro hy
    exact hbackward ⟨e y, hy, e.symm_apply_apply y⟩
  · intro hy
    exact hforward ⟨y, hy, rfl⟩

def pullback_partial_chart
    {X : Type u} {Y : Type v} {Z : Type w} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] (e : X ≃ₜ Y)
    (c : PartialHomeomorph Y Z) : PartialHomeomorph X Z where
  toFun := c ∘ e
  invFun := e.symm ∘ c.symm
  source := e ⁻¹' c.source
  target := c.target
  map_source' := fun _ hx => c.map_source hx
  map_target' := fun _ hx => by simpa using c.map_target hx
  left_inv' := by
    intro x hx
    change e.symm (c.symm (c (e x))) = x
    rw [c.left_inv hx, e.symm_apply_apply]
  right_inv' := by
    intro y hy
    change c (e (e.symm (c.symm y))) = y
    rw [e.apply_symm_apply, c.right_inv hy]
  continuousOn_toFun := c.continuousOn.comp e.continuous.continuousOn (fun _ hx => hx)
  continuousOn_invFun := e.symm.continuous.comp_continuousOn c.symm.continuousOn

variable {M : Type w} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M] {S R : CompactOrientedSurface.{v}}

theorem boundary_membership_transport (e : S ≃ₜ R)
    (hb : e '' S.boundary = R.boundary) (x : S) :
    e x ∈ R.boundary ↔ x ∈ S.boundary := by
  rw [← hb]
  exact e.injective.mem_set_image

def pullback_seam (G : GeometricPiecewiseSurface R M) (e : S ≃ₜ R)
    (hb : e '' S.boundary = R.boundary) : SeamGraph S (G.map ∘ e) where
  arcCount := G.seam.arcCount
  circleCount := G.seam.circleCount
  arc i := ⟨e.symm ∘ G.seam.arc i, e.symm.continuous.comp (G.seam.arc i).continuous⟩
  circle i := ⟨e.symm ∘ G.seam.circle i, e.symm.continuous.comp (G.seam.circle i).continuous⟩
  arc_embedding i := e.symm.isEmbedding.comp (G.seam.arc_embedding i)
  circle_embedding i := e.symm.isEmbedding.comp (G.seam.circle_embedding i)
  arc_smooth_image i := by simpa [Function.comp_def] using G.seam.arc_smooth_image i
  arc_differential_injective i x := by
    have heq : (G.map ∘ e) ∘
        (⟨e.symm ∘ G.seam.arc i, e.symm.continuous.comp (G.seam.arc i).continuous⟩ : C(Time,S)) =
        G.map ∘ G.seam.arc i := by funext t; simp
    rw [heq]
    exact G.seam.arc_differential_injective i x
  circle_smooth_image i := by simpa [Function.comp_def] using G.seam.circle_smooth_image i
  circle_differential_injective i x := by
    have heq : (G.map ∘ e) ∘
        (⟨e.symm ∘ G.seam.circle i, e.symm.continuous.comp (G.seam.circle i).continuous⟩ : C(Circle,S)) =
        G.map ∘ G.seam.circle i := by funext t; simp
    rw [heq]
    exact G.seam.circle_differential_injective i x
  arc_boundary i := by
    intro t ht
    apply G.seam.arc_boundary i
    simpa [Function.comp_def] using (boundary_membership_transport e hb _).2 ht
  circle_off_boundary i := by
    apply disjoint_left.2
    rintro x ⟨t, rfl⟩ hx
    apply disjoint_left.1 (G.seam.circle_off_boundary i) (mem_range_self t)
    simpa using (boundary_membership_transport e hb _).2 hx
  arc_intersections i j hij := by
    rintro x ⟨⟨t, ht⟩, ⟨u, hu⟩⟩
    have ht' : G.seam.arc i t = e x := by
      have hh := congrArg e ht
      simpa [Function.comp_def] using hh
    have hu' : G.seam.arc j u = e x := by
      have hh := congrArg e hu
      simpa [Function.comp_def] using hh
    have hh := G.seam.arc_intersections i j hij ⟨⟨t, ht'⟩, ⟨u, hu'⟩⟩
    constructor
    · rcases hh.1 with hh | hh <;> simp only [mem_insert_iff, mem_singleton_iff] at hh ⊢
      · exact Or.inl (e.injective (by simpa [Function.comp_def] using hh))
      · exact Or.inr (e.injective (by simpa [Function.comp_def] using hh))
    · rcases hh.2 with hh | hh <;> simp only [mem_insert_iff, mem_singleton_iff] at hh ⊢
      · exact Or.inl (e.injective (by simpa [Function.comp_def] using hh))
      · exact Or.inr (e.injective (by simpa [Function.comp_def] using hh))
  circle_intersections i j hij := by
    apply disjoint_left.2
    rintro x ⟨t, ht⟩ ⟨u, hu⟩
    apply disjoint_left.1 (G.seam.circle_intersections hij)
      (mem_range_self t)
    refine ⟨u, ?_⟩
    have hh := congrArg e (hu.trans ht.symm)
    simpa [Function.comp_def] using hh
  arc_circle_disjoint i j := by
    apply disjoint_left.2
    rintro x ⟨t, ht⟩ ⟨u, hu⟩
    apply disjoint_left.1 (G.seam.arc_circle_disjoint i j)
      (mem_range_self t)
    refine ⟨u, ?_⟩
    have hh := congrArg e (hu.trans ht.symm)
    simpa [Function.comp_def] using hh

theorem pullback_seam_carrier (G : GeometricPiecewiseSurface R M) (e : S ≃ₜ R)
    (hb : e '' S.boundary = R.boundary) :
    (pullback_seam G e hb).carrier = e ⁻¹' G.seam.carrier := by
  ext x
  simp only [SeamGraph.carrier, mem_union, mem_iUnion, mem_range, mem_preimage]
  constructor
  · rintro (⟨i, t, ht⟩ | ⟨i, t, ht⟩)
    · exact Or.inl ⟨i, t, by simpa [pullback_seam, Function.comp_def] using congrArg e ht⟩
    · exact Or.inr ⟨i, t, by simpa [pullback_seam, Function.comp_def] using congrArg e ht⟩
  · rintro (⟨i, t, ht⟩ | ⟨i, t, ht⟩)
    · exact Or.inl ⟨i, t, by simpa [pullback_seam, Function.comp_def] using congrArg e.symm ht⟩
    · exact Or.inr ⟨i, t, by simpa [pullback_seam, Function.comp_def] using congrArg e.symm ht⟩

def pullback_smooth_image_chart (G : GeometricPiecewiseSurface R M) (e : S ≃ₜ R)
    (hb : e '' S.boundary = R.boundary) (c : SmoothImageChart R G.map) :
    SmoothImageChart S (G.map ∘ e) where
  chart := pullback_partial_chart e c.chart
  source_open := c.source_open.preimage e.continuous
  target_open := c.target_open
  cInfinity := by
    have heq : (G.map ∘ e) ∘ (pullback_partial_chart e c.chart).symm =
        G.map ∘ c.chart.symm := by funext z; simp [pullback_partial_chart]
    rw [heq]
    exact c.cInfinity
  differential_injective := by
    have heq : (G.map ∘ e) ∘ (pullback_partial_chart e c.chart).symm =
        G.map ∘ c.chart.symm := by funext z; simp [pullback_partial_chart]
    rw [heq]
    exact c.differential_injective
  boundary_image := by
    change (c.chart ∘ e) '' (S.boundary ∩ e ⁻¹' c.chart.source) = _
    rw [image_comp, image_inter_preimage, hb]
    exact c.boundary_image

def pullback_geometric_surface (G : GeometricPiecewiseSurface R M) (e : S ≃ₜ R)
    (hb : e '' S.boundary = R.boundary) : GeometricPiecewiseSurface S M where
  map := G.map.comp ⟨e, e.continuous⟩
  embedding := G.embedding.comp e.isEmbedding
  boundary_preimage := by
    ext x
    change G.map (e x) ∈ (𝓡∂ 3).boundary M ↔ x ∈ S.boundary
    have h := congrArg (fun a : Set R => e x ∈ a) G.boundary_preimage
    exact (iff_of_eq h).trans (boundary_membership_transport e hb x)
  seam := pullback_seam G e hb
  smooth_off_seam := by
    intro x hx
    have hxG : e x ∈ G.seam.carrierᶜ := by
      change x ∉ (pullback_seam G e hb).carrier at hx
      rwa [pullback_seam_carrier] at hx
    obtain ⟨c, hc, hclean⟩ := G.smooth_off_seam (e x) hxG
    refine ⟨pullback_smooth_image_chart G e hb c, hc, ?_⟩
    intro y hy
    change y ∉ (pullback_seam G e hb).carrier
    rw [pullback_seam_carrier]
    exact hclean hy
  pieceCount := G.pieceCount
  domain := G.domain
  parametrization i :=
    ⟨e.symm ∘ G.parametrization i, e.symm.continuous.comp (G.parametrization i).continuous⟩
  parametrization_embedding i := e.symm.isEmbedding.comp (G.parametrization_embedding i)
  piece_c1 i j := by
    have heq :
        (G.map.comp ⟨e, e.continuous⟩ : C(S,M)) ∘
          (⟨e.symm ∘ G.parametrization i,
            e.symm.continuous.comp (G.parametrization i).continuous⟩ : C(G.domain i,S)) =
        G.map ∘ G.parametrization i := by funext z; simp
    rw [heq]
    exact G.piece_c1 i j
  piece_topological_embedding i := by
    have heq :
        (G.map.comp ⟨e, e.continuous⟩ : C(S,M)) ∘
          (⟨e.symm ∘ G.parametrization i,
            e.symm.continuous.comp (G.parametrization i).continuous⟩ : C(G.domain i,S)) =
        G.map ∘ G.parametrization i := by funext z; simp
    rw [heq]
    exact G.piece_topological_embedding i
  piece_differential_injective i j := by
    have heq :
        (G.map.comp ⟨e, e.continuous⟩ : C(S,M)) ∘
          (⟨e.symm ∘ G.parametrization i,
            e.symm.continuous.comp (G.parametrization i).continuous⟩ : C(G.domain i,S)) =
        G.map ∘ G.parametrization i := by funext z; simp
    rw [heq]
    exact G.piece_differential_injective i j
  piece_smooth_interior i j := by
    have heq :
        (G.map.comp ⟨e, e.continuous⟩ : C(S,M)) ∘
          (⟨e.symm ∘ G.parametrization i,
            e.symm.continuous.comp (G.parametrization i).continuous⟩ : C(G.domain i,S)) =
        G.map ∘ G.parametrization i := by funext z; simp
    rw [heq]
    exact G.piece_smooth_interior i j
  piece_edges_smooth i j := by
    have heq :
        (G.map.comp ⟨e, e.continuous⟩ : C(S,M)) ∘
          (⟨e.symm ∘ G.parametrization i,
            e.symm.continuous.comp (G.parametrization i).continuous⟩ : C(G.domain i,S)) =
        G.map ∘ G.parametrization i := by funext z; simp
    rw [heq]
    exact G.piece_edges_smooth i j
  piece_interior_component i := by
    obtain ⟨x, hx, he⟩ := G.piece_interior_component i
    have hclean : ((pullback_seam G e hb).carrier ∪ S.boundary)ᶜ =
        e ⁻¹' (G.seam.carrier ∪ R.boundary)ᶜ := by
      ext y
      rw [pullback_seam_carrier]
      simp only [mem_compl_iff, mem_union, mem_preimage,
        boundary_membership_transport e hb]
    refine ⟨e.symm x, ?_, ?_⟩
    · rw [hclean]
      simpa using hx
    · change (e.symm ∘ G.parametrization i) '' (G.domain i).interior = _
      rw [image_comp, he, hclean]
      have hpre : e.symm '' connectedComponentIn (G.seam.carrier ∪ R.boundary)ᶜ x =
          e ⁻¹' connectedComponentIn (G.seam.carrier ∪ R.boundary)ᶜ x := by
        ext y
        constructor
        · rintro ⟨z, hz, rfl⟩
          simpa using hz
        · intro hy
          exact ⟨e y, hy, e.symm_apply_apply y⟩
      rw [hpre]
      simpa using homeomorph_component_transport e
        (x := e.symm x) (s := (G.seam.carrier ∪ R.boundary)ᶜ) (by simpa using hx)
  pieces_distinct i j hij := by
    apply disjoint_left.2
    rintro x ⟨a, ha, hea⟩ ⟨b, hb', heb⟩
    exact disjoint_left.1 (G.pieces_distinct hij)
      ⟨a, ha, by simpa using congrArg e hea⟩
      ⟨b, hb', by simpa using congrArg e heb⟩
  piece_closure i := by
    change range (e.symm ∘ G.parametrization i) =
      closure ((e.symm ∘ G.parametrization i) '' (G.domain i).interior)
    rw [range_comp, G.piece_closure, image_comp, e.symm.image_closure]
  covers := by
    ext x
    constructor
    · intro _
      trivial
    · intro _
      have hx : e x ∈ ⋃ i, range (G.parametrization i) := by rw [G.covers]; trivial
      obtain ⟨i, z, hz⟩ := mem_iUnion.1 hx
      exact mem_iUnion.2 ⟨i, z, by simpa using congrArg e.symm hz⟩
  piece_boundary i := by
    rintro x ⟨z, hz, rfl⟩
    have h := G.piece_boundary i ⟨z, hz, rfl⟩
    change e.symm (G.parametrization i z) ∈ (pullback_seam G e hb).carrier ∪ S.boundary
    rw [pullback_seam_carrier]
    rcases h with h | h
    · exact Or.inl (by simpa using h)
    · exact Or.inr ((boundary_membership_transport e hb _).1 (by simpa using h))

theorem pullback_geometric_area (g : SmoothMetric M) (G : GeometricPiecewiseSurface R M)
    (e : S ≃ₜ R) (hb : e '' S.boundary = R.boundary) :
    geometricArea g (pullback_geometric_surface G e hb) = geometricArea g G := by
  unfold geometricArea
  apply Finset.sum_congr rfl
  intro i _
  have heq : (pullback_geometric_surface G e hb).map ∘
      (pullback_geometric_surface G e hb).parametrization i =
      G.map ∘ G.parametrization i := by
    funext z
    change G.map (e (e.symm (G.parametrization i z))) = G.map (G.parametrization i z)
    rw [e.apply_symm_apply]
  rw [heq]
  rfl

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.NearbyDeformations.SurfaceTransport
