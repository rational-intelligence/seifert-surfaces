import CurveComplexGenusTwo.Topology.ThetaRetention.ActualSourceFirstReturn

namespace CurveComplex

/-- Connectedness of the complement of an actual nonseparating curve produces
path connectedness because the complement is an open surface. -/
theorem source_nonseparating_complement_pathConnected
    (S : Type) [TopologicalSpace S] [T2Space S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (c : Curve S) (hns : Nonseparating c) : PathConnectedSpace ↥(c.imageᶜ) := by
  let : LocallyPathConnectedSpace S :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) S
  have hopen : IsOpen c.imageᶜ :=
    (isCompact_range c.embedded.continuous).isClosed.isOpen_compl
  exact isPathConnected_iff_pathConnectedSpace.mp
    (hopen.isConnected_iff_isPathConnected.mp hns)

/-- A genuine path in the original surface avoiding the actual nonseparating
curve image, obtained without an additional path-connectivity assumption. -/
noncomputable def source_nonseparating_complement_path
    (S : Type) [TopologicalSpace S] [T2Space S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (c : Curve S) (hns : Nonseparating c)
    (x y : S) (hx : x ∉ c.image) (hy : y ∉ c.image) : Path x y := by
  let : PathConnectedSpace ↥(c.imageᶜ) :=
    source_nonseparating_complement_pathConnected S c hns
  exact (PathConnectedSpace.somePath
    (⟨x,hx⟩ : ↥(c.imageᶜ)) (⟨y,hy⟩ : ↥(c.imageᶜ))).map continuous_subtype_val

theorem source_nonseparating_complement_path_avoids
    (S : Type) [TopologicalSpace S] [T2Space S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (c : Curve S) (hns : Nonseparating c)
    (x y : S) (hx : x ∉ c.image) (hy : y ∉ c.image) (t : Interval) :
    source_nonseparating_complement_path S c hns x y hx hy t ∉ c.image := by
  let : PathConnectedSpace ↥(c.imageᶜ) :=
    source_nonseparating_complement_pathConnected S c hns
  exact (PathConnectedSpace.somePath
    (X := ↥(c.imageᶜ)) (⟨x,hx⟩ : ↥(c.imageᶜ)) (⟨y,hy⟩ : ↥(c.imageᶜ)) t).property

/-- Concrete topological first-return surgery data. The closing boundary is
an actual embedded curve; the still-required nonseparating retention and
push-off count bounds are not encoded as assumptions. -/
structure SourceFirstReturnBoundary
    {S : Type} [TopologicalSpace S] (a b : Curve S) where
  start : S
  finish : S
  distinct : start ≠ finish
  start_mem : start ∈ a.image ∩ b.image
  finish_mem : finish ∈ a.image ∩ b.image
  first : C(Interval,S)
  second : C(Interval,S)
  first_embedded : Topology.IsEmbedding first
  second_embedded : Topology.IsEmbedding second
  first_zero : first 0 = start
  second_zero : second 0 = start
  first_one : first 1 = finish
  second_one : second 1 = finish
  first_subset : Set.range first ⊆ a.image
  second_subset : Set.range second ⊆ b.image
  first_interior_avoids : ∀ t : Interval, t ≠ 0 → t ≠ 1 → first t ∉ b.image
  intersection : Set.range first ∩ Set.range second = {start,finish}
  boundary : Curve S
  boundary_image : boundary.image = Set.range first ∪ Set.range second
  boundary_compact : IsCompact boundary.image

/-- The geometric starting configuration for direct nonseparating surgery is
produced from arbitrary source vertices with intersection greater than one.
The first return runs along the target curve and avoids the current curve in
its interior. Both selected representatives retain connected complements. -/
theorem source_nonseparating_minimal_first_return
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (α β : {v : Vertex S // nonseparatingVertex v})
    (hlarge : 1 < geometricIntersection α.val β.val) :
    ∃ a b : EssentialCurve S,
      Quotient.mk (essentialCurveSetoid S) a = α.val ∧
      Quotient.mk (essentialCurveSetoid S) b = β.val ∧
      Nonseparating a.val ∧ Nonseparating b.val ∧
      ∃ h : Transverse a.val b.val,
        h.1.toFinset.card = geometricIntersection α.val β.val ∧
        Nonempty (SourceFirstReturnBoundary b.val a.val) := by
  classical
  obtain ⟨a,b,ha,hb,hna,hnb,ht,hmin⟩ :=
    source_nonseparating_geometric_intersection_attained S α β
  have hcard : 1 < ht.1.toFinset.card := by rw [hmin]; exact hlarge
  obtain ⟨u,v,hu,hv,huv⟩ := Finset.one_lt_card_iff.mp hcard
  have hu' : u ∈ a.val.image ∩ b.val.image := by simpa using hu
  have hv' : v ∈ a.val.image ∩ b.val.image := by simpa using hv
  obtain ⟨w,huw,hw,f,g,hf,hg,hf0,hg0,hf1,hg1,hfb,hga,havoid,hmeet,c,hc,hcompact⟩ :=
    LocalSurgery.source_two_curve_first_return_boundary b.val a.val
      (transverse_symm_of_chart ht) u v ⟨hu'.2,hu'.1⟩ ⟨hv'.2,hv'.1⟩ huv
  refine ⟨a,b,ha,hb,hna,hnb,ht,hmin,?_⟩
  exact ⟨{
    start := u, finish := w, distinct := huw,
    start_mem := ⟨hu'.2,hu'.1⟩, finish_mem := hw,
    first := f, second := g, first_embedded := hf, second_embedded := hg,
    first_zero := hf0, second_zero := hg0, first_one := hf1, second_one := hg1,
    first_subset := hfb, second_subset := hga, first_interior_avoids := havoid,
    intersection := hmeet, boundary := c, boundary_image := hc,
    boundary_compact := hcompact }⟩

end CurveComplex

#print axioms CurveComplex.source_nonseparating_complement_pathConnected
#print axioms CurveComplex.source_nonseparating_complement_path
#print axioms CurveComplex.source_nonseparating_complement_path_avoids
#print axioms CurveComplex.source_nonseparating_minimal_first_return
