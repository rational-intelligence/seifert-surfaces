import Mathlib

open Topology Set Filter
open scoped unitInterval Manifold

namespace CurveComplex

/-- A compact set avoiding a closed obstacle has finitely many chart-local compact
neighborhoods which still avoid that obstacle. -/
theorem compact_finite_chart_neighborhoods
    {S : Type*} [TopologicalSpace S] [T2Space S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (K F : Set S) (hK : IsCompact K) (hF : IsClosed F) (hKF : Disjoint K F) :
    ∃ (centers : Finset K) (C : K → Set S),
      (∀ z, IsCompact (C z) ∧ C z ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) z.val).source ∧
        Disjoint (C z) F) ∧
      K ⊆ ⋃ z ∈ centers, interior (C z) := by
  classical
  letI : LocallyCompactSpace S := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 2)) S
  have hlocal (z : K) : ∃ C : Set S, C ∈ 𝓝 z.val ∧
      C ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) z.val).source ∩ Fᶜ ∧ IsCompact C := by
    apply local_compact_nhds
    exact ((chartAt (EuclideanSpace ℝ (Fin 2)) z.val).open_source.inter
      hF.isOpen_compl).mem_nhds ⟨mem_chart_source _ z.val,
        fun hz => Set.disjoint_left.mp hKF z.property hz⟩
  choose C hCn hCs hCc using hlocal
  have cov : K ⊆ ⋃ z : K, interior (C z) := by
    intro z hz
    exact mem_iUnion.mpr ⟨⟨z,hz⟩, mem_interior_iff_mem_nhds.mpr (hCn ⟨z,hz⟩)⟩
  obtain ⟨centers,hcov⟩ := hK.elim_finite_subcover (fun z => interior (C z))
    (fun _ => isOpen_interior) cov
  refine ⟨centers,C,?_,hcov⟩
  intro z
  exact ⟨hCc z, fun x hx => (hCs z hx).1,
    Set.disjoint_left.mpr (fun x hx hf => (hCs z hx).2 hf)⟩



/-- Trimming both ends of an embedded attaching arc removes all intersection
with the crossing square. -/
theorem trimmed_arc_disjoint_attachment
    {S : Type*} [TopologicalSpace S] {x y : S} (p : Path x y)
    (hp : Topology.IsEmbedding p) (D : Set S)
    (hattach : Set.range p ∩ D = {x,y})
    (l r : I) (hl : 0 < l) (hr : r < 1) :
    Disjoint (p '' Icc l r) D := by
  rw [Set.disjoint_left]
  rintro z ⟨t,ht,rfl⟩ hz
  have he : p t ∈ ({x,y} : Set S) := hattach ▸ ⟨Set.mem_range_self t,hz⟩
  rcases he with he | he
  · have ht0 : t = 0 := hp.injective (he.trans p.source.symm)
    rw [ht0] at ht
    exact (not_le_of_gt hl) ht.1
  · have ht1 : t = 1 := hp.injective (he.trans p.target.symm)
    rw [ht1] at ht
    exact (not_le_of_gt hr) ht.2

/-- A trimmed outside arc admits a finite collection of compact chart patches
whose entire closures avoid the square and the other outside arc. -/
theorem outside_arc_finite_chart_neighborhoods
    {S : Type*} [TopologicalSpace S] [T2Space S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    {x y u v : S} (p : Path x y) (q : Path u v)
    (hp : Topology.IsEmbedding p) (D : Set S) (hD : IsCompact D)
    (hattach : Set.range p ∩ D = {x,y})
    (hdisj : Disjoint (Set.range p) (Set.range q))
    (l r : I) (hl : 0 < l) (hr : r < 1) :
    ∃ (centers : Finset (p '' Icc l r)) (C : (p '' Icc l r) → Set S),
      (∀ z, IsCompact (C z) ∧ C z ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) z.val).source ∧
        Disjoint (C z) (D ∪ Set.range q)) ∧
      p '' Icc l r ⊆ ⋃ z ∈ centers, interior (C z) := by
  apply compact_finite_chart_neighborhoods
  · exact isCompact_Icc.image p.continuous
  · exact hD.isClosed.union (isCompact_range q.continuous).isClosed
  · exact disjoint_union_right.mpr
      ⟨trimmed_arc_disjoint_attachment p hp D hattach l r hl hr,
        hdisj.mono_left (Set.image_subset_range _ _)⟩

/-- Every path admits a finite monotone subdivision whose successive closed
subarcs lie in individual surface charts. -/
theorem path_finite_chart_subdivision
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    {x y : S} (p : Path x y) :
    ∃ t : ℕ → I, t 0 = 0 ∧ Monotone t ∧ (∃ n, ∀ m ≥ n, t m = 1) ∧
      ∀ n, ∃ z : S, p '' Icc (t n) (t (n+1)) ⊆
        (chartAt (EuclideanSpace ℝ (Fin 2)) z).source := by
  obtain ⟨t,ht0,htmono,htend,hcharts⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (c := fun z : S => p ⁻¹' (chartAt (EuclideanSpace ℝ (Fin 2)) z).source)
      (fun z => (chartAt (EuclideanSpace ℝ (Fin 2)) z).open_source.preimage p.continuous)
      (fun a _ => mem_iUnion.mpr ⟨p a,mem_chart_source _ (p a)⟩)
  refine ⟨t,ht0,htmono,htend,?_⟩
  intro n
  obtain ⟨z,hz⟩ := hcharts n
  exact ⟨z, Set.image_subset_iff.mpr hz⟩

/-- Around any point of an embedded arc, a compact chart patch can be chosen
inside a prescribed parameter window and away from a closed obstacle. The
window condition excludes all distant returns of the same embedded arc. -/
theorem embedded_arc_isolated_compact_chart_patch
    {S : Type*} [TopologicalSpace S] [T2Space S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    {x y : S} (p : Path x y) (hp : Topology.IsEmbedding p)
    (t : I) (W : Set I) (hW : IsOpen W) (htW : t ∈ W)
    (F : Set S) (hF : IsClosed F) (htF : p t ∉ F) :
    ∃ C : Set S, IsCompact C ∧ p t ∈ interior C ∧
      C ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) (p t)).source ∧
      Disjoint C F ∧ Set.range p ∩ C ⊆ p '' W := by
  letI : LocallyCompactSpace S := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 2)) S
  have hbad : IsClosed (p '' Wᶜ) := (hW.isClosed_compl.isCompact.image p.continuous).isClosed
  have htbad : p t ∉ p '' Wᶜ := by
    rintro ⟨s,hs,he⟩
    exact hs (hp.injective he ▸ htW)
  obtain ⟨C,hCn,hCs,hCc⟩ := local_compact_nhds
    (((chartAt (EuclideanSpace ℝ (Fin 2)) (p t)).open_source.inter
      (hF.isOpen_compl.inter hbad.isOpen_compl)).mem_nhds
      ⟨mem_chart_source _ (p t),htF,htbad⟩)
  refine ⟨C,hCc,mem_interior_iff_mem_nhds.mpr hCn,
    fun z hz => (hCs hz).1,
    Set.disjoint_left.mpr (fun z hz hf => (hCs hz).2.1 hf),?_⟩
  rintro z ⟨⟨s,rfl⟩,hz⟩
  refine ⟨s,?_,rfl⟩
  by_contra hs
  exact (hCs hz).2.2 ⟨s,hs,rfl⟩

/-- Compact collections of arc parameters have a finite cover by patches with
prescribed branch-isolating windows. This does not assume any local flattening. -/
theorem embedded_arc_finite_isolated_chart_patches
    {S : Type*} [TopologicalSpace S] [T2Space S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    {x y : S} (p : Path x y) (hp : Topology.IsEmbedding p)
    (T : Set I) (hT : IsCompact T)
    (W : T → Set I) (hW : ∀ t, IsOpen (W t)) (htW : ∀ t, t.val ∈ W t)
    (F : Set S) (hF : IsClosed F) (hTF : Disjoint (p '' T) F) :
    ∃ (centers : Finset T) (C : T → Set S),
      (∀ t, IsCompact (C t) ∧ p t.val ∈ interior (C t) ∧
        C t ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) (p t.val)).source ∧
        Disjoint (C t) F ∧ Set.range p ∩ C t ⊆ p '' W t) ∧
      p '' T ⊆ ⋃ t ∈ centers, interior (C t) := by
  classical
  choose C hCc hCt hCchart hCF hCbranch using fun t : T =>
    embedded_arc_isolated_compact_chart_patch p hp t.val (W t) (hW t) (htW t)
      F hF (fun hf => Set.disjoint_left.mp hTF ⟨t.val,t.property,rfl⟩ hf)
  have hcov : p '' T ⊆ ⋃ t : T, interior (C t) := by
    rintro z ⟨t,ht,rfl⟩
    exact mem_iUnion.mpr ⟨⟨t,ht⟩,hCt ⟨t,ht⟩⟩
  obtain ⟨centers,hcenters⟩ := (hT.image p.continuous).elim_finite_subcover
    (fun t => interior (C t)) (fun _ => isOpen_interior) hcov
  exact ⟨centers,C,fun t => ⟨hCc t,hCt t,hCchart t,hCF t,hCbranch t⟩,hcenters⟩

/-- Actual chart balls, not an assumed regular neighborhood: every open
neighborhood of a surface point contains a compact connected chart disk whose
open inner disk contains that point. -/
theorem exists_compact_chart_disk_in_open
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (x : S) (U : Set S) (hU : IsOpen U) (hxU : x ∈ U) :
    let e := chartAt (EuclideanSpace ℝ (Fin 2)) x
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall (e x) r ⊆ e.target ∧
      e.symm '' Metric.closedBall (e x) r ⊆ U ∧
      IsCompact (e.symm '' Metric.closedBall (e x) r) ∧
      IsConnected (e.symm '' Metric.closedBall (e x) r) ∧
      IsOpen (e.symm '' Metric.ball (e x) r) ∧
      x ∈ e.symm '' Metric.ball (e x) r := by
  dsimp only
  let e := chartAt (EuclideanSpace ℝ (Fin 2)) x
  have hx : x ∈ e.source := mem_chart_source _ x
  have hopen : IsOpen (e.target ∩ e.symm ⁻¹' U) := e.isOpen_inter_preimage_symm hU
  have hmem : e x ∈ e.target ∩ e.symm ⁻¹' U :=
    ⟨e.map_source hx,by simpa only [Set.mem_preimage,e.left_inv hx] using hxU⟩
  obtain ⟨δ,hδ,hδsub⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hmem)
  have hr : 0 < δ / 2 := half_pos hδ
  have hsub : Metric.closedBall (e x) (δ/2) ⊆ e.target ∩ e.symm ⁻¹' U := by
    intro z hz
    exact hδsub (Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hz).trans_lt
      (half_lt_self hδ)))
  have ht : Metric.closedBall (e x) (δ/2) ⊆ e.target := fun z hz => (hsub hz).1
  have hc : ContinuousOn e.symm (Metric.closedBall (e x) (δ/2)) :=
    e.continuousOn_symm.mono ht
  refine ⟨δ/2,hr,ht,?_,(isCompact_closedBall _ _).image_of_continuousOn hc,
    (Metric.isConnected_closedBall hr.le).image e.symm hc,?_,?_⟩
  · exact Set.image_subset_iff.mpr (fun z hz => (hsub hz).2)
  · exact e.symm.isOpen_image_of_subset_source Metric.isOpen_ball
      (fun z hz => ht (Metric.ball_subset_closedBall hz))
  · exact ⟨e x,Metric.mem_ball_self hr,e.left_inv hx⟩

/-- Compact connected subsets of a surface have compact connected neighborhoods
inside any prescribed open set, constructed from finitely many actual chart
disks. No assertion about the frontier or regular-neighborhood type is made. -/
theorem compact_connected_surface_thickening
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (K U : Set S) (hK : IsCompact K) (hcK : IsConnected K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ N : Set S, IsCompact N ∧ IsConnected N ∧ K ⊆ interior N ∧ N ⊆ U := by
  classical
  have hlocal (x : K) : ∃ C : Set S, IsCompact C ∧ IsConnected C ∧
      x.val ∈ interior C ∧ C ⊆ U := by
    obtain ⟨r,hr,ht,hsub,hcomp,hconn,hop,hin⟩ :=
      exists_compact_chart_disk_in_open x.val U hU (hKU x.property)
    let e := chartAt (EuclideanSpace ℝ (Fin 2)) x.val
    refine ⟨e.symm '' Metric.closedBall (e x.val) r,hcomp,hconn,?_,hsub⟩
    exact (interior_mono (Set.image_mono Metric.ball_subset_closedBall))
      (by rwa [IsOpen.interior_eq hop])
  choose C hCc hCconn hxC hCU using hlocal
  obtain ⟨centers,hcov⟩ := hK.elim_finite_subcover (fun x => interior (C x))
    (fun _ => isOpen_interior)
    (fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,hxC ⟨x,hx⟩⟩)
  have conn (f : Finset K) : IsConnected (K ∪ ⋃ x ∈ f, C x) := by
    induction f using Finset.induction_on with
    | empty => simpa using hcK
    | @insert x f hx ih =>
      have heq : (K ∪ ⋃ z ∈ insert x f, C z) = (K ∪ ⋃ z ∈ f, C z) ∪ C x := by
        ext z
        simp only [Finset.mem_insert, Set.mem_union, Set.mem_iUnion]
        aesop
      rw [heq]
      exact ih.union ⟨x.val,Or.inl x.property,interior_subset (hxC x)⟩ (hCconn x)
  refine ⟨K ∪ ⋃ x ∈ centers, C x,
    hK.union (centers.isCompact_biUnion (fun x _ => hCc x)),conn centers,?_,?_⟩
  · intro x hx
    obtain ⟨z,hz,hin⟩ := mem_iUnion₂.mp (hcov hx)
    apply interior_mono (show C z ⊆ K ∪ ⋃ z ∈ centers, C z from
      fun w hw => Or.inr (mem_iUnion₂.mpr ⟨z,hz,hw⟩)) hin
  · exact union_subset hKU (iUnion₂_subset fun z _ => hCU z)

/-- Two disjoint outside arcs have disjoint compact connected thickened cores,
separated from the crossing square. Their frontier shape is deliberately not
asserted: the remaining rectangular band construction must establish it. -/
theorem outside_arcs_disjoint_compact_connected_cores
    {S : Type*} [TopologicalSpace S] [T2Space S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    {x y u v : S} (p : Path x y) (q : Path u v)
    (hp : Topology.IsEmbedding p) (hq : Topology.IsEmbedding q)
    (D : Set S) (hD : IsCompact D)
    (hpa : Set.range p ∩ D = {x,y}) (hqa : Set.range q ∩ D = {u,v})
    (hpq : Disjoint (Set.range p) (Set.range q))
    (l r : I) (hl : 0 < l) (hlr : l ≤ r) (hr : r < 1) :
    ∃ Np Nq : Set S,
      IsCompact Np ∧ IsConnected Np ∧ IsCompact Nq ∧ IsConnected Nq ∧
      p '' Icc l r ⊆ interior Np ∧ q '' Icc l r ⊆ interior Nq ∧
      Disjoint Np Nq ∧ Disjoint Np D ∧ Disjoint Nq D := by
  have hpD := trimmed_arc_disjoint_attachment p hp D hpa l r hl hr
  have hqD := trimmed_arc_disjoint_attachment q hq D hqa l r hl hr
  have hcp : IsConnected (p '' Icc l r) :=
    (isConnected_Icc hlr).image p p.continuous.continuousOn
  have hcq : IsConnected (q '' Icc l r) :=
    (isConnected_Icc hlr).image q q.continuous.continuousOn
  obtain ⟨Np,hNpc,hNpn,hpNp,hNpavoid⟩ := compact_connected_surface_thickening
    (p '' Icc l r) (D ∪ Set.range q)ᶜ (isCompact_Icc.image p.continuous) hcp
    ((hD.isClosed.union (isCompact_range q.continuous).isClosed).isOpen_compl)
    (fun z hz hf => by
      rcases hf with h | h
      · exact Set.disjoint_left.mp hpD hz h
      · exact Set.disjoint_left.mp hpq (Set.image_subset_range p _ hz) h)
  have hqNp : Disjoint (q '' Icc l r) Np := by
    rw [Set.disjoint_left]
    intro z hz hn
    exact hNpavoid hn (Or.inr (Set.image_subset_range q _ hz))
  obtain ⟨Nq,hNqc,hNqn,hqNq,hNqavoid⟩ := compact_connected_surface_thickening
    (q '' Icc l r) (D ∪ Np)ᶜ (isCompact_Icc.image q.continuous) hcq
    ((hD.isClosed.union hNpc.isClosed).isOpen_compl)
    (fun z hz hf => by
      rcases hf with h | h
      · exact Set.disjoint_left.mp hqD hz h
      · exact Set.disjoint_left.mp hqNp hz h)
  exact ⟨Np,Nq,hNpc,hNpn,hNqc,hNqn,hpNp,hqNq,
    Set.disjoint_left.mpr (fun z hpz hqz => hNqavoid hqz (Or.inr hpz)),
    Set.disjoint_left.mpr (fun z hn hd => hNpavoid hn (Or.inl hd)),
    Set.disjoint_left.mpr (fun z hn hd => hNqavoid hn (Or.inl hd))⟩

#print axioms compact_finite_chart_neighborhoods
#print axioms trimmed_arc_disjoint_attachment
#print axioms outside_arc_finite_chart_neighborhoods
#print axioms path_finite_chart_subdivision
#print axioms embedded_arc_isolated_compact_chart_patch
#print axioms embedded_arc_finite_isolated_chart_patches
#print axioms exists_compact_chart_disk_in_open
#print axioms compact_connected_surface_thickening
#print axioms outside_arcs_disjoint_compact_connected_cores
end CurveComplex
