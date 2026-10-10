import B1ActualGermSeed_v475

noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
universe u
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
/-- Small chart domains have a connected, nonempty manifold interior, also at boundary centers. -/
theorem native_surface_connected_interior_chart_neighborhood_v475 (S : CompactOrientedSurface.{u}) (p : S) :
    ∃ U : Set S, IsOpen U ∧ p ∈ U ∧ U ⊆ (extChartAt (𝓡∂ 2) p).source ∧
      IsPreconnected (U ∩ (𝓡∂ 2).interior S) ∧ (U ∩ (𝓡∂ 2).interior S).Nonempty := by
  let c := extChartAt (𝓡∂ 2) p
  let y := c p
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhdsWithin_iff.mp
    (extChartAt_target_mem_nhdsWithin (I := 𝓡∂ 2) p)
  let U : Set S := c.source ∩ c ⁻¹' Metric.ball y r
  let V : Set (Euc 2) := Metric.ball y r ∩ interior (range (𝓡∂ 2))
  have hVopen : IsOpen V := Metric.isOpen_ball.inter isOpen_interior
  have hVsub : V ⊆ c.target := fun z hz => hball ⟨hz.1,interior_subset hz.2⟩
  have hVint : V ⊆ interior c.target := by
    rw [← hVopen.interior_eq]
    exact interior_mono hVsub
  have hUopen : IsOpen U := isOpen_extChartAt_preimage' p Metric.isOpen_ball
  have hpeq : p ∈ U := ⟨mem_extChartAt_source p,Metric.mem_ball_self hr⟩
  have himage : c.symm '' V = U ∩ (𝓡∂ 2).interior S := by
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      have hzs := c.map_target (hVsub hz)
      have hright := c.right_inv (hVsub hz)
      refine ⟨⟨hzs,by simpa only [mem_preimage,hright] using hz.1⟩,?_⟩
      change (𝓡∂ 2).IsInteriorPoint (c.symm z)
      apply ((𝓡∂ 2).isInteriorPoint_iff_of_mem_atlas (n := (∞ : ℕ∞ω)) (by simp)
        (chart_mem_atlas (EuclideanHalfSpace 2) p)
        (by simpa only [c,extChartAt_source] using hzs)).mpr
      change c (c.symm z) ∈ interior c.target
      rw [hright]
      exact hVint hz
    · rintro ⟨hx,hi⟩
      have hxi : c x ∈ interior c.target := by
        exact ((𝓡∂ 2).isInteriorPoint_iff_of_mem_atlas (n := (∞ : ℕ∞ω)) (by simp)
          (chart_mem_atlas (EuclideanHalfSpace 2) p)
          (by simpa only [c,extChartAt_source] using hx.1)).mp hi
      refine ⟨c x,⟨hx.2,?_⟩,c.left_inv hx.1⟩
      exact interior_mono (extChartAt_target_subset_range p) hxi
  have hVpre : IsPreconnected V :=
    ((convex_ball y r).inter (𝓡∂ 2).convex_range.interior).isPreconnected
  have hVnon : V.Nonempty := by
    have hy : y ∈ closure (interior (range (𝓡∂ 2))) :=
      (𝓡∂ 2).range_subset_closure_interior (mem_range_self _)
    obtain ⟨z,hzball,hzint⟩ := mem_closure_iff.mp hy (Metric.ball y r)
      Metric.isOpen_ball (Metric.mem_ball_self hr)
    exact ⟨z,hzball,hzint⟩
  refine ⟨U,hUopen,hpeq,inter_subset_left,?_,?_⟩
  · rw [←himage]
    exact hVpre.image c.symm ((continuousOn_extChartAt_symm p).mono hVsub)
  · rw [←himage]
    exact hVnon.image c.symm


/-- The actual manifold interior is dense in the entire source, including its
boundary. This is proved through the chart target, rather than from an
arbitrary closed boundary predicate. -/
theorem native_surface_interior_dense_v475 (S : CompactOrientedSurface.{u}) :
    closure ((𝓡∂ 2).interior S) = univ := by
  apply eq_univ_of_forall
  intro p
  apply mem_closure_iff_nhds.mpr
  intro U hU
  let c := extChartAt (𝓡∂ 2) p
  have hUp : U ∩ c.source ∈ 𝓝 p :=
    inter_mem hU ((isOpen_extChartAt_source p).mem_nhds (mem_extChartAt_source p))
  have himage : c '' (U ∩ c.source) ∈ 𝓝[range (𝓡∂ 2)] (c p) := by
    rw [← map_extChartAt_nhds p]
    exact Filter.image_mem_map hUp
  obtain ⟨V,hV,hVimage⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp himage
  have hy : c p ∈ closure (interior (range (𝓡∂ 2))) :=
    (𝓡∂ 2).range_subset_closure_interior (mem_range_self _)
  obtain ⟨y,hyV,hyint⟩ := mem_closure_iff_nhds.mp hy V hV
  obtain ⟨q,hq,hqy⟩ := hVimage ⟨hyV,interior_subset hyint⟩
  refine ⟨q,hq.1,?_⟩
  have hyt : y ∈ c.target := hqy ▸ c.map_source hq.2
  have hyti : y ∈ interior c.target := by
    exact (extChartAt_target_eventuallyEqSet_of_mem hyt).symm.mem_interior hyint
  exact ((𝓡∂ 2).isInteriorPoint_iff_of_mem_atlas (n := ∞) (by simp)
    (chart_mem_atlas (EuclideanHalfSpace 2) p)
    (by simpa only [c,extChartAt_source] using hq.2)).mpr (hqy ▸ hyti)

/-- Removing the manifold boundary preserves preconnectedness of a connected
smooth surface. Local half-ball interiors prevent a separating boundary. -/
theorem native_surface_interior_preconnected_v475
    (S : CompactOrientedSurface.{u}) [ConnectedSpace S] :
    IsPreconnected ((𝓡∂ 2).interior S) := by
  let I : Set S := (𝓡∂ 2).interior S
  apply isPreconnected_closed_iff.mpr
  intro t v ht hv hcover hIt hIv
  by_contra hno
  let A := I ∩ t
  let B := I ∩ v
  have hIAB : I ⊆ A ∪ B := by
    intro x hx
    rcases hcover hx with hxt | hxv
    · exact Or.inl ⟨hx,hxt⟩
    · exact Or.inr ⟨hx,hxv⟩
  have hcov : univ ⊆ closure A ∪ closure B := by
    rw [← closure_union,← native_surface_interior_dense_v475 S]
    exact closure_mono hIAB
  obtain ⟨p,hpu,hpa,hpb⟩ := isPreconnected_closed_iff.mp
    (isPreconnected_univ : IsPreconnected (univ : Set S))
    (closure A) (closure B) isClosed_closure isClosed_closure hcov
    (by obtain ⟨x,hx⟩ := hIt; exact ⟨x,mem_univ _,subset_closure hx⟩)
    (by obtain ⟨x,hx⟩ := hIv; exact ⟨x,mem_univ _,subset_closure hx⟩)
  obtain ⟨U,hU,hpU,hUc,hconn,hne⟩ := native_surface_connected_interior_chart_neighborhood_v475 S p
  obtain ⟨a,haU,haI,hat⟩ := mem_closure_iff_nhds.mp hpa U (hU.mem_nhds hpU)
  obtain ⟨b,hbU,hbI,hbv⟩ := mem_closure_iff_nhds.mp hpb U (hU.mem_nhds hpU)
  obtain ⟨z,hzUI,hzt,hzv⟩ := isPreconnected_closed_iff.mp hconn t v ht hv
    (fun x hx => hcover hx.2) ⟨a,⟨haU,haI⟩,hat⟩ ⟨b,⟨hbU,hbI⟩,hbv⟩
  exact hno ⟨z,hzUI.2,hzt,hzv⟩

#print axioms native_surface_interior_preconnected_v475

#print axioms native_surface_interior_dense_v475

#print axioms native_surface_connected_interior_chart_neighborhood_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
