import Section5UniformBoundaryStripV489
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
open Set Function Filter Manifold Topology
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.OriginalEndpoints.Section5.SurfaceInverseV489
noncomputable section
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}

/-- The actual compact neat surface is one graph in the actual distance collar;
the equivalence excludes every other part of the original surface. -/
theorem actual_surface_circle_graph {S : CompactOrientedSurface.{0}}
    (F : NeatEmbedding S E.Carrier) (g : SmoothMetric E.Carrier)
    (J : LongitudeFoliation.{0} E) (a : Circle)
    (ha : F.toFun '' S.boundary = J.leaf a)
    (U : Set E.Carrier) (hU : IsOpen U) (r : E.Carrier → ℝ)
    (hr : IsInwardDistanceCoordinate g U r)
    (b : ℝ) (V : TopologicalSpace.Opens E.Carrier)
    (C : Diffeomorph (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) (𝓡∂ 3) longitudeProductStrip V ∞)
    (hVU : (V : Set E.Carrier) ⊆ U)
    (hC0 : ∀ p : Circle × Circle,
      (C ⟨(p,0),by change (0:ℝ)<1; norm_num⟩ : E.Carrier) = J.torus p)
    (hCr : ∀ q : longitudeProductStrip, r (C q : E.Carrier) = b*(q.val.2 : ℝ)) :
    ∃ d : ℝ, 0 < d ∧ d < 1 ∧ ∃ h : Circle × Time → Circle,
      ContMDiffOn ((𝓡 1).prod (𝓡∂ 1)) (𝓡 1) ∞ h {p | (p.2 : ℝ) ≤ d} ∧
      (∀ z, h (z,0) = a) ∧
      (∀ q : longitudeProductStrip, (q.val.2 : ℝ) ≤ d →
        ((C q : E.Carrier) ∈ F.image ↔ q.val.1.1 = h (q.val.1.2,q.val.2))) := by
  classical
  obtain ⟨W,q,beta,hq,hbeta,hqF,hbetaF,hbRange,hqB,hloc⟩ :=
    actual_surface_cylinder_projection F g J a ha U hU r hr b V C hVU hC0 hCr
  let proj : W → Circle × Time := fun x => ((q x).val.1.2,(q x).val.2)
  have hp : ContMDiff (𝓡∂ 2) ((𝓡 1).prod (𝓡∂ 1)) ∞ proj :=
    (contMDiff_subtype_val.comp hq).fst.snd.prodMk (contMDiff_subtype_val.comp hq).snd
  have hpB (z) : proj (beta z) = (z,0) := by simp only [proj,hqB]
  obtain ⟨e,he,hbs,hbt,heB⟩ := compact_surface_cylinder_inverse proj hp beta hbeta.continuous hpB hloc
  obtain ⟨d₁,hd₁,hd₁one,hd₁target⟩ := compact_boundary_uniform_strip e.open_target hbt
  let h : Circle × Time → Circle := fun p => (q (e.symm p)).val.1.1
  have hh : ContMDiffOn ((𝓡 1).prod (𝓡∂ 1)) (𝓡 1) ∞ h e.target :=
    ((contMDiff_subtype_val.comp hq).fst.fst).comp_contMDiffOn e.symm.contMDiffOn
  have hha (z) : h (z,0) = a := by simp only [h,heB,hqB]
  let N : Set S := (Subtype.val : W → S) '' e.source
  have hN : IsOpen N := W.isOpen.isOpenMap_subtype_val _ e.open_source
  have hboundaryN : S.boundary ⊆ N := by
    intro x hx
    -- The projection window is exactly the inverse image of the ambient collar.
    have hxW : x ∈ W := by
      obtain ⟨z,hz⟩ : ∃ z, F.toFun x = J.torus (a,z) := by
        have hfleaf : F.toFun x ∈ J.leaf a := ha ▸ mem_image_of_mem F.toFun hx
        obtain ⟨z,hz⟩ := hfleaf
        exact ⟨z,hz.symm⟩
      have heq : x = (beta z).val := F.smoothEmbedding.isEmbedding.injective
        (hz.trans (hbetaF z).symm)
      rw [heq]
      exact (beta z).property
    let xx : W := ⟨x,hxW⟩
    have hxb : xx ∈ (𝓡∂ 2).boundary W :=
      (𝓡∂ 2).isBoundaryPoint_iff_isBoundaryPoint_val.mpr hx
    exact ⟨xx,hbs (hbRange.symm ▸ hxb),rfl⟩
  let Bad : Set E.Carrier := F.toFun '' Nᶜ
  have hBad : IsClosed Bad :=
    (isCompact_univ.of_isClosed_subset hN.isClosed_compl (subset_univ _)).image
      F.smoothEmbedding.contMDiff.continuous |>.isClosed
  have hB0 (p : Circle × Circle) : J.torus p ∉ Bad := by
    rintro ⟨x,hx,hFx⟩
    have hxb : x ∈ S.boundary := by
      rw [← F.boundary_preimage]
      change F.toFun x ∈ (𝓡∂ 3).boundary E.Carrier
      rw [hFx]
      exact J.torus_lands_boundary p
    exact hx (hboundaryN hxb)
  let O : Set longitudeProductStrip := {p | (C p : E.Carrier) ∉ Bad}
  have hO : IsOpen O := hBad.isOpen_compl.preimage
    (continuous_subtype_val.comp C.contMDiff.continuous)
  let P : Set ((Circle × Circle) × Time) := (Subtype.val : longitudeProductStrip → _) '' O
  have hP : IsOpen P := longitudeProductStrip.isOpen.isOpenMap_subtype_val O hO
  have hP0 (p : Circle × Circle) : (p,0) ∈ P := by
    refine ⟨⟨(p,0),by change (0:ℝ)<1; norm_num⟩,?_,rfl⟩
    change (C ⟨(p,0),by change (0:ℝ)<1; norm_num⟩ : E.Carrier) ∉ Bad
    rw [hC0]
    exact hB0 p
  obtain ⟨d₂,hd₂,hd₂one,hd₂P⟩ := compact_boundary_uniform_strip hP hP0
  let d := min d₁ d₂
  have htarget (z : Circle) (t : Time) (ht : (t:ℝ) ≤ d) : (z,t) ∈ e.target :=
    hd₁target z t (ht.trans (min_le_left _ _))
  have havoid (p : longitudeProductStrip) (ht : (p.val.2:ℝ) ≤ d) : (C p : E.Carrier) ∉ Bad := by
    have hm := hd₂P p.val.1 p.val.2 (ht.trans (min_le_right _ _))
    obtain ⟨p',hp',heq⟩ := hm
    have he : p' = p := Subtype.ext heq
    change (C p' : E.Carrier) ∉ Bad at hp'
    rwa [he] at hp'
  refine ⟨d,lt_min hd₁ hd₂,(min_le_left _ _).trans_lt hd₁one,h,
    hh.mono (fun p hp => htarget p.1 p.2 hp),hha,?_⟩
  intro p ht
  constructor
  · rintro ⟨x,hx⟩
    have hxN : x ∈ N := by
      by_contra hn
      exact havoid p ht ⟨x,hn,hx⟩
    obtain ⟨xx,hxx,hxxval⟩ := hxN
    have hqp : q xx = p := C.injective (Subtype.ext
      ((hqF xx).trans ((congrArg F.toFun hxxval).trans hx)))
    have heq : e xx = (p.val.1.2,p.val.2) := by rw [he]; simp only [proj,hqp]
    have hes : e.symm (p.val.1.2,p.val.2) = xx := by
      rw [← heq]
      exact e.left_inv hxx
    change p.val.1.1 = (q (e.symm (p.val.1.2,p.val.2))).val.1.1
    rw [hes,hqp]
  · intro heq
    let y := (p.val.1.2,p.val.2)
    have hy : y ∈ e.target := htarget _ _ ht
    let xx := e.symm y
    have hproj : proj xx = y := by rw [← he]; exact e.right_inv hy
    have hqp : q xx = p := by
      apply Subtype.ext
      apply Prod.ext
      · apply Prod.ext
        · exact heq.symm
        · exact congrArg (fun u : Circle × Time => u.1) hproj
      · exact congrArg (fun u : Circle × Time => u.2) hproj
    refine ⟨xx.val,?_⟩
    rw [← hqF,hqp]

#print axioms actual_surface_circle_graph
end
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
