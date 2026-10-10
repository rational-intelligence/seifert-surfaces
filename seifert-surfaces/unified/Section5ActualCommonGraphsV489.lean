import Section5ActualSurfaceGraphV489
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
open Set Function Filter Manifold Topology
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
noncomputable section
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}

/-- Original common-boundary surfaces are both actual graphs in one and the
same distance collar, with a single positive radial size and exact images. -/
theorem actual_common_leaf_circle_graphs (G : A7.SourceGeometry E)
    (J : LongitudeFoliation.{0} E) (A B : IncompressibleSpanningSurface.{0} E)
    (hA : J.BoundaryIn A.1.embedding.toFun) (hB : J.BoundaryIn B.1.embedding.toFun)
    (hcommon : SurfaceBoundary E A = SurfaceBoundary E B) :
    ∃ a : Circle, ∃ U : Set E.Carrier, IsOpen U ∧ (𝓡∂ 3).boundary E.Carrier ⊆ U ∧
    ∃ r : E.Carrier → ℝ, IsInwardDistanceCoordinate G.metric U r ∧
    ∃ b : ℝ, 0 < b ∧ ∃ V : TopologicalSpace.Opens E.Carrier,
    ∃ C : Diffeomorph (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) (𝓡∂ 3) longitudeProductStrip V ∞,
    ∃ Phi : B1SourceFoliationFlow J,
    ∃ d : ℝ, 0 < d ∧ d < 1/4 ∧ ∃ hA hB : Circle × Time → Circle,
      ContMDiffOn ((𝓡 1).prod (𝓡∂ 1)) (𝓡 1) ∞ hA {p | (p.2:ℝ) ≤ d} ∧
      ContMDiffOn ((𝓡 1).prod (𝓡∂ 1)) (𝓡 1) ∞ hB {p | (p.2:ℝ) ≤ d} ∧
      (∀ z, hA (z,0) = a ∧ hB (z,0) = a) ∧
      (∀ p : Circle × Circle,
        (C ⟨(p,0),by change (0:ℝ)<1; norm_num⟩ : E.Carrier) = J.torus p) ∧
      (∀ q : longitudeProductStrip, (C q : E.Carrier) ∈ U ∧ r (C q : E.Carrier) = b*(q.val.2:ℝ)) ∧
      (∀ q : longitudeProductStrip, (q.val.2:ℝ) ≤ d →
        ((C q : E.Carrier) ∈ A.1.image ↔ q.val.1.1 = hA (q.val.1.2,q.val.2)) ∧
        ((C q : E.Carrier) ∈ B.1.image ↔ q.val.1.1 = hB (q.val.1.2,q.val.2))) ∧
      Phi.labels = longitudeLabelFlow ∧
      (∀ t : ℝ, ∀ q : longitudeProductStrip,
        Phi.ambient t (C q : E.Carrier) = (C (longitudeStripFlow t q) : E.Carrier)) := by
  obtain ⟨a,haA,haB⟩ := common_boundary_label J A B hA hB hcommon
  obtain ⟨U,hU,hbd,r,hr,b,hb,V,C,m,Phi,hm,hmc,hmb,hmr,hVU,hbdV,hlabels,hflow,_⟩ :=
    actual_distance_compatible_leaf_flow G J
  have hC0 (p : Circle × Circle) :
      (C ⟨(p,0),by change (0:ℝ)<1; norm_num⟩ : E.Carrier) = J.torus p :=
    (hmc _).symm.trans (hmb p)
  have hCr (q : longitudeProductStrip) : r (C q : E.Carrier) = b*(q.val.2:ℝ) :=
    (congrArg r (hmc q)).symm.trans (hmr q.val).2
  obtain ⟨dA,hdA,hdAone,fA,hfA,hfA0,hgraphA⟩ :=
    actual_surface_circle_graph A.1.embedding G.metric J a haA U hU r hr b V C hVU hC0 hCr
  obtain ⟨dB,hdB,hdBone,fB,hfB,hfB0,hgraphB⟩ :=
    actual_surface_circle_graph B.1.embedding G.metric J a haB U hU r hr b V C hVU hC0 hCr
  let d := min (min dA dB) (1/8)
  have hd : 0 < d := lt_min (lt_min hdA hdB) (by norm_num)
  have hddA : d ≤ dA := (min_le_left _ _).trans (min_le_left _ _)
  have hddB : d ≤ dB := (min_le_left _ _).trans (min_le_right _ _)
  refine ⟨a,U,hU,hbd,r,hr,b,hb,V,C,Phi,d,hd,
    (min_le_right _ _).trans_lt (by norm_num),fA,fB,
    hfA.mono (fun p hp => hp.trans hddA),hfB.mono (fun p hp => hp.trans hddB),
    fun z => ⟨hfA0 z,hfB0 z⟩,hC0,
    fun q => ⟨hVU (C q).property,hCr q⟩,?_,hlabels,hflow⟩
  intro q hq
  exact ⟨hgraphA q (hq.trans hddA),hgraphB q (hq.trans hddB)⟩

#print axioms actual_common_leaf_circle_graphs
end
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
