import Section5StraightenedRealGraphsV489
import Section5NativeStrictConvexityV481
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
open Set Function Filter Manifold Topology
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.Complexity SeifertSurfaces.GenusLinking Section4
noncomputable section
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}

/-- The original minimizers themselves produce every field of the exact
Appendix B collar record; no collar or graph is assumed. -/
theorem original_minimizer_common_leaf_data (H : Section4.SourceGeometry E)
    (A B : IncompressibleSpanningSurface.{0} E)
    (hA : IsRelativeAreaMinimizer H.metric H.foliation A)
    (hB : IsRelativeAreaMinimizer H.metric H.foliation B)
    (hAB : graphDistance E (SurfaceVertex E A) (SurfaceVertex E B) = 2)
    (hcommon : SurfaceBoundary E A = SurfaceBoundary E B) :
    ∃ D : B1OriginalData H.metric H.foliation, D.A = A ∧ D.B = B := by
  obtain ⟨a,U,hU,hbd,r,hr,b,hb,V,C,Phi,d0,hd0,hd0small,hAgraph,hBgraph,
    hAgsmooth,hBgsmooth,hgzero,hC0,hCr,hgraphs,hlabels,hflow⟩ :=
    actual_common_leaf_circle_graphs H.ambient H.foliation A B hA.1 hB.1 hcommon
  obtain ⟨d,hd,hdd0,hd1,FA,FB,hFA,hFB,hFzero,hFlift⟩ :=
    common_circle_graphs_real_pair a hAgraph hBgraph hd0 hAgsmooth hBgsmooth hgzero
      (show (0:ℝ)<1 by norm_num)
  obtain ⟨rho,hrho⟩ := unit_leaf_parameter_diffeomorph H.metric H.foliation a
  have hdsmall : d ≤ 1/4 := hdd0.le.trans hd0small.le
  have hXA (q : longitudeProductStrip) (hq : (q.val.2:ℝ) ≤ d) :
      (C q : E.Carrier) ∈ A.1.image ↔
        q.val.1.1 = longitudeLabelFlow (FA (q.val.1.2,(q.val.2:ℝ))) a := by
    rw [(hFlift q.val.1.2 q.val.2 hq).1]
    exact (hgraphs q (hq.trans hdd0.le)).1
  have hXB (q : longitudeProductStrip) (hq : (q.val.2:ℝ) ≤ d) :
      (C q : E.Carrier) ∈ B.1.image ↔
        q.val.1.1 = longitudeLabelFlow (FB (q.val.1.2,(q.val.2:ℝ))) a := by
    rw [(hFlift q.val.1.2 q.val.2 hq).2.1]
    exact (hgraphs q (hq.trans hdd0.le)).2
  obtain ⟨a0,hAa0,hBa0⟩ := common_boundary_label H.foliation A B hA.1 hB.1 hcommon
  have haa : a0 = a := by
    let q : longitudeProductStrip := ⟨((a0,1),0),by change (0:ℝ)<1; norm_num⟩
    have hmem : (C q : E.Carrier) ∈ A.1.image := by
      have hm : H.foliation.torus (a0,1) ∈ H.foliation.leaf a0 := ⟨1,rfl⟩
      rw [← hAa0] at hm
      obtain ⟨x,hx,he⟩ := hm
      rw [hC0 (a0,1)]
      exact ⟨x,he⟩
    have hh := ((hgraphs q (by change (0:ℝ) ≤ d0; exact hd0.le)).1).mp hmem
    change a0 = hAgraph (1,0) at hh
    exact hh.trans (hgzero 1).1
  subst a0
  let kappa := straightenedRealCollar a rho FB d hd hd1 V C (b*d)
  let f := straightenedRealHeight rho FA FB b
  have hR : 0 < b*d := mul_pos hb hd
  have hkU (p : T2Coordinate) : kappa p ∈ U :=
    (hCr (straightenedStripPoint a rho FB d hd hd1 (radialCylinderRescaling (b*d) p))).1
  have hradial (p : T2Coordinate) (hp : p ∈ halfCylinder (b*d) 1) : r (kappa p) = p.2.1 :=
    straightened_real_collar_radial a rho FB d hd hd1 V C b hb r (fun q => (hCr q).2) p hp
  have hinside (s : Circle) (x : ℝ) (hx : x ∈ Icc (0:ℝ) (b*d)) : |f s x| < 1 := by
    have hxd : x/b ≤ d := (div_le_iff₀ hb).mpr (by simpa [mul_comm] using hx.2)
    let t : Time := ⟨x/b,div_nonneg hx.1 hb.le,hxd.trans hd1.le⟩
    exact (hFlift (rho s) t hxd).2.2.2.1
  have hmemA (p : T2Coordinate) (hp : p ∈ halfCylinder (b*d) 1) :
      kappa p ∈ A.1.image ↔ p.2.2 = f p.1 p.2.1 :=
    straightened_real_collar_mem_iff a rho FB d hd hd1 V C b hb FA A.1.image hXA
      (fun z t ht => (hFlift z t ht).2.2.2.1.le) p hp
  have hmemB (p : T2Coordinate) (hp : p ∈ halfCylinder (b*d) 1) :
      kappa p ∈ B.1.image ↔ p.2.2 = 0 := by
    simpa only [straightenedRealHeight,sub_self] using
      straightened_real_collar_mem_iff a rho FB d hd hd1 V C b hb FB B.1.image hXB
        (fun z t ht => by simp) p hp
  refine ⟨{
    boundary_strictly_convex := WholeAssemblyV480.source_geometry_strictly_convex H
    A := A
    B := B
    A_relative_minimum := hA
    B_relative_minimum := hB
    foliation_analytic := H.analytic
    distance_two := hAB
    boundaryLabel := a
    A_boundary := hAa0
    B_boundary := hBa0
    leafParameter := longitudeUnitParameter H.metric H.foliation a
    leafParameter_embedding := longitude_unit_parameter_smoothEmbedding H.metric H.foliation a
    leafParameter_image := longitude_unit_parameter_image H.metric H.foliation a
    leafLength := longitudeLength H.metric H.foliation a
    leafLength_pos := longitude_length_positive H.metric H.foliation a
    leaf_arclength := longitude_unit_parameter_arclength H.metric H.foliation a
    r0 := b*d
    r0_pos := hR
    eta := 1
    eta_pos := by norm_num
    collar := kappa
    collar_smooth := straightened_real_collar_smooth a rho FB hFB d hd hd1 V C (b*d) hR 1
    collar_embedding := straightened_real_collar_embedding a rho FB hFB d hd hd1 V C (b*d) hR
    collar_immersion := straightened_real_collar_immersion a rho FB hFB d hd hd1 V C (b*d) hR 1
    collar_boundary := ?_
    collar_leaf := ?_
    radialCoordinate := r
    radial_exact := hradial
    radial_inward_distance := ?_
    sourceFlow := Phi
    collar_flow := ?_
    f := f
    extendedDomain := univ
    extendedDomain_open := isOpen_univ
    extendedDomain_contains := subset_univ _
    f_smooth := (straightened_real_height_smooth rho FA FB hFA hFB b).contMDiffOn
    f_boundary_zero := ?_
    graph_inside := hinside
    A_graph_exact := exact_graph_image_of_membership kappa A.1.image f hinside hmemA
    B_graph_exact := exact_graph_image_of_membership kappa B.1.image (fun _ _ => 0)
      (fun _ _ _ => by norm_num) hmemB
    },rfl,rfl⟩
  · intro p hp
    rw [hr.2.2.1 _ (hkU p),hradial p hp]
  · intro s
    exact (straightened_real_collar_leaf a rho FB d hd hd1 V C b (fun z => (hFzero z).2)
      H.foliation hC0 s).trans (hrho s)
  · exact inward_distance_restrict_unique H.metric hr (by rintro _ ⟨p,hp,rfl⟩; exact hkU p)
      (straightened_real_collar_image_unique a rho FB hFB d hd hd1 V C (b*d) hR 1)
  · intro s x y hx hy
    exact straightened_real_collar_flow a rho FB d hd hd1 V C b hdsmall H.foliation Phi hflow s x y
  · intro s
    change FA (rho s,0/b)-FB (rho s,0/b) = 0
    rw [zero_div,(hFzero _).1,(hFzero _).2,sub_self]

#print axioms original_minimizer_common_leaf_data
end
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
