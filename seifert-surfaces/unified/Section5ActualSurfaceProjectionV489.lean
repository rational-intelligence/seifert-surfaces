import Section5SurfaceOpenDifferentialV489
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

theorem actual_surface_cylinder_projection {S : CompactOrientedSurface.{0}}
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
    ∃ W : TopologicalSpace.Opens S,
    ∃ q : W → longitudeProductStrip, ∃ beta : Circle → W,
      ContMDiff (𝓡∂ 2) (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) ∞ q ∧
      ContMDiff (𝓡 1) (𝓡∂ 2) ∞ beta ∧
      (∀ x : W, (C (q x) : E.Carrier) = F.toFun x.val) ∧
      (∀ z, F.toFun (beta z).val = J.torus (a,z)) ∧
      range beta = (𝓡∂ 2).boundary W ∧
      (∀ z, (q (beta z)).val = ((a,z),0)) ∧
      (∀ z, IsLocalDiffeomorphAt (𝓡∂ 2) ((𝓡 1).prod (𝓡∂ 1)) ∞
        (fun x : W => ((q x).val.1.2,(q x).val.2)) (beta z)) := by
  classical
  have hgam : IsSmoothEmbedding (𝓡 1) (𝓡∂ 3) ∞ (fun z => J.torus (a,z)) := by
    have hh := longitude_leaf_regular J a
    apply SeifertSurfaces.OriginalEndpoints.Section5.BoundaryNormalFormV488.boundary_curve_isSmoothEmbedding
      hh.1 (fun z => J.torus_lands_boundary (a,z)) hh.2.2 hh.2.1
  obtain ⟨beta0,hbeta0,_,hbeta0F,hbeta0Range,_⟩ :=
    actual_surface_boundary_parameter F (fun z => J.torus (a,z)) hgam ha.symm
  let W : TopologicalSpace.Opens S := ⟨F.toFun ⁻¹' V,
    V.isOpen.preimage F.smoothEmbedding.contMDiff.continuous⟩
  let FF : W → V := fun x => ⟨F.toFun x.val,x.property⟩
  have hFF : ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ FF := by
    apply (ContMDiff.subtypeVal_comp_iff V FF).mp
    exact F.smoothEmbedding.contMDiff.comp contMDiff_subtype_val
  let q : W → longitudeProductStrip := C.symm ∘ FF
  have hq : ContMDiff (𝓡∂ 2) (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) ∞ q :=
    C.symm.contMDiff.comp hFF
  have hqF (x : W) : (C (q x) : E.Carrier) = F.toFun x.val :=
    congrArg Subtype.val (C.apply_symm_apply (FF x))
  have hbetaW (z : Circle) : beta0 z ∈ W := by
    change F.toFun (beta0 z) ∈ V
    rw [hbeta0F,← hC0 (a,z)]
    exact (C _).property
  let beta : Circle → W := fun z => ⟨beta0 z,hbetaW z⟩
  have hbeta : ContMDiff (𝓡 1) (𝓡∂ 2) ∞ beta := by
    apply (ContMDiff.subtypeVal_comp_iff W beta).mp
    exact hbeta0
  have hbetaF (z) : F.toFun (beta z).val = J.torus (a,z) := hbeta0F z
  have hbRange : range beta = (𝓡∂ 2).boundary W := by
    ext x
    constructor
    · rintro ⟨z,rfl⟩
      apply (𝓡∂ 2).isBoundaryPoint_iff_isBoundaryPoint_val.mpr
      change beta0 z ∈ S.boundary
      rw [← hbeta0Range]
      exact mem_range_self z
    · intro hx
      have hx0 : x.val ∈ range beta0 := hbeta0Range ▸
        (𝓡∂ 2).isBoundaryPoint_iff_isBoundaryPoint_val.mp hx
      obtain ⟨z,hz⟩ := hx0
      exact ⟨z,Subtype.ext hz⟩
  have hqB (z) : (q (beta z)).val = ((a,z),0) := by
    let p : longitudeProductStrip := ⟨((a,z),0),by change (0:ℝ)<1; norm_num⟩
    have he : q (beta z) = p := C.injective (Subtype.ext ((hqF _).trans ((hbetaF z).trans (hC0 (a,z)).symm)))
    exact congrArg Subtype.val he
  refine ⟨W,q,beta,hq,hbeta,hqF,hbetaF,hbRange,hqB,?_⟩
  let proj : W → Circle × Time := fun x => ((q x).val.1.2,(q x).val.2)
  have hp : ContMDiff (𝓡∂ 2) ((𝓡 1).prod (𝓡∂ 1)) ∞ proj :=
    (contMDiff_subtype_val.comp hq).fst.snd.prodMk (contMDiff_subtype_val.comp hq).snd
  have hpB (z) : proj (beta z) = (z,0) := by simp only [proj,hqB]
  have hpr : ∀ x : W, r (F.toFun x.val) = b*((proj x).2 : ℝ) := by
    intro x
    rw [← hqF x,hCr]
  have hpb : ∀ x : W, x ∈ (𝓡∂ 2).boundary W → (proj x).2 = 0 := by
    intro x hx
    obtain ⟨z,rfl⟩ := hbRange.symm ▸ hx
    exact congrArg Prod.snd (hpB z)
  intro z
  apply cylinder_projection_local_inverse isOpen_univ hp.contMDiffOn
    (fun x _ hx => hpb x hx) (mem_univ _) (hbRange ▸ mem_range_self z)
  apply cylinder_projection_rank (hp.mdifferentiableAt (by simp))
    (hbeta.mdifferentiableAt (by simp)) hpB
  have hboundary : (beta z).val ∈ S.boundary := hbeta0Range ▸ mem_range_self z
  obtain ⟨hdf,hn⟩ := actual_surface_distance_noncritical F g hU hr hboundary (hVU (beta z).property)
  have hnW := surface_open_derivative_ne_zero W (beta z) hdf hn
  intro hz
  apply hnW
  have he : (r ∘ F.toFun) ∘ (Subtype.val : W → S) =
      (fun t : ℝ => b*t) ∘ (fun x : W => ((proj x).2 : ℝ)) := funext hpr
  have hdscale : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ) (fun t : ℝ => b*t) ((proj (beta z)).2 : ℝ) :=
    (contMDiff_const.mul contMDiff_id).mdifferentiableAt (n:=∞) (by simp)
  have hdt : MDifferentiableAt (𝓡∂ 2) 𝓘(ℝ) (fun x : W => ((proj x).2 : ℝ)) (beta z) :=
    (contMDiff_subtypeVal_Icc.comp hp.snd).mdifferentiableAt (n:=∞) (by simp)
  rw [he,mfderiv_comp (beta z) hdscale hdt,hz,ContinuousLinearMap.comp_zero]

#print axioms actual_surface_cylinder_projection
end
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
