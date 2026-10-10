import B1ActualFixedBoundaryMinima_v475
import DifferentialGeometry.Analysis.ODE.Flow.CompactSupport
import Mathlib.Geometry.Manifold.VectorField.Pullback
import SectorRegularityHelpers

set_option autoImplicit false
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped Manifold ContDiff
open DifferentialGeometry.Analysis.ODE
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
universe u
variable {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
set_option maxHeartbeats 0

structure NativeInteriorSmoothVectorField_v475 where
  field : ∀ p : ThreeSphere, TangentSpace (𝓡 3) p
  smooth : ContMDiff (𝓡 3) (𝓡 3).tangent ∞
    (fun p => Bundle.TotalSpace.mk' (Euc 3) p (field p))
  compact_support : IsCompact (closure {p | field p ≠ 0})
  support_interior : closure {p | field p ≠ 0} ⊆
    E.toSphere '' (𝓡∂ 3).interior E.Carrier
private theorem native_field_zero_outside_v475 (X : NativeInteriorSmoothVectorField_v475 E)
    {p : ThreeSphere} (hp : p ∉ E.toSphere '' (𝓡∂ 3).interior E.Carrier) :
    X.field p = 0 := by
  by_contra h
  exact hp (X.support_interior (subset_closure h))
private theorem native_field_tsupport_compact_v475 (X : NativeInteriorSmoothVectorField_v475 E) :
    IsCompact (tsupport X.field) := by
  exact X.compact_support
private theorem native_field_complete_v475 (X : NativeInteriorSmoothVectorField_v475 E) :
    ∀ p : ThreeSphere, ∃ γ : ℝ → ThreeSphere,
      γ 0 = p ∧ IsMIntegralCurve γ X.field := by
  apply DifferentialGeometry.Analysis.ODE.exists_globalIntegralCurve_of_compactSupport
  · exact X.smooth
  · exact native_field_tsupport_compact_v475 E X
private theorem native_field_flow_joint_v475 (X : NativeInteriorSmoothVectorField_v475 E) :
    ContMDiff (𝓘(ℝ).prod (𝓡 3)) (𝓡 3) ∞
      (fun q : ℝ × ThreeSphere => curveAt X.field (native_field_complete_v475 E X) q.2 q.1) := by
  exact DifferentialGeometry.Analysis.ODE.contMDiff_curveAt
    X.field X.smooth (native_field_complete_v475 E X)
private theorem native_field_flow_diffeomorph_v475 (X : NativeInteriorSmoothVectorField_v475 E) (t : ℝ) :
    ∃ d : Diffeomorph (𝓡 3) (𝓡 3) ThreeSphere ThreeSphere ∞,
      (∀ p, d p = curveAt X.field (native_field_complete_v475 E X) p t) ∧
      (∀ p, d.symm p = curveAt X.field (native_field_complete_v475 E X) p (-t)) := by
  exact DifferentialGeometry.Analysis.ODE.globalFlow_diffeomorph_of_complete
    X.field X.smooth (native_field_complete_v475 E X) t
private theorem native_field_flow_fixed_v475 (X : NativeInteriorSmoothVectorField_v475 E)
    {p : ThreeSphere} (hp : p ∉ E.toSphere '' (𝓡∂ 3).interior E.Carrier) (t : ℝ) :
    curveAt X.field (native_field_complete_v475 E X) p t = p := by
  apply DifferentialGeometry.Analysis.ODE.curveAt_eq_self_of_eq_zero
  · exact X.smooth.of_le (by simp)
  · exact native_field_zero_outside_v475 E X hp
private theorem native_field_flow_preserves_range_v475 (X : NativeInteriorSmoothVectorField_v475 E)
    (p : ThreeSphere) (hp : p ∈ Set.range E.toSphere) (t : ℝ) :
    curveAt X.field (native_field_complete_v475 E X) p t ∈ Set.range E.toSphere := by
  by_contra h
  have hnot : curveAt X.field (native_field_complete_v475 E X) p t ∉
      E.toSphere '' (𝓡∂ 3).interior E.Carrier := by
    intro he
    obtain ⟨q, _, heq⟩ := he
    exact h ⟨q, heq⟩
  have hfix := native_field_flow_fixed_v475 E X hnot (-t)
  rw [← curveAt_add X.field (X.smooth.of_le (by simp)) (native_field_complete_v475 E X),
    add_neg_cancel, curveAt_zero] at hfix
  exact h (hfix ▸ hp)
private def native_field_flow_homeomorph_v475 (X : NativeInteriorSmoothVectorField_v475 E) (t : ℝ) :
    E.Carrier ≃ₜ E.Carrier := by
  let f : E.Carrier → E.Carrier := fun p =>
    ⟨curveAt X.field (native_field_complete_v475 E X) (E.toSphere p) t,
      by
        obtain ⟨q, hq⟩ := native_field_flow_preserves_range_v475 E X _ ⟨p, rfl⟩ t
        exact hq ▸ q.property⟩
  let g : E.Carrier → E.Carrier := fun p =>
    ⟨curveAt X.field (native_field_complete_v475 E X) (E.toSphere p) (-t),
      by
        obtain ⟨q, hq⟩ := native_field_flow_preserves_range_v475 E X _ ⟨p, rfl⟩ (-t)
        exact hq ▸ q.property⟩
  refine {
    toFun := f
    invFun := g
    left_inv := ?_
    right_inv := ?_
    continuous_toFun := ?_
    continuous_invFun := ?_ }
  · intro p
    apply Subtype.ext
    change curveAt X.field (native_field_complete_v475 E X)
      (curveAt X.field (native_field_complete_v475 E X) (E.toSphere p) t) (-t) = E.toSphere p
    rw [← curveAt_add X.field (X.smooth.of_le (by simp)) (native_field_complete_v475 E X),
      add_neg_cancel, curveAt_zero]
  · intro p
    apply Subtype.ext
    change curveAt X.field (native_field_complete_v475 E X)
      (curveAt X.field (native_field_complete_v475 E X) (E.toSphere p) (-t)) t = E.toSphere p
    rw [← curveAt_add X.field (X.smooth.of_le (by simp)) (native_field_complete_v475 E X),
      neg_add_cancel, curveAt_zero]
  · apply Continuous.subtype_mk
    exact (native_field_flow_joint_v475 E X).continuous.comp
      (continuous_const.prodMk continuous_subtype_val)
  · apply Continuous.subtype_mk
    exact (native_field_flow_joint_v475 E X).continuous.comp
      (continuous_const.prodMk continuous_subtype_val)
private def native_field_flow_exterior_diffeomorph_v475 (X : NativeInteriorSmoothVectorField_v475 E) (t : ℝ) :
    Diffeomorph (𝓡∂ 3) (𝓡∂ 3) E.Carrier E.Carrier ∞ := by
  let h := native_field_flow_homeomorph_v475 E X t
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  refine {
    toEquiv := h.toEquiv
    contMDiff_toFun := ?_
    contMDiff_invFun := ?_ }
  · apply (ContMDiff.iff_comp_isImmersion hinc.isImmersion).mpr
    refine ⟨h.continuous, ?_⟩
    exact (native_field_flow_joint_v475 E X).comp
      (contMDiff_const.prodMk hinc.contMDiff)
  · apply (ContMDiff.iff_comp_isImmersion hinc.isImmersion).mpr
    refine ⟨h.symm.continuous, ?_⟩
    exact (native_field_flow_joint_v475 E X).comp
      (contMDiff_const.prodMk hinc.contMDiff)

private theorem native_diffeo_derivative_injective_v475
    (d : Diffeomorph (𝓡∂ 3) (𝓡∂ 3) E.Carrier E.Carrier ∞) (p : E.Carrier) :
    Function.Injective (mfderiv (𝓡∂ 3) (𝓡∂ 3) d p) := by
  exact (d.mfderivToContinuousLinearEquiv (by simp) p).injective
private def native_transformed_seam_v475 {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier)
    (d : Diffeomorph (𝓡∂ 3) (𝓡∂ 3) E.Carrier E.Carrier ∞) :
    SeamGraph S (d ∘ F.map) where
  arcCount := F.seam.arcCount
  circleCount := F.seam.circleCount
  arc := F.seam.arc
  circle := F.seam.circle
  arc_embedding := F.seam.arc_embedding
  circle_embedding := F.seam.circle_embedding
  arc_smooth_image := fun i => d.contMDiff.comp (F.seam.arc_smooth_image i)
  arc_differential_injective := by
    intro i x
    rw [show (d ∘ ⇑F.map) ∘ ⇑(F.seam.arc i) = d ∘ (F.map ∘ F.seam.arc i) from rfl,
      mfderiv_comp x (d.mdifferentiable (by simp) _) 
        ((F.seam.arc_smooth_image i).mdifferentiable (by simp) x)]
    exact (native_diffeo_derivative_injective_v475 E d _).comp (F.seam.arc_differential_injective i x)
  circle_smooth_image := fun i => d.contMDiff.comp (F.seam.circle_smooth_image i)
  circle_differential_injective := by
    intro i x
    rw [show (d ∘ ⇑F.map) ∘ ⇑(F.seam.circle i) = d ∘ (F.map ∘ F.seam.circle i) from rfl,
      mfderiv_comp x (d.mdifferentiable (by simp) _)
        ((F.seam.circle_smooth_image i).mdifferentiable (by simp) x)]
    exact (native_diffeo_derivative_injective_v475 E d _).comp (F.seam.circle_differential_injective i x)
  arc_boundary := F.seam.arc_boundary
  circle_off_boundary := F.seam.circle_off_boundary
  arc_intersections := F.seam.arc_intersections
  circle_intersections := F.seam.circle_intersections
  arc_circle_disjoint := F.seam.arc_circle_disjoint
private def native_transformed_surface_v475 {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier)
    (d : Diffeomorph (𝓡∂ 3) (𝓡∂ 3) E.Carrier E.Carrier ∞) :
    GeometricPiecewiseSurface S E.Carrier where
  map := ⟨d ∘ F.map, d.continuous.comp F.map.continuous⟩
  embedding := d.toHomeomorph.isEmbedding.comp F.embedding
  boundary_preimage := by
    change F.map ⁻¹' (d ⁻¹' (𝓡∂ 3).boundary E.Carrier) = S.boundary
    rw [d.preimage_boundary (by simp), F.boundary_preimage]
  seam := native_transformed_seam_v475 E F d
  smooth_off_seam := by
    intro x hx
    obtain ⟨c, hc, hsub⟩ := F.smooth_off_seam x hx
    refine ⟨{
      chart := c.chart
      source_open := c.source_open
      target_open := c.target_open
      cInfinity := d.contMDiff.comp_contMDiffOn c.cInfinity
      differential_injective := ?_
      boundary_image := c.boundary_image }, hc, hsub⟩
    intro y hy
    rw [mfderivWithin_of_mem_nhds (c.target_open.mem_nhds hy)]
    change Function.Injective (mfderiv (𝓡∂ 2) (𝓡∂ 3) (d ∘ (F.map ∘ c.chart.symm)) y)
    rw [mfderiv_comp y (d.mdifferentiable (by simp) _)
        ((c.cInfinity.contMDiffAt (c.target_open.mem_nhds hy)).mdifferentiableAt (by simp))]
    apply (native_diffeo_derivative_injective_v475 E d _).comp
    have hc := c.differential_injective y hy
    rw [mfderivWithin_of_mem_nhds (c.target_open.mem_nhds hy)] at hc
    exact fun v w h => hc h
  pieceCount := F.pieceCount
  domain := F.domain
  parametrization := F.parametrization
  parametrization_embedding := F.parametrization_embedding
  piece_c1 := fun i j => (d.contMDiff.of_le (by simp)).comp_contMDiffOn (F.piece_c1 i j)
  piece_topological_embedding := fun i => d.toHomeomorph.isEmbedding.comp (F.piece_topological_embedding i)
  piece_differential_injective := by
    intro i j y hy
    change Function.Injective (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 3)
      (d ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j)
      ((F.domain i).chart j).map.target y)
    rw [mfderiv_comp_mfderivWithin y (d.mdifferentiable (by simp) _)
      (((F.piece_c1 i j).mdifferentiableOn (by simp)) y hy) ?_]
    · exact (native_diffeo_derivative_injective_v475 E d _).comp (F.piece_differential_injective i j y hy)
    · apply UniqueDiffWithinAt.uniqueMDiffWithinAt
      have hUD : UniqueDiffOn ℝ ((F.domain i).chart j).map.target := by
        rw [((F.domain i).chart j).target_eq]
        exact SectorModel.uniqueDiffOn_domain _
      exact hUD y hy
  piece_smooth_interior := fun i j => d.contMDiff.comp_contMDiffOn (F.piece_smooth_interior i j)
  piece_edges_smooth := fun i j t ht => d.contMDiff.comp_contMDiffOn (F.piece_edges_smooth i j t ht)
  piece_interior_component := F.piece_interior_component
  pieces_distinct := F.pieces_distinct
  piece_closure := F.piece_closure
  covers := F.covers
  piece_boundary := F.piece_boundary
private def native_transformed_source_map_v475 {S R : CompactOrientedSurface.{u}}
    {F : GeometricPiecewiseSurface S E.Carrier}
    {G : GeometricPiecewiseSurface R E.Carrier} {f : S → R}
    (H : GeometricSourceMap F G f)
    (d0 d1 : Diffeomorph (𝓡∂ 3) (𝓡∂ 3) E.Carrier E.Carrier ∞) :
    GeometricSourceMap (native_transformed_surface_v475 E F d0) (native_transformed_surface_v475 E G d1) f where
  count := H.count
  domain := H.domain
  parametrization := H.parametrization
  embedding := H.embedding
  covers := H.covers
  source_c1 := fun i => (d0.contMDiff.of_le (by simp)).comp (H.source_c1 i)
  source_injective := by
    intro i q
    change Function.Injective (mfderiv CornerModel (𝓡∂ 3)
      (d0 ∘ (F.map ∘ H.parametrization i)) q)
    rw [mfderiv_comp q (d0.mdifferentiable (by simp) _)
      ((H.source_c1 i).mdifferentiable (by simp) q)]
    exact (native_diffeo_derivative_injective_v475 E d0 _).comp (H.source_injective i q)
  source_smooth_interior := fun i => d0.contMDiff.comp_contMDiffOn (H.source_smooth_interior i)
  target_c1 := fun i => (d1.contMDiff.of_le (by simp)).comp (H.target_c1 i)
  target_injective := by
    intro i q
    change Function.Injective (mfderiv CornerModel (𝓡∂ 3)
      (d1 ∘ (G.map ∘ f ∘ H.parametrization i)) q)
    rw [mfderiv_comp q (d1.mdifferentiable (by simp) _)
      ((H.target_c1 i).mdifferentiable (by simp) q)]
    exact (native_diffeo_derivative_injective_v475 E d1 _).comp (H.target_injective i q)
  target_smooth_interior := fun i => d1.contMDiff.comp_contMDiffOn (H.target_smooth_interior i)
private theorem native_exterior_flow_joint_v475 (X : NativeInteriorSmoothVectorField_v475 E) :
    ContMDiff (𝓘(ℝ).prod (𝓡∂ 3)) (𝓡∂ 3) ∞
      (fun q : ℝ × E.Carrier => native_field_flow_exterior_diffeomorph_v475 E X q.1 q.2) := by
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  apply (ContMDiff.iff_comp_isImmersion hinc.isImmersion).mpr
  refine ⟨?_, ?_⟩
  · apply Continuous.subtype_mk
    exact (native_field_flow_joint_v475 E X).continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  · exact (native_field_flow_joint_v475 E X).comp
      (contMDiff_fst.prodMk (hinc.contMDiff.comp contMDiff_snd))
private theorem native_exterior_flow_fixed_boundary_v475 (X : NativeInteriorSmoothVectorField_v475 E)
    (t : ℝ) (p : E.Carrier) (hp : p ∈ (𝓡∂ 3).boundary E.Carrier) :
    native_field_flow_exterior_diffeomorph_v475 E X t p = p := by
  apply Subtype.ext
  apply native_field_flow_fixed_v475 E X
  rintro ⟨q, hq, heq⟩
  have hqp : q = p := Subtype.ext heq
  subst q
  exact (𝓡∂ 3).disjoint_interior_boundary (M := E.Carrier) |>.le_bot ⟨hq, hp⟩
private def native_flow_graph_homeomorph_v475 (X : NativeInteriorSmoothVectorField_v475 E) (ε : ℝ) :
    (Time × E.Carrier) ≃ₜ (Time × E.Carrier) where
  toFun q := (q.1, native_field_flow_exterior_diffeomorph_v475 E X (ε * (q.1 : ℝ)) q.2)
  invFun q := (q.1, native_field_flow_exterior_diffeomorph_v475 E X (-(ε * (q.1 : ℝ))) q.2)
  left_inv := by
    intro q
    refine Prod.ext ?_ ?_
    · rfl
    apply Subtype.ext
    change curveAt X.field (native_field_complete_v475 E X)
      (curveAt X.field (native_field_complete_v475 E X) (E.toSphere q.2) (ε * (q.1 : ℝ)))
      (-(ε * (q.1 : ℝ))) = E.toSphere q.2
    rw [← curveAt_add X.field (X.smooth.of_le (by simp)) (native_field_complete_v475 E X),
      add_neg_cancel, curveAt_zero]
  right_inv := by
    intro q
    refine Prod.ext ?_ ?_
    · rfl
    apply Subtype.ext
    change curveAt X.field (native_field_complete_v475 E X)
      (curveAt X.field (native_field_complete_v475 E X) (E.toSphere q.2) (-(ε * (q.1 : ℝ))))
      (ε * (q.1 : ℝ)) = E.toSphere q.2
    rw [← curveAt_add X.field (X.smooth.of_le (by simp)) (native_field_complete_v475 E X),
      neg_add_cancel, curveAt_zero]
  continuous_toFun := continuous_fst.prodMk ((native_exterior_flow_joint_v475 E X).continuous.comp
    ((continuous_const.mul (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd))
  continuous_invFun := continuous_fst.prodMk ((native_exterior_flow_joint_v475 E X).continuous.comp
    ((continuous_const.mul (continuous_subtype_val.comp continuous_fst)).neg.prodMk continuous_snd))
private def native_flow_graph_diffeomorph_v475 (X : NativeInteriorSmoothVectorField_v475 E) (ε : ℝ) :
    Diffeomorph ((𝓡∂ 1).prod (𝓡∂ 3)) ((𝓡∂ 1).prod (𝓡∂ 3))
      (Time × E.Carrier) (Time × E.Carrier) ∞ where
  toEquiv := (native_flow_graph_homeomorph_v475 E X ε).toEquiv
  contMDiff_toFun := by
    apply contMDiff_fst.prodMk
    exact (native_exterior_flow_joint_v475 E X).comp (f := fun q : Time × E.Carrier =>
      (ε * (q.1 : ℝ), q.2))
      ((contMDiff_const.mul (contMDiff_subtypeVal_Icc.comp contMDiff_fst)).prodMk contMDiff_snd)
  contMDiff_invFun := by
    apply contMDiff_fst.prodMk
    exact (native_exterior_flow_joint_v475 E X).comp (f := fun q : Time × E.Carrier =>
      (-(ε * (q.1 : ℝ)), q.2))
      ((contMDiff_const.mul (contMDiff_subtypeVal_Icc.comp contMDiff_fst)).neg.prodMk contMDiff_snd)
private def native_transformed_track_v475 {S : CompactOrientedSurface.{u}}
    {F : GeometricPiecewiseSurface S E.Carrier} {track : Time × S → E.Carrier}
    (H : GeometricTrack F track) (X : NativeInteriorSmoothVectorField_v475 E) (ε : ℝ) :
    GeometricTrack F (fun q => native_field_flow_exterior_diffeomorph_v475 E X (ε * (q.1 : ℝ)) (track q)) where
  count := H.count
  prism := H.prism
  parametrization := H.parametrization
  embedding := H.embedding
  covers := H.covers
  source_c1 := H.source_c1
  source_injective := H.source_injective
  source_smooth_interior := H.source_smooth_interior
  target_c1 := fun i => ((native_flow_graph_diffeomorph_v475 E X ε).contMDiff.of_le (by simp)).comp (H.target_c1 i)
  target_injective := by
    intro i q
    change Function.Injective (mfderiv (modelWithCornersEuclideanQuadrant 3)
      ((𝓡∂ 1).prod (𝓡∂ 3))
      (native_flow_graph_diffeomorph_v475 E X ε ∘
        (fun q => ((H.parametrization i q).1, track (H.parametrization i q)))) q)
    rw [mfderiv_comp q ((native_flow_graph_diffeomorph_v475 E X ε).mdifferentiable (by simp) _)
      ((H.target_c1 i).mdifferentiable (by simp) q)]
    exact ((native_flow_graph_diffeomorph_v475 E X ε).mfderivToContinuousLinearEquiv (by simp) _).injective.comp
      (H.target_injective i q)
  target_smooth_interior := fun i => (native_flow_graph_diffeomorph_v475 E X ε).contMDiff.comp_contMDiffOn
    (H.target_smooth_interior i)
private theorem native_flow_admissible_v475 {S R : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier)
    (G : GeometricPiecewiseSurface R E.Carrier)
    (h : FixedBoundaryImageIsotopic E F G) (X : NativeInteriorSmoothVectorField_v475 E) (ε : ℝ) :
    FixedBoundaryImageIsotopic E F
      (native_transformed_surface_v475 E G (native_field_flow_exterior_diffeomorph_v475 E X ε)) := by
  classical
  obtain ⟨e, stage, hcont, ⟨htrack⟩, hzero, hone, hbdry⟩ := h
  let dt := native_field_flow_exterior_diffeomorph_v475 E X
  let stage' : Time → GeometricPiecewiseSurface S E.Carrier :=
    fun t => native_transformed_surface_v475 E (stage t) (dt (ε * (t : ℝ)))
  let e' : GeometricSourceHomeomorph F (native_transformed_surface_v475 E G (dt ε)) := {
    homeomorph := e.homeomorph
    forward := native_transformed_source_map_v475 E e.forward (Diffeomorph.refl (𝓡∂ 3) E.Carrier ∞) (dt ε)
    backward := native_transformed_source_map_v475 E e.backward (dt ε) (Diffeomorph.refl (𝓡∂ 3) E.Carrier ∞)
    boundary_image := e.boundary_image }
  refine ⟨e', stage', ?_, ⟨native_transformed_track_v475 E htrack X ε⟩, ?_, ?_, ?_⟩
  · exact (native_exterior_flow_joint_v475 E X).continuous.comp
      ((continuous_const.mul (continuous_subtype_val.comp continuous_fst)).prodMk hcont)
  · ext x
    change dt (ε * (0 : ℝ)) ((stage 0).map x) = F.map x
    rw [mul_zero, hzero]
    apply Subtype.ext
    exact curveAt_zero _ _ _
  · ext x
    change dt (ε * (1 : ℝ)) ((stage 1).map x) = dt ε (G.map (e.homeomorph x))
    rw [mul_one, hone]
    rfl
  · intro t x hx
    change dt (ε * (t : ℝ)) ((stage t).map x) = F.map x
    rw [hbdry t x hx]
    apply native_exterior_flow_fixed_boundary_v475 E X
    rw [← F.boundary_preimage] at hx
    exact hx

private theorem native_flow_zero_map_v475 {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier) (X : NativeInteriorSmoothVectorField_v475 E) :
    (native_transformed_surface_v475 E F (native_field_flow_exterior_diffeomorph_v475 E X 0)).map = F.map := by
  ext p
  apply Subtype.ext
  exact curveAt_zero _ _ _
private theorem native_flow_area_at_zero_v475 {S : CompactOrientedSurface.{u}}
    (g : SmoothMetric E.Carrier) (F : GeometricPiecewiseSurface S E.Carrier)
    (X : NativeInteriorSmoothVectorField_v475 E) :
    geometricArea g (native_transformed_surface_v475 E F (native_field_flow_exterior_diffeomorph_v475 E X 0)) =
      geometricArea g F := by
  apply piecewiseArea_same_image
  dsimp [GeometricPiecewiseSurface.image]
  rw [native_flow_zero_map_v475 E F X]

variable {E} {g : SmoothMetric E.Carrier}
theorem native_actual_ambient_flow_minimum_v475
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (hminimum : FixedBoundaryMinimizer E g F F)
    (X : NativeInteriorSmoothVectorField_v475 E) :
    IsLocalMin (fun t => geometricArea g
      (native_transformed_surface_v475 E F (native_field_flow_exterior_diffeomorph_v475 E X t))) 0 := by
  apply Filter.Eventually.of_forall
  intro t
  change geometricArea g (native_transformed_surface_v475 E F
    (native_field_flow_exterior_diffeomorph_v475 E X 0)) ≤ _
  rw [native_flow_area_at_zero_v475 E g F X]
  exact hminimum.area_le _ (native_flow_admissible_v475 E F F hminimum.in_class X t)

theorem native_actual_field_complete_v475 (X : NativeInteriorSmoothVectorField_v475 E) :
    ∀ p : ThreeSphere, ∃ γ : ℝ → ThreeSphere,
      γ 0 = p ∧ IsMIntegralCurve γ X.field :=
  native_field_complete_v475 E X

/-- The admissible native flow with its literal exterior map exposed for area
localization. -/
def native_actual_exterior_flow_v475 (X : NativeInteriorSmoothVectorField_v475 E) (t : ℝ) :
    Diffeomorph (𝓡∂ 3) (𝓡∂ 3) E.Carrier E.Carrier ∞ :=
  native_field_flow_exterior_diffeomorph_v475 E X t

theorem native_actual_exterior_flow_joint_v475 (X : NativeInteriorSmoothVectorField_v475 E) :
    ContMDiff (𝓘(ℝ).prod (𝓡∂ 3)) (𝓡∂ 3) ∞
      (fun q : ℝ × E.Carrier => native_actual_exterior_flow_v475 X q.1 q.2) :=
  native_exterior_flow_joint_v475 E X

theorem native_actual_exterior_flow_sphere_v475 (X : NativeInteriorSmoothVectorField_v475 E)
    (t : ℝ) (p : E.Carrier) :
    E.toSphere (native_actual_exterior_flow_v475 X t p) =
      curveAt X.field (native_actual_field_complete_v475 X) (E.toSphere p) t := rfl

theorem native_actual_exterior_flow_zero_v475 (X : NativeInteriorSmoothVectorField_v475 E)
    (p : E.Carrier) : native_actual_exterior_flow_v475 X 0 p = p := by
  apply Subtype.ext
  exact curveAt_zero _ _ _

/-- The fixed-boundary geometric minimum is an actual minimum of the smooth
source-area functional along the same admissible ambient flow. -/
theorem native_actual_smooth_ambient_flow_minimum_v475
    {S : CompactOrientedSurface.{u}} (f : ProperSmoothEmbedding S E.Carrier)
    (F : GeometricPiecewiseSurface S E.Carrier)
    (hmap : F.map = f.continuousMap)
    (hminimum : FixedBoundaryMinimizer E g F F)
    (X : NativeInteriorSmoothVectorField_v475 E) :
    IsLocalMin (fun t => area g (native_actual_exterior_flow_v475 X t ∘ f.toFun)) 0 := by
  have hsmooth (t : ℝ) :
      geometricArea g (native_transformed_surface_v475 E F
        (native_field_flow_exterior_diffeomorph_v475 E X t)) =
      area g (native_actual_exterior_flow_v475 X t ∘ f.toFun) := by
    let d := native_field_flow_exterior_diffeomorph_v475 E X t
    let ft : ProperSmoothEmbedding S E.Carrier := {
      toFun := d ∘ f.toFun
      smooth := d.contMDiff.comp f.smooth
      embedding := d.toHomeomorph.isEmbedding.comp f.embedding
      differential_injective := by
        intro p
        rw [mfderiv_comp p (d.mdifferentiable (by simp) _)
          (f.smooth.mdifferentiable (by simp) p)]
        exact (native_diffeo_derivative_injective_v475 E d _).comp
          (f.differential_injective p)
      boundary_preimage := by
        change f.toFun ⁻¹' (d ⁻¹' (𝓡∂ 3).boundary E.Carrier) = S.boundary
        rw [d.preimage_boundary (by simp),f.boundary_preimage] }
    apply smooth_piecewise_area g ft
    ext p
    change d (F.map p) = d (f.toFun p)
    rw [hmap]
    rfl
  have hm := native_actual_ambient_flow_minimum_v475 F hminimum X
  simpa only [hsmooth] using hm

end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.native_actual_ambient_flow_minimum_v475
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.native_actual_smooth_ambient_flow_minimum_v475
