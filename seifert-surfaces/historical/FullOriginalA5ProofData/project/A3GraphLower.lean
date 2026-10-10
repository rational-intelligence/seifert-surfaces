import OriginalA3

noncomputable section
open Set Topology Function
open scoped Manifold ContDiff

namespace SeifertSurfaces.OriginalEndpoints
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
open SeifertSurfaces.Foundations

namespace A3GraphLower

theorem same_local_inverse_open_control
    (Q : E2 → E2) (U : Set E2) (a : E2)
    (g : OpenPartialHomeomorph E2 E2)
    (hU : IsOpen U) (haU : a ∈ U) (hQ : ContDiffOn ℝ ∞ Q U)
    (hDQ : (fderiv ℝ Q a).IsInvertible)
    (hg : (g : E2 → E2) = Q) (hag : a ∈ g.source) :
    let z0 := Q a
    let j : E2 → E2 := fun x => g.symm (z0 + x)
    ∃ V : Set E2,
      IsOpen V ∧ (0 : E2) ∈ V ∧
      (∀ x ∈ V, z0 + x ∈ g.target ∧ j x ∈ g.source ∩ U) ∧
      ContDiffOn ℝ ∞ j V ∧
      (∀ x ∈ V, (fderiv ℝ Q (j x)).IsInvertible) ∧
      (∀ x ∈ V,
        (fderiv ℝ Q (j x)).comp (fderiv ℝ j x) = ContinuousLinearMap.id ℝ E2 ∧
        (fderiv ℝ j x).comp (fderiv ℝ Q (j x)) = ContinuousLinearMap.id ℝ E2) ∧
      j 0 = a ∧ (∀ x ∈ V, Q (j x) = z0 + x) := by
  classical
  let z0 := Q a
  let j : E2 → E2 := fun x => g.symm (z0 + x)
  let S := U ∩ {y | (fderiv ℝ Q y).IsInvertible}
  have hS : IsOpen S :=
    (hQ.continuousOn_fderiv_of_isOpen hU (by simp)).isOpen_inter_preimage hU
      ContinuousLinearMap.isOpen_setOfPred_isInvertible
  have haS : a ∈ S := ⟨haU, hDQ⟩
  let T := g.target ∩ g.symm ⁻¹' S
  have hT : IsOpen T := g.symm.continuousOn.isOpen_inter_preimage g.open_target hS
  have hza : z0 = g a := by exact congrFun hg a |>.symm
  have hzT : z0 ∈ T := by
    rw [hza]
    exact ⟨g.map_source hag, by change g.symm (g a) ∈ S; rw [g.left_inv hag]; exact haS⟩
  let V := (fun x : E2 => z0 + x) ⁻¹' T
  have hV : IsOpen V := hT.preimage (continuous_const.add continuous_id)
  have hzero : (0 : E2) ∈ V := by change z0 + 0 ∈ T; simpa using hzT
  have hctrl : ∀ x ∈ V, z0 + x ∈ g.target ∧ j x ∈ g.source ∩ U := by
    intro x hx
    exact ⟨hx.1, g.symm.map_source hx.1, hx.2.1⟩
  have hInv : ∀ x ∈ V, (fderiv ℝ Q (j x)).IsInvertible := fun x hx => hx.2.2
  have hQj : ∀ x ∈ V, Q (j x) = z0 + x := by
    intro x hx
    rw [← hg]
    exact g.right_inv hx.1
  have hjsmooth : ∀ x ∈ V, ContDiffAt ℝ ∞ j x := by
    intro x hx
    obtain ⟨A, hA⟩ := hInv x hx
    have hq : ContDiffAt ℝ ∞ Q (j x) := hQ.contDiffAt (hU.mem_nhds (hctrl x hx).2.2)
    have hd : HasFDerivAt (g : E2 → E2) (A : E2 →L[ℝ] E2) (j x) := by
      rw [hg, hA]
      exact (hq.differentiableAt (by simp)).hasFDerivAt
    have hi : ContDiffAt ℝ ∞ g.symm (z0 + x) :=
      g.contDiffAt_symm hx.1 hd (by simpa only [hg] using hq)
    exact hi.comp x (contDiffAt_const.add contDiffAt_id)
  refine ⟨V, hV, hzero, hctrl, fun x hx => (hjsmooth x hx).contDiffWithinAt, hInv, ?_, ?_, hQj⟩
  · intro x hx
    have hq : DifferentiableAt ℝ Q (j x) :=
      (hQ.contDiffAt (hU.mem_nhds (hctrl x hx).2.2)).differentiableAt (by simp)
    have hj : DifferentiableAt ℝ j x := (hjsmooth x hx).differentiableAt (by simp)
    have heq : Q ∘ j =ᶠ[𝓝 x] (fun x => z0 + x) :=
      Filter.eventuallyEq_of_mem (hV.mem_nhds hx) hQj
    have hleft : (fderiv ℝ Q (j x)).comp (fderiv ℝ j x) = ContinuousLinearMap.id ℝ E2 := by
      rw [← fderiv_comp x hq hj, heq.fderiv_eq]
      exact (hasFDerivAt_id x |>.const_add z0).fderiv
    refine ⟨hleft, ?_⟩
    apply ContinuousLinearMap.ext
    intro v
    apply (hInv x hx).injective
    have hv := congrArg (fun L : E2 →L[ℝ] E2 => L ((fderiv ℝ Q (j x)) v)) hleft
    exact hv
  · change g.symm (z0 + 0) = a
    rw [add_zero, hza, g.left_inv hag]

universe w w'

theorem embedding_ambient_open_source_isolation
    {A : Type w} {B : Type w'} [TopologicalSpace A] [TopologicalSpace B]
    (f : A → B) (hf : IsEmbedding f) (a : A)
    (O : Set A) (hO : IsOpen O) (haO : a ∈ O)
    (W : Set B) (hW : IsOpen W) (hfaW : f a ∈ W) :
    ∃ V : Set B,
      IsOpen V ∧ f a ∈ V ∧ V ⊆ W ∧ f ⁻¹' V ⊆ O ∧
      range f ∩ V = f '' (O ∩ (f ⁻¹' V)) := by
  obtain ⟨T, hT, hpre⟩ := hf.isInducing.isOpen_iff.mp hO
  refine ⟨T ∩ W, hT.inter hW, ⟨?_, hfaW⟩, inter_subset_right, ?_, ?_⟩
  · change a ∈ f ⁻¹' T
    rw [hpre]
    exact haO
  · intro x hx
    rw [← hpre]
    exact hx.1
  · ext y
    constructor
    · rintro ⟨⟨x, rfl⟩, hx⟩
      exact ⟨x, ⟨by rw [← hpre]; exact hx.1, hx⟩, rfl⟩
    · rintro ⟨x, ⟨_, hx⟩, rfl⟩
      exact ⟨⟨x, rfl⟩, hx⟩

universe u v
variable {N : Type u} [TopologicalSpace N] [ChartedSpace E3 N]
  [IsManifold 𝓘(ℝ, E3) ∞ N]

theorem fixed_maximal_halfspace_chart_boundary_normal
    (P : EmbeddedSheet.{u,v} N)
    (e : OpenPartialHomeomorph P.carrier (EuclideanHalfSpace 2))
    (he : e ∈ IsManifold.maximalAtlas (𝓡∂ 2) ∞ P.carrier)
    (y : P.carrier) (hy : y ∈ e.source)
    (hyBoundary : y ∈ (𝓡∂ 2).boundary P.carrier) :
    let b := e.extend (𝓡∂ 2)
    let z := b y
    let J := (tangentSpaceCastModel 𝓘(ℝ, E2) z).toContinuousLinearMap.comp
      (mfderiv (𝓡∂ 2) 𝓘(ℝ, E2) b y)
    z 0 = 0 ∧
    (∃ O : Set E2, IsOpen O ∧ z ∈ O ∧
      ∀ w ∈ O, w ∈ b.target ↔ 0 ≤ w 0) ∧
    (∃ lam : ℝ, 0 < lam ∧
      ∀ v : TangentSpace (𝓡∂ 2) y, (J v) 0 = lam * inwardCoordinate y v) := by
  classical
  let I := 𝓡∂ 2
  let b := e.extend I
  let z := b y
  let J := (tangentSpaceCastModel 𝓘(ℝ, E2) z).toContinuousLinearMap.comp
    (mfderiv I 𝓘(ℝ, E2) b y)
  change z 0 = 0 ∧ (∃ O : Set E2, IsOpen O ∧ z ∈ O ∧
    ∀ w ∈ O, w ∈ b.target ↔ 0 ≤ w 0) ∧
    (∃ lam : ℝ, 0 < lam ∧ ∀ v : TangentSpace I y, (J v) 0 = lam * inwardCoordinate y v)
  let Φ : PartialDiffeomorph I I P.carrier (EuclideanHalfSpace 2) ∞ := {
    toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas he
    contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas he }
  have hed : IsLocalDiffeomorphAt I I ∞ e y := ⟨Φ, hy, fun _ _ => rfl⟩
  have hey := (hed.isBoundaryPoint_iff (by simp)).mp hyBoundary
  have hz : z 0 = 0 := by
    change extChartAt I (e y) (e y) ∈ frontier (range I) at hey
    rw [extChartAt_self_apply, frontier_range_modelWithCornersEuclideanHalfSpace] at hey
    exact hey.symm
  refine ⟨hz, ?_, ?_⟩
  · refine ⟨I.symm ⁻¹' e.target, e.open_target.preimage I.continuous_symm, ?_, ?_⟩
    · change I.symm (I (e y)) ∈ e.target
      rw [I.left_inv]
      exact e.map_source hy
    · intro w hw
      change w ∈ (e.extend I).target ↔ _
      rw [e.extend_target]
      rw [range_modelWithCornersEuclideanHalfSpace]
      exact and_iff_right hw
  · have he1 := IsManifold.maximalAtlas_subset_of_le (show (1 : ℕ∞ω) ≤ ∞ by simp) he
    have hd := e.mdifferentiableAt_extend he1 hy
    have hJ : J.IsInvertible :=
      ContinuousLinearMap.isInvertible_equiv.comp (isInvertible_mfderiv_extend he1 hy)
    let c0 := extChartAt I y
    let a := c0 y
    let F : E2 → E2 := b ∘ c0.symm
    let L := J.comp (tangentSpaceCastModel I y).symm.toContinuousLinearMap
    have hL : L.IsInvertible := hJ.comp ContinuousLinearMap.isInvertible_equiv
    have ha : a 0 = 0 := by
      change a ∈ frontier (range I) at hyBoundary
      rw [frontier_range_modelWithCornersEuclideanHalfSpace] at hyBoundary
      exact hyBoundary.symm
    have hFa : F a = z := by
      change b (c0.symm (c0 y)) = b y
      rw [c0.left_inv (mem_extChartAt_source y)]
    have hF : HasFDerivWithinAt F L (range I) a := by
      have hh := hd.hasMFDerivAt.2
      simpa only [writtenInExtChartAt, extChartAt_model_space_eq_id,
        PartialEquiv.refl_coe, Function.id_comp] using! hh
    let ev : E2 →L[ℝ] ℝ := EuclideanSpace.proj 0
    have hscalar : HasFDerivWithinAt (fun x => F x 0) (ev.comp L) (range I) a :=
      ev.hasFDerivAt.comp_hasFDerivWithinAt a hF
    have hmin : IsLocalMinOn (fun x => F x 0) (range I) a := by
      filter_upwards [] with x
      rw [hFa, hz]
      exact (e (c0.symm x)).property
    have haS : a ∈ range I := by rw [range_modelWithCornersEuclideanHalfSpace]; exact le_of_eq ha.symm
    have hcone : ∀ v : E2, 0 ≤ v 0 → v ∈ posTangentConeAt (range I) a := by
      intro v hv
      apply mem_posTangentConeAt_of_segment_subset
      apply I.convex_range.segment_subset haS
      rw [range_modelWithCornersEuclideanHalfSpace]
      change 0 ≤ a 0 + v 0
      rw [ha, zero_add]
      exact hv
    have htangent : ∀ v : E2, v 0 = 0 → (L v) 0 = 0 := by
      intro v hv
      exact hmin.hasFDerivWithinAt_eq_zero hscalar
        (hcone v (le_of_eq hv.symm)) (hcone (-v) (by change 0 ≤ -(v 0); rw [hv]; simp))
    let v0 : E2 := EuclideanSpace.single 0 1
    have hv0 : v0 0 = 1 := by simp [v0]
    let lam := (L v0) 0
    have hnonneg : 0 ≤ lam := hmin.hasFDerivWithinAt_nonneg hscalar (hcone v0 (by rw [hv0]; norm_num))
    have hrow : ∀ v : E2, (L v) 0 = lam * v 0 := by
      intro v
      have ht := htangent (v - v 0 • v0) (by change v 0 - v 0 * v0 0 = 0; rw [hv0]; ring)
      change (L (v - v 0 • v0)) 0 = 0 at ht
      rw [map_sub, map_smul] at ht
      change (L v) 0 - v 0 * lam = 0 at ht
      nlinarith
    have hpos : 0 < lam := by
      apply lt_of_le_of_ne hnonneg
      intro hzero
      obtain ⟨v, hv⟩ := hL.surjective v0
      have ht := hrow v
      rw [hv, hv0, ← hzero, zero_mul] at ht
      norm_num at ht
    refine ⟨lam, hpos, ?_⟩
    intro v
    have ht := hrow ((tangentSpaceCastModel I y) v)
    simpa only [L, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply, inwardCoordinate, mfderiv_extChartAt_self,
      ContinuousLinearMap.id_apply, tangentSpaceCastModel] using! ht

end A3GraphLower
end SeifertSurfaces.OriginalEndpoints
