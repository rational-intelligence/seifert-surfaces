import B1ActualInteriorSlicePoint_v475
import B1ActualGermNormalClosure_v475
noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
universe u v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- At an accumulation point of actual agreement germs, the two neat
surfaces admit a common interior graph. Rank and the common tangent plane
are derived from the same smooth slice charts and accumulating zero germs. -/
theorem native_actual_common_interior_graph_v475
    {S : CompactOrientedSurface.{u}} {B : CompactOrientedSurface.{v}}
    (f : NeatEmbedding S E.Carrier) (g : NeatEmbedding B E.Carrier)
    (x : (𝓡∂ 2).interior S)
    (hacc : x ∈ closure {z : (𝓡∂ 2).interior S |
      native_surface_germ_eq_v475 f.image g.image (f.toFun z)}) :
    ∃ y : (𝓡∂ 2).interior B,
    ∃ Φ Ψ : OpenPartialHomeomorph ThreeSphere (E2 × ℝ),
    ∃ O : Set E2, ∃ p : E2,
    ∃ e : OpenPartialHomeomorph E2 E2, ∃ u : E2 → ℝ,
      g.toFun y=f.toFun x ∧
      O = {z : E2 | (z,0) ∈ Ψ.target ∧ Ψ.symm (z,0) ∈ Φ.source} ∩ interior (range (𝓡∂ 2)) ∧ IsOpen O ∧ p ∈ O ∧ p ∈ e.source ∧ e.source ⊆ O ∧
      ContMDiffOn (𝓡 3) 𝓘(ℝ,E2 × ℝ) ∞ Φ Φ.source ∧
      ContMDiffOn 𝓘(ℝ,E2 × ℝ) (𝓡 3) ∞ Φ.symm Φ.target ∧
      ContMDiffOn (𝓡 3) 𝓘(ℝ,E2 × ℝ) ∞ Ψ Ψ.source ∧
      ContMDiffOn 𝓘(ℝ,E2 × ℝ) (𝓡 3) ∞ Ψ.symm Ψ.target ∧
      Φ '' (Φ.source ∩ range (E.toSphere ∘ f.toFun)) =
        Φ.target ∩ (range (𝓡∂ 2) ×ˢ ({0}:Set ℝ)) ∧
      Ψ '' (Ψ.source ∩ range (E.toSphere ∘ g.toFun)) =
        Ψ.target ∩ (range (𝓡∂ 2) ×ˢ ({0}:Set ℝ)) ∧
      E.toSphere (f.toFun x) ∈ Φ.source ∩ Ψ.source ∧
      Ψ (E.toSphere (g.toFun y))=(p,0) ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      ContDiffOn ℝ ∞ u e.target ∧ u (e p)=0 ∧ planarGradient u (e p)=0 ∧
      (∀ z ∈ e.target, Φ (Ψ.symm (e.symm z,0))=(z,u z)) ∧
      (∀ z ∈ e.source, Φ (Ψ.symm (z,0))=(e z,u (e z))) ∧
      (e p) ∈ interior (range (𝓡∂ 2)) ∧
      (e p) ∈ closure {z | z ∈ e.target ∧ native_planar_zero_germ_v475 e.target u z} := by
  classical
  let f₀ := ProperSmoothEmbedding.ofNeat f
  let g₀ := ProperSmoothEmbedding.ofNeat g
  obtain ⟨y,hy⟩ := native_actual_germ_contact_v475 f₀ g₀ x hacc
  change g.toFun y = f.toFun x at hy
  have hyacc := native_actual_germ_accumulation_reciprocity_v475 f₀ g₀ x y hy hacc
  have hxnb : (x : S) ∉ S.boundary := by
    have hn (a : S) (ha : a ∈ (𝓡∂ 2).interior S) : a ∉ S.boundary := by
      rw [← (𝓡∂ 2).compl_boundary] at ha
      exact ha
    exact hn x x.property
  have hynb : (y : B) ∉ B.boundary := by
    have hn (a : B) (ha : a ∈ (𝓡∂ 2).interior B) : a ∉ B.boundary := by
      rw [← (𝓡∂ 2).compl_boundary] at ha
      exact ha
    exact hn y y.property
  obtain ⟨Φ,hxΦ,hΦ,hΦi,hA,hΦbase⟩ :=
    native_actual_interior_slice_chart_with_base_v475 f x hxnb
  obtain ⟨Ψ,hyΨ,hΨ,hΨi,hB,hΨbase⟩ :=
    native_actual_interior_slice_chart_with_base_v475 g y hynb
  have hyΦ : E.toSphere (g.toFun y) ∈ Φ.source := by rwa [hy]
  let O₀ := {z : E2 | (z,0) ∈ Ψ.target ∧ Ψ.symm (z,0) ∈ Φ.source}
  let O := O₀ ∩ interior (range (𝓡∂ 2))
  let P := fun z : E2 => Φ (Ψ.symm (z,0))
  let p := (Ψ (E.toSphere (g.toFun y))).1
  obtain ⟨hpO,hpacc⟩ := native_actual_normal_germ_accumulation_v475 f g y hyacc Φ Ψ
    hΦ hΦi hΨ hΨi hA hB hyΦ hyΨ hΨbase
  obtain ⟨hO₀,hP,hPi⟩ := native_interior_slice_transition_v475 Φ Ψ hΦ hΦi hΨ hΨi
  have hO : IsOpen O := hO₀.inter isOpen_interior
  have hPO : ContDiffOn ℝ ∞ P O := hP.mono inter_subset_left
  obtain ⟨hpzero,hpnormal⟩ := native_zero_germ_value_derivative_closure_v475 O hO
    (fun z => (P z).2) ((hPO.snd).of_le (by simp)) p hpO hpacc
  obtain ⟨e,u,hpe,heO,heS,heI,hu,hgraph,hgraphS,himage⟩ :=
    native_interior_graph_of_projection_v475 O hO P hPO p hpO (hPi p hpO.1) hpnormal
  have hBnormal : (Ψ (E.toSphere (g.toFun y))).2=0 := by
    have hh : Ψ (E.toSphere (g.toFun y)) ∈
        Ψ.target ∩ (range (𝓡∂ 2) ×ˢ ({0}:Set ℝ)) := by
      rw [← hB]
      exact mem_image_of_mem Ψ ⟨hyΨ,⟨y,rfl⟩⟩
    exact hh.2.2
  have hpair : Ψ (E.toSphere (g.toFun y))=(p,0) := Prod.ext rfl hBnormal
  have hPpoint : P p=Φ (E.toSphere (g.toFun y)) := by
    change Φ (Ψ.symm (p,0))=Φ (E.toSphere (g.toFun y))
    rw [← hpair,Ψ.left_inv hyΨ]
  have hz : u (e p)=0 := by
    have hh := congrArg Prod.snd (hgraphS p hpe)
    exact hh.symm.trans hpzero
  have hgrad : planarGradient u (e p)=0 := by
    have hUs : e.source ∈ 𝓝 p := e.open_source.mem_nhds hpe
    have hevent : (fun z => (P z).2) =ᶠ[𝓝 p] u ∘ e := by
      filter_upwards [hUs] with z hz
      exact congrArg Prod.snd (hgraphS z hz)
    have hUd : DifferentiableAt ℝ u (e p) :=
      (hu.contDiffAt (e.open_target.mem_nhds (e.map_source hpe))).differentiableAt (by simp)
    have hEd : DifferentiableAt ℝ e p :=
      (heS.contDiffAt (e.open_source.mem_nhds hpe)).differentiableAt (by simp)
    have hId : DifferentiableAt ℝ e.symm (e p) :=
      (heI.contDiffAt (e.open_target.mem_nhds (e.map_source hpe))).differentiableAt (by simp)
    have hev : (fun z : E2 => z) =ᶠ[𝓝 p] e.symm ∘ e := by
      filter_upwards [hUs] with z hz
      exact (e.left_inv hz).symm
    have hInv := (hId.hasFDerivAt.comp p hEd.hasFDerivAt).congr_of_eventuallyEq hev
    have hProd : (fderiv ℝ e.symm (e p)).comp (fderiv ℝ e p)=ContinuousLinearMap.id ℝ E2 :=
      hInv.unique (hasFDerivAt_id p)
    have heInv : (fderiv ℝ e p).IsInvertible := by
      have hi : Function.Injective (fderiv ℝ e p) := by
        intro a b hab
        have hh := congrArg (fun L : E2 →L[ℝ] E2 => L a) hProd
        have hk := congrArg (fun L : E2 →L[ℝ] E2 => L b) hProd
        simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] using
          hh.symm.trans ((congrArg (fderiv ℝ e.symm (e p)) hab).trans hk)
      exact ⟨(LinearEquiv.ofBijective _ ⟨hi,LinearMap.injective_iff_surjective.mp hi⟩).toContinuousLinearEquiv,rfl⟩
    have hcomp : (fderiv ℝ u (e p)).comp (fderiv ℝ e p)=0 := by
      rw [← fderiv_comp p hUd hEd,← hevent.fderiv_eq]
      exact hpnormal
    have hdu : fderiv ℝ u (e p)=0 := by
      ext v
      obtain ⟨w,rfl⟩ := heInv.surjective v
      exact congrArg (fun L : E2 →L[ℝ] ℝ => L w) hcomp
    unfold planarGradient
    rw [hdu]
    simp
  have hebase : e p ∈ interior (range (𝓡∂ 2)) := by
    have hh := congrArg Prod.fst (hgraphS p hpe)
    rw [hPpoint,hy] at hh
    change (Φ (E.toSphere (f.toFun x))).1 = e p at hh
    rwa [← hh]
  have haccU : e p ∈ closure {z | z ∈ e.target ∧ native_planar_zero_germ_v475 e.target u z} := by
    rw [mem_closure_iff]
    intro V hV hpV
    let Q := e.source ∩ e ⁻¹' V
    have hQ : IsOpen Q := e.isOpen_inter_preimage hV
    have hpQ : p ∈ Q := ⟨hpe,hpV⟩
    obtain ⟨z,hzQ,hzO,hzG⟩ := mem_closure_iff.mp hpacc Q hQ hpQ
    obtain ⟨W,hW,hzW,hWO,hWz⟩ := hzG
    let Z := e.target ∩ e.symm ⁻¹' (W ∩ e.source)
    have hZ : IsOpen Z := e.continuousOn_symm.isOpen_inter_preimage e.open_target (hW.inter e.open_source)
    have hzZ : e z ∈ Z := by
      refine ⟨e.map_source hzQ.1,?_⟩
      change e.symm (e z) ∈ W ∩ e.source
      rw [e.left_inv hzQ.1]
      exact ⟨hzW,hzQ.1⟩
    refine ⟨e z,hzQ.2,e.map_source hzQ.1,Z,hZ,hzZ,inter_subset_left,?_⟩
    intro s hs
    have hh := congrArg Prod.snd (hgraph s hs.1)
    exact hh.symm.trans (hWz hs.2.1)
  refine ⟨y,Φ,Ψ,O,p,e,u,hy,rfl,hO,hpO,hpe,heO,hΦ,hΦi,hΨ,hΨi,hA,hB,
    ⟨hxΦ,?_⟩,hpair,heS,heI,hu,hz,hgrad,hgraph,hgraphS,hebase,haccU⟩
  rwa [← hy] 

#print axioms native_actual_common_interior_graph_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
