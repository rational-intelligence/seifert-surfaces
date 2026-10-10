import B1ActualGermReciprocity_v475
import B1InteriorSliceTransition_v475
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

/-- The opposite sheet's normal coordinate has an accumulating open zero
germ in the actual common slice transition. -/
theorem native_actual_normal_germ_accumulation_v475
    {S : CompactOrientedSurface.{u}} {B : CompactOrientedSurface.{v}}
    (f : NeatEmbedding S E.Carrier) (g : NeatEmbedding B E.Carrier)
    (y : (𝓡∂ 2).interior B)
    (hacc : y ∈ closure {z : (𝓡∂ 2).interior B |
      native_surface_germ_eq_v475 g.image f.image (g.toFun z)})
    (Φ Ψ : OpenPartialHomeomorph ThreeSphere (E2 × ℝ))
    (hΦ : ContMDiffOn (𝓡 3) 𝓘(ℝ,E2 × ℝ) ∞ Φ Φ.source)
    (hΦi : ContMDiffOn 𝓘(ℝ,E2 × ℝ) (𝓡 3) ∞ Φ.symm Φ.target)
    (hΨ : ContMDiffOn (𝓡 3) 𝓘(ℝ,E2 × ℝ) ∞ Ψ Ψ.source)
    (hΨi : ContMDiffOn 𝓘(ℝ,E2 × ℝ) (𝓡 3) ∞ Ψ.symm Ψ.target)
    (hAexact : Φ '' (Φ.source ∩ range (E.toSphere ∘ f.toFun)) =
      Φ.target ∩ (range (𝓡∂ 2) ×ˢ ({0}:Set ℝ)))
    (hBexact : Ψ '' (Ψ.source ∩ range (E.toSphere ∘ g.toFun)) =
      Ψ.target ∩ (range (𝓡∂ 2) ×ˢ ({0}:Set ℝ)))
    (hyΦ : E.toSphere (g.toFun y) ∈ Φ.source)
    (hyΨ : E.toSphere (g.toFun y) ∈ Ψ.source)
    (hyR : (Ψ (E.toSphere (g.toFun y))).1 ∈ interior (range (𝓡∂ 2))) :
    let U := {z : E2 | (z,0) ∈ Ψ.target ∧ Ψ.symm (z,0) ∈ Φ.source} ∩
      interior (range (𝓡∂ 2))
    let P := fun z : E2 => Φ (Ψ.symm (z,0))
    let q := (Ψ (E.toSphere (g.toFun y))).1
    q ∈ U ∧ q ∈ closure {z | z ∈ U ∧ native_planar_zero_germ_v475 U (fun z => (P z).2) z} := by
  classical
  let U₀ := {z : E2 | (z,0) ∈ Ψ.target ∧ Ψ.symm (z,0) ∈ Φ.source}
  let U := U₀ ∩ interior (range (𝓡∂ 2))
  let P := fun z : E2 => Φ (Ψ.symm (z,0))
  let C : B → E2 := fun z => (Ψ (E.toSphere (g.toFun z))).1
  have hcoordinates (z : B) (hz : E.toSphere (g.toFun z) ∈ Ψ.source) :
      (Ψ (E.toSphere (g.toFun z))).2=0 := by
    have hh : Ψ (E.toSphere (g.toFun z)) ∈
        Ψ.target ∩ (range (𝓡∂ 2) ×ˢ ({0}:Set ℝ)) := by
      rw [← hBexact]
      exact mem_image_of_mem Ψ ⟨hz,⟨z,rfl⟩⟩
    exact hh.2.2
  have hpair (z : B) (hz : E.toSphere (g.toFun z) ∈ Ψ.source) :
      (C z,0)=Ψ (E.toSphere (g.toFun z)) := by
    exact Prod.ext rfl (hcoordinates z hz).symm
  have hqU : C y ∈ U := by
    refine ⟨⟨?_,?_⟩,hyR⟩
    · rw [hpair y hyΨ]
      exact Ψ.map_source hyΨ
    · rw [hpair y hyΨ,Ψ.left_inv hyΨ]
      exact hyΦ
  obtain ⟨hU₀,hP,-⟩ := native_interior_slice_transition_v475 Φ Ψ hΦ hΦi hΨ hΨi
  have hU : IsOpen U := hU₀.inter isOpen_interior
  let Q := {z : B | E.toSphere (g.toFun z) ∈ Ψ.source}
  have hQ : IsOpen Q := Ψ.open_source.preimage
    (continuous_subtype_val.comp g.smoothEmbedding.isEmbedding.continuous)
  have hC : ContinuousOn C Q :=
    continuous_fst.comp_continuousOn (Ψ.continuousOn.comp
      (continuous_subtype_val.comp g.smoothEmbedding.isEmbedding.continuous).continuousOn (fun z hz => hz))
  have hCy : ContinuousAt C (y : B) := (hC y hyΨ).continuousAt (hQ.mem_nhds hyΨ)
  refine ⟨hqU,?_⟩
  rw [mem_closure_iff]
  intro V hV hqV
  have hpre : IsOpen (Q ∩ C ⁻¹' (V ∩ U)) :=
    hC.isOpen_inter_preimage hQ (hV.inter hU)
  have hpreI : IsOpen {z : (𝓡∂ 2).interior B | (z : B) ∈ Q ∩ C ⁻¹' (V ∩ U)} :=
    hpre.preimage continuous_subtype_val
  obtain ⟨z,hzPre,hzg⟩ := mem_closure_iff.mp hacc _ hpreI ⟨hyΨ,hqV,hqU⟩
  obtain ⟨W,hW,hzW,heq⟩ := hzg
  have hinc₀ : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  have hinc : IsEmbedding E.toSphere := hinc₀.isEmbedding
  obtain ⟨W',hW',hWpre⟩ := hinc.isInducing.isOpen_iff.mp hW
  let Z := U ∩ (fun s : E2 => Ψ.symm (s,0)) ⁻¹' W'
  have hinv : ContinuousOn (fun s : E2 => Ψ.symm (s,0)) U :=
    Ψ.continuousOn_symm.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => hs.1.1)
  have hZ : IsOpen Z := hinv.isOpen_inter_preimage hU hW' 
  have hzZ : C z ∈ Z := by
    refine ⟨hzPre.2.2,?_⟩
    change Ψ.symm (C z,0) ∈ W'
    rw [hpair z hzPre.1,Ψ.left_inv hzPre.1]
    change g.toFun z ∈ E.toSphere ⁻¹' W'
    rwa [hWpre]
  refine ⟨C z,hzPre.2.1,hzPre.2.2,Z,hZ,hzZ,inter_subset_left,?_⟩
  intro s hs
  have hst : (s,0) ∈ Ψ.target := hs.1.1.1
  have hsource : Ψ.symm (s,0) ∈ Ψ.source := Ψ.map_target hst
  have hb : Ψ.symm (s,0) ∈ range (E.toSphere ∘ g.toFun) := by
    have hh : (s,0) ∈ Ψ '' (Ψ.source ∩ range (E.toSphere ∘ g.toFun)) := by
      rw [hBexact]
      exact ⟨hst,interior_subset hs.1.2,rfl⟩
    obtain ⟨p,⟨hp,hpg⟩,he⟩ := hh
    have hh' := congrArg Ψ.symm he
    rw [Ψ.left_inv hp] at hh'
    rwa [← hh']
  obtain ⟨t,ht⟩ := hb
  have hrW : g.toFun t ∈ W := by
    rw [← hWpre]
    change E.toSphere (g.toFun t) ∈ W'
    change (E.toSphere ∘ g.toFun) t ∈ W'
    rw [ht]
    exact hs.2
  have hrf : g.toFun t ∈ f.image :=
    (heq ▸ (show g.toFun t ∈ g.image ∩ W from ⟨⟨t,rfl⟩,hrW⟩)).1
  have hh : Φ (Ψ.symm (s,0)) ∈ Φ '' (Φ.source ∩ range (E.toSphere ∘ f.toFun)) := by
    apply mem_image_of_mem
    refine ⟨hs.1.1.2,?_⟩
    obtain ⟨a,ha⟩ := hrf
    exact ⟨a,(congrArg E.toSphere ha).trans ht⟩
  rw [hAexact] at hh
  exact hh.2.2

#print axioms native_actual_normal_germ_accumulation_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
