import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualTorusIsotopyDescent
import CurveComplexGenusTwo.Foundations.FoundationsIntersectionPort

open Set Topology Schoenflies CurveComplex

/-- Restrict an actual simultaneous-axis chart to an actual prescribed open
neighborhood. The target open set and restricted homeomorphism are constructed. -/
theorem actual_surface_crossing_chart_restrict_to_open
    {X : Type*} [TopologicalSpace X] (U : Set X) (V : Set (ℝ×ℝ)) (_hU : IsOpen U) (hV : IsOpen V)
    (h : U ≃ₜ V) (N : Set X) (hN : IsOpen N) :
    ∃ W : Set (ℝ×ℝ), IsOpen W ∧
    ∃ e : ↥(U∩N) ≃ₜ W,
      ∀ z (hz : z∈U∩N), ((e ⟨z,hz⟩ : W) : ℝ×ℝ)=((h ⟨z,hz.1⟩ : V) : ℝ×ℝ) := by
  let S : Set U := {u | (u : X)∈N}
  let W := Subtype.val '' (h '' S)
  have hW : IsOpen W := hV.isOpenMap_subtype_val _
    (h.isOpenMap _ (hN.preimage continuous_subtype_val))
  have hWV : W⊆V := by rintro z ⟨v,_,rfl⟩; exact v.property
  have hInv (w : W) : ((h.symm ⟨w.val,hWV w.property⟩ : U) : X)∈N := by
    obtain ⟨v,⟨u,hu,he⟩,hv⟩ := w.property
    have hv' : v=⟨w.val,hWV w.property⟩ := Subtype.ext hv
    have hu' : h u=⟨w.val,hWV w.property⟩ := he.trans hv'
    change (u : X)∈N at hu
    simpa only [←hu',h.symm_apply_apply] using hu
  let e : ↥(U∩N) ≃ₜ W := {
    toFun := fun z => ⟨((h ⟨z.val,z.property.1⟩ : V) : ℝ×ℝ),
      ⟨h ⟨z.val,z.property.1⟩,⟨⟨z.val,z.property.1⟩,z.property.2,rfl⟩,rfl⟩⟩
    invFun := fun w => ⟨((h.symm ⟨w.val,hWV w.property⟩ : U) : X),
      ⟨(h.symm ⟨w.val,hWV w.property⟩).property,hInv w⟩⟩
    left_inv := by intro z; apply Subtype.ext; exact congrArg (fun u : U => (u : X)) (h.symm_apply_apply ⟨z.val,z.property.1⟩)
    right_inv := by intro w; apply Subtype.ext; exact congrArg (fun v : V => (v : ℝ×ℝ)) (h.apply_symm_apply ⟨w.val,hWV w.property⟩)
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact continuous_subtype_val.comp (h.continuous.comp (continuous_subtype_val.subtype_mk _))
    continuous_invFun := by
      apply Continuous.subtype_mk
      exact continuous_subtype_val.comp (h.symm.continuous.comp (continuous_subtype_val.subtype_mk _)) }
  exact ⟨W,hW,e,by intro z hz; rfl⟩

/-- Pull back actual common-axis charts through an actual local homeomorphism;
its two full lifted sets are literal preimages of the source curve images. -/
theorem actual_crossing_axis_chart_lifts_through_local_homeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (q : X → Y) (hq : IsLocalHomeomorph q) (a b : Curve Y) (x : X)
    (hc : CrossesAt a b (q x)) :
    ∃ (U : Set X) (V : Set (ℝ×ℝ)) (hx : x∈U) (h : U ≃ₜ V),
      IsOpen U ∧ IsOpen V ∧ ((h ⟨x,hx⟩ : V) : ℝ×ℝ)=(0,0) ∧
      (∀ z (hz : z∈U),
        (q z∈a.image ↔ ((h ⟨z,hz⟩ : V) : ℝ×ℝ).1=0) ∧
        (q z∈b.image ↔ ((h ⟨z,hz⟩ : V) : ℝ×ℝ).2=0)) := by
  obtain ⟨A,B,hxA,h,hA,hB,hzero,haxes⟩ := hc
  obtain ⟨e,hxe,he⟩ := hq x
  let l := e.trans (OpenPartialHomeomorph.ofSet A hA)
  have hxl : x∈l.source := by
    change x∈e.source ∩ e ⁻¹' A
    exact ⟨hxe,by simpa [← he] using hxA⟩
  have ht : l.target⊆A := by
    intro z hz
    exact hz.1
  have htEq : A∩l.target=l.target := inter_eq_right.mpr ht
  obtain ⟨W,hW,hR,hRval⟩ :=
    actual_surface_crossing_chart_restrict_to_open A B hA hB h l.target l.open_target
  let E : l.source ≃ₜ W := l.toHomeomorphSourceTarget.trans
    ((Homeomorph.setCongr htEq).symm.trans hR)
  have hlq (z : X) : l z=q z := by
    change e z=q z
    exact (congrFun he z).symm
  have hqm (z : X) (hz : z∈l.source) : q z∈A := by
    simpa only [hlq] using ht (l.map_source hz)
  have hE (z : X) (hz : z∈l.source) :
      ((E ⟨z,hz⟩ : W) : ℝ×ℝ)=((h ⟨q z,hqm z hz⟩ : B) : ℝ×ℝ) := by
    change ((hR ⟨l z, _⟩ : W) : ℝ×ℝ)=_
    exact (hRval (l z) ⟨ht (l.map_source hz),l.map_source hz⟩).trans
      (by simp only [hlq])
  refine ⟨l.source,W,hxl,E,l.open_source,hW,?_,?_⟩
  · exact (hE x hxl).trans hzero
  · intro z hz
    rw [hE]
    exact haxes (q z) (hqm z hz)

#print axioms actual_surface_crossing_chart_restrict_to_open
#print axioms actual_crossing_axis_chart_lifts_through_local_homeomorph
