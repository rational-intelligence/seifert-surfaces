import Section5DistanceStripDiffeomorphV489
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.LongitudeProducers SeifertSurfaces.LongitudeProducers.CollarCutHelpers
noncomputable section
local instance : TopologicalSpace PolarDomain := inferInstanceAs (TopologicalSpace (Circle × (Circle × Time)))
local instance : ChartedSpace (ModelProd (Euc 1) (ModelProd (Euc 1) (EuclideanHalfSpace 1))) PolarDomain :=
  inferInstanceAs (ChartedSpace (ModelProd (Euc 1) (ModelProd (Euc 1) (EuclideanHalfSpace 1))) (Circle × (Circle × Time)))
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {D : TubeCoordinates T} (P : GivenExteriorPolarCollar E D)

def polarProductAssociation : Diffeomorph (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) PolarModel
    longitudeProductStrip longitudePolarStrip ∞ where
  toFun p := ⟨(p.val.1.1,p.val.1.2,p.val.2),p.property⟩
  invFun q := ⟨((q.val.1,q.val.2.1),q.val.2.2),q.property⟩
  left_inv p := rfl
  right_inv p := rfl
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff longitudePolarStrip _).mp
    exact contMDiff_subtype_val.fst.fst.prodMk
      (contMDiff_subtype_val.fst.snd.prodMk contMDiff_subtype_val.snd)
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff longitudeProductStrip _).mp
    exact (contMDiff_subtype_val.fst.prodMk contMDiff_subtype_val.snd.fst).prodMk
      contMDiff_subtype_val.snd.snd

def polarProductCoordinates : Diffeomorph (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) (𝓡∂ 3)
    longitudeProductStrip P.image ∞ := polarProductAssociation.trans P.coordinates

include P in
theorem polar_collar_restrict_open (O : TopologicalSpace.Opens ((Circle × Circle) × Time))
    (hO : ∀ q ∈ O, (q.2 : ℝ) < 1) :
    ∃ V : TopologicalSpace.Opens E.Carrier,
    ∃ d : Diffeomorph (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) (𝓡∂ 3) O V ∞,
      ∀ q : O, (d q : E.Carrier) = givenExteriorPolarMap E (q.val.1.1,q.val.1.2,q.val.2) := by
  let e := polarProductCoordinates P
  let A : Set longitudeProductStrip := {q | q.val ∈ O}
  have hA : IsOpen A := O.isOpen.preimage continuous_subtype_val
  let B : Set P.image := e '' A
  have hB : IsOpen B := e.toHomeomorph.isOpenMap A hA
  let V : TopologicalSpace.Opens E.Carrier :=
    ⟨((↑) : P.image → E.Carrier) '' B,P.image.isOpen.isOpenMap_subtype_val B hB⟩
  let inc : O → longitudeProductStrip := fun q => ⟨q.val,hO q.val q.property⟩
  have hinc : ContMDiff (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1))
      (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) ∞ inc := by
    apply (ContMDiff.subtypeVal_comp_iff longitudeProductStrip _).mp
    exact contMDiff_subtype_val
  let f : O → V := fun q => ⟨e (inc q),e (inc q),⟨inc q,q.property,rfl⟩,rfl⟩
  have hVB (y : V) : y.val ∈ P.image := by
    obtain ⟨z,hz,heq⟩ := y.property
    exact heq ▸ z.property
  let back : V → P.image := fun y => ⟨y.val,hVB y⟩
  have hbackA (y : V) : (e.symm (back y)).val ∈ O := by
    obtain ⟨z,⟨q,hq,heq⟩,heq'⟩ := y.property
    have hz : back y = z := Subtype.ext heq'.symm
    rw [hz,← heq,Diffeomorph.symm_apply_apply]
    exact hq
  let inv : V → O := fun y => ⟨(e.symm (back y)).val,hbackA y⟩
  have hleft (q : O) : inv (f q) = q := by
    apply Subtype.ext
    change (e.symm (back (f q))).val = q.val
    have heq : back (f q) = e (inc q) := Subtype.ext rfl
    rw [heq,Diffeomorph.symm_apply_apply]
  have hright (y : V) : f (inv y) = y := by
    apply Subtype.ext
    change (e (inc (inv y)) : E.Carrier) = y.val
    have heq : inc (inv y) = e.symm (back y) := Subtype.ext rfl
    rw [heq,Diffeomorph.apply_symm_apply]
  have hf : ContMDiff (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) (𝓡∂ 3) ∞ f := by
    apply (ContMDiff.subtypeVal_comp_iff V _).mp
    change ContMDiff _ _ ∞ (fun q : O => (e (inc q) : E.Carrier))
    exact contMDiff_subtype_val.comp (e.contMDiff.comp hinc)
  have hi : ContMDiff (𝓡∂ 3) (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) ∞ inv := by
    apply (ContMDiff.subtypeVal_comp_iff O _).mp
    have hb : ContMDiff (𝓡∂ 3) (𝓡∂ 3) ∞ back := by
      apply (ContMDiff.subtypeVal_comp_iff P.image _).mp
      exact contMDiff_subtype_val
    change ContMDiff _ _ ∞ (fun y : V => (e.symm (back y)).val)
    exact contMDiff_subtype_val.comp (e.symm.contMDiff.comp hb)
  refine ⟨V,⟨⟨f,inv,hleft,hright⟩,hf,hi⟩,?_⟩
  intro q
  exact P.equation (polarProductAssociation (inc q))

#print axioms polar_collar_restrict_open
end
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
