import ShearHelpers

set_option maxSynthPendingDepth 3
set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology
namespace SeifertSurfaces.LongitudeProducers.CollarCutHelpers.Remaining
open Foundations
noncomputable section

section Pasting
variable {K : OrientedKnot} {T : TubularNeighborhood K} (D : TubeCoordinates T)
  (Psi : Diffeomorph TubeModel TubeModel TubeDomain TubeDomain ∞) (S : TubeSupport Psi)

theorem P1_inverse_support :
    (∀ p ∉ S.compact, Psi.symm p=p) ∧
    Psi '' S.compact = S.compact ∧ Psi.symm '' S.compact = S.compact ∧
    IsCompact (T.tube 0 '' S.compact) ∧ IsClosed (T.tube 0 '' S.compact) ∧
    T.tube 0 '' S.compact ⊆ (tubeImageOpen T : Set ThreeSphere) := by
  have hinv : ∀ p ∉ S.compact, Psi.symm p = p := by
    intro p hp
    apply Psi.injective
    change Psi (Psi.symm p) = Psi p
    rw [Psi.apply_symm_apply, S.outside p hp]
  have hforward : Psi '' S.compact = S.compact := by
    ext p
    constructor
    · rintro ⟨q,hq,rfl⟩
      by_contra hp
      have heq := hinv (Psi q) hp
      rw [Psi.symm_apply_apply] at heq
      exact hp (heq ▸ hq)
    · intro hp
      refine ⟨Psi.symm p, ?_, Psi.apply_symm_apply p⟩
      by_contra hq
      have heq := S.outside (Psi.symm p) hq
      rw [Psi.apply_symm_apply] at heq
      exact hq (heq ▸ hp)
  have hbackward : Psi.symm '' S.compact = S.compact := by
    ext p
    constructor
    · rintro ⟨q,hq,rfl⟩
      by_contra hp
      have heq := S.outside (Psi.symm q) hp
      rw [Psi.apply_symm_apply] at heq
      exact hp (heq ▸ hq)
    · intro hp
      refine ⟨Psi p, ?_, Psi.symm_apply_apply p⟩
      by_contra hq
      have heq := hinv (Psi p) hq
      rw [Psi.symm_apply_apply] at heq
      exact hq (heq ▸ hp)
  have hcompact := S.isCompact.image (T.smoothEmbedding 0).isEmbedding.continuous
  exact ⟨hinv, hforward, hbackward, hcompact, hcompact.isClosed,
    fun _ hx => by obtain ⟨p,hp,rfl⟩ := hx; exact ⟨p,rfl⟩⟩

structure TubeConjugation where
  map : OpenPartialHomeomorph ThreeSphere ThreeSphere
  source_eq : map.source = (tubeImageOpen T : Set ThreeSphere)
  target_eq : map.target = (tubeImageOpen T : Set ThreeSphere)
  inside : ∀ p, map (T.tube 0 p)=T.tube 0 (Psi p)
  inverse_inside : ∀ p, map.symm (T.tube 0 p)=T.tube 0 (Psi.symm p)
  D_equation : ∀ y : tubeImageOpen T, map y = T.tube 0 (Psi (D.map.symm y))
  D_inverse_equation : ∀ y : tubeImageOpen T, map.symm y = T.tube 0 (Psi.symm (D.map.symm y))
  smooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ map map.source
  inverse_smooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ map.symm map.target
  outside : ∀ x ∈ map.source, x ∉ T.tube 0 '' S.compact → map x=x ∧ map.symm x=x

theorem P2_inside_conjugation : Nonempty (TubeConjugation D Psi S) := by
  classical
  let U := tubeImageOpen T
  let H := D.map.symm.trans (Psi.trans D.map)
  let extend (J : Diffeomorph (𝓡 3) (𝓡 3) U U ∞) (x : ThreeSphere) : ThreeSphere :=
    if hx : x ∈ (U : Set ThreeSphere) then J ⟨x,hx⟩ else x
  have hext (J : Diffeomorph (𝓡 3) (𝓡 3) U U ∞) (x : ThreeSphere)
      (hx : x ∈ (U : Set ThreeSphere)) : extend J x = (J ⟨x,hx⟩ : ThreeSphere) := by
    dsimp only [extend]
    rw [dif_pos hx]
  have hrestrict (J : Diffeomorph (𝓡 3) (𝓡 3) U U ∞) :
      (fun x : U => extend J x) = Subtype.val ∘ J := by
    funext x
    exact hext J x (show (x : ThreeSphere) ∈ (U : Set ThreeSphere) from x.property)
  have hsmooth (J : Diffeomorph (𝓡 3) (𝓡 3) U U ∞) :
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ (extend J) (U : Set ThreeSphere) := by
    intro x hx
    have hres : ContMDiff (𝓡 3) (𝓡 3) ∞ (fun x : U => extend J x) := by
      rw [hrestrict]
      exact contMDiff_subtype_val.comp J.contMDiff
    exact ((contMDiffAt_subtype_iff (x := (⟨x,hx⟩ : U))).mp (hres ⟨x,hx⟩)).contMDiffWithinAt
  have hmem (J : Diffeomorph (𝓡 3) (𝓡 3) U U ∞) (x : ThreeSphere)
      (hx : x ∈ (U : Set ThreeSphere)) : extend J x ∈ (U : Set ThreeSphere) := by
    rw [hext J x hx]
    exact (J ⟨x,hx⟩).property
  have hleft (J : Diffeomorph (𝓡 3) (𝓡 3) U U ∞) (x : ThreeSphere)
      (hx : x ∈ (U : Set ThreeSphere)) : extend J.symm (extend J x) = x := by
    rw [hext J x hx, hext J.symm _ (show (J ⟨x,hx⟩ : ThreeSphere) ∈
      (U : Set ThreeSphere) from (J ⟨x,hx⟩).property)]
    exact congrArg Subtype.val (J.symm_apply_apply ⟨x,hx⟩)
  let e : OpenPartialHomeomorph ThreeSphere ThreeSphere := {
    toPartialEquiv := {
      toFun := extend H
      invFun := extend H.symm
      source := U
      target := U
      map_source' := hmem H
      map_target' := hmem H.symm
      left_inv' := hleft H
      right_inv' := hleft H.symm }
    open_source := U.isOpen
    open_target := U.isOpen
    continuousOn_toFun := (hsmooth H).continuousOn
    continuousOn_invFun := (hsmooth H.symm).continuousOn }
  have hinside (p : TubeDomain) : e (T.tube 0 p) = T.tube 0 (Psi p) := by
    have hp : T.tube 0 p ∈ (U : Set ThreeSphere) := ⟨p,rfl⟩
    have hep : (⟨T.tube 0 p,hp⟩ : U) = D.map p := Subtype.ext (D.equation p).symm
    change extend H (T.tube 0 p) = _
    simp only [extend, dif_pos hp, hep]
    change (D.map (Psi (D.map.symm (D.map p))) : ThreeSphere) = _
    rw [D.map.symm_apply_apply]
    exact D.equation (Psi p)
  have hinverse (p : TubeDomain) : e.symm (T.tube 0 p) = T.tube 0 (Psi.symm p) := by
    have hp : T.tube 0 p ∈ (U : Set ThreeSphere) := ⟨p,rfl⟩
    have hep : (⟨T.tube 0 p,hp⟩ : U) = D.map p := Subtype.ext (D.equation p).symm
    change extend H.symm (T.tube 0 p) = _
    simp only [extend, dif_pos hp, hep]
    change (D.map (Psi.symm (D.map.symm (D.map p))) : ThreeSphere) = _
    rw [D.map.symm_apply_apply]
    exact D.equation (Psi.symm p)
  refine ⟨{ map := e
            source_eq := rfl
            target_eq := rfl
            inside := hinside
            inverse_inside := hinverse
            D_equation := ?_
            D_inverse_equation := ?_
            smooth := hsmooth H
            inverse_smooth := hsmooth H.symm
            outside := ?_ }⟩
  · intro y
    have hy : T.tube 0 (D.map.symm y) = (y : ThreeSphere) :=
      (D.equation (D.map.symm y)).symm.trans (congrArg Subtype.val (D.map.apply_symm_apply y))
    rw [← hy]
    exact hinside (D.map.symm y)
  · intro y
    have hy : T.tube 0 (D.map.symm y) = (y : ThreeSphere) :=
      (D.equation (D.map.symm y)).symm.trans (congrArg Subtype.val (D.map.apply_symm_apply y))
    rw [← hy]
    exact hinverse (D.map.symm y)
  · intro x hx hout
    let p := D.map.symm (⟨x,hx⟩ : U)
    have hp : T.tube 0 p = x :=
      (D.equation p).symm.trans (congrArg Subtype.val (D.map.apply_symm_apply ⟨x,hx⟩))
    have hps : p ∉ S.compact := fun h => hout ⟨p,h,hp⟩
    have hinv := (P1_inverse_support (T := T) Psi S).1 p hps
    constructor
    · rw [← hp, hinside, S.outside p hps]
    · rw [← hp, hinverse, hinv]

def pastedTubeForward (P : TubeConjugation D Psi S) (x : ThreeSphere) : ThreeSphere :=
  @ite ThreeSphere (x ∈ (tubeImageOpen T : Set ThreeSphere)) (Classical.propDecidable _)
    (P.map x) x
def pastedTubeInverse (P : TubeConjugation D Psi S) (x : ThreeSphere) : ThreeSphere :=
  @ite ThreeSphere (x ∈ (tubeImageOpen T : Set ThreeSphere)) (Classical.propDecidable _)
    (P.map.symm x) x

theorem P3_pasting_and_inverse (P : TubeConjugation D Psi S) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (pastedTubeForward D Psi S P) ∧
    ContMDiff (𝓡 3) (𝓡 3) ∞ (pastedTubeInverse D Psi S P) ∧
    Function.LeftInverse (pastedTubeInverse D Psi S P) (pastedTubeForward D Psi S P) ∧
    Function.RightInverse (pastedTubeInverse D Psi S P) (pastedTubeForward D Psi S P) ∧
    (∀ x ∉ Set.range (T.tube 0), ∃ U : Set ThreeSphere, IsOpen U ∧ x ∈ U ∧
      EqOn (pastedTubeForward D Psi S P) id U ∧ EqOn (pastedTubeInverse D Psi S P) id U) := by
  classical
  let C := T.tube 0 '' S.compact
  have hclosed : IsClosed C := (P1_inverse_support (T := T) Psi S).2.2.2.2.1
  have hsub : C ⊆ (tubeImageOpen T : Set ThreeSphere) :=
    (P1_inverse_support (T := T) Psi S).2.2.2.2.2
  have hfix (x : ThreeSphere) (hx : x ∉ C) :
      pastedTubeForward D Psi S P x = x ∧ pastedTubeInverse D Psi S P x = x := by
    by_cases hin : x ∈ (tubeImageOpen T : Set ThreeSphere)
    · have hp : x ∈ P.map.source := by rw [P.source_eq]; exact hin
      have heq := P.outside x hp hx
      simpa only [pastedTubeForward, pastedTubeInverse, if_pos hin] using heq
    · simp only [pastedTubeForward, pastedTubeInverse, if_neg hin, and_self]
  have hforward : ContMDiff (𝓡 3) (𝓡 3) ∞ (pastedTubeForward D Psi S P) := by
    intro x
    by_cases hin : x ∈ (tubeImageOpen T : Set ThreeSphere)
    · have hp : x ∈ P.map.source := by rw [P.source_eq]; exact hin
      apply (P.smooth.contMDiffAt (P.map.open_source.mem_nhds hp)).congr_of_eventuallyEq
      filter_upwards [(tubeImageOpen T).isOpen.mem_nhds hin] with y hy
      exact if_pos hy
    · have hx : x ∉ C := fun hc => hin (hsub hc)
      apply contMDiffAt_id.congr_of_eventuallyEq
      filter_upwards [hclosed.isOpen_compl.mem_nhds hx] with y hy
      exact (hfix y hy).1
  have hbackward : ContMDiff (𝓡 3) (𝓡 3) ∞ (pastedTubeInverse D Psi S P) := by
    intro x
    by_cases hin : x ∈ (tubeImageOpen T : Set ThreeSphere)
    · have hp : x ∈ P.map.target := by rw [P.target_eq]; exact hin
      apply (P.inverse_smooth.contMDiffAt (P.map.open_target.mem_nhds hp)).congr_of_eventuallyEq
      filter_upwards [(tubeImageOpen T).isOpen.mem_nhds hin] with y hy
      exact if_pos hy
    · have hx : x ∉ C := fun hc => hin (hsub hc)
      apply contMDiffAt_id.congr_of_eventuallyEq
      filter_upwards [hclosed.isOpen_compl.mem_nhds hx] with y hy
      exact (hfix y hy).2
  have hleft : Function.LeftInverse (pastedTubeInverse D Psi S P) (pastedTubeForward D Psi S P) := by
    intro x
    by_cases hin : x ∈ (tubeImageOpen T : Set ThreeSphere)
    · have hp : x ∈ P.map.source := by rw [P.source_eq]; exact hin
      have hm : P.map x ∈ (tubeImageOpen T : Set ThreeSphere) := by
        rw [← P.target_eq]; exact P.map.map_source hp
      simpa only [pastedTubeForward, pastedTubeInverse, if_pos hin, if_pos hm] using P.map.left_inv hp
    · simp only [pastedTubeForward, pastedTubeInverse, if_neg hin]
  have hright : Function.RightInverse (pastedTubeInverse D Psi S P) (pastedTubeForward D Psi S P) := by
    intro x
    by_cases hin : x ∈ (tubeImageOpen T : Set ThreeSphere)
    · have hp : x ∈ P.map.target := by rw [P.target_eq]; exact hin
      have hm : P.map.symm x ∈ (tubeImageOpen T : Set ThreeSphere) := by
        rw [← P.source_eq]; exact P.map.map_target hp
      simpa only [pastedTubeForward, pastedTubeInverse, if_pos hin, if_pos hm] using P.map.right_inv hp
    · simp only [pastedTubeForward, pastedTubeInverse, if_neg hin]
  refine ⟨hforward,hbackward,hleft,hright,?_⟩
  intro x hx
  refine ⟨Cᶜ,hclosed.isOpen_compl,fun hc => hx (hsub hc),?_,?_⟩
  · exact fun y hy => (hfix y hy).1
  · exact fun y hy => (hfix y hy).2

theorem P4_sphere_extension_assembly (P : TubeConjugation D Psi S) :
    ∃ A : SphereTubeExtension T D Psi,
      (A.ambient : ThreeSphere → ThreeSphere)=pastedTubeForward D Psi S P ∧
      (A.ambient.symm : ThreeSphere → ThreeSphere)=pastedTubeInverse D Psi S P := by
  obtain ⟨hf,hg,hl,hr,hn⟩ := P3_pasting_and_inverse D Psi S P
  let ambient : Diffeomorph (𝓡 3) (𝓡 3) ThreeSphere ThreeSphere ∞ := {
    toEquiv := { toFun := pastedTubeForward D Psi S P
                 invFun := pastedTubeInverse D Psi S P
                 left_inv := hl
                 right_inv := hr }
    contMDiff_toFun := hf
    contMDiff_invFun := hg }
  have hin (p : TubeDomain) : T.tube 0 p ∈ (tubeImageOpen T : Set ThreeSphere) := ⟨p,rfl⟩
  let A : SphereTubeExtension T D Psi := {
    ambient := ambient
    inside := by intro p; change pastedTubeForward D Psi S P (T.tube 0 p) = _
                 rw [pastedTubeForward,if_pos (hin p)]; exact P.inside p
    inverse_inside := by intro p; change pastedTubeInverse D Psi S P (T.tube 0 p) = _
                         rw [pastedTubeInverse,if_pos (hin p)]; exact P.inverse_inside p
    outside := by intro x hx; exact if_neg hx
    core := by
      intro z
      let p : TubeDomain := (z,⟨0,by simp [tubeDiskOpen]⟩)
      have hp : T.tube 0 p = K.component 0 z := T.core 0 z
      change pastedTubeForward D Psi S P (K.component 0 z) = _
      rw [← hp,pastedTubeForward,if_pos (hin p),P.inside p,S.core z p.2 rfl]
    identity_near_outside := hn }
  exact ⟨A,rfl,rfl⟩
end Pasting

end
end SeifertSurfaces.LongitudeProducers.CollarCutHelpers.Remaining
