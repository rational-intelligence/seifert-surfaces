import ActualAnnulusWholeFamilyWithSideChoiceV780

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Topology
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
noncomputable section
namespace CompressionActualVariableAnnulusOuterProductV786

/-- Distinct normal levels separate a whole family of annulus embeddings.
    Thus the complete literal outer band can transition to the contained band
    at the common disk-collar level while retaining a joint product embedding. -/
theorem variable_annulus_outer_product
    {Y : Type} [TopologicalSpace Y] [T2Space Y]
    (wide : C(Time × (Circle × Time),Y)) (hwide : IsEmbedding wide)
    (H : C(Time × (Circle × Time),Circle × Time))
    (hH : ∀ a,IsEmbedding (fun p => H (a,p)))
    (hH1 : ∀ p,H (1,p) = p)
    (hHcore : ∀ a z,H (a,(z,middleTime)) = (z,middleTime))
    (r : Time) (hr : 0 < r.val) :
    ∃ out : C((Circle × Time) × Time,Y),IsEmbedding out ∧
      (∀ z t,out ((z,0),t) = wide (0,(z,t))) ∧
      (∀ z t,out ((z,r),t) = wide (r,H (0,(z,t)))) ∧
      ∀ z s,out ((z,s),middleTime) = wide (s,(z,middleTime)) := by
  let a : Time → Time := fun s => Set.projIcc 0 1 zero_le_one (1-s.val/r.val)
  have hac : Continuous a := continuous_projIcc.comp
    (continuous_const.sub (continuous_subtype_val.div_const _))
  have ha0 : a 0 = 1 := by
    apply Subtype.ext
    dsimp [a]
    norm_num
  have har : a r = 0 := by
    apply Subtype.ext
    dsimp [a]
    rw [div_self hr.ne']
    norm_num
  let Q : (Circle × Time) × Time → Time × (Circle × Time) :=
    fun p => (p.1.2,H (a p.1.2,(p.1.1,p.2)))
  have hQc : Continuous Q := continuous_fst.snd.prodMk (H.continuous.comp
    ((hac.comp continuous_fst.snd).prodMk (continuous_fst.fst.prodMk continuous_snd)))
  have hQi : Function.Injective Q := by
    intro p q he
    have hs := congrArg (fun x : Time × (Circle × Time) => x.1) he
    have hparam := congrArg (fun x : Time × (Circle × Time) => x.2) he
    change p.1.2 = q.1.2 at hs
    change H (a p.1.2,(p.1.1,p.2)) = H (a q.1.2,(q.1.1,q.2)) at hparam
    rw [← hs] at hparam
    have hh := (hH (a p.1.2)).injective hparam
    have hz := congrArg (fun x : Circle × Time => x.1) hh
    have ht := congrArg (fun x : Circle × Time => x.2) hh
    exact Prod.ext (Prod.ext hz hs) ht
  let out : C((Circle × Time) × Time,Y) := ⟨wide ∘ Q,wide.continuous.comp hQc⟩
  refine ⟨out,(out.continuous.isClosedEmbedding (hwide.injective.comp hQi)).isEmbedding,?_,?_,?_⟩
  · intro z t
    change wide (0,H (a 0,(z,t))) = _
    rw [ha0,hH1]
  · intro z t
    change wide (r,H (a r,(z,t))) = _
    rw [har]
  · intro z s
    change wide (s,H (a s,(z,middleTime))) = _
    rw [hHcore]

end CompressionActualVariableAnnulusOuterProductV786
