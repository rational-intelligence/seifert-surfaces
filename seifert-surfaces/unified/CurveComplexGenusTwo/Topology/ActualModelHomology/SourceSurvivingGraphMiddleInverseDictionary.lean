import CurveComplexGenusTwo.Topology.ActualModelHomology.ActualEdgeParameterQuotientCandidate
import CurveComplexGenusTwo.Topology.ActualModelHomology.SourceSurvivingHandleIntervalOpenEmbedding
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Piecewise
import Mathlib.Topology.Homotopy.Contractible
namespace CurveComplex.Hyperbolic.OneBoundaryRay
open Set Topology ContinuousMap
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 900000
theorem source_surviving_graph_middle_inverse_dictionary (p : ℕ) :
    let e : (Fin p × Bool) ≃ Fin (2*p) := Fintype.equivFinOfCardEq (by simp [Nat.mul_comm])
    ∃ V : Set (actualSurvivingBoundary p), IsOpen V ∧
      V=range (fun z : (Fin p × Bool) × Ioo (1/4:ℝ) (3/4:ℝ) =>
        handleEdge p z.1.1 z.1.2 ⟨z.2.val,⟨by linarith [z.2.property.1],by linarith [z.2.property.2]⟩⟩) ∧
      ∃ T : V ≃ₜ (Fin (2*p) × Ioo (1/4:ℝ) (3/4:ℝ)), ∀ z,
        (T.symm z).val=handleEdge p (e.symm z.1).1 (e.symm z.1).2
          ⟨z.2.val,⟨by linarith [z.2.property.1],by linarith [z.2.property.2]⟩⟩ := by
  classical
  have hHandleOpen (p : ℕ) (i : Fin p) (b : Bool) (a c : ℝ)
      (ha : 0<a) (hc : c<1) :
      ∃ h : C(Ioo a c,actualSurvivingBoundary p), IsOpenEmbedding h ∧
        ∀ t, h t=handleEdge p i b ⟨t.val,⟨(ha.trans t.property.1).le,(t.property.2.trans hc).le⟩⟩ := by
    classical
    have hRawArc (p : ℕ) (a b : ℝ) (hab : b-a < modelSideCount p)
        (hcap : ∀ s ∈ Ioo a b, Complex.ClosedUnitDisc.bdyPtOfReal (s/modelSideCount p) ∉ rawDeletedArc p) :
        ∃ q : C(Ioo a b,RawSurvivingBoundary p), IsOpenEmbedding q ∧
          ∀ s, q s=⟨⟨Complex.ClosedUnitDisc.bdyPtOfReal (s.val/modelSideCount p),hcap s s.property⟩,
            Circle.norm_coe _⟩ := by
      classical
      let d : C(Circle,Complex.ClosedUnitDisc) := {
        toFun := fun w => ⟨w.val,by simp⟩
        continuous_toFun := by fun_prop
      }
      let W : Set Circle := {w | d w ∉ rawDeletedArc p}
      have hWO : IsOpen W := (rawDeletedArc_isClosed p).isOpen_compl.preimage d.continuous
      let T : W ≃ₜ RawSurvivingBoundary p := {
        toFun := fun w => ⟨⟨d w.val,w.property⟩,Circle.norm_coe w.val⟩
        invFun := fun z => ⟨⟨z.val.val.val,by change z.val.val.val ∈ Metric.sphere (0:ℂ) 1; exact mem_sphere_zero_iff_norm.mpr z.property⟩,z.val.property⟩
        left_inv := by intro w; rfl
        right_inv := by intro z; rfl
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop
      }
      let k : ℝ := 2*Real.pi/modelSideCount p
      have hk : 0 < k := div_pos (by positivity) (modelSideCount_pos p)
      let f : C(Ioo a b,Circle) := ⟨fun s => Circle.exp (k*s.val),by fun_prop⟩
      have hfO : IsOpenMap f := by
        exact isLocalHomeomorph_circleExp.isOpenMap.comp
          ((Homeomorph.mulLeft₀ k hk.ne').isOpenMap.comp isOpen_Ioo.isOpenEmbedding_subtypeVal.isOpenMap)
      have hwidth : k*b-k*a < 2*Real.pi := by
        have hm := mul_lt_mul_of_pos_left hab hk
        have hc : k*modelSideCount p=2*Real.pi := div_mul_cancel₀ _ (modelSideCount_pos p).ne'
        nlinarith
      have hfI : Function.Injective f := by
        intro s t hst
        have he := Circle.exp_injOn_Icc hwidth
          ⟨mul_le_mul_of_nonneg_left s.property.1.le hk.le,mul_le_mul_of_nonneg_left s.property.2.le hk.le⟩
          ⟨mul_le_mul_of_nonneg_left t.property.1.le hk.le,mul_le_mul_of_nonneg_left t.property.2.le hk.le⟩ hst
        apply Subtype.ext
        exact mul_left_cancel₀ hk.ne' he
      have hfE : IsOpenEmbedding f :=
        IsOpenEmbedding.of_continuous_injective_isOpenMap f.continuous hfI hfO
      have hfD (s : Ioo a b) : d (f s)=Complex.ClosedUnitDisc.bdyPtOfReal (s.val/modelSideCount p) := by
        apply Subtype.ext
        change (Circle.exp (k*s.val) : ℂ)=Real.fourierChar (s.val/modelSideCount p)
        rw [Real.fourierChar_apply']
        have heq : k*s.val=2*Real.pi*(s.val/modelSideCount p) := by dsimp [k]; ring
        rw [heq]
      have hfW : ∀ s : Ioo a b, f s ∈ W := by
        intro s
        change d (f s) ∉ rawDeletedArc p
        rw [hfD]; exact hcap s s.property
      let fw : C(Ioo a b,W) := ⟨fun s => ⟨f s,hfW s⟩,f.continuous.subtype_mk hfW⟩
      have hfwE : IsOpenEmbedding fw :=
        (IsOpenEmbedding.of_comp_iff fw hWO.isOpenEmbedding_subtypeVal).mp hfE
      let q : C(Ioo a b,RawSurvivingBoundary p) := ⟨T ∘ fw,T.continuous.comp fw.continuous⟩
      refine ⟨q,T.isOpenEmbedding.comp hfwE,?_⟩
      intro s
      apply Subtype.ext;apply Subtype.ext
      exact hfD s
  
    let α : ℝ := 4*(i:ℝ)+(if b then 1 else 0)
    let β : ℝ := 4*(i:ℝ)+(if b then 4 else 3)
    let it : Ioo a c → unitInterval := fun t =>
      ⟨t.val,⟨(ha.trans t.property.1).le,(t.property.2.trans hc).le⟩⟩
    have hi : (i:ℝ)+1≤(p:ℝ) := by exact_mod_cast Nat.succ_le_of_lt i.isLt
    have hi0 : 0≤(i:ℝ) := by positivity
    have hSafe (e : Bool) (s : ℝ)
        (hs : s ∈ Ioo (if e then β-c else α+a) (if e then β-a else α+c)) :
        Complex.ClosedUnitDisc.bdyPtOfReal (s/modelSideCount p) ∉ rawDeletedArc p := by
      apply handle_boundary_not_mem_rawDeletedArc
      all_goals cases b <;> cases e <;> dsimp [α,β] at hs <;> linarith [hs.1,hs.2]
    have hbranch (e : Bool) :
        ∃ r : C(Ioo a c,RawSurvivingBoundary p), IsOpenEmbedding r ∧
          ∀ t, (r t).val.val=rawEdgePoint (.inl (i,b)) (it t) e := by
      let A : ℝ := if e then β-c else α+a
      let B : ℝ := if e then β-a else α+c
      have hw : B-A < modelSideCount p := by
        have hp0 : 0≤(p:ℝ) := by positivity
        cases e <;> dsimp [A,B,modelSideCount] <;> linarith
      obtain ⟨q,hq,hqv⟩ := hRawArc p A B hw (hSafe e)
      let T : Ioo a c ≃ₜ Ioo A B := {
        toFun := fun t => ⟨if e then β-t.val else α+t.val,by
          cases e <;> dsimp [A,B] <;> constructor <;> linarith [t.property.1,t.property.2]⟩
        invFun := fun s => ⟨if e then β-s.val else s.val-α,by
          cases e <;> dsimp [A,B] at s ⊢ <;> constructor <;> linarith [s.property.1,s.property.2]⟩
        left_inv := by intro t;apply Subtype.ext;cases e <;> simp
        right_inv := by intro s;apply Subtype.ext;cases e <;> simp
        continuous_toFun := by cases e <;> simp only [Bool.false_eq_true,↓reduceIte] <;> fun_prop
        continuous_invFun := by cases e <;> simp only [Bool.false_eq_true,↓reduceIte] <;> fun_prop
      }
      let r : C(Ioo a c,RawSurvivingBoundary p) := ⟨q ∘ T,q.continuous.comp T.continuous⟩
      refine ⟨r,hq.comp T.isOpenEmbedding,?_⟩
      intro t
      change (q (T t)).val.val=_
      rw [hqv]
      rw [rawEdgePoint_handle]
      rfl
    obtain ⟨r0,hr0,hr0v⟩ := hbranch false
    obtain ⟨r1,hr1,hr1v⟩ := hbranch true
    let h : C(Ioo a c,actualSurvivingBoundary p) :=
      (survivingBoundaryQuotientMap p).comp r0
    have hv (t : Ioo a c) : h t=handleEdge p i b (it t) := by
      apply Subtype.ext;apply Subtype.ext
      exact congrArg (Quot.mk _) (by
        rw [hr0v,rawEdgePoint_handle]
        rfl)
    have hfiber (t : Ioo a c) (z : RawSurvivingBoundary p) :
        h t=survivingBoundaryQuotientMap p z ↔ z=r0 t ∨ z=r1 t := by
      have h0 : 0<(it t:ℝ) := ha.trans t.property.1
      have h1 : (it t:ℝ)<1 := t.property.2.trans hc
      constructor
      · intro he
        have heq := congrArg (fun x : actualSurvivingBoundary p => x.val.val) he
        change Quot.mk _ (r0 t).val.val=Quot.mk _ z.val.val at heq
        rw [hr0v] at heq
        rcases (raw_quotient_interior_fiber (.inl (i,b)) (it t) h0 h1 z.val.val).mp heq with h|h
        · left; apply Subtype.ext;apply Subtype.ext; exact h.trans (hr0v t).symm
        · right;apply Subtype.ext;apply Subtype.ext;exact h.trans (hr1v t).symm
      · rintro (rfl|rfl)
        · rfl
        · apply Subtype.ext;apply Subtype.ext
          change Quot.mk _ (r0 t).val.val=Quot.mk _ (r1 t).val.val
          rw [hr0v,hr1v]
          exact Quot.sound (raw_edge_points_related (.inl (i,b)) (it t))
    have hInj : Function.Injective h := by
      intro t u he
      have heq := (hfiber t (r0 u)).mp he
      rcases heq with heq|heq
      · exact hr0.injective heq.symm
      · have heq' := congrArg (fun z : RawSurvivingBoundary p => z.val.val) heq
        rw [hr0v,hr1v] at heq'
        have ht0 := ha.trans u.property.1
        have ht1 := u.property.2.trans hc
        have hh := (rawEdgePoint_eq_iff (.inl (i,b)) (.inl (i,b)) (it u) (it t) ht0 ht1 false true).mp heq'
        exact Bool.noConfusion hh.2.2
    have hOpen : IsOpenMap h := by
      intro W hW
      apply (survivingBoundaryQuotientMap_isQuotientMap p).1.isOpen_preimage.mp
      have he : (survivingBoundaryQuotientMap p) ⁻¹' (h '' W)=r0 '' W ∪ r1 '' W := by
        ext z
        constructor
        · rintro ⟨t,ht,he⟩
          rcases (hfiber t z).mp he with hz|hz
          · exact Or.inl ⟨t,ht,hz.symm⟩
          · exact Or.inr ⟨t,ht,hz.symm⟩
        · rintro (⟨t,ht,rfl⟩|⟨t,ht,rfl⟩)
          · exact ⟨t,ht,rfl⟩
          · exact ⟨t,ht,(hfiber t (r1 t)).mpr (Or.inr rfl)⟩
      rw [he]
      exact (hr0.isOpenMap W hW).union (hr1.isOpenMap W hW)
    exact ⟨h,IsOpenEmbedding.of_continuous_injective_isOpenMap h.continuous hInj hOpen,hv⟩
  let J := Ioo (1/4:ℝ) (3/4:ℝ)
  let it : J → unitInterval := fun t => ⟨t.val,⟨by linarith [t.property.1],by linarith [t.property.2]⟩⟩
  have it0 (t : J) : 0<(it t:ℝ) := by dsimp [it];linarith [t.property.1]
  have it1 (t : J) : (it t:ℝ)<1 := by dsimp [it];linarith [t.property.2]
  have he (d : Fin p × Bool) :
      ∃ h : C(J,actualSurvivingBoundary p), IsOpenEmbedding h ∧
        ∀ t, h t=handleEdge p d.1 d.2 (it t) :=
    hHandleOpen p d.1 d.2 (1/4) (3/4) (by norm_num) (by norm_num)
  choose h hh hv using he
  let g : C((Fin p × Bool) × J,actualSurvivingBoundary p) := {
    toFun := fun z => h z.1 z.2
    continuous_toFun := continuous_prod_of_discrete_left.mpr (fun d => (h d).continuous)
  }
  have hgInj : Function.Injective g := by
    intro z w heq
    change h z.1 z.2=h w.1 w.2 at heq
    rw [hv,hv] at heq
    have heq' := congrArg (fun x : actualSurvivingBoundary p => x.val.val) heq
    change Quot.mk _ (handleEdgeRaw p z.1.1 z.1.2 (it z.2)).val.val=
      Quot.mk _ (handleEdgeRaw p w.1.1 w.1.2 (it w.2)).val.val at heq'
    have heq'' : Quot.mk (LeanEval.Topology.ClassificationOfSurfaces.OrientableRel p 1)
        (rawEdgePoint (.inl z.1) (it z.2) false)=Quot.mk _ (rawEdgePoint (.inl w.1) (it w.2) false) := by
      have hz : rawEdgePoint (.inl z.1) (it z.2) false=
          Complex.ClosedUnitDisc.bdyPtOfReal (handleNumerator z.1.1 z.1.2 (it z.2)/modelSideCount p) := by
        rcases z with ⟨⟨i,b⟩,t⟩
        rw [rawEdgePoint_handle]
        rfl
      have hw : rawEdgePoint (.inl w.1) (it w.2) false=
          Complex.ClosedUnitDisc.bdyPtOfReal (handleNumerator w.1.1 w.1.2 (it w.2)/modelSideCount p) := by
        rcases w with ⟨⟨i,b⟩,t⟩
        rw [rawEdgePoint_handle]
        rfl
      rw [hz,hw]
      exact heq' 
    have hf := (raw_quotient_interior_fiber (.inl z.1) (it z.2) (it0 z.2) (it1 z.2)
      (rawEdgePoint (.inl w.1) (it w.2) false)).mp heq''
    have hm : rawEdgePoint (.inl w.1) (it w.2) false ∈ rawInteriorPair (.inl z.1) (it z.2) := hf
    have hh := (rawEdgePoint_mem_interior_pair_iff (.inl z.1) (.inl w.1)
      (it z.2) (it w.2) (it0 z.2) (it1 z.2) false).mp hm
    apply Prod.ext (Sum.inl.inj hh.1)
    apply Subtype.ext
    exact congrArg (fun t : unitInterval => t.val) hh.2
  have hgOpen : IsOpenMap g := by
    intro W hW
    have hs (d : Fin p × Bool) : IsOpen {t : J | (d,t) ∈ W} :=
      hW.preimage (continuous_const.prodMk continuous_id)
    have him : g '' W=⋃ d : Fin p × Bool, h d '' {t : J | (d,t) ∈ W} := by
      ext x
      simp only [mem_image,mem_iUnion,mem_ofPred_eq]
      constructor
      · rintro ⟨⟨d,t⟩,ht,rfl⟩
        exact ⟨d,t,ht,rfl⟩
      · rintro ⟨d,t,ht,rfl⟩
        exact ⟨(d,t),ht,rfl⟩
    rw [him]
    exact isOpen_iUnion (fun d => (hh d).isOpenMap _ (hs d))
  have hgE : IsOpenEmbedding g :=
    IsOpenEmbedding.of_continuous_injective_isOpenMap g.continuous hgInj hgOpen
  let V := range g
  have hV : IsOpen V := hgE.isOpen_range
  let q : C((Fin p × Bool) × J,V) := ⟨fun z => ⟨g z,⟨z,rfl⟩⟩,g.continuous.subtype_mk _⟩
  have hqE : IsOpenEmbedding q :=
    (IsOpenEmbedding.of_comp_iff q hV.isOpenEmbedding_subtypeVal).mp hgE
  have hqS : Function.Surjective q := by
    rintro ⟨x,z,hz⟩
    exact ⟨z,Subtype.ext hz⟩
  let T := ((isHomeomorph_iff_isEmbedding_surjective).mpr ⟨hqE.isEmbedding,hqS⟩).homeomorph q
  let e : (Fin p × Bool) ≃ Fin (2*p) := Fintype.equivFinOfCardEq (by simp [Nat.mul_comm])
  let TFin : V ≃ₜ (Fin (2*p) × J) := T.symm.trans
    ((Homeomorph.ofDiscrete e).prodCongr (Homeomorph.refl J))
  have hRange : V=range (fun z : (Fin p × Bool) × J =>
      handleEdge p z.1.1 z.1.2 (it z.2)) := by
    change range g=_
    congr 1;funext z;exact hv z.1 z.2
  refine ⟨V,hV,hRange,TFin,?_⟩
  intro z
  change g (e.symm z.1,z.2)=_
  exact hv (e.symm z.1) z.2
end CurveComplex.Hyperbolic.OneBoundaryRay
