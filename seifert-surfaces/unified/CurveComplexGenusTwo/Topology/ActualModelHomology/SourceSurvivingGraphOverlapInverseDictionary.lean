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
theorem source_surviving_graph_overlap_inverse_dictionary (p : ℕ) :
    let e : (Fin p × Bool) ≃ Fin (2*p) := Fintype.equivFinOfCardEq (by simp [Nat.mul_comm])
    ∃ U V : Set (actualSurvivingBoundary p), IsOpen U ∧ IsOpen V ∧ U∪V=univ ∧
      (∀ i b (t : unitInterval), handleEdge p i b t ∈ U ↔ (t:ℝ)<3/8 ∨ 5/8<(t:ℝ)) ∧
      (∀ x : actualSurvivingBoundary p, ∀ t : unitInterval, (t:ℝ)<1 →
        x.val.val=Quot.mk (LeanEval.Topology.ClassificationOfSurfaces.OrientableRel p 1)
          (rawEdgePoint (p:=p) (.inr ()) t false) → x∈U) ∧
      V=range (fun z : (Fin p × Bool) × Ioo (1/4:ℝ) (3/4:ℝ) =>
        handleEdge p z.1.1 z.1.2 ⟨z.2.val,⟨by linarith [z.2.property.1],by linarith [z.2.property.2]⟩⟩) ∧
      ∃ T : ↥(U∩V) ≃ₜ ((Fin (2*p) × Bool) × Ioo (1/4:ℝ) (3/8:ℝ)), ∀ z,
        (T.symm z).val=handleEdge p (e.symm z.1.1).1 (e.symm z.1.1).2
          ⟨if z.1.2 then 1-z.2.val else z.2.val,by
            cases z.1.2 <;> simp only [Bool.false_eq_true,↓reduceIte] <;>
              constructor <;> linarith [z.2.property.1,z.2.property.2]⟩ := by
  classical
  have hCover (p : ℕ) :
      ∃ U V : Set (actualSurvivingBoundary p), IsOpen U ∧ IsOpen V ∧ U∪V=univ ∧
        (∀ i b (t : unitInterval), handleEdge p i b t ∈ U ↔ (t:ℝ)<3/8 ∨ 5/8<(t:ℝ)) ∧
        (∀ x : actualSurvivingBoundary p, ∀ t : unitInterval, (t:ℝ)<1 →
          x.val.val=Quot.mk (LeanEval.Topology.ClassificationOfSurfaces.OrientableRel p 1)
            (rawEdgePoint (p:=p) (.inr ()) t false) → x∈U) ∧
        V=range (fun z : (Fin p × Bool) × Ioo (1/4:ℝ) (3/4:ℝ) =>
          handleEdge p z.1.1 z.1.2 ⟨z.2.val,⟨by linarith [z.2.property.1],by linarith [z.2.property.2]⟩⟩) := by
    classical
    have hCentralClosed (p : ℕ) (i : Fin p) (b : Bool) (a c : ℝ) (ha : 0<a) (hc : c<1) :
        IsClosed (range (fun t : Icc a c => handleEdge p i b
          ⟨t.val,⟨by linarith [t.property.1],by linarith [t.property.2]⟩⟩)) := by
      classical
      let J := Icc a c
      let it : J → unitInterval := fun t =>
        ⟨t.val,⟨by linarith [t.property.1],by linarith [t.property.2]⟩⟩
      have hit0 (t : J) : 0<(it t:ℝ) := by dsimp [it];linarith [t.property.1]
      have hit1 (t : J) : (it t:ℝ)<1 := by dsimp [it];linarith [t.property.2]
      have hs (t : J) (e : Bool) : rawEdgePoint (.inl (i,b)) (it t) e ∉ rawDeletedArc p := by
        rw [rawEdgePoint_handle]
        unfold rawBoundaryPoint
        have hi : (i:ℝ)+1≤(p:ℝ) := by exact_mod_cast Nat.succ_le_of_lt i.isLt
        have hi0 : 0≤(i:ℝ) := by positivity
        apply handle_boundary_not_mem_rawDeletedArc
        all_goals cases e <;> cases b <;> simp only [Bool.false_eq_true,↓reduceIte] <;>
          nlinarith [hit0 t,hit1 t]
      let r (e : Bool) : C(J,RawSurvivingBoundary p) := {
        toFun := fun t => ⟨⟨rawEdgePoint (.inl (i,b)) (it t) e,hs t e⟩,by
          change ‖(rawEdgePoint (.inl (i,b)) (it t) e:ℂ)‖=1
          rw [rawEdgePoint_handle]
          exact Circle.norm_coe _⟩
        continuous_toFun := by
          apply Continuous.subtype_mk
          apply Continuous.subtype_mk
          apply Continuous.subtype_mk
          change Continuous (fun t : J => (rawEdgePoint (.inl (i,b)) (it t) e:ℂ))
          simp only [rawEdgePoint_handle,rawBoundaryPoint,Complex.ClosedUnitDisc.bdyPtOfReal]
          exact continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by
            cases e <;> cases b <;> simp only [Bool.false_eq_true,↓reduceIte] <;> dsimp [it] <;> fun_prop))
      }
      let h : C(J,actualSurvivingBoundary p) := (survivingBoundaryQuotientMap p).comp (r false)
      have hv (t : J) : h t=handleEdge p i b (it t) := by
        apply Subtype.ext;apply Subtype.ext
        apply congrArg (Quot.mk _)
        change rawEdgePoint (.inl (i,b)) (it t) false=(handleEdgeRaw p i b (it t)).val.val
        rw [rawEdgePoint_handle]
        rfl
      have hpre : (survivingBoundaryQuotientMap p) ⁻¹' range h=range (r false) ∪ range (r true) := by
        ext z
        constructor
        · rintro ⟨t,ht⟩
          have he := congrArg (fun x : actualSurvivingBoundary p => x.val.val) ht
          change Quot.mk _ (rawEdgePoint (.inl (i,b)) (it t) false)=Quot.mk _ z.val.val at he
          rcases (raw_quotient_interior_fiber (.inl (i,b)) (it t) (hit0 t) (hit1 t) z.val.val).mp he with he|he
          · left;exact ⟨t,by apply Subtype.ext;apply Subtype.ext;exact he.symm⟩
          · right;exact ⟨t,by apply Subtype.ext;apply Subtype.ext;exact he.symm⟩
        · rintro (⟨t,rfl⟩|⟨t,rfl⟩)
          · exact ⟨t,rfl⟩
          · refine ⟨t,?_⟩
            apply Subtype.ext;apply Subtype.ext
            exact Quot.sound (raw_edge_points_related (.inl (i,b)) (it t))
      have hClosed : IsClosed (range h) := by
        apply (survivingBoundaryQuotientMap_isQuotientMap p).1.isClosed_preimage.mp
        rw [hpre]
        exact ((isCompact_range (r false).continuous).isClosed).union ((isCompact_range (r true).continuous).isClosed)
      have him : range h=range (fun t : J => handleEdge p i b (it t)) := by
        congr 1;funext t;exact hv t
      rwa [him] at hClosed
    have hMiddleChart (p : ℕ) :
        ∃ V : Set (actualSurvivingBoundary p), IsOpen V ∧
          Nonempty (V ≃ₜ ((Fin p × Bool) × Ioo (1/4:ℝ) (3/4:ℝ))) ∧
          V=range (fun z : (Fin p × Bool) × Ioo (1/4:ℝ) (3/4:ℝ) =>
            handleEdge p z.1.1 z.1.2 ⟨z.2.val,⟨by linarith [z.2.property.1],by linarith [z.2.property.2]⟩⟩) := by
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
      refine ⟨V,hV,⟨T.symm⟩,?_⟩
      change range g=_
      congr 1
      funext z
      exact hv z.1 z.2
    let A : (Fin p × Bool) → Set (actualSurvivingBoundary p) := fun d => range
      (fun t : Icc (3/8:ℝ) (5/8:ℝ) => handleEdge p d.1 d.2
        ⟨t.val,⟨by linarith [t.property.1],by linarith [t.property.2]⟩⟩)
    let K : Set (actualSurvivingBoundary p) := ⋃ d, A d
    let U : Set (actualSurvivingBoundary p) := Kᶜ
    have hK : IsClosed K := isClosed_iUnion_of_finite (fun d =>
      hCentralClosed p d.1 d.2 (3/8) (5/8) (by norm_num) (by norm_num))
    have hU : IsOpen U := hK.isOpen_compl
    have hF (i j : Fin p) (b c : Bool) (t s : unitInterval) (hs0 : 0<(s:ℝ)) (hs1 : (s:ℝ)<1)
        (he : handleEdge p j c s=handleEdge p i b t) : (j,c)=(i,b) ∧ s=t := by
      have heq := congrArg (fun x : actualSurvivingBoundary p => x.val.val) he
      have hraw : Quot.mk (LeanEval.Topology.ClassificationOfSurfaces.OrientableRel p 1)
          (rawEdgePoint (.inl (j,c)) s false)=Quot.mk _ (rawEdgePoint (.inl (i,b)) t false) := by
        simpa [handleEdge,handleEdgeRaw,survivingBoundaryQuotientMap,rawQuotientMap,
          handleNumerator,rawEdgePoint_handle,rawBoundaryPoint] using heq
      have hf := (raw_quotient_interior_fiber (.inl (j,c)) s hs0 hs1
        (rawEdgePoint (.inl (i,b)) t false)).mp hraw
      have hm : rawEdgePoint (.inl (i,b)) t false ∈ rawInteriorPair (.inl (j,c)) s := hf
      have hh := (rawEdgePoint_mem_interior_pair_iff (.inl (j,c)) (.inl (i,b)) s t hs0 hs1 false).mp hm
      exact ⟨Sum.inl.inj hh.1,hh.2⟩
    have hKU (i : Fin p) (b : Bool) (t : unitInterval) :
        handleEdge p i b t ∈ K ↔ 3/8≤(t:ℝ) ∧ (t:ℝ)≤5/8 := by
      constructor
      · intro ht
        obtain ⟨⟨j,c⟩,s,hs⟩ := mem_iUnion.mp ht
        have hf := hF i j b c t ⟨s.val,⟨by linarith [s.property.1],by linarith [s.property.2]⟩⟩
          (by linarith [s.property.1]) (by linarith [s.property.2]) hs
        have he := congrArg (fun t : unitInterval => t.val) hf.2
        constructor <;> dsimp at he <;> linarith [s.property.1,s.property.2]
      · intro ht
        exact mem_iUnion.mpr ⟨(i,b),⟨⟨t.val,ht⟩,by congr⟩⟩
    have hEU (i : Fin p) (b : Bool) (t : unitInterval) :
        handleEdge p i b t ∈ U ↔ (t:ℝ)<3/8 ∨ 5/8<(t:ℝ) := by
      change ¬(handleEdge p i b t ∈ K) ↔ _
      rw [hKU]
      constructor
      · intro h
        by_cases h0 : (t:ℝ)<3/8
        · exact Or.inl h0
        · exact Or.inr (lt_of_not_ge (fun h1 => h ⟨le_of_not_gt h0,h1⟩))
      · rintro (h|h) ⟨h0,h1⟩ <;> linarith
    have hCU (x : actualSurvivingBoundary p) (t : unitInterval) (_ht : (t:ℝ)<1)
        (hx : x.val.val=Quot.mk (LeanEval.Topology.ClassificationOfSurfaces.OrientableRel p 1)
          (rawEdgePoint (p:=p) (.inr ()) t false)) : x∈U := by
      intro h
      obtain ⟨⟨i,b⟩,s,hs⟩ := mem_iUnion.mp h
      let it : unitInterval := ⟨s.val,⟨by linarith [s.property.1],by linarith [s.property.2]⟩⟩
      have heq := (congrArg (fun x : actualSurvivingBoundary p => x.val.val) hs).trans hx
      have hraw : Quot.mk (LeanEval.Topology.ClassificationOfSurfaces.OrientableRel p 1)
          (rawEdgePoint (.inl (i,b)) it false)=Quot.mk _ (rawEdgePoint (p:=p) (.inr ()) t false) := by
        simpa [handleEdge,handleEdgeRaw,survivingBoundaryQuotientMap,rawQuotientMap,
          handleNumerator,rawEdgePoint_handle,rawBoundaryPoint,it] using heq
      have hs0 : 0<(it:ℝ) := by dsimp [it];linarith [s.property.1]
      have hs1 : (it:ℝ)<1 := by dsimp [it];linarith [s.property.2]
      have hf := (raw_quotient_interior_fiber (.inl (i,b)) it hs0 hs1
        (rawEdgePoint (p:=p) (.inr ()) t false)).mp hraw
      have hm : rawEdgePoint (p:=p) (.inr ()) t false ∈ rawInteriorPair (.inl (i,b)) it := hf
      have hh := (rawEdgePoint_mem_interior_pair_iff (.inl (i,b)) (.inr ()) it t hs0 hs1 false).mp hm
      cases hh.1
    obtain ⟨V,hV,_,hVr⟩ := hMiddleChart p
    have hcover : U∪V=univ := by
      apply eq_univ_of_forall
      intro x
      obtain ⟨z,hz⟩ := (survivingBoundaryQuotientMap_isQuotientMap p).surjective x
      rcases surviving_raw_class_curve_cover p z.val z.property with ⟨i,b,t,he⟩|⟨t,ht,he⟩
      · have hxe : handleEdge p i b t=x := by
          apply Subtype.ext;apply Subtype.ext
          have hz' := congrArg (fun x : actualSurvivingBoundary p => x.val.val) hz
          change Quot.mk _ z.val.val=x.val.val at hz'
          have hre : Quot.mk (LeanEval.Topology.ClassificationOfSurfaces.OrientableRel p 1)
              (rawEdgePoint (.inl (i,b)) t false)=x.val.val := he.symm.trans hz'
          simpa [handleEdge,handleEdgeRaw,survivingBoundaryQuotientMap,rawQuotientMap,
            handleNumerator,rawEdgePoint_handle,rawBoundaryPoint] using hre
        by_cases hstar : (t:ℝ)<3/8 ∨ 5/8<(t:ℝ)
        · exact Or.inl (hxe ▸ (hEU i b t).mpr hstar)
        · right
          have hm : (t:ℝ)∈Ioo (1/4:ℝ) (3/4:ℝ) := by
            push Not at hstar
            constructor <;> linarith [hstar.1,hstar.2]
          rw [hVr]
          exact ⟨((i,b),⟨t.val,hm⟩),by simpa using hxe⟩
      · left
        apply hCU x t ht
        have hz' := congrArg (fun x : actualSurvivingBoundary p => x.val.val) hz
        change Quot.mk _ z.val.val=x.val.val at hz'
        exact hz'.symm.trans he
    exact ⟨U,V,hU,hV,hcover,hEU,hCU,hVr⟩
  have hPorts (p : ℕ) :
      ∃ g : C(((Fin p × Bool) × Bool) × Ioo (1/4:ℝ) (3/8:ℝ),actualSurvivingBoundary p),
        IsOpenEmbedding g ∧ ∀ z, g z=handleEdge p z.1.1.1 z.1.1.2
          ⟨if z.1.2 then 1-z.2.val else z.2.val,by
            cases z.1.2 <;> simp only [Bool.false_eq_true,↓reduceIte] <;>
              constructor <;> linarith [z.2.property.1,z.2.property.2]⟩ := by
    classical
    let J := Ioo (1/4:ℝ) (3/8:ℝ)
    let it (e : Bool) (t : J) : unitInterval :=
      ⟨if e then 1-t.val else t.val,by
        cases e <;> simp only [Bool.false_eq_true,↓reduceIte] <;>
          constructor <;> linarith [t.property.1,t.property.2]⟩
    have it0 (e : Bool) (t : J) : 0<(it e t:ℝ) := by
      cases e <;> dsimp [it] <;> linarith [t.property.1,t.property.2]
    have it1 (e : Bool) (t : J) : (it e t:ℝ)<1 := by
      cases e <;> dsimp [it] <;> linarith [t.property.1,t.property.2]
    have he (d : (Fin p × Bool) × Bool) :
        ∃ h : C(J,actualSurvivingBoundary p), IsOpenEmbedding h ∧
          ∀ t, h t=handleEdge p d.1.1 d.1.2 (it d.2 t) := by
      rcases d with ⟨⟨i,b⟩,e⟩
      cases e
      · exact source_surviving_handle_interval_open_embedding p i b (1/4) (3/8)
          (by norm_num) (by norm_num)
      · obtain ⟨h,hh,hv⟩ := source_surviving_handle_interval_open_embedding p i b (5/8) (3/4)
          (by norm_num) (by norm_num)
        let T : J ≃ₜ Ioo (5/8:ℝ) (3/4:ℝ) := {
          toFun := fun t => ⟨1-t.val,by constructor <;> linarith [t.property.1,t.property.2]⟩
          invFun := fun s => ⟨1-s.val,by constructor <;> linarith [s.property.1,s.property.2]⟩
          left_inv := by intro t;apply Subtype.ext;simp
          right_inv := by intro s;apply Subtype.ext;simp
          continuous_toFun := by fun_prop
          continuous_invFun := by fun_prop
        }
        let r : C(J,actualSurvivingBoundary p) := ⟨h ∘ T,h.continuous.comp T.continuous⟩
        refine ⟨r,hh.comp T.isOpenEmbedding,?_⟩
        intro t
        change h (T t)=_
        rw [hv]
        rfl
    choose h hh hv using he
    let g : C((((Fin p × Bool) × Bool) × J),actualSurvivingBoundary p) := {
      toFun := fun z => h z.1 z.2
      continuous_toFun := continuous_prod_of_discrete_left.mpr (fun d => (h d).continuous)
    }
    have hInj : Function.Injective g := by
      rintro ⟨⟨⟨i,b⟩,e⟩,t⟩ ⟨⟨⟨j,c⟩,f⟩,u⟩ heq
      change h ((i,b),e) t=h ((j,c),f) u at heq
      rw [hv,hv] at heq
      have heq' := congrArg (fun x : actualSurvivingBoundary p => x.val.val) heq
      have hraw : Quot.mk (LeanEval.Topology.ClassificationOfSurfaces.OrientableRel p 1)
          (rawEdgePoint (.inl (i,b)) (it e t) false)=Quot.mk _ (rawEdgePoint (.inl (j,c)) (it f u) false) := by
        simpa [handleEdge,handleEdgeRaw,survivingBoundaryQuotientMap,rawQuotientMap,
          handleNumerator,rawEdgePoint_handle,rawBoundaryPoint] using heq'
      have hf := (raw_quotient_interior_fiber (.inl (i,b)) (it e t) (it0 e t) (it1 e t)
        (rawEdgePoint (.inl (j,c)) (it f u) false)).mp hraw
      have hm : rawEdgePoint (.inl (j,c)) (it f u) false ∈ rawInteriorPair (.inl (i,b)) (it e t) := hf
      have hp := (rawEdgePoint_mem_interior_pair_iff (.inl (i,b)) (.inl (j,c))
        (it e t) (it f u) (it0 e t) (it1 e t) false).mp hm
      have hij : (i,b)=(j,c) := Sum.inl.inj hp.1
      have hn := congrArg (fun t : unitInterval => t.val) hp.2
      have hef : e=f := by
        cases e <;> cases f <;> dsimp [it] at hn <;> try rfl
        all_goals exfalso;linarith [t.property.2,u.property.2]
      subst f
      have htu : t=u := by
        apply Subtype.ext
        cases e <;> dsimp [it] at hn <;> linarith
      exact Prod.ext (Prod.ext hij rfl) htu
    have hOpen : IsOpenMap g := by
      intro W hW
      have hs (d : (Fin p × Bool) × Bool) : IsOpen {t : J | (d,t) ∈ W} :=
        hW.preimage (continuous_const.prodMk continuous_id)
      have him : g '' W=⋃ d : (Fin p × Bool) × Bool, h d '' {t : J | (d,t) ∈ W} := by
        ext x
        simp only [mem_image,mem_iUnion,mem_ofPred_eq]
        constructor
        · rintro ⟨⟨d,t⟩,ht,rfl⟩
          exact ⟨d,t,ht,rfl⟩
        · rintro ⟨d,t,ht,rfl⟩
          exact ⟨(d,t),ht,rfl⟩
      rw [him]
      exact isOpen_iUnion (fun d => (hh d).isOpenMap _ (hs d))
    exact ⟨g,IsOpenEmbedding.of_continuous_injective_isOpenMap g.continuous hInj hOpen,
      fun z => hv z.1 z.2⟩
  obtain ⟨U,V,hU,hV,hcover,hEU,hCU,hVr⟩ := hCover p
  obtain ⟨g,hg,hgv⟩ := hPorts p
  let J := Ioo (1/4:ℝ) (3/8:ℝ)
  let P := ((Fin p × Bool) × Bool) × J
  have hgmem (z : P) : g z∈U∩V := by
    rcases z with ⟨⟨⟨i,b⟩,e⟩,t⟩
    rw [hgv]
    let s : unitInterval := ⟨if e then 1-t.val else t.val,by
      cases e <;> simp only [Bool.false_eq_true,↓reduceIte] <;>
        constructor <;> linarith [t.property.1,t.property.2]⟩
    change handleEdge p i b s∈U∩V
    have hs : (s:ℝ)∈Ioo (1/4:ℝ) (3/4:ℝ) := by
      cases e <;> dsimp [s] <;> constructor <;> linarith [t.property.1,t.property.2]
    constructor
    · apply (hEU i b s).mpr
      cases e
      · left;exact t.property.2
      · right;change 5/8<1-t.val;linarith [t.property.2]
    · rw [hVr]
      exact ⟨((i,b),⟨s.val,hs⟩),by congr⟩
  have him : range g=U∩V := by
    apply subset_antisymm
    · rintro x ⟨z,rfl⟩;exact hgmem z
    · intro x hx
      have hxV := hx.2
      rw [hVr] at hxV
      obtain ⟨⟨⟨i,b⟩,t⟩,ht⟩ := hxV
      let s : unitInterval := ⟨t.val,⟨by linarith [t.property.1],by linarith [t.property.2]⟩⟩
      change handleEdge p i b s=x at ht
      have hsU : handleEdge p i b s∈U := ht.symm ▸ hx.1
      rcases (hEU i b s).mp hsU with hlo|hhi
      · let u : J := ⟨t.val,t.property.1,hlo⟩
        refine ⟨(((i,b),false),u),?_⟩
        rw [hgv]
        exact ht
      · let u : J := ⟨1-t.val,⟨by linarith [t.property.2],by change 5/8<t.val at hhi;linarith⟩⟩
        refine ⟨(((i,b),true),u),?_⟩
        rw [hgv]
        convert ht using 1
        apply congrArg (handleEdge p i b)
        apply Subtype.ext
        dsimp [u]
        ring
  let q : C(P,↥(U∩V)) := ⟨fun z => ⟨g z,hgmem z⟩,g.continuous.subtype_mk hgmem⟩
  have hqE : IsOpenEmbedding q :=
    (IsOpenEmbedding.of_comp_iff q (hU.inter hV).isOpenEmbedding_subtypeVal).mp hg
  have hqS : Function.Surjective q := by
    rintro ⟨x,hx⟩
    obtain ⟨z,hz⟩ := (show x∈range g by rw [him];exact hx)
    exact ⟨z,Subtype.ext hz⟩
  let T := ((isHomeomorph_iff_isEmbedding_surjective).mpr ⟨hqE.isEmbedding,hqS⟩).homeomorph q
  let e : (Fin p × Bool) ≃ Fin (2*p) := Fintype.equivFinOfCardEq (by simp [Nat.mul_comm])
  let TFin : ↥(U∩V) ≃ₜ ((Fin (2*p) × Bool) × J) := T.symm.trans
    (((Homeomorph.ofDiscrete e).prodCongr (Homeomorph.refl Bool)).prodCongr (Homeomorph.refl J))
  refine ⟨U,V,hU,hV,hcover,hEU,hCU,hVr,TFin,?_⟩
  intro z
  change g (((e.symm z.1.1),z.1.2),z.2)=_
  exact hgv (((e.symm z.1.1),z.1.2),z.2)
end CurveComplex.Hyperbolic.OneBoundaryRay
