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
theorem source_surviving_graph_joint_star_contraction (p : ℕ) :
    ∃ U V : Set (actualSurvivingBoundary p), IsOpen U ∧ IsOpen V ∧ U∪V=univ ∧
      (∀ i b (t : unitInterval), handleEdge p i b t ∈ U ↔ (t:ℝ)<3/8 ∨ 5/8<(t:ℝ)) ∧
      (∀ x : actualSurvivingBoundary p, ∀ t : unitInterval, (t:ℝ)<1 →
        x.val.val=Quot.mk (LeanEval.Topology.ClassificationOfSurfaces.OrientableRel p 1)
          (rawEdgePoint (p:=p) (.inr ()) t false) → x∈U) ∧
      V=range (fun z : (Fin p × Bool) × Ioo (1/4:ℝ) (3/4:ℝ) =>
        handleEdge p z.1.1 z.1.2 ⟨z.2.val,⟨by linarith [z.2.property.1],by linarith [z.2.property.2]⟩⟩) ∧ ContractibleSpace U := by
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
  have hWholeFiber (p : ℕ) (k l : RawEdgeIndex p) (t s : unitInterval)
      (hk : match k with | .inl _ => True | .inr _ => (t:ℝ)<1)
      (hl : match l with | .inl _ => True | .inr _ => (s:ℝ)<1) :
      let B : RawEdgeIndex p → unitInterval → Prop := fun k t => t=0 ∨
        match k with | .inl _ => t=1 | .inr _ => False
      Quot.mk (LeanEval.Topology.ClassificationOfSurfaces.OrientableRel p 1) (rawEdgePoint k t false)=
        Quot.mk _ (rawEdgePoint l s false) ↔ (k=l ∧ t=s) ∨ (B k t ∧ B l s) := by
    classical
    dsimp only
    let B : RawEdgeIndex p → unitInterval → Prop := fun k t => t=0 ∨
      match k with | .inl _ => t=1 | .inr _ => False
    have hBase (k : RawEdgeIndex p) (t : unitInterval) (h : B k t) :
        Quot.mk (LeanEval.Topology.ClassificationOfSurfaces.OrientableRel p 1) (rawEdgePoint k t false)=
          Quot.mk _ (rawBoundaryPoint p 0) := by
      cases k with
      | inl d =>
        rcases d with ⟨i,b⟩
        change t=0 ∨ t=1 at h
        rcases h with rfl|rfl
        · have he := congrArg (fun x : actualSurvivingBoundary p => x.val.val) (handleEdge_source p i b)
          simpa [handleEdge,handleEdgeRaw,survivingBoundaryQuotientMap,rawQuotientMap,
            handleNumerator,rawEdgePoint_handle,rawBoundaryPoint,survivingBase] using he
        · have he := congrArg (fun x : actualSurvivingBoundary p => x.val.val) (handleEdge_target p i b)
          simpa [handleEdge,handleEdgeRaw,survivingBoundaryQuotientMap,rawQuotientMap,
            handleNumerator,rawEdgePoint_handle,rawBoundaryPoint,survivingBase] using he
      | inr u =>
        have ht : t=0 := h.resolve_right id
        subst t
        rw [rawEdgePoint_seam]
        simp
    have hStrict (k : RawEdgeIndex p) (t : unitInterval)
        (hk : match k with | .inl _ => True | .inr _ => (t:ℝ)<1)
        (h : ¬B k t) : 0<(t:ℝ) ∧ (t:ℝ)<1 := by
      have ht0 : 0<(t:ℝ) := by
        by_contra hn
        have ht : t=0 := Subtype.ext (le_antisymm (le_of_not_gt hn) t.property.1)
        exact h (Or.inl ht)
      refine ⟨ht0,?_⟩
      cases k with
      | inl d =>
        by_contra hn
        have ht : t=1 := Subtype.ext (le_antisymm t.property.2 (le_of_not_gt hn))
        exact h (Or.inr ht)
      | inr u => exact hk
    have hInterior (k l : RawEdgeIndex p) (t s : unitInterval)
        (ht0 : 0<(t:ℝ)) (ht1 : (t:ℝ)<1)
        (he : Quot.mk (LeanEval.Topology.ClassificationOfSurfaces.OrientableRel p 1) (rawEdgePoint k t false)=
          Quot.mk _ (rawEdgePoint l s false)) : k=l ∧ t=s := by
      have hf := (raw_quotient_interior_fiber k t ht0 ht1 (rawEdgePoint l s false)).mp he
      have hm : rawEdgePoint l s false ∈ rawInteriorPair k t := hf
      exact (rawEdgePoint_mem_interior_pair_iff k l t s ht0 ht1 false).mp hm
    constructor
    · intro he
      by_cases hkt : B k t
      · right
        refine ⟨hkt,?_⟩
        by_contra hls
        have hs := hStrict l s hl hls
        obtain ⟨hkl,hts⟩ := hInterior l k s t hs.1 hs.2 he.symm
        exact hls (hkl.symm ▸ hts.symm ▸ hkt)
      · left
        have ht := hStrict k t hk hkt
        exact hInterior k l t s ht.1 ht.2 he
    · rintro (⟨rfl,rfl⟩|⟨hkt,hls⟩)
      · rfl
      · exact (hBase k t hkt).trans (hBase l s hls).symm
  obtain ⟨U,V,hU,hV,hcover,hEU,hCU,hVr⟩ := hCover p
  let f := actualEdgeParameterMap p
  have hf := source_actual_edge_parameter_map_isQuotientMap p
  let Q := f ⁻¹' U
  let L := {z : (Fin p × Bool) × unitInterval | f (.inl z) ∈ U}
  let R := {z : Ico (0:ℝ) 1 | f (.inr z) ∈ U}
  let P := L ⊕ R
  let qL : L → Q := Q.restrictPreimage Sum.inl
  let qR : R → Q := Q.restrictPreimage Sum.inr
  let eq : P ≃ Q := (Equiv.subtypeSum (p:=fun z : ActualEdgeParameterSpace p => z∈Q)).symm
  have heq : (eq : P → Q)=Sum.elim qL qR := by
    funext z;cases z <;> rfl
  have hEq : IsOpenEmbedding eq := by
    rw [heq]
    apply IsOpenEmbedding.sumElim
      (IsOpenEmbedding.inl.restrictPreimage Q) (IsOpenEmbedding.inr.restrictPreimage Q)
    rw [← heq]
    exact eq.injective
  let T : P ≃ₜ Q := ((isHomeomorph_iff_isEmbedding_surjective).mpr
    ⟨hEq.isEmbedding,eq.surjective⟩).homeomorph eq
  let q : P → U := U.restrictPreimage f ∘ T
  have hq : IsQuotientMap q := (hf.restrictPreimage_isOpen hU).comp T.isQuotientMap
  have hLp (z : L) : (z.val.2:ℝ)<3/8 ∨ 5/8<(z.val.2:ℝ) :=
    (hEU z.val.1.1 z.val.1.2 z.val.2).mp z.property
  let low : Set L := {z | (z.val.2:ℝ)<3/8}
  have hLow : IsClopen low := by
    have hct : Continuous (fun z : L => (z.val.2:ℝ)) := by fun_prop
    constructor
    · apply isOpen_compl_iff.mp
      have he : lowᶜ={z : L | 5/8<(z.val.2:ℝ)} := by
        ext z
        change ¬((z.val.2:ℝ)<3/8) ↔ 5/8<(z.val.2:ℝ)
        rcases hLp z with hz|hz <;> constructor <;> intro h <;> linarith
      rw [he]
      exact isOpen_Ioi.preimage hct
    · exact isOpen_Iio.preimage hct
  let param (s : unitInterval) (z : L) : unitInterval :=
    if (z.val.2:ℝ)<3/8 then unitInterval.symm s * z.val.2
    else unitInterval.symm (unitInterval.symm s * unitInterval.symm z.val.2)
  have hp0 (z : L) : param 0 z=z.val.2 := by
    dsimp [param];split_ifs <;> simp
  have hp1 (z : L) : param 1 z=(if (z.val.2:ℝ)<3/8 then 0 else 1) := by
    dsimp [param];split_ifs <;> simp
  have hpCont : Continuous (fun z : L × unitInterval => param z.2 z.1) := by
    let A : Set (L × unitInterval) := {z | z.1∈low}
    have hA : IsClopen A := hLow.preimage continuous_fst
    have h1 : Continuous (fun z : L × unitInterval => unitInterval.symm z.2 * z.1.val.2) := by fun_prop
    have h2 : Continuous (fun z : L × unitInterval =>
        unitInterval.symm (unitInterval.symm z.2 * unitInterval.symm z.1.val.2)) := by fun_prop
    have h := continuous_if (p:=fun z : L × unitInterval => z∈A)
      (f:=fun z => unitInterval.symm z.2 * z.1.val.2)
      (g:=fun z => unitInterval.symm (unitInterval.symm z.2 * unitInterval.symm z.1.val.2))
      (by simp [hA.frontier_eq]) h1.continuousOn h2.continuousOn
    simpa [param,A,low] using h
  have hpMem (s : unitInterval) (z : L) : handleEdge p z.val.1.1 z.val.1.2 (param s z)∈U := by
    apply (hEU _ _ _).mpr
    by_cases hlo : (z.val.2:ℝ)<3/8
    · left
      have he : (param s z:ℝ)=(1-(s:ℝ))*(z.val.2:ℝ) := by
        simp [param,hlo,unitInterval.coe_symm_eq]
      rw [he]
      nlinarith [mul_nonneg s.property.1 z.val.2.property.1]
    · right
      have hhi := (hLp z).resolve_left hlo
      have he : (param s z:ℝ)=1-(1-(s:ℝ))*(1-(z.val.2:ℝ)) := by
        simp [param,hlo,unitInterval.coe_symm_eq]
      rw [he]
      nlinarith [mul_nonneg s.property.1 (sub_nonneg.mpr z.val.2.property.2)]
  let cparam (s : unitInterval) (z : R) : Ico (0:ℝ) 1 :=
    ⟨(1-(s:ℝ))*z.val.val,⟨mul_nonneg (sub_nonneg.mpr s.property.2) z.val.property.1,by
      nlinarith [mul_nonneg s.property.1 z.val.property.1,z.val.property.2]⟩⟩
  have cp0 (z : R) : cparam 0 z=z.val := by
    apply Subtype.ext;simp [cparam]
  have cp1 (z : R) : cparam 1 z=⟨0,by constructor <;> norm_num⟩ := by
    apply Subtype.ext;simp [cparam]
  have cpCont : Continuous (fun z : R × unitInterval => cparam z.2 z.1) := by
    dsimp [cparam];fun_prop
  have cpMem (s : unitInterval) (z : R) : f (.inr (cparam s z))∈U := by
    let tc : unitInterval := ⟨(cparam s z).val,⟨(cparam s z).property.1,(cparam s z).property.2.le⟩⟩
    apply hCU _ tc (cparam s z).property.2
    rw [rawEdgePoint_seam]
    rfl
  let HL : C(L × unitInterval,U) := {
    toFun := fun z => ⟨handleEdge p z.1.val.1.1 z.1.val.1.2 (param z.2 z.1),hpMem z.2 z.1⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact hf.continuous.comp (continuous_inl.comp
        ((by fun_prop : Continuous (fun z : L × unitInterval => z.1.val.1)).prodMk hpCont))
  }
  let HR : C(R × unitInterval,U) := {
    toFun := fun z => ⟨f (.inr (cparam z.2 z.1)),cpMem z.2 z.1⟩
    continuous_toFun := (hf.continuous.comp (continuous_inr.comp cpCont)).subtype_mk _
  }
  let Hsum : C((L × unitInterval) ⊕ (R × unitInterval),U) :=
    ⟨Sum.elim HL HR,HL.continuous.sumElim HR.continuous⟩
  let H : C(P × unitInterval,U) :=
    ⟨Hsum ∘ Homeomorph.sumProdDistrib,Hsum.continuous.comp Homeomorph.sumProdDistrib.continuous⟩
  have Hzero (z : P) : H (z,0)=q z := by
    cases z with
    | inl z =>
      apply Subtype.ext
      change handleEdge p z.val.1.1 z.val.1.2 (param 0 z)=handleEdge p z.val.1.1 z.val.1.2 z.val.2
      rw [hp0]
    | inr z =>
      apply Subtype.ext
      change f (.inr (cparam 0 z))=f (.inr z.val)
      rw [cp0]
  have hBaseU : survivingBase p∈U := by
    apply hCU _ 0 (by norm_num)
    rw [rawEdgePoint_seam]
    simp [survivingBase,survivingBoundaryQuotientMap,rawQuotientMap,rawBoundaryPoint]
  let v : U := ⟨survivingBase p,hBaseU⟩
  have Hone (z : P) : H (z,1)=v := by
    cases z with
    | inl z =>
      apply Subtype.ext
      change handleEdge p z.val.1.1 z.val.1.2 (param 1 z)=survivingBase p
      rw [hp1]
      split_ifs
      · exact handleEdge_source p _ _
      · exact handleEdge_target p _ _
    | inr z =>
      apply Subtype.ext;apply Subtype.ext;apply Subtype.ext
      change (f (.inr (cparam 1 z))).val.val=(survivingBase p).val.val
      rw [cp1]
      simp [f,actualEdgeParameterMap,survivingSeamRaw,survivingBoundaryQuotientMap,rawQuotientMap,survivingBase,rawBoundaryPoint]
  let key : P → RawEdgeIndex p := Sum.elim (fun z => .inl z.val.1) (fun _ => .inr ())
  let pt : P → unitInterval := Sum.elim (fun z => z.val.2)
    (fun z => ⟨z.val.val,⟨z.val.property.1,z.val.property.2.le⟩⟩)
  let B : RawEdgeIndex p → unitInterval → Prop := fun k t => t=0 ∨
    match k with | .inl _ => t=1 | .inr _ => False
  have hCap (z : P) : match key z with | .inl _ => True | .inr _ => (pt z:ℝ)<1 := by
    cases z with
    | inl z => trivial
    | inr z => exact z.val.property.2
  have hCode (z : P) : (q z).val.val.val=
      Quot.mk (LeanEval.Topology.ClassificationOfSurfaces.OrientableRel p 1) (rawEdgePoint (key z) (pt z) false) := by
    cases z with
    | inl z =>
      rcases z with ⟨⟨⟨i,b⟩,t⟩,hz⟩
      change (handleEdge p i b t).val.val=Quot.mk _ (rawEdgePoint (.inl (i,b)) t false)
      rw [rawEdgePoint_handle]
      rfl
    | inr z =>
      change (f (.inr z.val)).val.val=Quot.mk _ (rawEdgePoint (p:=p) (.inr ()) (pt (.inr z)) false)
      rw [rawEdgePoint_seam]
      rfl
  have hCodeInj (z w : P) (hk : key z=key w) (ht : pt z=pt w) : z=w := by
    cases z with
    | inl z =>
      cases w with
      | inl w =>
        apply congrArg Sum.inl
        apply Subtype.ext
        exact Prod.ext (Sum.inl.inj hk) ht
      | inr w => cases hk
    | inr z =>
      cases w with
      | inl w => cases hk
      | inr w =>
        apply congrArg Sum.inr
        apply Subtype.ext;apply Subtype.ext
        exact congrArg (fun t : unitInterval => t.val) ht
  have Hbase (s : unitInterval) (z : P) (hb : B (key z) (pt z)) : H (z,s)=v := by
    cases z with
    | inl z =>
      change z.val.2=0 ∨ z.val.2=1 at hb
      apply Subtype.ext
      change handleEdge p z.val.1.1 z.val.1.2 (param s z)=survivingBase p
      rcases hb with hb|hb
      · have he : param s z=0 := by simp [param,hb]
        rw [he]
        exact handleEdge_source p _ _
      · have he : param s z=1 := by norm_num [param,hb]
        rw [he]
        exact handleEdge_target p _ _
    | inr z =>
      have ht : pt (.inr z)=0 := hb.resolve_right id
      have ht' : z.val.val=0 := congrArg (fun t : unitInterval => t.val) ht
      have he : cparam s z=⟨0,by constructor <;> norm_num⟩ := by
        apply Subtype.ext;simp [cparam,ht']
      apply Subtype.ext;apply Subtype.ext;apply Subtype.ext
      change (f (.inr (cparam s z))).val.val=(survivingBase p).val.val
      rw [he]
      simp [f,actualEdgeParameterMap,survivingSeamRaw,survivingBoundaryQuotientMap,rawQuotientMap,survivingBase,rawBoundaryPoint]
  have Hfiber (s : unitInterval) (z w : P) (he : q z=q w) : H (z,s)=H (w,s) := by
    have he' := congrArg (fun x : U => x.val.val.val) he
    rw [hCode,hCode] at he'
    have hf := (hWholeFiber p (key z) (key w) (pt z) (pt w) (hCap z) (hCap w)).mp he'
    rcases hf with ⟨hk,ht⟩|⟨hz,hw⟩
    · exact congrArg (fun z => H (z,s)) (hCodeInj z w hk ht)
    · exact (Hbase s z hz).trans (Hbase s w hw).symm
  let hFun : U × unitInterval → U := fun z => H (Function.surjInv hq.surjective z.1,z.2)
  have hFactor (z : P) (s : unitInterval) : hFun (q z,s)=H (z,s) := by
    exact Hfiber s _ z (Function.rightInverse_surjInv hq.surjective (q z))
  have hCont : Continuous hFun := by
    apply hq.continuous_lift_prod_left
    have he : (fun z : P × unitInterval => hFun (q z.1,z.2))=H := by
      funext z;exact hFactor z.1 z.2
    rw [he]
    exact H.continuous
  have hZero (x : U) : hFun (x,0)=x := by
    change H (Function.surjInv hq.surjective x,0)=x
    rw [Hzero]
    exact Function.rightInverse_surjInv hq.surjective x
  have hOne (x : U) : hFun (x,1)=v := Hone _
  let hDesc : ContinuousMap.Homotopy (ContinuousMap.id U) (ContinuousMap.const U v) := {
    toFun := fun z => hFun (z.2,z.1)
    continuous_toFun := hCont.comp continuous_swap
    map_zero_left := hZero
    map_one_left := hOne
  }
  exact ⟨U,V,hU,hV,hcover,hEU,hCU,hVr,(contractible_iff_id_nullhomotopic U).mpr ⟨v,⟨hDesc⟩⟩⟩
end CurveComplex.Hyperbolic.OneBoundaryRay
