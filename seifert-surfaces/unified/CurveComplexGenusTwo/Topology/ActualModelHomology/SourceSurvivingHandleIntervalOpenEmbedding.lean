import CurveComplexGenusTwo.Topology.ActualModelHomology.ActualOneBoundaryHandleEdges
import CurveComplexGenusTwo.Topology.ActualModelHomology.ActualOneBoundaryRawInteriorFibers
import CurveComplexGenusTwo.Topology.ActualModelHomology.ActualOneBoundarySurvivingArcNormalization
import CurveComplexGenusTwo.CWHurewicz.SingularRepresentation
namespace CurveComplex.Hyperbolic.OneBoundaryRay
open Set Topology CategoryTheory CategoryTheory.Limits
open CurveComplexGenusTwo.CWHurewicz
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
theorem source_surviving_handle_interval_open_embedding (p : ℕ) (i : Fin p) (b : Bool) (a c : ℝ)
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
end CurveComplex.Hyperbolic.OneBoundaryRay
