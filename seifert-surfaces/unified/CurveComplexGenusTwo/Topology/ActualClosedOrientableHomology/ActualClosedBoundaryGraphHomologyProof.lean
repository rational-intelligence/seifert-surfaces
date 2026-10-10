import CurveComplexGenusTwo.Topology.ActualClosedOrientableHomology.ActualClosedBoundaryDefinitions
import CurveComplexGenusTwo.Topology.ActualModelHomology.SourceSurvivingGraphWholePortFiber
import CurveComplexGenusTwo.Topology.ActualModelHomology.ActualOneBoundarySurvivingGraphH1Proof
import Mathlib.Topology.Order.ProjIcc
namespace CurveComplex.Hyperbolic
open Set Topology CategoryTheory ContinuousMap
open LeanEval.Topology.ClassificationOfSurfaces
open CurveComplex.Hyperbolic.OneBoundaryRay
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
set_option maxRecDepth 8000
/-- Genuine integral singular H1 of the actual closed boundary graph. -/
theorem actual_closed_orientable_boundary_graph_homology_one
    (p : ℕ) (hp : 1 ≤ p) :
    Nonempty (CurveComplex.integralHomology (ActualClosedOrientableBoundaryGraph p) 1 ≅
      ModuleCat.of ℤ (Fin (2 * p) → ℤ)) := by
  have hHomeomorph :
      ∃ radius : C(Quot (OrientableRel p 0),ℝ),
        (∀ z : Complex.ClosedUnitDisc, radius (Quot.mk (OrientableRel p 0) z) = ‖(z:ℂ)‖) ∧
        ∃ K : Set (actualSurvivingBoundary p),
          K = Set.range (fun z : (Fin p × Bool) × unitInterval => handleEdge p z.1.1 z.1.2 z.2) ∧
          Nonempty (({z | radius z=1} : Set (Quot (OrientableRel p 0))) ≃ₜ K)
 := by
    have hCircle :
        ∃ f : C(Circle, actualSurvivingBoundary p),
          (∀ s : ℝ, 0 ≤ s → s ≤ 4*(p:ℝ) →
            (f (Real.fourierChar (s/(4*(p:ℝ))))).val.val = rawBoundaryClass p s) ∧
          (∀ (t : unitInterval) (i : Fin p),
            f (Real.fourierChar ((4*(i:ℝ)+(t:ℝ))/(4*(p:ℝ)))) =
              f (Real.fourierChar ((4*(i:ℝ)+3-(t:ℝ))/(4*(p:ℝ))))) ∧
          (∀ (t : unitInterval) (i : Fin p),
            f (Real.fourierChar ((4*(i:ℝ)+1+(t:ℝ))/(4*(p:ℝ)))) =
              f (Real.fourierChar ((4*(i:ℝ)+4-(t:ℝ))/(4*(p:ℝ)))))
   := by
      have hpR : (1:ℝ) ≤ p := by exact_mod_cast hp
      have hN : 0 < 4*(p:ℝ) := by positivity
      let Q : C(unitInterval,actualSurvivingBoundary p) := {
        toFun t := survivingBoundaryQuotientMap p
          ⟨⟨Complex.ClosedUnitDisc.bdyPtOfReal ((4*(p:ℝ)*(t:ℝ))/modelSideCount p),
            handle_boundary_not_mem_rawDeletedArc p _ (mul_nonneg hN.le t.property.1)
              (by nlinarith [t.property.2])⟩,Circle.norm_coe _⟩
        continuous_toFun := by
          apply (survivingBoundaryQuotientMap p).continuous.comp
          apply Continuous.subtype_mk
          apply Continuous.subtype_mk
          apply Continuous.subtype_mk
          exact continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop)) }
      have hQ (t : unitInterval) : (Q t).val.val = rawBoundaryClass p (4*(p:ℝ)*(t:ℝ)) := rfl
      have hends : Q 0 = Q 1 := by
        apply Subtype.ext
        apply Subtype.ext
        rw [hQ,hQ]
        simpa using
          (handle_initial_vertex_class p p le_rfl).symm
      let q : ℝ → actualSurvivingBoundary p := fun t => Q (Set.projIcc 0 1 (by norm_num) t)
      have hc : Continuous q := Q.continuous.comp continuous_projIcc
      have hq0 : q 0 = Q 0 := by simp [q,Set.projIcc_of_mem]
      have hq1 : q 1 = Q 1 := by simp [q,Set.projIcc_of_mem]
      let A : C(AddCircle (1:ℝ),actualSurvivingBoundary p) :=
        ⟨AddCircle.liftIco (1:ℝ) 0 q,
          AddCircle.liftIco_continuous (by simpa only [zero_add,hq0,hq1] using hends) hc.continuousOn⟩
      let H := AddCircle.homeomorphCircle (T := (1:ℝ)) one_ne_zero
      let f : C(Circle,actualSurvivingBoundary p) := A.comp ⟨H.symm,H.symm.continuous⟩
      have hH (t : ℝ) : H (t : AddCircle (1:ℝ)) = Real.fourierChar t := by
        simp only [H,AddCircle.homeomorphCircle_apply,AddCircle.toCircle_apply_mk,
          div_one,Real.fourierChar_apply']
      have hparam (t : unitInterval) : f (Real.fourierChar (t:ℝ)) = Q t := by
        rw [← hH,show f (H ((t:ℝ) : AddCircle (1:ℝ))) = A ((t:ℝ) : AddCircle (1:ℝ)) by
          simp only [f,ContinuousMap.comp_apply,ContinuousMap.coe_mk,H.symm_apply_apply]]
        rcases lt_or_eq_of_le t.property.2 with ht | ht
        · change AddCircle.liftIco (1:ℝ) 0 q ((t:ℝ) : AddCircle (1:ℝ)) = Q t
          rw [AddCircle.liftIco_coe_apply (by simpa only [zero_add,mem_Ico] using And.intro t.property.1 ht)]
          change Q (Set.projIcc 0 1 _ (t:ℝ)) = Q t
          rw [Set.projIcc_of_mem (by norm_num) t.property]
        · have ht' : t = 1 := Subtype.ext ht
          subst t
          have hz : ((1:ℝ) : AddCircle (1:ℝ)) = 0 := by simp
          change A ((1:ℝ) : AddCircle (1:ℝ)) = Q 1
          rw [hz]
          change AddCircle.liftIco (1:ℝ) 0 q (0 : AddCircle (1:ℝ)) = Q 1
          rw [← AddCircle.coe_zero,AddCircle.liftIco_coe_apply (by norm_num),hq0,hends]
      have hvalue (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 4*(p:ℝ)) :
          (f (Real.fourierChar (s/(4*(p:ℝ))))).val.val = rawBoundaryClass p s := by
        let t : unitInterval := ⟨s/(4*(p:ℝ)),
          div_nonneg hs0 hN.le,(div_le_one hN).mpr hs1⟩
        rw [show Real.fourierChar (s/(4*(p:ℝ))) = Real.fourierChar (t:ℝ) from rfl,hparam,hQ]
        dsimp only [t]
        rw [mul_div_cancel₀ s hN.ne']
      refine ⟨f,hvalue,?_,?_⟩
      · intro t i
        have hi : (i:ℝ)+1 ≤ p := by exact_mod_cast Nat.succ_le_of_lt i.isLt
        have hi0 : (0:ℝ) ≤ i := by positivity
        apply Subtype.ext
        apply Subtype.ext
        rw [hvalue _ (by nlinarith [t.property.1]) (by nlinarith [t.property.2]),
          hvalue _ (by nlinarith [t.property.2]) (by nlinarith [t.property.1])]
        simpa only [rawBoundaryClass,modelSideCount,Nat.cast_one,mul_one] using
          Quot.sound (OrientableRel.a (p:=p) (n:=1) t i)
      · intro t i
        have hi : (i:ℝ)+1 ≤ p := by exact_mod_cast Nat.succ_le_of_lt i.isLt
        have hi0 : (0:ℝ) ≤ i := by positivity
        apply Subtype.ext
        apply Subtype.ext
        rw [hvalue _ (by nlinarith [t.property.1]) (by nlinarith [t.property.2]),
          hvalue _ (by nlinarith [t.property.2]) (by nlinarith [t.property.1])]
        simpa only [rawBoundaryClass,modelSideCount,Nat.cast_one,mul_one] using
          Quot.sound (OrientableRel.b (p:=p) (n:=1) t i)
    have hBoundary :
        ∃ radius : C(Quot (OrientableRel p 0),ℝ),
          (∀ z : Complex.ClosedUnitDisc, radius (Quot.mk (OrientableRel p 0) z) = ‖(z:ℂ)‖) ∧
          ∃ q : C(Circle, ({z | radius z = 1} : Set (Quot (OrientableRel p 0)))),
            IsQuotientMap q ∧
            ∀ z : Circle, (q z).val = Quot.mk (OrientableRel p 0)
              (⟨(z:ℂ),by simpa only [Metric.mem_closedBall,dist_zero_right] using (Circle.norm_coe z).le⟩ : Complex.ClosedUnitDisc)
   := by
      let R := OrientableRel p 0
      have respects : ∀ z w : Complex.ClosedUnitDisc, R z w → ‖(z:ℂ)‖ = ‖(w:ℂ)‖ := by
        intro z w h
        cases h with
        | a t i => exact (Circle.norm_coe _).trans (Circle.norm_coe _).symm
        | b t i => exact (Circle.norm_coe _).trans (Circle.norm_coe _).symm
        | c t i => exact Fin.elim0 i
      let radius : C(Quot R,ℝ) :=
        ⟨Quot.lift (fun z : Complex.ClosedUnitDisc => ‖(z:ℂ)‖) respects,
          continuous_quot_lift respects continuous_subtype_val.norm⟩
      let G : Set (Quot R) := {z | radius z = 1}
      have hG : IsClosed G := isClosed_eq radius.continuous continuous_const
      let e : Circle ≃ₜ (Quot.mk R ⁻¹' G) := {
        toFun := fun z => ⟨⟨(z:ℂ),by simpa only [Metric.mem_closedBall,dist_zero_right] using (Circle.norm_coe z).le⟩,Circle.norm_coe z⟩
        invFun := fun z => ⟨(z.val:ℂ),by
          have hz : ‖(z.val:ℂ)‖ = 1 := z.property
          simpa [Submonoid.unitSphere,Metric.mem_sphere,dist_zero_right] using hz⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        continuous_toFun := by
          apply Continuous.subtype_mk
          apply Continuous.subtype_mk
          exact continuous_subtype_val
        continuous_invFun := by
          apply Continuous.subtype_mk
          exact continuous_subtype_val.subtype_val }
      have hf : IsQuotientMap (G.restrictPreimage (Quot.mk R)) := by
        refine (isQuotientMap_iff _).mpr
          ⟨?_,(isQuotientMap_quot_mk (r:=R)).surjective.restrictPreimage _⟩
        apply IsCoinducing.of_isClosed_preimage_iff_isClosed
        intro a
        rw [hG.isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed,
          ← (isQuotientMap_quot_mk (r:=R)).isCoinducing.isClosed_preimage,
          (hG.preimage (continuous_quot_mk (r:=R))).isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed,
          image_val_preimage_restrictPreimage]
      let q : C(Circle,G) :=
        ⟨fun z => G.restrictPreimage (Quot.mk R) (e z),hf.continuous.comp e.continuous⟩
      exact ⟨radius,fun _ => rfl,q,hf.comp e.isQuotientMap,fun _ => rfl⟩
    have hHandleQuotient :
        let K : Set (actualSurvivingBoundary p) :=
          Set.range (fun z : (Fin p × Bool) × unitInterval => handleEdge p z.1.1 z.1.2 z.2)
        ∃ H : C((Fin p × Bool) × unitInterval,K), IsQuotientMap H ∧
          ∀ d, (H d).val=handleEdge p d.1.1 d.1.2 d.2
   := by
      classical
      dsimp only
      let P := (Fin p × Bool) × unitInterval
      let E := actualEdgeParameterMap p
      let K : Set (actualSurvivingBoundary p) :=
        Set.range (fun z : P => handleEdge p z.1.1 z.1.2 z.2)
      let H : C(P,K) := ⟨fun d => ⟨handleEdge p d.1.1 d.1.2 d.2,⟨d,rfl⟩⟩,by
        apply Continuous.subtype_mk
        exact continuous_prod_of_discrete_left.mpr (fun d => (handleEdge p d.1 d.2).continuous)⟩
      have hE : IsQuotientMap E := source_actual_edge_parameter_map_isQuotientMap p
      have hLeft (d : P) : (E (.inl d)).val.val =
          Quot.mk (OrientableRel p 1) (rawEdgePoint (.inl d.1) d.2 false) := by
        change Quot.mk (OrientableRel p 1)
          (Complex.ClosedUnitDisc.bdyPtOfReal (handleNumerator d.1.1 d.1.2 d.2/modelSideCount p)) = _
        rw [rawEdgePoint_handle]
        simp [handleNumerator,rawBoundaryPoint]
      have hRight (t : Ico (0:ℝ) 1) : (E (.inr t)).val.val =
          Quot.mk (OrientableRel p 1) (rawEdgePoint (p:=p) (.inr ())
            ⟨t.val,t.property.1,t.property.2.le⟩ false) := by
        rw [rawEdgePoint_seam]
        rfl
      have hzero : E (.inr (⟨0,by norm_num⟩ : Ico (0:ℝ) 1))=survivingBase p := by
        apply Subtype.ext
        apply Subtype.ext
        rw [hRight]
        change Quot.mk (OrientableRel p 1) (rawEdgePoint (p:=p) (.inr ()) 0 false)=_
        rw [raw_seam_zero_main_class]
        rfl
      have hSeam (t : Ico (0:ℝ) 1) : E (.inr t) ∈ K ↔ t.val=0 := by
        constructor
        · rintro ⟨d,hd⟩
          have he := congrArg (fun z : actualSurvivingBoundary p => z.val.val) hd
          change (E (.inl d)).val.val=(E (.inr t)).val.val at he
          rw [hLeft,hRight] at he
          have hf := (source_surviving_graph_whole_port_fiber p (.inl d.1) (.inr ()) d.2
            ⟨t.val,t.property.1,t.property.2.le⟩ trivial t.property.2).mp he
          rcases hf with ⟨he,_⟩|⟨_,ht⟩
          · cases he
          · rcases ht with ht|ht
            · exact congrArg (fun z : unitInterval => (z:ℝ)) ht
            · exact False.elim ht
        · intro ht
          have ht' : t=⟨0,by norm_num⟩ := Subtype.ext ht
          rw [ht',hzero]
          exact ⟨((⟨0,by omega⟩,false),0),handleEdge_source p ⟨0,by omega⟩ false⟩
      have hK : IsClosed K := by
        apply hE.isCoinducing.isClosed_preimage.mp
        apply isClosed_sum_iff.mpr
        constructor
        · have he : Sum.inl ⁻¹' (E ⁻¹' K) = (Set.univ : Set P) := by
            ext d
            simp only [mem_preimage,mem_univ,iff_true]
            exact ⟨d,rfl⟩
          rw [he]
          exact isClosed_univ
        · have he : Sum.inr ⁻¹' (E ⁻¹' K) = {t : Ico (0:ℝ) 1 | t.val=0} := by
            ext t
            exact hSeam t
          rw [he]
          exact isClosed_eq continuous_subtype_val continuous_const
      have hrestrict : IsQuotientMap (K.restrictPreimage E) := by
        refine (isQuotientMap_iff _).mpr ⟨?_,hE.surjective.restrictPreimage _⟩
        apply IsCoinducing.of_isClosed_preimage_iff_isClosed
        intro a
        rw [hK.isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed,
          ← hE.isCoinducing.isClosed_preimage,
          (hK.preimage hE.continuous).isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed,
          image_val_preimage_restrictPreimage]
      let b : P := ((⟨0,by omega⟩,false),0)
      let L : (E ⁻¹' K) → P := fun z => match z.val with
        | .inl d => d
        | .inr _ => b
      have hLc : Continuous L := by
        have hc : Continuous (fun z : ActualEdgeParameterSpace p =>
            match z with | .inl d => d | .inr _ => b) :=
          continuous_sum_dom.mpr ⟨continuous_id,continuous_const⟩
        exact hc.comp continuous_subtype_val
      have hcomp : (fun z : E ⁻¹' K => H (L z))=K.restrictPreimage E := by
        funext z
        apply Subtype.ext
        cases hz : z.val with
        | inl d => simp [L,H,Set.restrictPreimage,hz,E,actualEdgeParameterMap]
        | inr t =>
          have ht : t.val=0 := (hSeam t).mp (hz ▸ z.property)
          have ht' : t=⟨0,by norm_num⟩ := Subtype.ext ht
          change handleEdge p (L z).1.1 (L z).1.2 (L z).2=E z.val
          have hL : L z=b := by simp [L,hz]
          rw [hL,hz,ht',hzero]
          exact handleEdge_source p ⟨0,by omega⟩ false
      have hHQ : IsQuotientMap H := by
        apply IsQuotientMap.of_comp hLc H.continuous
        change IsQuotientMap (fun z => H (L z))
        rw [hcomp]
        exact hrestrict
      exact ⟨H,hHQ,fun _ => rfl⟩
    obtain ⟨f,hfparam,hfa,hfb⟩ := hCircle
    obtain ⟨radius,hrad,q,hq,hqpoint⟩ := hBoundary
    let j : Circle → Complex.ClosedUnitDisc := fun z =>
      ⟨(z:ℂ),by simpa only [Metric.mem_closedBall,dist_zero_right] using (Circle.norm_coe z).le⟩
    let g : Complex.ClosedUnitDisc → actualSurvivingBoundary p := fun z =>
      if hz : ‖(z:ℂ)‖=1 then
        f ⟨(z:ℂ),by simpa [Submonoid.unitSphere,Metric.mem_sphere,dist_zero_right] using hz⟩
      else survivingBase p
    have hgj (z : Circle) : g (j z)=f z := by
      dsimp only [g,j]
      rw [dif_pos (Circle.norm_coe z)]
      congr 1
    have hgb (r : ℝ) : g (Complex.ClosedUnitDisc.bdyPtOfReal r)=f (Real.fourierChar r) := by
      dsimp only [g,Complex.ClosedUnitDisc.bdyPtOfReal]
      rw [dif_pos (Circle.norm_coe (Real.fourierChar r))]
      congr 1
    have hgr (z w : Complex.ClosedUnitDisc) (h : OrientableRel p 0 z w) : g z=g w := by
      cases h with
      | a t i =>
        simp only [Nat.cast_zero,mul_zero,add_zero,hgb]
        exact hfa t i
      | b t i =>
        simp only [Nat.cast_zero,mul_zero,add_zero,hgb]
        exact hfb t i
      | c t i => exact Fin.elim0 i
    have hge (z w : Complex.ClosedUnitDisc) (h : Relation.EqvGen (OrientableRel p 0) z w) : g z=g w := by
      induction h with
      | rel z w h => exact hgr z w h
      | refl z => rfl
      | symm z w h ih => exact ih.symm
      | trans z w u h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
    have hffiber (z w : Circle) (h : q z=q w) : f z=f w := by
      have he := congrArg Subtype.val h
      rw [hqpoint,hqpoint] at he
      have hh := hge (j z) (j w) (Quot.eqvGen_exact he)
      simpa only [hgj] using hh
    let F := hq.lift f hffiber
    have hFq (z : Circle) : F (q z)=f z :=
      ContinuousMap.congr_fun (hq.lift_comp f hffiber) z
    have hpR : (1:ℝ)≤p := by exact_mod_cast hp
    have hFhandle :
      ∀ (t : unitInterval) (i : Fin p) (b : Bool),
          ∀ hz : radius (Quot.mk (OrientableRel p 0)
            (Complex.ClosedUnitDisc.bdyPtOfReal ((4*(i:ℝ)+(if b then 1 else 0)+(t:ℝ))/(4*(p:ℝ)))))=1,
          F ⟨Quot.mk (OrientableRel p 0)
            (Complex.ClosedUnitDisc.bdyPtOfReal ((4*(i:ℝ)+(if b then 1 else 0)+(t:ℝ))/(4*(p:ℝ)))),hz⟩ =
            handleEdge p i b t
      := by
      intro t i b hz
      let s : ℝ := 4*(i:ℝ)+(if b then 1 else 0)+(t:ℝ)
      have hs : 0 ≤ s ∧ s ≤ 4*(p:ℝ) := handleNumerator_bounds i b t
      have he : (⟨Quot.mk (OrientableRel p 0) (Complex.ClosedUnitDisc.bdyPtOfReal (s/(4*(p:ℝ)))),hz⟩ :
          {z : Quot (OrientableRel p 0) | radius z=1}) = q (Real.fourierChar (s/(4*(p:ℝ)))) := by
        apply Subtype.ext
        rw [hqpoint]
        rfl
      change F ⟨Quot.mk (OrientableRel p 0) (Complex.ClosedUnitDisc.bdyPtOfReal (s/(4*(p:ℝ)))),hz⟩=_
      rw [he,hFq]
      apply Subtype.ext
      apply Subtype.ext
      rw [hfparam s hs.1 hs.2]
      rfl
    let P := (Fin p × Bool) × unitInterval
    let K : Set (actualSurvivingBoundary p) :=
      Set.range (fun z : P => handleEdge p z.1.1 z.1.2 z.2)
    obtain ⟨H,hHQ,hHpoint⟩ := hHandleQuotient
    let G : Set (Quot (OrientableRel p 0)) := {z | radius z=1}
    let Q : ℝ → Quot (OrientableRel p 0) := fun s =>
      Quot.mk (OrientableRel p 0) (Complex.ClosedUnitDisc.bdyPtOfReal (s/(4*(p:ℝ))))
    have hQrad (s : ℝ) : radius (Q s)=1 := by
      rw [hrad]
      exact Circle.norm_coe _
    let J : C(P,G) := {
      toFun d := ⟨Q (handleNumerator d.1.1 d.1.2 d.2),hQrad _⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        apply (continuous_quot_mk (r:=OrientableRel p 0)).comp
        apply Continuous.subtype_mk
        apply continuous_subtype_val.comp
        apply Real.continuous_fourierChar.comp
        apply continuous_prod_of_discrete_left.mpr
        intro d
        dsimp [handleNumerator]
        rcases d with ⟨i,b⟩
        cases b <;> simp only [Bool.false_eq_true,↓reduceIte] <;> fun_prop }
    have hFJ (d : P) : F (J d)=handleEdge p d.1.1 d.1.2 d.2 := hFhandle d.2 d.1.1 d.1.2 _
    have hblock (i : Fin p) : Q (4*(i:ℝ))=Q (4*(i:ℝ)+1) ∧
        Q (4*(i:ℝ))=Q (4*(i:ℝ)+2) ∧ Q (4*(i:ℝ))=Q (4*(i:ℝ)+3) ∧
        Q (4*(i:ℝ))=Q (4*(i:ℝ)+4) := by
      have ha0 := Quot.sound (OrientableRel.a (p:=p) (n:=0) (0 : unitInterval) i)
      have ha1 := Quot.sound (OrientableRel.a (p:=p) (n:=0) (1 : unitInterval) i)
      have hb0 := Quot.sound (OrientableRel.b (p:=p) (n:=0) (0 : unitInterval) i)
      have hb1 := Quot.sound (OrientableRel.b (p:=p) (n:=0) (1 : unitInterval) i)
      simp only [Nat.cast_zero,mul_zero,add_zero] at ha0 ha1 hb0 hb1
      change Q (4*(i:ℝ)+0)=Q (4*(i:ℝ)+3-0) at ha0
      change Q (4*(i:ℝ)+1)=Q (4*(i:ℝ)+3-1) at ha1
      change Q (4*(i:ℝ)+1+0)=Q (4*(i:ℝ)+4-0) at hb0
      change Q (4*(i:ℝ)+1+1)=Q (4*(i:ℝ)+4-1) at hb1
      have he1 : 4*(i:ℝ)+3-1=4*(i:ℝ)+2 := by ring
      have he2 : 4*(i:ℝ)+1+1=4*(i:ℝ)+2 := by ring
      have he3 : 4*(i:ℝ)+4-1=4*(i:ℝ)+3 := by ring
      simp only [add_zero,sub_zero] at ha0 hb0
      rw [he1] at ha1
      rw [he2,he3] at hb1
      have h01 := ha0.trans (hb1.symm.trans ha1.symm)
      exact ⟨h01,ha0.trans hb1.symm,ha0,h01.trans hb0⟩
    have hvertex (n : ℕ) (hn : n ≤ p) : Q (4*(n:ℝ))=Q 0 := by
      induction n with
      | zero => simp
      | succ n ih =>
        have he := (hblock ⟨n,by omega⟩).2.2.2
        have hi := ih (by omega)
        have hh : 4*((n+1:ℕ):ℝ)=4*(n:ℝ)+4 := by push_cast;ring
        rw [hh]
        exact he.symm.trans hi
    have hJbase (d : P) (hd : d.2=0 ∨ d.2=1) : (J d).val=Q 0 := by
      have hv := hvertex d.1.1.val d.1.1.isLt.le
      have hb := hblock d.1.1
      change Q (handleNumerator d.1.1 d.1.2 d.2)=Q 0
      rcases d with ⟨⟨i,b⟩,t⟩
      rcases hd with rfl|rfl
      · cases b
        · simpa [handleNumerator] using hv
        · simpa [handleNumerator] using hb.1.symm.trans hv
      · cases b
        · simpa [handleNumerator] using hb.1.symm.trans hv
        · have hh : handleNumerator i true 1=4*(i:ℝ)+2 := by simp [handleNumerator];ring
          rw [hh]
          exact hb.2.1.symm.trans hv
    have hJfiber (d e : P) (h : H d=H e) : J d=J e := by
      have he := congrArg (fun z : K => z.val.val.val) h
      have hEdge (d : P) : (handleEdge p d.1.1 d.1.2 d.2).val.val =
          Quot.mk (OrientableRel p 1) (rawEdgePoint (.inl d.1) d.2 false) := by
        change Quot.mk (OrientableRel p 1)
          (Complex.ClosedUnitDisc.bdyPtOfReal (handleNumerator d.1.1 d.1.2 d.2/modelSideCount p)) = _
        rw [rawEdgePoint_handle]
        simp [handleNumerator,rawBoundaryPoint]
      change (H d).val.val.val=(H e).val.val.val at he
      rw [hHpoint,hHpoint,hEdge,hEdge] at he
      have hf := (source_surviving_graph_whole_port_fiber p (.inl d.1) (.inl e.1) d.2 e.2
        trivial trivial).mp he
      rcases hf with ⟨hk,ht⟩|⟨hd,he⟩
      · have hkey : d.1=e.1 := Sum.inl.inj hk
        have hde : d=e := Prod.ext hkey ht
        rw [hde]
      · apply Subtype.ext
        exact (hJbase d hd).trans (hJbase e he).symm
    let B := hHQ.lift J hJfiber
    have hBH (d : P) : B (H d)=J d := ContinuousMap.congr_fun (hHQ.lift_comp J hJfiber) d
    -- Every actual closed boundary point is covered by a/b edge parameters.
    have hNumeric (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 4*(p:ℝ)) :
        ∃ d : P, (J d).val=Q s := by
      let k : ℕ := Nat.floor s
      have hklt : k<4*p := by
        apply (Nat.floor_lt hs0).mpr
        simpa only [Nat.cast_mul,Nat.cast_ofNat] using hs1
      let i : Fin p := ⟨k/4,by omega⟩
      have hk0 : (k:ℝ) ≤ s := Nat.floor_le hs0
      have hk1 : s<(k:ℝ)+1 := Nat.lt_floor_add_one s
      let x : unitInterval := ⟨s-(k:ℝ),by constructor <;> linarith⟩
      have hk : k=4*i.val+k%4 := by dsimp [i];omega
      have hkr : (k:ℝ)=4*(i:ℝ)+((k%4:ℕ):ℝ) := by exact_mod_cast hk
      have hn : s=4*(i:ℝ)+((k%4:ℕ):ℝ)+(x:ℝ) := by dsimp [x];linarith
      have hj : k%4=0 ∨ k%4=1 ∨ k%4=2 ∨ k%4=3 := by omega
      rcases hj with hj|hj|hj|hj
      · refine ⟨((i,false),x),?_⟩
        change Q (handleNumerator i false x)=Q s
        congr 1
        simp [handleNumerator,hj] at hn ⊢
        exact hn.symm
      · refine ⟨((i,true),x),?_⟩
        change Q (handleNumerator i true x)=Q s
        congr 1
        simp [handleNumerator,hj] at hn ⊢
        exact hn.symm
      · refine ⟨((i,false),unitInterval.symm x),?_⟩
        have ha := Quot.sound (OrientableRel.a (p:=p) (n:=0) (unitInterval.symm x) i)
        simp only [Nat.cast_zero,mul_zero,add_zero] at ha
        change Q (handleNumerator i false (unitInterval.symm x))=Q s
        have hnum : 4*(i:ℝ)+3-(unitInterval.symm x:ℝ)=s := by
          change 4*(i:ℝ)+3-(1-(x:ℝ))=s
          norm_num [hj] at hn
          linarith
        simpa only [Q,handleNumerator,Bool.false_eq_true,↓reduceIte,add_zero,← hnum] using ha
      · refine ⟨((i,true),unitInterval.symm x),?_⟩
        have hb := Quot.sound (OrientableRel.b (p:=p) (n:=0) (unitInterval.symm x) i)
        simp only [Nat.cast_zero,mul_zero,add_zero] at hb
        change Q (handleNumerator i true (unitInterval.symm x))=Q s
        have hnum : 4*(i:ℝ)+4-(unitInterval.symm x:ℝ)=s := by
          change 4*(i:ℝ)+4-(1-(x:ℝ))=s
          norm_num [hj] at hn
          linarith
        simpa only [Q,handleNumerator,Bool.true_eq,↓reduceIte,← hnum] using hb
    have hJS : Function.Surjective J := by
      intro y
      obtain ⟨z,hz⟩ := hq.surjective y
      let HC := AddCircle.homeomorphCircle (T:=(1:ℝ)) one_ne_zero
      let t := AddCircle.equivIco (1:ℝ) 0 (HC.symm z)
      have ht : (t:ℝ) ∈ Ico (0:ℝ) 1 := by simpa only [zero_add] using t.property
      have htz : Real.fourierChar (t:ℝ)=z := by
        have he : (((t:ℝ) : AddCircle (1:ℝ)))=HC.symm z := AddCircle.coe_equivIco
        have hh := congrArg HC he
        simpa only [HC,AddCircle.homeomorphCircle_apply,AddCircle.toCircle_apply_mk,
          div_one,Real.fourierChar_apply',HC.apply_symm_apply] using hh
      have hN : 0<4*(p:ℝ) := by positivity
      let s : ℝ := 4*(p:ℝ)*(t:ℝ)
      obtain ⟨d,hd⟩ := hNumeric s (mul_nonneg hN.le ht.1) (by dsimp [s];nlinarith [ht.2])
      refine ⟨d,?_⟩
      apply Subtype.ext
      rw [hd,← hz,hqpoint]
      rw [← htz]
      apply congrArg (Quot.mk (OrientableRel p 0))
      apply Subtype.ext
      change (Real.fourierChar (s/(4*(p:ℝ))) : ℂ)=(Real.fourierChar (t:ℝ) : ℂ)
      dsimp [s]
      rw [mul_div_cancel_left₀ (t:ℝ) hN.ne']
    have hFK (y : G) : F y ∈ K := by
      obtain ⟨d,rfl⟩ := hJS y
      rw [hFJ]
      exact ⟨d,rfl⟩
    let FB : C(G,K) := ⟨fun y => ⟨F y,hFK y⟩,F.continuous.subtype_mk _⟩
    have hFBJ (d : P) : FB (J d)=H d := by
      apply Subtype.ext
      exact (hFJ d).trans (hHpoint d).symm
    have hleft (y : G) : B (FB y)=y := by
      obtain ⟨d,rfl⟩ := hJS y
      rw [hFBJ,hBH]
    have hright (y : K) : FB (B y)=y := by
      obtain ⟨d,rfl⟩ := hHQ.surjective y
      rw [hBH,hFBJ]
    exact ⟨radius,hrad,K,rfl,⟨{
      toFun := FB
      invFun := B
      left_inv := hleft
      right_inv := hright
      continuous_toFun := FB.continuous
      continuous_invFun := B.continuous }⟩⟩
  have hContraction :
      ∃ K : Set (actualSurvivingBoundary p),
        K = Set.range (fun z : (Fin p × Bool) × unitInterval => handleEdge p z.1.1 z.1.2 z.2) ∧
        Nonempty (actualSurvivingBoundary p ≃ₕ K)
 := by
    classical
    let A := ActualEdgeParameterSpace p
    let E := actualEdgeParameterMap p
    have hE : IsQuotientMap E := source_actual_edge_parameter_map_isQuotientMap p
    let scaled (u : unitInterval) (t : Ico (0:ℝ) 1) : Ico (0:ℝ) 1 :=
      ⟨(1-(u:ℝ))*t.val,mul_nonneg (sub_nonneg.mpr u.property.2) t.property.1,
        by nlinarith [u.property.1,u.property.2,t.property.1,t.property.2]⟩
    let S : unitInterval × A → A := fun z =>
      match z.2 with
      | .inl d => .inl d
      | .inr t => .inr (scaled z.1 t)
    have hSc : Continuous S := by
      apply (Homeomorph.prodSumDistrib).symm.isQuotientMap.continuous_iff.mpr
      apply continuous_sum_dom.mpr
      constructor
      · exact continuous_inl.comp continuous_snd
      · apply continuous_inr.comp
        apply Continuous.subtype_mk
        change Continuous (fun z : unitInterval × Ico (0:ℝ) 1 => (1-(z.1:ℝ))*z.2.val)
        fun_prop
    let D : unitInterval × A → actualSurvivingBoundary p := fun z => E (S z)
    have hDc : Continuous D := hE.continuous.comp hSc
    have hLeft (d : (Fin p × Bool) × unitInterval) :
        (E (.inl d)).val.val = Quot.mk (OrientableRel p 1) (rawEdgePoint (.inl d.1) d.2 false) := by
      change Quot.mk (OrientableRel p 1)
        (Complex.ClosedUnitDisc.bdyPtOfReal (handleNumerator d.1.1 d.1.2 d.2/modelSideCount p)) = _
      rw [rawEdgePoint_handle]
      simp [handleNumerator,rawBoundaryPoint]
    have hRight (t : Ico (0:ℝ) 1) :
        (E (.inr t)).val.val = Quot.mk (OrientableRel p 1)
          (rawEdgePoint (p:=p) (.inr ()) ⟨t.val,t.property.1,t.property.2.le⟩ false) := by
      rw [rawEdgePoint_seam]
      rfl
    have hSeamZero : E (.inr (⟨0,by norm_num⟩ : Ico (0:ℝ) 1)) = survivingBase p := by
      apply Subtype.ext
      apply Subtype.ext
      rw [hRight]
      change Quot.mk (OrientableRel p 1) (rawEdgePoint (p:=p) (.inr ()) 0 false) = _
      rw [raw_seam_zero_main_class]
      rfl
    have hScaledZero (u : unitInterval) (t : Ico (0:ℝ) 1) (ht : t.val=0) :
        E (.inr (scaled u t)) = survivingBase p := by
      have hs : scaled u t = ⟨0,by norm_num⟩ := Subtype.ext (by simp [scaled,ht])
      rw [hs,hSeamZero]
    have hFix (u : unitInterval) (x y : A) (h : E x = E y) : D (u,x)=D (u,y) := by
      cases x with
      | inl d =>
        cases y with
        | inl e => exact h
        | inr t =>
          have he := congrArg (fun q : actualSurvivingBoundary p => q.val.val) h
          rw [hLeft,hRight] at he
          have hf := (source_surviving_graph_whole_port_fiber p (.inl d.1) (.inr ()) d.2
            ⟨t.val,t.property.1,t.property.2.le⟩ trivial t.property.2).mp he
          rcases hf with ⟨he,_⟩ | ⟨hd,ht⟩
          · cases he
          · have ht0 : t.val=0 := by
              rcases ht with ht|ht
              · exact congrArg Subtype.val ht
              · exact False.elim ht
            change E (.inl d)=E (.inr (scaled u t))
            rw [hScaledZero u t ht0]
            change d.2=0 ∨ d.2=1 at hd
            rcases hd with hd|hd
            · simpa [E,actualEdgeParameterMap,hd] using handleEdge_source p d.1.1 d.1.2
            · simpa [E,actualEdgeParameterMap,hd] using handleEdge_target p d.1.1 d.1.2
      | inr s =>
        cases y with
        | inl e =>
          have he := congrArg (fun q : actualSurvivingBoundary p => q.val.val) h.symm
          rw [hLeft,hRight] at he
          have hf := (source_surviving_graph_whole_port_fiber p (.inl e.1) (.inr ()) e.2
            ⟨s.val,s.property.1,s.property.2.le⟩ trivial s.property.2).mp he
          rcases hf with ⟨he,_⟩ | ⟨he,hs⟩
          · cases he
          · have hs0 : s.val=0 := by
              rcases hs with hs|hs
              · exact congrArg Subtype.val hs
              · exact False.elim hs
            change E (.inr (scaled u s))=E (.inl e)
            rw [hScaledZero u s hs0]
            change e.2=0 ∨ e.2=1 at he
            rcases he with he|he
            · simpa [E,actualEdgeParameterMap,he] using (handleEdge_source p e.1.1 e.1.2).symm
            · simpa [E,actualEdgeParameterMap,he] using (handleEdge_target p e.1.1 e.1.2).symm
        | inr t =>
          have he := congrArg (fun q : actualSurvivingBoundary p => q.val.val) h
          rw [hRight,hRight] at he
          have hf := (source_surviving_graph_whole_port_fiber p (.inr ()) (.inr ())
            ⟨s.val,s.property.1,s.property.2.le⟩ ⟨t.val,t.property.1,t.property.2.le⟩
            s.property.2 t.property.2).mp he
          have hst : s=t := by
            apply Subtype.ext
            rcases hf with ⟨_,hval⟩ | ⟨hs,ht⟩
            · exact congrArg (fun z : unitInterval => (z:ℝ)) hval
            · rcases hs with hs|hs
              · rcases ht with ht|ht
                · exact (congrArg Subtype.val hs).trans (congrArg Subtype.val ht).symm
                · exact False.elim ht
              · exact False.elim hs
          rw [hst]
    let rep : actualSurvivingBoundary p → A := Function.surjInv hE.surjective
    have hr (q : actualSurvivingBoundary p) : E (rep q)=q := Function.rightInverse_surjInv hE.surjective q
    let Hfun : unitInterval × actualSurvivingBoundary p → actualSurvivingBoundary p :=
      fun z => D (z.1,rep z.2)
    have hH (u : unitInterval) (x : A) : Hfun (u,E x)=D (u,x) := hFix u _ _ (hr (E x))
    have hHc : Continuous Hfun := by
      apply hE.continuous_lift_prod_right
      convert hDc using 1
      funext z
      exact hH z.1 z.2
    let K : Set (actualSurvivingBoundary p) :=
      Set.range (fun z : (Fin p × Bool) × unitInterval => handleEdge p z.1.1 z.1.2 z.2)
    have hH0 (q : actualSurvivingBoundary p) : Hfun (0,q)=q := by
      obtain ⟨x,rfl⟩ := hE.surjective q
      rw [hH]
      cases x with
      | inl d => rfl
      | inr t =>
        change E (.inr (scaled 0 t))=E (.inr t)
        have hs : scaled 0 t=t := Subtype.ext (by simp [scaled])
        rw [hs]
    have hH1 (q : actualSurvivingBoundary p) : Hfun (1,q) ∈ K := by
      obtain ⟨x,rfl⟩ := hE.surjective q
      rw [hH]
      cases x with
      | inl d => exact ⟨d,rfl⟩
      | inr t =>
        have hs : scaled 1 t = ⟨0,by norm_num⟩ := Subtype.ext (by simp [scaled])
        change E (.inr (scaled 1 t)) ∈ K
        rw [hs,hSeamZero]
        exact ⟨((⟨0,by omega⟩,false),0),handleEdge_source p ⟨0,by omega⟩ false⟩
    have hHK (u : unitInterval) (q : K) : Hfun (u,q.val)=q.val := by
      obtain ⟨d,hd⟩ := q.property
      change handleEdge p d.1.1 d.1.2 d.2=q.val at hd
      rw [← hd]
      exact hH u (.inl d)
    let ret : C(actualSurvivingBoundary p,K) :=
      ⟨fun q => ⟨Hfun (1,q),hH1 q⟩,
        (hHc.comp (continuous_const.prodMk continuous_id)).subtype_mk _⟩
    let inc : C(K,actualSurvivingBoundary p) := ⟨Subtype.val,continuous_subtype_val⟩
    let HH : Homotopy (ContinuousMap.id (actualSurvivingBoundary p)) (inc.comp ret) := {
      toFun := Hfun
      continuous_toFun := hHc
      map_zero_left := hH0
      map_one_left := fun _ => rfl }
    have hri : ret.comp inc=ContinuousMap.id K := by
      apply ContinuousMap.ext
      intro q
      apply Subtype.ext
      exact hHK 1 q
    exact ⟨K,rfl,⟨{
      toFun := ret
      invFun := inc
      left_inv := ⟨HH.symm⟩
      right_inv := by rw [hri] }⟩⟩
  obtain ⟨radius,hrad,K,hK,⟨eHomeo⟩⟩ := hHomeomorph
  obtain ⟨K',hK',⟨eContract⟩⟩ := hContraction
  have hKK : K'=K := hK'.trans hK.symm
  cases hKK
  have hBoundary : ActualClosedOrientableBoundaryGraph p =
      ({z | radius z=1} : Set (Quot (OrientableRel p 0))) := by
    ext q
    constructor
    · rintro ⟨z,rfl⟩
      change radius (Quot.mk (OrientableRel p 0) _)=1
      rw [hrad]
      exact Circle.norm_coe z
    · intro hq
      induction q using Quot.inductionOn with
      | h z =>
        have hz : ‖(z:ℂ)‖=1 := by
          change radius (Quot.mk (OrientableRel p 0) z)=1 at hq
          rw [hrad] at hq
          exact hq
        let w : Circle := ⟨(z:ℂ),by
          simpa [Submonoid.unitSphere,Metric.mem_sphere,dist_zero_right] using hz⟩
        refine ⟨w,?_⟩
        apply congrArg (Quot.mk (OrientableRel p 0))
        rfl
  let eBoundary := Homeomorph.setCongr hBoundary
  obtain ⟨eExisting⟩ := actual_one_boundary_surviving_graph_homology_one p
  exact ⟨CircleHomologyComputation.homotopyHomologyIso eBoundary.toHomotopyEquiv 1 ≪≫
    CircleHomologyComputation.homotopyHomologyIso eHomeo.toHomotopyEquiv 1 ≪≫
    (CircleHomologyComputation.homotopyHomologyIso eContract 1).symm ≪≫ eExisting⟩
end CurveComplex.Hyperbolic
