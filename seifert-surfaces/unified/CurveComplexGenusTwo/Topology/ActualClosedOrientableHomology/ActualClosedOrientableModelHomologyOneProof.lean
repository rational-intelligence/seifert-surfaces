import CurveComplexGenusTwo.Octagon.SurfaceAssembly.OuterBandRetraction
import CurveComplexGenusTwo.Topology.ActualClosedOrientableHomology.ActualClosedBoundaryGraphHomologyProof
import CurveComplexGenusTwo.Topology.ActualClosedOrientableHomology.ActualClosedAttachingMapHomologyZeroProof
import CurveComplexGenusTwo.Octagon.SurfaceAssembly.SurfaceActualMV
open Set Topology CategoryTheory CategoryTheory.Limits ContinuousMap
open CurveComplexGenusTwo.CWHurewicz
open LeanEval.Topology.ClassificationOfSurfaces
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
set_option maxRecDepth 10000
namespace CurveComplex.Hyperbolic
theorem actual_closed_orientable_model_homology_one
    (p : ℕ) (hp : 1 ≤ p) :
    Nonempty (integralHomology (Quot (OrientableRel p 0)) 1 ≅
      ModuleCat.of ℤ (Fin (2 * p) → ℤ)) := by
  have hattach (p : ℕ) (hp : 1 ≤ p) :
      ∃ radius : C(Quot (OrientableRel p 0), ℝ),
        (∀ z : Complex.ClosedUnitDisc, radius (Quot.mk (OrientableRel p 0) z)=‖(z:ℂ)‖) ∧
        ∃ e : ({q | (1/2:ℝ)<radius q} : Set (Quot (OrientableRel p 0))) ≃ₕ
          ({q | radius q=1} : Set (Quot (OrientableRel p 0))),
        actualSubsetHomologyMap (TopCat.of (Quot (OrientableRel p 0)))
          ({q | radius q<1} ∩ {q | (1/2:ℝ)<radius q}) {q | (1/2:ℝ)<radius q} inter_subset_right 1=0 := by
    clear * - p hp
    have hband (p : ℕ) :
        ∃ radius : C(Quot (OrientableRel p 0), ℝ),
          (∀ z : Complex.ClosedUnitDisc, radius (Quot.mk (OrientableRel p 0) z) = ‖(z : ℂ)‖) ∧
          ∃ e : ({q | (1/2 : ℝ) < radius q} : Set (Quot (OrientableRel p 0))) ≃ₕ
            ({q | radius q = 1} : Set (Quot (OrientableRel p 0))),
          ∀ (x : CurveComplex.Octagon.outerBand) (hx : (1/2:ℝ)<radius (Quot.mk (OrientableRel p 0) x.val)),
            (e.toFun ⟨Quot.mk (OrientableRel p 0) x.val,hx⟩).val =
              Quot.mk (OrientableRel p 0) (CurveComplex.Octagon.rawBandDeform (1,x)).val := by
      classical
      let R := OrientableRel p 0
      have hrel {z w : Complex.ClosedUnitDisc} (h : R z w) :
          ‖(z : ℂ)‖ = 1 ∧ ‖(w : ℂ)‖ = 1 := by
        cases h with
        | a t i => exact ⟨Circle.norm_coe _, Circle.norm_coe _⟩
        | b t i => exact ⟨Circle.norm_coe _, Circle.norm_coe _⟩
        | c t i => exact Fin.elim0 i
      have heqv {z w : Complex.ClosedUnitDisc} (h : Relation.EqvGen R z w) :
          z = w ∨ (‖(z : ℂ)‖ = 1 ∧ ‖(w : ℂ)‖ = 1) := by
        induction h with
        | rel z w h => exact Or.inr (hrel h)
        | refl z => exact Or.inl rfl
        | symm z w h ih => exact ih.elim (fun he => Or.inl he.symm) (fun hb => Or.inr hb.symm)
        | trans z w u h₁ h₂ ih₁ ih₂ =>
          rcases ih₁ with rfl | ⟨hz, hw⟩
          · exact ih₂
          · rcases ih₂ with rfl | ⟨hw', hu⟩
            · exact Or.inr ⟨hz, hw⟩
            · exact Or.inr ⟨hz, hu⟩
      have respects : ∀ z w : Complex.ClosedUnitDisc, R z w → ‖(z : ℂ)‖ = ‖(w : ℂ)‖ :=
        fun z w h => (hrel h).1.trans (hrel h).2.symm
      let radius : C(Quot R, ℝ) :=
        ⟨Quot.lift (fun z : Complex.ClosedUnitDisc => ‖(z : ℂ)‖) respects,
          continuous_quot_lift respects continuous_subtype_val.norm⟩
      let B : Set (Quot R) := {q | (1/2 : ℝ) < radius q}
      let G : Set (Quot R) := {q | radius q = 1}
      let q : C(CurveComplex.Octagon.outerBand, B) :=
        ⟨fun x => ⟨Quot.mk R x.val, x.property⟩,
          ((continuous_quot_mk (r := R)).comp continuous_subtype_val).subtype_mk _⟩
      have hq : IsQuotientMap q :=
        (isQuotientMap_quot_mk (r := R)).restrictPreimage_isOpen
          (isOpen_lt continuous_const radius.continuous)
      have hfix (t : unitInterval) {x y : CurveComplex.Octagon.outerBand} (h : q x = q y) :
          q (CurveComplex.Octagon.rawBandDeform (t,x)) =
            q (CurveComplex.Octagon.rawBandDeform (t,y)) := by
        have he := congrArg Subtype.val h
        rcases heqv (Quot.eqvGen_exact he) with he | ⟨hx,hy⟩
        · have he' : x = y := Subtype.ext he
          rw [he']
        · rw [CurveComplex.Octagon.rawBandDeform_fixed t x hx,
            CurveComplex.Octagon.rawBandDeform_fixed t y hy]
          exact h
      let rep : B → CurveComplex.Octagon.outerBand := Function.surjInv hq.surjective
      have hr (z : B) : q (rep z) = z := Function.rightInverse_surjInv hq.surjective z
      let D : unitInterval × B → B := fun z =>
        q (CurveComplex.Octagon.rawBandDeform (z.1, rep z.2))
      have hD (t : unitInterval) (x : CurveComplex.Octagon.outerBand) :
          D (t,q x) = q (CurveComplex.Octagon.rawBandDeform (t,x)) := hfix t (hr (q x))
      have hDc : Continuous D := by
        apply hq.continuous_lift_prod_right
        convert q.continuous.comp CurveComplex.Octagon.rawBandDeform_continuous using 1
        funext z
        exact hD z.1 z.2
      have hDzero (z : B) : D (0,z) = z := by
        change q (CurveComplex.Octagon.rawBandDeform (0,rep z)) = z
        rw [CurveComplex.Octagon.rawBandDeform_zero, hr]
      have hDone (z : B) : radius (D (1,z)).val = 1 :=
        CurveComplex.Octagon.rawBandDeform_one_norm (rep z)
      let ret : C(B,G) :=
        ⟨fun z => ⟨(D (1,z)).val, hDone z⟩,
          (continuous_subtype_val.comp (hDc.comp (continuous_const.prodMk continuous_id))).subtype_mk _⟩
      have hgB (z : G) : z.val ∈ B := by
        change (1/2 : ℝ) < radius z.val
        rw [z.property]
        norm_num
      let inc : C(G,B) :=
        ⟨fun z => ⟨z.val, hgB z⟩,
          continuous_subtype_val.subtype_mk (fun z => hgB z)⟩
      have hfixed (t : unitInterval) (z : G) : D (t,inc z) = inc z := by
        obtain ⟨x,hx⟩ := hq.surjective (inc z)
        have hn : ‖(x.val : ℂ)‖ = 1 := by
          have hz := z.property
          have he : radius (q x).val = radius (inc z).val := congrArg (fun w : B => radius w.val) hx
          exact he.trans hz
        rw [← hx, hD, CurveComplex.Octagon.rawBandDeform_fixed t x hn]
      let H : ContinuousMap.Homotopy (ContinuousMap.id B) (inc.comp ret) := {
        toFun := D
        continuous_toFun := hDc
        map_zero_left := hDzero
        map_one_left := fun _ => rfl }
      have hri : ret.comp inc = ContinuousMap.id G := by
        apply ContinuousMap.ext
        intro z
        apply Subtype.ext
        change (D (1,inc z)).val = z.val
        exact congrArg (fun w : B => w.val) (hfixed 1 z)
      refine ⟨radius, fun z => rfl, {
        toFun := ret
        invFun := inc
        left_inv := ⟨H.symm⟩
        right_inv := by rw [hri] },?_⟩
      intro x hx
      change (D (1,q x)).val=_
      exact congrArg Subtype.val (hD 1 x)
    have hcoords (p : ℕ) (radius : C(Quot (OrientableRel p 0), ℝ))
        (hr : ∀ z : Complex.ClosedUnitDisc, radius (Quot.mk (OrientableRel p 0) z)=‖(z:ℂ)‖) :
        ∃ e : CurveComplex.Octagon.radialAnnulusSet ≃ₜ
          ({q | radius q < 1 ∧ (1/2:ℝ)<radius q} : Set (Quot (OrientableRel p 0))),
          ∀ z, (e z).val=Quot.mk (OrientableRel p 0) z.val := by
      have hEmb (p : ℕ) :
          Topology.IsOpenEmbedding
            (({z : Complex.ClosedUnitDisc | ‖(z : ℂ)‖ < 1}).domRestrict
              (Quot.mk (OrientableRel p 0))) := by
        let R := OrientableRel p 0
        let U : Set Complex.ClosedUnitDisc := {z | ‖(z : ℂ)‖ < 1}
        let q := Quot.mk R
        have hrel {z w : Complex.ClosedUnitDisc} (h : R z w) :
            ‖(z : ℂ)‖ = 1 ∧ ‖(w : ℂ)‖ = 1 := by
          cases h with
          | a t i => exact ⟨Circle.norm_coe _, Circle.norm_coe _⟩
          | b t i => exact ⟨Circle.norm_coe _, Circle.norm_coe _⟩
          | c t i => exact Fin.elim0 i
        have heqv {z w : Complex.ClosedUnitDisc} (h : Relation.EqvGen R z w) :
            z = w ∨ (‖(z : ℂ)‖ = 1 ∧ ‖(w : ℂ)‖ = 1) := by
          induction h with
          | rel z w h => exact Or.inr (hrel h)
          | refl z => exact Or.inl rfl
          | symm z w h ih => exact ih.elim (fun he => Or.inl he.symm) (fun hb => Or.inr hb.symm)
          | trans z w u h₁ h₂ ih₁ ih₂ =>
            rcases ih₁ with rfl | ⟨hz, hw⟩
            · exact ih₂
            · rcases ih₂ with rfl | ⟨hw', hu⟩
              · exact Or.inr ⟨hz, hw⟩
              · exact Or.inr ⟨hz, hu⟩
        have hident {z w : Complex.ClosedUnitDisc} (hz : z ∈ U) (h : q z = q w) : z = w := by
          rcases heqv (Quot.eq.mp h) with he | hn
          · exact he
          · exact False.elim (by change ‖(z : ℂ)‖ < 1 at hz; linarith [hn.1])
        have hU : IsOpen U := isOpen_lt continuous_subtype_val.norm continuous_const
        have hcont : Continuous (U.domRestrict q) := (continuous_quot_mk (r := R)).comp continuous_subtype_val
        have hinj : Function.Injective (U.domRestrict q) := by
          intro x y h
          exact Subtype.ext (hident x.property h)
        have hopen : IsOpenMap (U.domRestrict q) := by
          intro s hs
          let A : Set Complex.ClosedUnitDisc := Subtype.val '' s
          have hA : IsOpen A := hU.isOpenEmbedding_subtypeVal.isOpenMap s hs
          have himage : U.domRestrict q '' s = q '' A := by
            ext x
            simp [A, Set.mem_image]
          rw [himage]
          apply (isQuotientMap_quot_mk (r := R)).isCoinducing.isOpen_preimage.mp
          have hsat : q ⁻¹' (q '' A) = A := by
            ext x
            constructor
            · rintro ⟨z, ⟨a, ha, rfl⟩, he⟩
              have hax : a.val = x := hident a.property he
              exact ⟨a, ha, hax⟩
            · intro hx
              exact ⟨x, hx, rfl⟩
          rw [hsat]
          exact hA
        exact Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hcont hinj hopen
      let D : Set Complex.ClosedUnitDisc := {z | ‖(z:ℂ)‖ < 1}
      let O : Set (Quot (OrientableRel p 0)) := {q | radius q < 1 ∧ (1/2:ℝ)<radius q}
      let q : D → Quot (OrientableRel p 0) := D.domRestrict (Quot.mk (OrientableRel p 0))
      have hs : O ⊆ Set.range q := by
        intro y hy
        obtain ⟨z,rfl⟩ := Quot.mk_surjective y
        refine ⟨⟨z,?_⟩,rfl⟩
        change radius (Quot.mk (OrientableRel p 0) z)<1 ∧ _ at hy
        rw [hr] at hy
        exact hy.1
      let e₁ : (q ⁻¹' O) ≃ₜ O := (hEmb p).isEmbedding.homeomorphOfSubsetRange hs
      let e₀ : CurveComplex.Octagon.radialAnnulusSet ≃ₜ (q ⁻¹' O) := {
        toFun := fun z => ⟨⟨z.val,z.property.2⟩,by
          change radius (Quot.mk (OrientableRel p 0) z.val)<1 ∧ (1/2:ℝ)<radius (Quot.mk (OrientableRel p 0) z.val)
          rw [hr]
          exact ⟨z.property.2,z.property.1⟩⟩
        invFun := fun z => ⟨z.val.val,by
          have hz := z.property
          change radius (Quot.mk (OrientableRel p 0) z.val.val)<1 ∧ (1/2:ℝ)<radius (Quot.mk (OrientableRel p 0) z.val.val) at hz
          rw [hr] at hz
          exact ⟨hz.2,hz.1⟩⟩
        left_inv := fun z => rfl
        right_inv := fun z => rfl
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
      exact ⟨e₀.trans e₁,fun z => rfl⟩
    obtain ⟨radius,hr,e,hret⟩ := hband p
    let B : Set (Quot (OrientableRel p 0)) := {q | (1/2:ℝ)<radius q}
    let G : Set (Quot (OrientableRel p 0)) := {q | radius q=1}
    let O : Set (Quot (OrientableRel p 0)) := {q | radius q<1 ∧ (1/2:ℝ)<radius q}
    obtain ⟨eO,heO⟩ := hcoords p radius hr
    let i : C(O,B) := ⟨fun z => ⟨z.val,z.property.2⟩,by fun_prop⟩
    have hG : ActualClosedOrientableBoundaryGraph p=G := by
      ext q
      constructor
      · rintro ⟨z,rfl⟩
        change radius (Quot.mk (OrientableRel p 0) _)=1
        rw [hr]
        exact Circle.norm_coe z
      · intro hq
        induction q using Quot.inductionOn with
        | h z =>
          have hz : ‖(z:ℂ)‖=1 := by
            change radius (Quot.mk (OrientableRel p 0) z)=1 at hq
            rwa [hr] at hq
          let w : Circle := ⟨(z:ℂ),by simpa [Submonoid.unitSphere,Metric.mem_sphere,dist_zero_right] using hz⟩
          refine ⟨w,?_⟩
          apply congrArg (Quot.mk (OrientableRel p 0))
          exact Subtype.ext rfl
    let toG : C(ActualClosedOrientableBoundaryGraph p,G) :=
      ⟨Homeomorph.setCongr hG,(Homeomorph.setCongr hG).continuous⟩
    let direction : C(O,Circle) := {
      toFun := fun q => ⟨‖((eO.symm q).val:ℂ)‖⁻¹ • ((eO.symm q).val:ℂ),by
        change ‖((eO.symm q).val:ℂ)‖⁻¹ • ((eO.symm q).val:ℂ) ∈ Metric.sphere (0:ℂ) 1
        rw [Metric.mem_sphere,dist_zero_right]
        change ‖‖((eO.symm q).val:ℂ)‖⁻¹ • ((eO.symm q).val:ℂ)‖=1
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (lt_trans (by norm_num) (eO.symm q).property.1))]
        exact inv_mul_cancel₀ (ne_of_gt (lt_trans (by norm_num) (eO.symm q).property.1))⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        have hc : Continuous (fun q : O => ((eO.symm q).val:ℂ)) := by fun_prop
        exact (hc.norm.inv₀ (fun q => ne_of_gt (lt_trans (by norm_num) (eO.symm q).property.1))).smul hc }
    have hmap : e.toFun.comp i = toG.comp ((actualClosedOrientableAttachingMap p).comp direction) := by
      apply ContinuousMap.ext
      intro q
      obtain ⟨x,rfl⟩ := eO.surjective q
      apply Subtype.ext
      have hpoint : i (eO x)=⟨Quot.mk (OrientableRel p 0) x.val,by change (1/2:ℝ)<radius (Quot.mk (OrientableRel p 0) x.val);rw [hr];exact x.property.1⟩ := by
        apply Subtype.ext
        exact heO x
      change (e.toFun (i (eO x))).val=_
      rw [hpoint]
      rw [hret ⟨x.val,x.property.1⟩]
      simp only [ContinuousMap.comp_apply,actualClosedOrientableAttachingMap,actualClosedBoundaryPoint,ContinuousMap.coe_mk,direction,Homeomorph.symm_apply_apply]
      apply congrArg (Quot.mk (OrientableRel p 0))
      apply Subtype.ext
      dsimp [CurveComplex.Octagon.rawBandDeform,CurveComplex.Octagon.bandScale,toG]
      simp
    let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ ℤ)
    letI : IsIso (F.map (TopCat.ofHom e.toFun)) := (CircleHomologyComputation.homotopyHomologyIso e 1).isIso_hom
    have hm : F.map (TopCat.ofHom i) ≫ F.map (TopCat.ofHom e.toFun)=0 := by
      rw [← F.map_comp]
      have heq : TopCat.ofHom i ≫ TopCat.ofHom e.toFun =
        TopCat.ofHom direction ≫ TopCat.ofHom (actualClosedOrientableAttachingMap p) ≫ TopCat.ofHom toG := by
        exact congrArg TopCat.ofHom hmap
      rw [heq,F.map_comp,F.map_comp,actual_closed_orientable_attaching_map_homology_one_zero p hp,CategoryTheory.Limits.zero_comp,CategoryTheory.Limits.comp_zero]
    have hi : F.map (TopCat.ofHom i)=0 := by
      apply (cancel_mono (F.map (TopCat.ofHom e.toFun))).mp
      simpa using hm
    exact ⟨radius,hr,e,hi⟩
  have hface (p : ℕ) (radius : C(Quot (OrientableRel p 0), ℝ))
      (hr : ∀ z : Complex.ClosedUnitDisc, radius (Quot.mk (OrientableRel p 0) z)=‖(z:ℂ)‖) :
      ContractibleSpace ({q | radius q < 1} : Set (Quot (OrientableRel p 0))) := by
    clear * - p radius hr
    have hEmb (p : ℕ) :
        Topology.IsOpenEmbedding
          (({z : Complex.ClosedUnitDisc | ‖(z : ℂ)‖ < 1}).domRestrict
            (Quot.mk (OrientableRel p 0))) := by
      let R := OrientableRel p 0
      let U : Set Complex.ClosedUnitDisc := {z | ‖(z : ℂ)‖ < 1}
      let q := Quot.mk R
      have hrel {z w : Complex.ClosedUnitDisc} (h : R z w) :
          ‖(z : ℂ)‖ = 1 ∧ ‖(w : ℂ)‖ = 1 := by
        cases h with
        | a t i => exact ⟨Circle.norm_coe _, Circle.norm_coe _⟩
        | b t i => exact ⟨Circle.norm_coe _, Circle.norm_coe _⟩
        | c t i => exact Fin.elim0 i
      have heqv {z w : Complex.ClosedUnitDisc} (h : Relation.EqvGen R z w) :
          z = w ∨ (‖(z : ℂ)‖ = 1 ∧ ‖(w : ℂ)‖ = 1) := by
        induction h with
        | rel z w h => exact Or.inr (hrel h)
        | refl z => exact Or.inl rfl
        | symm z w h ih => exact ih.elim (fun he => Or.inl he.symm) (fun hb => Or.inr hb.symm)
        | trans z w u h₁ h₂ ih₁ ih₂ =>
          rcases ih₁ with rfl | ⟨hz, hw⟩
          · exact ih₂
          · rcases ih₂ with rfl | ⟨hw', hu⟩
            · exact Or.inr ⟨hz, hw⟩
            · exact Or.inr ⟨hz, hu⟩
      have hident {z w : Complex.ClosedUnitDisc} (hz : z ∈ U) (h : q z = q w) : z = w := by
        rcases heqv (Quot.eq.mp h) with he | hn
        · exact he
        · exact False.elim (by change ‖(z : ℂ)‖ < 1 at hz; linarith [hn.1])
      have hU : IsOpen U := isOpen_lt continuous_subtype_val.norm continuous_const
      have hcont : Continuous (U.domRestrict q) := (continuous_quot_mk (r := R)).comp continuous_subtype_val
      have hinj : Function.Injective (U.domRestrict q) := by
        intro x y h
        exact Subtype.ext (hident x.property h)
      have hopen : IsOpenMap (U.domRestrict q) := by
        intro s hs
        let A : Set Complex.ClosedUnitDisc := Subtype.val '' s
        have hA : IsOpen A := hU.isOpenEmbedding_subtypeVal.isOpenMap s hs
        have himage : U.domRestrict q '' s = q '' A := by
          ext x
          simp [A, Set.mem_image]
        rw [himage]
        apply (isQuotientMap_quot_mk (r := R)).isCoinducing.isOpen_preimage.mp
        have hsat : q ⁻¹' (q '' A) = A := by
          ext x
          constructor
          · rintro ⟨z, ⟨a, ha, rfl⟩, he⟩
            have hax : a.val = x := hident a.property he
            exact ⟨a, ha, hax⟩
          · intro hx
            exact ⟨x, hx, rfl⟩
        rw [hsat]
        exact hA
      exact Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hcont hinj hopen
    let D : Set Complex.ClosedUnitDisc := {z | ‖(z:ℂ)‖ < 1}
    let U : Set (Quot (OrientableRel p 0)) := {q | radius q < 1}
    let q : D → Quot (OrientableRel p 0) := D.domRestrict (Quot.mk (OrientableRel p 0))
    have hRange : Set.range q=U := by
      ext y
      constructor
      · rintro ⟨x,rfl⟩
        change radius (Quot.mk (OrientableRel p 0) x.val)<1
        rw [hr]
        exact x.property
      · intro hy
        obtain ⟨z,rfl⟩ := Quot.mk_surjective y
        refine ⟨⟨z,?_⟩,rfl⟩
        change radius (Quot.mk (OrientableRel p 0) z)<1 at hy
        rwa [hr] at hy
    let e : D ≃ₜ U := (hEmb p).isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hRange)
    haveI : ContractibleSpace D := by
      change ContractibleSpace CurveComplex.Octagon.diskInterior
      letI := CurveComplex.Octagon.surfaceFace_contractible
      exact CurveComplex.Octagon.faceCoordinates.contractibleSpace
    exact e.symm.contractibleSpace
  have hH0 (p : ℕ) (radius : C(Quot (OrientableRel p 0), ℝ))
      (hr : ∀ z : Complex.ClosedUnitDisc, radius (Quot.mk (OrientableRel p 0) z)=‖(z:ℂ)‖) :
      Mono (actualSubsetHomologyMap (TopCat.of (Quot (OrientableRel p 0)))
        ({q | radius q < 1} ∩ {q | (1/2:ℝ)<radius q}) {q | radius q < 1} inter_subset_left 0) := by
    clear * - p radius hr
    have hface (p : ℕ) (radius : C(Quot (OrientableRel p 0), ℝ))
        (hr : ∀ z : Complex.ClosedUnitDisc, radius (Quot.mk (OrientableRel p 0) z)=‖(z:ℂ)‖) :
        ContractibleSpace ({q | radius q < 1} : Set (Quot (OrientableRel p 0))) := by
      have hEmb (p : ℕ) :
          Topology.IsOpenEmbedding
            (({z : Complex.ClosedUnitDisc | ‖(z : ℂ)‖ < 1}).domRestrict
              (Quot.mk (OrientableRel p 0))) := by
        let R := OrientableRel p 0
        let U : Set Complex.ClosedUnitDisc := {z | ‖(z : ℂ)‖ < 1}
        let q := Quot.mk R
        have hrel {z w : Complex.ClosedUnitDisc} (h : R z w) :
            ‖(z : ℂ)‖ = 1 ∧ ‖(w : ℂ)‖ = 1 := by
          cases h with
          | a t i => exact ⟨Circle.norm_coe _, Circle.norm_coe _⟩
          | b t i => exact ⟨Circle.norm_coe _, Circle.norm_coe _⟩
          | c t i => exact Fin.elim0 i
        have heqv {z w : Complex.ClosedUnitDisc} (h : Relation.EqvGen R z w) :
            z = w ∨ (‖(z : ℂ)‖ = 1 ∧ ‖(w : ℂ)‖ = 1) := by
          induction h with
          | rel z w h => exact Or.inr (hrel h)
          | refl z => exact Or.inl rfl
          | symm z w h ih => exact ih.elim (fun he => Or.inl he.symm) (fun hb => Or.inr hb.symm)
          | trans z w u h₁ h₂ ih₁ ih₂ =>
            rcases ih₁ with rfl | ⟨hz, hw⟩
            · exact ih₂
            · rcases ih₂ with rfl | ⟨hw', hu⟩
              · exact Or.inr ⟨hz, hw⟩
              · exact Or.inr ⟨hz, hu⟩
        have hident {z w : Complex.ClosedUnitDisc} (hz : z ∈ U) (h : q z = q w) : z = w := by
          rcases heqv (Quot.eq.mp h) with he | hn
          · exact he
          · exact False.elim (by change ‖(z : ℂ)‖ < 1 at hz; linarith [hn.1])
        have hU : IsOpen U := isOpen_lt continuous_subtype_val.norm continuous_const
        have hcont : Continuous (U.domRestrict q) := (continuous_quot_mk (r := R)).comp continuous_subtype_val
        have hinj : Function.Injective (U.domRestrict q) := by
          intro x y h
          exact Subtype.ext (hident x.property h)
        have hopen : IsOpenMap (U.domRestrict q) := by
          intro s hs
          let A : Set Complex.ClosedUnitDisc := Subtype.val '' s
          have hA : IsOpen A := hU.isOpenEmbedding_subtypeVal.isOpenMap s hs
          have himage : U.domRestrict q '' s = q '' A := by
            ext x
            simp [A, Set.mem_image]
          rw [himage]
          apply (isQuotientMap_quot_mk (r := R)).isCoinducing.isOpen_preimage.mp
          have hsat : q ⁻¹' (q '' A) = A := by
            ext x
            constructor
            · rintro ⟨z, ⟨a, ha, rfl⟩, he⟩
              have hax : a.val = x := hident a.property he
              exact ⟨a, ha, hax⟩
            · intro hx
              exact ⟨x, hx, rfl⟩
          rw [hsat]
          exact hA
        exact Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hcont hinj hopen
      let D : Set Complex.ClosedUnitDisc := {z | ‖(z:ℂ)‖ < 1}
      let U : Set (Quot (OrientableRel p 0)) := {q | radius q < 1}
      let q : D → Quot (OrientableRel p 0) := D.domRestrict (Quot.mk (OrientableRel p 0))
      have hRange : Set.range q=U := by
        ext y
        constructor
        · rintro ⟨x,rfl⟩
          change radius (Quot.mk (OrientableRel p 0) x.val)<1
          rw [hr]
          exact x.property
        · intro hy
          obtain ⟨z,rfl⟩ := Quot.mk_surjective y
          refine ⟨⟨z,?_⟩,rfl⟩
          change radius (Quot.mk (OrientableRel p 0) z)<1 at hy
          rwa [hr] at hy
      let e : D ≃ₜ U := (hEmb p).isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hRange)
      haveI : ContractibleSpace D := by
        change ContractibleSpace CurveComplex.Octagon.diskInterior
        letI := CurveComplex.Octagon.surfaceFace_contractible
        exact CurveComplex.Octagon.faceCoordinates.contractibleSpace
      exact e.symm.contractibleSpace
    have hcoords (p : ℕ) (radius : C(Quot (OrientableRel p 0), ℝ))
        (hr : ∀ z : Complex.ClosedUnitDisc, radius (Quot.mk (OrientableRel p 0) z)=‖(z:ℂ)‖) :
        ∃ e : CurveComplex.Octagon.radialAnnulusSet ≃ₜ
          ({q | radius q < 1 ∧ (1/2:ℝ)<radius q} : Set (Quot (OrientableRel p 0))),
          ∀ z, (e z).val=Quot.mk (OrientableRel p 0) z.val := by
      have hEmb (p : ℕ) :
          Topology.IsOpenEmbedding
            (({z : Complex.ClosedUnitDisc | ‖(z : ℂ)‖ < 1}).domRestrict
              (Quot.mk (OrientableRel p 0))) := by
        let R := OrientableRel p 0
        let U : Set Complex.ClosedUnitDisc := {z | ‖(z : ℂ)‖ < 1}
        let q := Quot.mk R
        have hrel {z w : Complex.ClosedUnitDisc} (h : R z w) :
            ‖(z : ℂ)‖ = 1 ∧ ‖(w : ℂ)‖ = 1 := by
          cases h with
          | a t i => exact ⟨Circle.norm_coe _, Circle.norm_coe _⟩
          | b t i => exact ⟨Circle.norm_coe _, Circle.norm_coe _⟩
          | c t i => exact Fin.elim0 i
        have heqv {z w : Complex.ClosedUnitDisc} (h : Relation.EqvGen R z w) :
            z = w ∨ (‖(z : ℂ)‖ = 1 ∧ ‖(w : ℂ)‖ = 1) := by
          induction h with
          | rel z w h => exact Or.inr (hrel h)
          | refl z => exact Or.inl rfl
          | symm z w h ih => exact ih.elim (fun he => Or.inl he.symm) (fun hb => Or.inr hb.symm)
          | trans z w u h₁ h₂ ih₁ ih₂ =>
            rcases ih₁ with rfl | ⟨hz, hw⟩
            · exact ih₂
            · rcases ih₂ with rfl | ⟨hw', hu⟩
              · exact Or.inr ⟨hz, hw⟩
              · exact Or.inr ⟨hz, hu⟩
        have hident {z w : Complex.ClosedUnitDisc} (hz : z ∈ U) (h : q z = q w) : z = w := by
          rcases heqv (Quot.eq.mp h) with he | hn
          · exact he
          · exact False.elim (by change ‖(z : ℂ)‖ < 1 at hz; linarith [hn.1])
        have hU : IsOpen U := isOpen_lt continuous_subtype_val.norm continuous_const
        have hcont : Continuous (U.domRestrict q) := (continuous_quot_mk (r := R)).comp continuous_subtype_val
        have hinj : Function.Injective (U.domRestrict q) := by
          intro x y h
          exact Subtype.ext (hident x.property h)
        have hopen : IsOpenMap (U.domRestrict q) := by
          intro s hs
          let A : Set Complex.ClosedUnitDisc := Subtype.val '' s
          have hA : IsOpen A := hU.isOpenEmbedding_subtypeVal.isOpenMap s hs
          have himage : U.domRestrict q '' s = q '' A := by
            ext x
            simp [A, Set.mem_image]
          rw [himage]
          apply (isQuotientMap_quot_mk (r := R)).isCoinducing.isOpen_preimage.mp
          have hsat : q ⁻¹' (q '' A) = A := by
            ext x
            constructor
            · rintro ⟨z, ⟨a, ha, rfl⟩, he⟩
              have hax : a.val = x := hident a.property he
              exact ⟨a, ha, hax⟩
            · intro hx
              exact ⟨x, hx, rfl⟩
          rw [hsat]
          exact hA
        exact Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hcont hinj hopen
      let D : Set Complex.ClosedUnitDisc := {z | ‖(z:ℂ)‖ < 1}
      let O : Set (Quot (OrientableRel p 0)) := {q | radius q < 1 ∧ (1/2:ℝ)<radius q}
      let q : D → Quot (OrientableRel p 0) := D.domRestrict (Quot.mk (OrientableRel p 0))
      have hs : O ⊆ Set.range q := by
        intro y hy
        obtain ⟨z,rfl⟩ := Quot.mk_surjective y
        refine ⟨⟨z,?_⟩,rfl⟩
        change radius (Quot.mk (OrientableRel p 0) z)<1 ∧ _ at hy
        rw [hr] at hy
        exact hy.1
      let e₁ : (q ⁻¹' O) ≃ₜ O := (hEmb p).isEmbedding.homeomorphOfSubsetRange hs
      let e₀ : CurveComplex.Octagon.radialAnnulusSet ≃ₜ (q ⁻¹' O) := {
        toFun := fun z => ⟨⟨z.val,z.property.2⟩,by
          change radius (Quot.mk (OrientableRel p 0) z.val)<1 ∧ (1/2:ℝ)<radius (Quot.mk (OrientableRel p 0) z.val)
          rw [hr]
          exact ⟨z.property.2,z.property.1⟩⟩
        invFun := fun z => ⟨z.val.val,by
          have hz := z.property
          change radius (Quot.mk (OrientableRel p 0) z.val.val)<1 ∧ (1/2:ℝ)<radius (Quot.mk (OrientableRel p 0) z.val.val) at hz
          rw [hr] at hz
          exact ⟨hz.2,hz.1⟩⟩
        left_inv := fun z => rfl
        right_inv := fun z => rfl
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
      exact ⟨e₀.trans e₁,fun z => rfl⟩
    let U : Set (Quot (OrientableRel p 0)) := {q | radius q<1}
    let O : Set (Quot (OrientableRel p 0)) := {q | radius q<1 ∧ (1/2:ℝ)<radius q}
    let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ ℤ)
    letI : ContractibleSpace U := hface p radius hr
    obtain ⟨e,he⟩ := hcoords p radius hr
    let eO := e.symm.trans CurveComplex.Octagon.annulusOverlapHomeomorph
    let E := CircleHomologyComputation.homotopyHomologyIso eO.toHomotopyEquiv 0
    letI : IsIso (F.map (TopCat.ofHom (⟨eO,eO.continuous⟩ : C(O,CurveComplex.Octagon.overlapSet)))) := E.isIso_hom
    letI := CurveComplex.Octagon.surfaceFace_contractible
    letI := CurveComplex.Octagon.surfaceOverlap_face_H0_isIso
    have hOct := CircleHomologyComputation.augmentation_naturality
      (TopCat.ofHom CurveComplex.Octagon.overlapToFace)
    haveI : IsIso ((TopCat.of CurveComplex.Octagon.overlapSet).singularHomology₀ε (ModuleCat.of ℤ ℤ)) := by
      rw [← hOct]
      infer_instance
    have hO := CircleHomologyComputation.augmentation_naturality
      (TopCat.ofHom (⟨eO,eO.continuous⟩ : C(O,CurveComplex.Octagon.overlapSet)))
    haveI : IsIso ((TopCat.of O).singularHomology₀ε (ModuleCat.of ℤ ℤ)) := by
      rw [← hO]
      infer_instance
    let i : C(O,U) := ⟨fun z => ⟨z.val,z.property.1⟩,by fun_prop⟩
    have hi := CircleHomologyComputation.augmentation_naturality (TopCat.ofHom i)
    haveI : IsIso (F.map (TopCat.ofHom i) ≫ (TopCat.of U).singularHomology₀ε (ModuleCat.of ℤ ℤ)) := by
      rw [hi]
      infer_instance
    haveI : IsIso (F.map (TopCat.ofHom i)) := IsIso.of_isIso_comp_right _ ((TopCat.of U).singularHomology₀ε (ModuleCat.of ℤ ℤ))
    change Mono (F.map (TopCat.ofHom i))
    infer_instance
  have hMV (X : TopCat) (U V : Set X)
      (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
      (hFace : IsZero (H U 1))
      (hOverlapZero : Mono (actualSubsetHomologyMap X (U ∩ V) U inter_subset_left 0))
      (hAttach : actualSubsetHomologyMap X (U ∩ V) V inter_subset_right 1 = 0) :
      IsIso (homologyInclusion X V 1) := by
    clear * - X U V hU hV hcover hFace hOverlapZero hAttach
    letI := hOverlapZero
    have hConnecting : actualMVConnecting X U V hU hV hcover 0 = 0 := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply (ModuleCat.mono_iff_injective
        (actualSubsetHomologyMap X (U ∩ V) U inter_subset_left 0)).mp inferInstance
      have h := congrArg (fun f => f x) (actualMVConnecting_difference X U V hU hV hcover 0)
      change actualMVDifference X U V 0 (actualMVConnecting X U V hU hV hcover 0 x) = 0 at h
      have hf := congrArg Prod.fst h
      rw [actualMVDifference_apply] at hf
      change actualSubsetHomologyMap X (U ∩ V) U inter_subset_left 0
        (actualMVConnecting X U V hU hV hcover 0 x) = 0 at hf
      simpa only [ModuleCat.hom_zero, LinearMap.zero_apply, map_zero] using hf
    have hEpi : Epi (actualMVSum X U V 1) :=
      (actualMV_exact_ambient X U V hU hV hcover 0).epi_f hConnecting
    letI := hEpi
    have hFaceMap : homologyInclusion X U 1 = 0 := hFace.eq_of_src _ _
    have hBandEpi : Epi (homologyInclusion X V 1) := by
      apply (ModuleCat.epi_iff_surjective _).mpr
      intro y
      obtain ⟨⟨u,v⟩, huv⟩ := (ModuleCat.epi_iff_surjective (actualMVSum X U V 1)).mp inferInstance y
      refine ⟨v, ?_⟩
      rw [actualMVSum_apply, hFaceMap] at huv
      simpa only [ModuleCat.hom_zero, LinearMap.zero_apply, zero_add] using huv
    have hBandMono : Mono (homologyInclusion X V 1) := by
      apply (ModuleCat.mono_iff_injective _).mpr
      apply LinearMap.ker_eq_bot.mp
      apply bot_unique
      intro x hx
      have hx' : homologyInclusion X V 1 x = 0 := hx
      have hpair : (0,x) ∈ LinearMap.ker (actualMVSum X U V 1).hom := by
        change actualMVSum X U V 1 (0,x) = 0
        rw [actualMVSum_apply, map_zero, zero_add]
        exact hx'
      rw [← (actualMV_exact_pair X U V hU hV hcover 1).moduleCat_range_eq_ker] at hpair
      obtain ⟨z,hz⟩ := hpair
      have hb := congrArg Prod.snd hz
      rw [actualMVDifference_apply, hAttach] at hb
      simpa using hb.symm
    letI := hBandEpi
    letI := hBandMono
    exact isIso_of_mono_of_epi _
  obtain ⟨radius,hr,e,hzero⟩ := hattach p hp
  let X := TopCat.of (Quot (OrientableRel p 0))
  let U : Set X := {q | radius q<1}
  let V : Set X := {q | (1/2:ℝ)<radius q}
  let G : Set X := {q | radius q=1}
  have hU : IsOpen U := isOpen_lt radius.continuous continuous_const
  have hV : IsOpen V := isOpen_lt continuous_const radius.continuous
  have hcover : U ∪ V=univ := by
    ext q
    simp only [mem_union,mem_setOf_eq,mem_univ,iff_true]
    change radius q<1 ∨ (1/2:ℝ)<radius q
    by_cases h : radius q<1
    · exact Or.inl h
    · exact Or.inr (by linarith [le_of_not_gt h])
  letI : ContractibleSpace U := hface p radius hr
  have hF : IsZero (H U 1) := CircleHomologyComputation.contractible_positive_homology U 1 (by omega)
  have hM : IsIso (homologyInclusion X V 1) := hMV X U V hU hV hcover hF (hH0 p radius hr) hzero
  letI := hM
  have hG : ActualClosedOrientableBoundaryGraph p=G := by
    ext q
    constructor
    · rintro ⟨z,rfl⟩
      change radius (Quot.mk (OrientableRel p 0) _)=1
      rw [hr]
      exact Circle.norm_coe z
    · intro hq
      induction q using Quot.inductionOn with
      | h z =>
        have hz : ‖(z:ℂ)‖=1 := by
          change radius (Quot.mk (OrientableRel p 0) z)=1 at hq
          rwa [hr] at hq
        let w : Circle := ⟨(z:ℂ),by simpa [Submonoid.unitSphere,Metric.mem_sphere,dist_zero_right] using hz⟩
        refine ⟨w,?_⟩
        apply congrArg (Quot.mk (OrientableRel p 0))
        exact Subtype.ext rfl
  obtain ⟨eBoundary⟩ := actual_closed_orientable_boundary_graph_homology_one p hp
  let eG := Homeomorph.setCongr hG.symm
  exact ⟨(asIso (homologyInclusion X V 1)).symm ≪≫
    CircleHomologyComputation.homotopyHomologyIso e 1 ≪≫
    CircleHomologyComputation.homotopyHomologyIso eG.toHomotopyEquiv 1 ≪≫ eBoundary⟩
end CurveComplex.Hyperbolic
