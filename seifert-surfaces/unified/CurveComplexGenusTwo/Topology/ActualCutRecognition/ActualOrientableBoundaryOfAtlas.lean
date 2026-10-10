import CurveComplexGenusTwo.Topology.ActualBoundaryModels.Definitions
import ClassificationOfSurfaces.Moise.BoundaryInvariant
import ClassificationOfSurfaces.RepresentativeCarrier
import Mathlib
open scoped Manifold
namespace CurveComplex.Hyperbolic
open Set Topology CategoryTheory Function
open LeanEval.Topology.ClassificationOfSurfaces
open InvarianceOfDomain
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000

theorem actual_orientable_normal_form_intrinsic_boundary_components_of_atlas
    (p n : ℕ) (hadmissible : 1 ≤ p ∨ 1 ≤ n)
    (modelCharts : ChartedSpace (EuclideanHalfSpace 2) (Quot (OrientableRel p n))) :
    letI := modelCharts
    letI : TopologicalSpace (Fin n) := ⊥
    Nonempty (((modelWithCornersEuclideanHalfSpace 2).boundary
      (Quot (OrientableRel p n))) ≃ₜ (Fin n × Circle)) ∧
    (∀ hn : n = 1,
      (modelWithCornersEuclideanHalfSpace 2).boundary (Quot (OrientableRel p n)) =
        hn.symm ▸ ActualOneBoundaryOrientableBoundary p) := by
  classical
  letI := modelCharts
  letI : TopologicalSpace (Fin n) := ⊥
  let I := modelWithCornersEuclideanHalfSpace 2
  let N : ℝ := 4*(p:ℝ)+3*(n:ℝ)
  let bp (x : ℝ) := Complex.ClosedUnitDisc.bdyPtOfReal (x/N)
  let q : Complex.ClosedUnitDisc → Quot (OrientableRel p n) := Quot.mk _
  let B : Set (Quot (OrientableRel p n)) := Set.range (fun z : Fin n × unitInterval =>
    q (bp (-(3*(z.1.val:ℝ)+1+(z.2:ℝ)))))
  have hcircles : Nonempty (B ≃ₜ (Fin n × Circle)) ∧ IsClosed B := by
    classical
    let N : ℝ := 4*(p : ℝ)+3*(n : ℝ)
    have hN : 0 < N := by
      dsimp [N]
      rcases hadmissible with hp | hn
      · have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
        positivity
      · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
        positivity
    let bp (x : ℝ) := Complex.ClosedUnitDisc.bdyPtOfReal (x/N)
    have hperiod (x y : ℝ) (he : bp x = bp y) :
        ∃ k : ℤ, x=y+(k : ℝ)*N := by
      have hc : Real.fourierChar (x/N) = Real.fourierChar (y/N) := by
        apply Subtype.ext
        exact congrArg (fun z : Complex.ClosedUnitDisc => z.val) he
      rw [Real.fourierChar_apply',Real.fourierChar_apply'] at hc
      obtain ⟨k,hk⟩ := Circle.exp_eq_exp.mp hc
      have hpi : 2*Real.pi ≠ 0 := by positivity
      have hfrac : x/N=y/N+(k : ℝ) := by
        apply mul_left_cancel₀ hpi
        nlinarith [hk]
      have hm := congrArg (fun r : ℝ => r*N) hfrac
      rw [add_mul,div_mul_cancel₀ _ hN.ne',div_mul_cancel₀ _ hN.ne'] at hm
      exact ⟨k,hm⟩
    have hnormalize (x y : ℝ) (hx0 : -3*(n : ℝ)<x) (hx1 : x<4*(p : ℝ))
        (hy0 : -3*(n : ℝ)≤y) (hy1 : y≤4*(p : ℝ)) (he : bp x=bp y) : x=y := by
      obtain ⟨k,hk⟩ := hperiod x y he
      have hlo : -N<x-y := by dsimp [N]; linarith
      have hhi : x-y<N := by dsimp [N]; linarith
      have hk0 : (-1 : ℝ)<(k : ℝ) := by nlinarith
      have hk1 : (k : ℝ)<1 := by nlinarith
      have ki0 : (-1 : ℤ)<k := by exact_mod_cast hk0
      have ki1 : k<(1 : ℤ) := by exact_mod_cast hk1
      have he0 : k=0 := by omega
      simpa [he0] using hk
    let hp (j : Fin n) (t : unitInterval) : Complex.ClosedUnitDisc :=
      bp (-(3*(j.val : ℝ)+1+(t : ℝ)))
    have hpbounds (j : Fin n) (t : unitInterval) :
        -3*(n : ℝ)< -(3*(j.val : ℝ)+1+(t : ℝ)) ∧
        -(3*(j.val : ℝ)+1+(t : ℝ)) < 4*(p : ℝ) := by
      have hj : (j.val : ℝ)+1 ≤ n := by exact_mod_cast j.isLt
      constructor <;> linarith [t.property.1,t.property.2, Nat.cast_nonneg (α := ℝ) j.val,
        Nat.cast_nonneg (α := ℝ) p]
    have hpairedBounds (i : Fin p) (t : unitInterval) (r : ℝ)
        (hr : 0 ≤ r ∧ r ≤ 4) :
        -3*(n : ℝ) ≤ 4*(i.val : ℝ)+r ∧ 4*(i.val : ℝ)+r ≤ 4*(p : ℝ) := by
      have hi : (i.val : ℝ)+1 ≤ p := by exact_mod_cast i.isLt
      constructor <;> linarith [hr.1,hr.2,Nat.cast_nonneg (α := ℝ) i.val,Nat.cast_nonneg (α := ℝ) n]
    have hcBounds (i : Fin n) (t : unitInterval) :
        (-3*(n : ℝ) ≤ -(3*(i.val : ℝ)+(t : ℝ)) ∧
          -(3*(i.val : ℝ)+(t : ℝ)) ≤ 4*(p : ℝ)) ∧
        (-3*(n : ℝ) ≤ -(3*(i.val : ℝ)+3-(t : ℝ)) ∧
          -(3*(i.val : ℝ)+3-(t : ℝ)) ≤ 4*(p : ℝ)) := by
      have hi : (i.val : ℝ)+1 ≤ n := by exact_mod_cast i.isLt
      constructor <;> constructor <;>
        linarith [t.property.1,t.property.2,Nat.cast_nonneg (α := ℝ) i.val,Nat.cast_nonneg (α := ℝ) p]
    have hindex_eq (j k : Fin n) (x y : ℝ)
        (hx : 0≤x ∧ x≤2) (hy : 0≤y ∧ y≤2)
        (he : 3*(j.val : ℝ)+x = 3*(k.val : ℝ)+y) : j=k := by
      have hlo : (-1 : ℝ)<(j.val : ℝ)-(k.val : ℝ) := by linarith
      have hhi : (j.val : ℝ)-(k.val : ℝ)<1 := by linarith
      have hlo' : (-1 : ℤ)<(j.val : ℤ)-(k.val : ℤ) := by exact_mod_cast hlo
      have hhi' : (j.val : ℤ)-(k.val : ℤ)<1 := by exact_mod_cast hhi
      have hv : j.val=k.val := by omega
      exact Fin.ext hv
    have hp_inj (j k : Fin n) (t u : unitInterval) (he : hp j t=hp k u) :
        j=k ∧ t=u := by
      have hj := hpbounds j t
      have hk := hpbounds k u
      have heq := hnormalize _ _ hj.1 hj.2 hk.1.le hk.2.le he
      have hidx : j=k := hindex_eq j k (1+(t : ℝ)) (1+(u : ℝ))
        ⟨by linarith [t.property.1],by linarith [t.property.2]⟩
        ⟨by linarith [u.property.1],by linarith [u.property.2]⟩ (by linarith)
      subst k
      refine ⟨rfl,Subtype.ext ?_⟩
      linarith
    have hp_not_handle (j : Fin n) (t : unitInterval) (i : Fin p) (r : ℝ)
        (hr : 0 ≤ r ∧ r ≤ 4) : hp j t ≠ bp (4*(i.val : ℝ)+r) := by
      intro he
      have hj := hpbounds j t
      have hi := hpairedBounds i t r hr
      have heq := hnormalize _ _ hj.1 hj.2 hi.1 hi.2 he
      linarith [t.property.1,Nat.cast_nonneg (α := ℝ) j.val,Nat.cast_nonneg (α := ℝ) i.val,hr.1]
    have hp_c_left (j i : Fin n) (t x : unitInterval)
        (he : hp j t=bp (-(3*(i.val : ℝ)+(x : ℝ)))) :
        j=i ∧ (t : ℝ)=0 ∧ (x : ℝ)=1 := by
      have hj := hpbounds j t
      have hi := (hcBounds i x).1
      have heq := hnormalize _ _ hj.1 hj.2 hi.1 hi.2 he
      have hidx : j=i := hindex_eq j i (1+(t : ℝ)) x
        ⟨by linarith [t.property.1],by linarith [t.property.2]⟩
        ⟨x.property.1,by linarith [x.property.2]⟩ (by linarith)
      subst i
      refine ⟨rfl,?_,?_⟩ <;> linarith [t.property.1,x.property.2]
    have hp_c_right (j i : Fin n) (t x : unitInterval)
        (he : hp j t=bp (-(3*(i.val : ℝ)+3-(x : ℝ)))) :
        j=i ∧ (t : ℝ)=1 ∧ (x : ℝ)=1 := by
      have hj := hpbounds j t
      have hi := (hcBounds i x).2
      have heq := hnormalize _ _ hj.1 hj.2 hi.1 hi.2 he
      -- Reverse the seam-side offset so both slot offsets lie in [0,2].
      have hidx : j=i := by
        have hlo : (-1 : ℝ)<(j.val : ℝ)-(i.val : ℝ) := by
          linarith [t.property.2,x.property.2]
        have hhi : (j.val : ℝ)-(i.val : ℝ)<1 := by
          linarith [t.property.1,x.property.1]
        have hlo' : (-1 : ℤ)<(j.val : ℤ)-(i.val : ℤ) := by exact_mod_cast hlo
        have hhi' : (j.val : ℤ)-(i.val : ℤ)<1 := by exact_mod_cast hhi
        apply Fin.ext
        omega
      subst i
      refine ⟨rfl,?_,?_⟩ <;> linarith [t.property.2,x.property.2]
    have hrel_src (j : Fin n) (t : unitInterval) {z w : Complex.ClosedUnitDisc}
        (hr : OrientableRel p n z w) (hz : z=hp j t) :
        (t : ℝ)=0 ∧ w=hp j 1 := by
      cases hr with
      | a x i =>
        have he : hp j t=bp (4*(i.val : ℝ)+(x : ℝ)) := hz.symm
        exact False.elim (hp_not_handle j t i x ⟨x.property.1,by linarith [x.property.2]⟩ he)
      | b x i =>
        have he : hp j t=bp (4*(i.val : ℝ)+(1+(x : ℝ))) := by
          convert hz.symm using 1 <;> congr 1 <;> ring
        exact False.elim (hp_not_handle j t i (1+(x : ℝ))
          ⟨by linarith [x.property.1],by linarith [x.property.2]⟩ he)
      | c x i =>
        have he : hp j t=bp (-(3*(i.val : ℝ)+(x : ℝ))) := hz.symm
        obtain ⟨hji,ht,hx⟩ := hp_c_left j i t x he
        subst i
        refine ⟨ht,?_⟩
        change bp (-(3*(j.val : ℝ)+3-(x : ℝ))) = bp (-(3*(j.val : ℝ)+1+(1 : unitInterval)))
        apply congrArg bp
        change -(3*(j.val : ℝ)+3-(x : ℝ)) = -(3*(j.val : ℝ)+1+1)
        linarith
    have hrel_tgt (j : Fin n) (t : unitInterval) {z w : Complex.ClosedUnitDisc}
        (hr : OrientableRel p n z w) (hw : w=hp j t) :
        (t : ℝ)=1 ∧ z=hp j 0 := by
      cases hr with
      | a x i =>
        have he : hp j t=bp (4*(i.val : ℝ)+(3-(x : ℝ))) := by
          convert hw.symm using 1 <;> congr 1 <;> ring
        exact False.elim (hp_not_handle j t i (3-(x : ℝ))
          ⟨by linarith [x.property.2],by linarith [x.property.1]⟩ he)
      | b x i =>
        have he : hp j t=bp (4*(i.val : ℝ)+(4-(x : ℝ))) := by
          convert hw.symm using 1 <;> congr 1 <;> ring
        exact False.elim (hp_not_handle j t i (4-(x : ℝ))
          ⟨by linarith [x.property.2],by linarith [x.property.1]⟩ he)
      | c x i =>
        have he : hp j t=bp (-(3*(i.val : ℝ)+3-(x : ℝ))) := hw.symm
        obtain ⟨hji,ht,hx⟩ := hp_c_right j i t x he
        subst i
        refine ⟨ht,?_⟩
        change bp (-(3*(j.val : ℝ)+(x : ℝ))) = bp (-(3*(j.val : ℝ)+1+(0 : unitInterval)))
        apply congrArg bp
        change -(3*(j.val : ℝ)+(x : ℝ)) = -(3*(j.val : ℝ)+1+0)
        linarith
    have hsingle_rel (j : Fin n) (t : unitInterval) (ht0 : 0<(t : ℝ))
        (ht1 : (t : ℝ)<1) {z w : Complex.ClosedUnitDisc}
        (hr : OrientableRel p n z w) : z=hp j t ↔ w=hp j t := by
      constructor
      · intro hz
        have ht := (hrel_src j t hr hz).1
        linarith
      · intro hw
        have ht := (hrel_tgt j t hr hw).1
        linarith
    have hsingle_eqv (j : Fin n) (t : unitInterval) (ht0 : 0<(t : ℝ))
        (ht1 : (t : ℝ)<1) {z w : Complex.ClosedUnitDisc}
        (hr : Relation.EqvGen (OrientableRel p n) z w) : z=hp j t ↔ w=hp j t := by
      induction hr with
      | rel z w hr => exact hsingle_rel j t ht0 ht1 hr
      | refl z => rfl
      | symm z w hr ih => exact ih.symm
      | trans z w u hr1 hr2 ih1 ih2 => exact ih1.trans ih2
    let ends (j : Fin n) : Set Complex.ClosedUnitDisc := {z | z=hp j 0 ∨ z=hp j 1}
    have hends_rel (j : Fin n) {z w : Complex.ClosedUnitDisc}
        (hr : OrientableRel p n z w) : z ∈ ends j ↔ w ∈ ends j := by
      constructor
      · rintro (hz|hz)
        · exact Or.inr (hrel_src j 0 hr hz).2
        · have ht := (hrel_src j 1 hr hz).1
          norm_num at ht
      · rintro (hw|hw)
        · have ht := (hrel_tgt j 0 hr hw).1
          norm_num at ht
        · exact Or.inl (hrel_tgt j 1 hr hw).2
    have hends_eqv (j : Fin n) {z w : Complex.ClosedUnitDisc}
        (hr : Relation.EqvGen (OrientableRel p n) z w) : z ∈ ends j ↔ w ∈ ends j := by
      induction hr with
      | rel z w hr => exact hends_rel j hr
      | refl z => rfl
      | symm z w hr ih => exact ih.symm
      | trans z w u hr1 hr2 ih1 ih2 => exact ih1.trans ih2
    have hquot_interior (j : Fin n) (t : unitInterval) (ht0 : 0<(t : ℝ))
        (ht1 : (t : ℝ)<1) (w : Complex.ClosedUnitDisc)
        (he : Quot.mk (OrientableRel p n) (hp j t)=Quot.mk (OrientableRel p n) w) :
        w=hp j t := (hsingle_eqv j t ht0 ht1 (Quot.eqvGen_exact he)).mp rfl
    have hquot_ends (j : Fin n) (t : unitInterval)
        (ht : (t : ℝ)=0 ∨ (t : ℝ)=1) (w : Complex.ClosedUnitDisc)
        (he : Quot.mk (OrientableRel p n) (hp j t)=Quot.mk (OrientableRel p n) w) :
        w ∈ ends j := by
      have hz : hp j t ∈ ends j := by
        rcases ht with ht|ht
        · have ht' : t=0 := Subtype.ext (by simpa using ht)
          rw [ht']; exact Or.inl rfl
        · have ht' : t=1 := Subtype.ext (by simpa using ht)
          rw [ht']; exact Or.inr rfl
      exact (hends_eqv j (Quot.eqvGen_exact he)).mp hz
    let h (j : Fin n) (t : CurveComplex.Interval) : Quot (OrientableRel p n) :=
      Quot.mk _ (Complex.ClosedUnitDisc.bdyPtOfReal
        (-(3*(j.val : ℝ)+1+(t : ℝ))/(4*(p : ℝ)+3*(n : ℝ))))
    have hcont (j : Fin n) : Continuous (h j) := by
      have hd : Continuous (fun t : CurveComplex.Interval =>
          Complex.ClosedUnitDisc.bdyPtOfReal
            (-(3*(j.val : ℝ)+1+(t : ℝ))/(4*(p : ℝ)+3*(n : ℝ)))) := by
        apply Continuous.subtype_mk
        change Continuous (fun t : CurveComplex.Interval =>
          (Real.fourierChar (-(3*(j.val : ℝ)+1+(t : ℝ))/(4*(p : ℝ)+3*(n : ℝ))) : ℂ))
        have ht : Continuous (fun t : CurveComplex.Interval =>
          -(3*(j.val : ℝ)+1+(t : ℝ))/(4*(p : ℝ)+3*(n : ℝ))) := by fun_prop
        exact continuous_subtype_val.comp (Real.continuous_fourierChar.comp ht)
      exact continuous_quot_mk.comp hd
    have hend (j : Fin n) : h j 0 = h j 1 := by
      have hc := Quot.sound (OrientableRel.c (p := p) (n := n)
        (⟨1,by norm_num⟩ : CurveComplex.Interval) j)
      dsimp only [h]
      convert hc using 1 <;> congr 2 <;> norm_num <;> ring
    let B : Set (Quot (OrientableRel p n)) :=
      Set.range (fun z : Fin n × CurveComplex.Interval => h z.1 z.2)
    have hn1 (hn : n=1) : B = hn.symm ▸ ActualOneBoundaryOrientableBoundary p := by
      subst n
      ext x
      constructor
      · rintro ⟨⟨j,t⟩,hx⟩
        have hj : j=0 := Subsingleton.elim _ _
        subst j
        refine ⟨t,?_⟩
        simpa [h] using hx
      · rintro ⟨t,hx⟩
        refine ⟨(0,t),?_⟩
        simpa [h] using hx
    have hn0 (hn : n=0) : B = ∅ := by
      subst n
      ext x
      simp only [B,Set.mem_range,Set.mem_empty_iff_false,iff_false]
      rintro ⟨⟨j,t⟩,_⟩
      exact Fin.elim0 j
    let hI (j : Fin n) (t : Icc (0 : ℝ) (0+1)) : Quot (OrientableRel p n) :=
      h j ⟨t,by simpa only [zero_add] using t.property⟩
    have hIc (j : Fin n) : Continuous (hI j) :=
      (hcont j).comp (continuous_subtype_val.subtype_mk _)
    have hIe (j : Fin n) : hI j ⟨0,by norm_num⟩ = hI j ⟨1,by norm_num⟩ :=
      hend j
    let hQ (j : Fin n) : Quot (AddCircle.EndpointIdent (1 : ℝ) 0) → Quot (OrientableRel p n) :=
      Quot.lift (hI j) (by
        rintro _ _ ⟨_⟩
        simpa only [zero_add] using hIe j)
    have hQc (j : Fin n) : Continuous (hQ j) := continuous_quot_lift _ (hIc j)
    let ec : Circle ≃ₜ Quot (AddCircle.EndpointIdent (1 : ℝ) 0) :=
      (AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0)).symm.trans
        (AddCircle.homeoIccQuot (1 : ℝ) 0)
    let loop (j : Fin n) : Circle → Quot (OrientableRel p n) := hQ j ∘ ec
    have hlc (j : Fin n) : Continuous (loop j) := (hQc j).comp ec.continuous
    let ti (t : Icc (0 : ℝ) (0+1)) : unitInterval :=
      ⟨t,by simpa only [zero_add] using t.property⟩
    have heqEnd : Quot.mk (AddCircle.EndpointIdent (1 : ℝ) 0) ⟨0,by norm_num⟩ =
        Quot.mk (AddCircle.EndpointIdent (1 : ℝ) 0) ⟨1,by norm_num⟩ := by
      simpa only [zero_add] using Quot.sound
        (AddCircle.EndpointIdent.mk (p := (1 : ℝ)) (a := 0))
    have hfullfiber (j : Fin n) (t : Icc (0 : ℝ) (0+1)) (w : Complex.ClosedUnitDisc)
        (he : Quot.mk (OrientableRel p n) (hp j (ti t))=Quot.mk (OrientableRel p n) w) :
        ∃ u : Icc (0 : ℝ) (0+1),
          Quot.mk (AddCircle.EndpointIdent (1 : ℝ) 0) u =
            Quot.mk (AddCircle.EndpointIdent (1 : ℝ) 0) t ∧ hp j (ti u)=w := by
      by_cases ht0 : (t : ℝ)=0
      · have ht' : t=⟨0,by norm_num⟩ := Subtype.ext ht0
        obtain hw|hw := hquot_ends j (ti t) (Or.inl ht0) w he
        · refine ⟨⟨0,by norm_num⟩,?_,hw.symm⟩
          rw [ht']
        · refine ⟨⟨1,by norm_num⟩,?_,hw.symm⟩
          rw [ht']
          exact heqEnd.symm
      · by_cases ht1 : (t : ℝ)=1
        · have ht' : t=⟨1,by norm_num⟩ := Subtype.ext ht1
          obtain hw|hw := hquot_ends j (ti t) (Or.inr ht1) w he
          · refine ⟨⟨0,by norm_num⟩,?_,hw.symm⟩
            rw [ht']
            exact heqEnd
          · refine ⟨⟨1,by norm_num⟩,?_,hw.symm⟩
            rw [ht']
        · have hlo : 0<(ti t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht0)
          have hhi : (ti t : ℝ)<1 := lt_of_le_of_ne
            (by simpa only [zero_add] using t.property.2) ht1
          exact ⟨t,rfl,(hquot_interior j (ti t) hlo hhi w he).symm⟩
    have hloop_inj (j k : Fin n) (c d' : Circle) (he : loop j c=loop k d') :
        j=k ∧ c=d' := by
      obtain ⟨t,ht⟩ := Quot.exists_rep (ec c)
      obtain ⟨u,hu⟩ := Quot.exists_rep (ec d')
      change hQ j (ec c)=hQ k (ec d') at he
      rw [← ht,← hu] at he
      obtain ⟨v,hv,hpv⟩ := hfullfiber j t (hp k (ti u)) he
      obtain ⟨hjk,hvu⟩ := hp_inj j k (ti v) (ti u) hpv
      have hvu' : v=u := Subtype.ext (congrArg (fun x : unitInterval => (x : ℝ)) hvu)
      refine ⟨hjk,ec.injective ?_⟩
      rw [← ht,← hu,← hvu']
      exact hv.symm
    have hlrange (j : Fin n) : Set.range (loop j) = Set.range (h j) := by
      ext x
      constructor
      · rintro ⟨c,hc⟩
        obtain ⟨t,ht⟩ := Quot.exists_rep (ec c)
        change hQ j (ec c) = x at hc
        rw [← ht] at hc
        exact ⟨⟨t,by simpa only [zero_add] using t.property⟩,hc⟩
      · rintro ⟨t,ht⟩
        let t' : Icc (0 : ℝ) (0+1) := ⟨t,by simpa only [zero_add] using t.property⟩
        refine ⟨ec.symm (Quot.mk _ t'),?_⟩
        change hQ j (ec (ec.symm (Quot.mk _ t'))) = x
        rw [Homeomorph.apply_symm_apply]
        exact ht
    have hlunion : Set.range (fun z : Fin n × Circle => loop z.1 z.2) = B := by
      ext x
      constructor
      · rintro ⟨⟨j,c⟩,hc⟩
        have hm : x ∈ Set.range (h j) := by rw [← hlrange j]; exact ⟨c,hc⟩
        obtain ⟨t,ht⟩ := hm
        exact ⟨(j,t),ht⟩
      · rintro ⟨⟨j,t⟩,ht⟩
        have hm : x ∈ Set.range (loop j) := by rw [hlrange j]; exact ⟨t,ht⟩
        obtain ⟨c,hc⟩ := hm
        exact ⟨(j,c),hc⟩
    letI : TopologicalSpace (Fin n) := ⊥
    letI : DiscreteTopology (Fin n) := ⟨rfl⟩
    let A := Fin n × Icc (0 : ℝ) (0+1)
    let U := Fin n × Circle
    let rawA : A → Complex.ClosedUnitDisc := fun a => hp a.1 (ti a.2)
    let tau : A → U := fun a => (a.1,ec.symm (Quot.mk _ a.2))
    let L : U → Quot (OrientableRel p n) := fun c => loop c.1 c.2
    have hLc : Continuous L := continuous_prod_of_discrete_left.mpr hlc
    have hLi : Function.Injective L := by
      rintro ⟨j,c⟩ ⟨k,d'⟩ he
      obtain ⟨hjk,hcd⟩ := hloop_inj j k c d' he
      exact Prod.ext hjk hcd
    have htauc : Continuous tau := by
      dsimp [tau]
      exact continuous_fst.prodMk
        (ec.symm.continuous.comp (continuous_quot_mk.comp continuous_snd))
    have htaus : Function.Surjective tau := by
      rintro ⟨j,c⟩
      obtain ⟨t,ht⟩ := Quot.exists_rep (ec c)
      refine ⟨(j,t),Prod.ext rfl ?_⟩
      change ec.symm (Quot.mk _ t)=c
      rw [ht,Homeomorph.symm_apply_apply]
    have hrawAc : Continuous rawA := by
      apply continuous_prod_of_discrete_left.mpr
      intro j
      apply Continuous.subtype_mk
      change Continuous (fun t : Icc (0 : ℝ) (0+1) =>
        (Real.fourierChar (-(3*(j.val : ℝ)+1+(t : ℝ))/N) : ℂ))
      have ht : Continuous (fun t : Icc (0 : ℝ) (0+1) =>
        -(3*(j.val : ℝ)+1+(t : ℝ))/N) := by fun_prop
      exact continuous_subtype_val.comp (Real.continuous_fourierChar.comp ht)
    have hLtau (a : A) : L (tau a)=Quot.mk (OrientableRel p n) (rawA a) := by
      change hQ a.1 (ec (ec.symm (Quot.mk _ a.2)))= _
      rw [Homeomorph.apply_symm_apply]
    have hsaturation (C : Set U) :
        (Quot.mk (OrientableRel p n)) ⁻¹' (L '' C) = rawA '' (tau ⁻¹' C) := by
      ext w
      constructor
      · rintro ⟨c,hc,he⟩
        obtain ⟨a,ha⟩ := htaus c
        have hqa : Quot.mk (OrientableRel p n) (rawA a)=Quot.mk (OrientableRel p n) w := by
          rw [← hLtau a,ha]
          exact he
        obtain ⟨u,hu,hpu⟩ := hfullfiber a.1 a.2 w hqa
        let b : A := (a.1,u)
        have htb : tau b=tau a := by
          apply Prod.ext
          · rfl
          · exact congrArg ec.symm hu
        refine ⟨b,?_,hpu⟩
        change tau b ∈ C
        rw [htb,ha]
        exact hc
      · rintro ⟨a,ha,rfl⟩
        exact ⟨tau a,ha,hLtau a⟩
    have hLclosed : IsClosedMap L := by
      intro C hC
      apply isQuotientMap_quot_mk.isCoinducing.isClosed_preimage.mp
      rw [hsaturation C]
      exact ((hC.preimage htauc).isCompact.image hrawAc).isClosed
    let LB : U → B := B.codRestrict L (fun c => by
      rw [← hlunion]
      exact ⟨c,rfl⟩)
    have hLBc : Continuous LB := hLc.codRestrict _
    have hLBclosed : IsClosedMap LB := hLclosed.codRestrict _
    have hLBbij : Function.Bijective LB := by
      constructor
      · intro c d' he
        exact hLi (congrArg Subtype.val he)
      · rintro ⟨x,hx⟩
        rw [← hlunion] at hx
        obtain ⟨c,hc⟩ := hx
        exact ⟨c,Subtype.ext hc⟩
    have hcirclesProved : Nonempty (B ≃ₜ (Fin n × Circle)) :=
      ⟨((Equiv.ofBijective LB hLBbij).toHomeomorphOfContinuousClosed hLBc hLBclosed).symm⟩
    have hLembedding : Topology.IsEmbedding L := (Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap hLc hLi hLclosed).isEmbedding
    have hloopDisjoint : Pairwise (fun j k : Fin n =>
        Disjoint (Set.range (loop j)) (Set.range (loop k))) := by
      intro j k hjk
      apply Set.disjoint_left.mpr
      rintro x ⟨c,hc⟩ ⟨d',hd⟩
      exact hjk (hloop_inj j k c d' (hc.trans hd.symm)).1
    refine ⟨hcirclesProved,?_⟩
    have hc := hLclosed Set.univ isClosed_univ
    have hr : Set.range L = B := hlunion
    simpa only [Set.image_univ,hr] using hc
  have hincl : B ⊆ I.boundary (Quot (OrientableRel p n)) := by
    classical
    have hstrict (j : Fin n) (t : unitInterval) (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1) :
      (modelWithCornersEuclideanHalfSpace 2).IsBoundaryPoint
        (Quot.mk (OrientableRel p n) (Complex.ClosedUnitDisc.bdyPtOfReal
          (-(3*(j.val : ℝ)+1+(t : ℝ))/(4*(p : ℝ)+3*(n : ℝ))))) := by
      classical
      have hquot :
        let A : Set Complex.ClosedUnitDisc :=
          {z | ∃ w, OrientableRel p n z w ∨ OrientableRel p n w z}
        let q : Complex.ClosedUnitDisc → Quot (OrientableRel p n) := Quot.mk _
        IsClosed A ∧ IsOpen (q '' Aᶜ) ∧ (∃ e : {z // z ∉ A} ≃ₜ (q '' Aᶜ), ∀ z, (e z).val = q z.val) := by
        classical
        let A : Set Complex.ClosedUnitDisc :=
          {z | ∃ w, OrientableRel p n z w ∨ OrientableRel p n w z}
        let J := (Fin p × Fin 2) ⊕ Fin n
        letI : TopologicalSpace J := ⊥
        letI : DiscreteTopology J := ⟨rfl⟩
        let N : ℝ := 4*(p : ℝ)+3*(n : ℝ)
        let src (j : J) (t : unitInterval) : Complex.ClosedUnitDisc :=
          match j with
          | Sum.inl (i,k) => Complex.ClosedUnitDisc.bdyPtOfReal
              ((4*(i.val : ℝ)+(if k.val=0 then 0 else 1)+(t : ℝ))/N)
          | Sum.inr i => Complex.ClosedUnitDisc.bdyPtOfReal (-(3*(i.val : ℝ)+(t : ℝ))/N)
        let tgt (j : J) (t : unitInterval) : Complex.ClosedUnitDisc :=
          match j with
          | Sum.inl (i,k) => Complex.ClosedUnitDisc.bdyPtOfReal
              ((4*(i.val : ℝ)+(if k.val=0 then 3 else 4)-(t : ℝ))/N)
          | Sum.inr i => Complex.ClosedUnitDisc.bdyPtOfReal (-(3*(i.val : ℝ)+3-(t : ℝ))/N)
        have hb : Continuous Complex.ClosedUnitDisc.bdyPtOfReal :=
          (continuous_subtype_val.comp Real.continuous_fourierChar).subtype_mk _
        have hsc (j : J) : Continuous (src j) := by
          rcases j with ⟨i,k⟩ | i
          · dsimp [src]; exact hb.comp (by fun_prop)
          · dsimp [src]; exact hb.comp (by fun_prop)
        have htc (j : J) : Continuous (tgt j) := by
          rcases j with ⟨i,k⟩ | i
          · dsimp [tgt]; exact hb.comp (by fun_prop)
          · dsimp [tgt]; exact hb.comp (by fun_prop)
        have hscomp : IsCompact (Set.range (fun a : J × unitInterval => src a.1 a.2)) :=
          isCompact_range (continuous_prod_of_discrete_left.mpr hsc)
        have htcomp : IsCompact (Set.range (fun a : J × unitInterval => tgt a.1 a.2)) :=
          isCompact_range (continuous_prod_of_discrete_left.mpr htc)
        have hr (j : J) (t : unitInterval) : OrientableRel p n (src j t) (tgt j t) := by
          rcases j with ⟨i,k⟩ | i
          · fin_cases k
            · simpa [src,tgt,N] using OrientableRel.a t i
            · simpa [src,tgt,N] using OrientableRel.b t i
          · simpa [src,tgt,N] using OrientableRel.c t i
        have ha : A = Set.range (fun a : J × unitInterval => src a.1 a.2) ∪
            Set.range (fun a : J × unitInterval => tgt a.1 a.2) := by
          ext z
          constructor
          · rintro ⟨w,hr | hr⟩
            · cases hr with
              | a t i => exact Or.inl ⟨(Sum.inl (i,0),t),by simp [src,N]⟩
              | b t i => exact Or.inl ⟨(Sum.inl (i,1),t),by simp [src,N]⟩
              | c t i => exact Or.inl ⟨(Sum.inr i,t),by simp [src,N]⟩
            · cases hr with
              | a t i => exact Or.inr ⟨(Sum.inl (i,0),t),by simp [tgt,N]⟩
              | b t i => exact Or.inr ⟨(Sum.inl (i,1),t),by simp [tgt,N]⟩
              | c t i => exact Or.inr ⟨(Sum.inr i,t),by simp [tgt,N]⟩
          · rintro (⟨⟨j,t⟩,rfl⟩ | ⟨⟨j,t⟩,rfl⟩)
            · exact ⟨tgt j t,Or.inl (hr j t)⟩
            · exact ⟨src j t,Or.inr (hr j t)⟩
        have hclosed : IsClosed A := by rw [ha]; exact (hscomp.union htcomp).isClosed
        have hgen {z w : Complex.ClosedUnitDisc} (h : Relation.EqvGen (OrientableRel p n) z w) :
            z=w ∨ (z ∈ A ∧ w ∈ A) := by
          induction h with
          | rel z w h => exact Or.inr ⟨⟨w,Or.inl h⟩,⟨z,Or.inr h⟩⟩
          | refl z => exact Or.inl rfl
          | symm z w h ih => exact ih.elim (fun h => Or.inl h.symm) (fun h => Or.inr ⟨h.2,h.1⟩)
          | trans z w v h₁ h₂ ih₁ ih₂ =>
            rcases ih₁ with h | h
            · subst w; exact ih₂
            · rcases ih₂ with h' | h'
              · subst v; exact Or.inr h
              · exact Or.inr ⟨h.1,h'.2⟩
        let U : Set Complex.ClosedUnitDisc := Aᶜ
        let q : Complex.ClosedUnitDisc → Quot (OrientableRel p n) := Quot.mk _
        have hfiberq {z w : Complex.ClosedUnitDisc} (hz : z ∈ U) (he : q z = q w) : w=z := by
          rcases hgen (Quot.eqvGen_exact he) with h | h
          · exact h.symm
          · exact False.elim (hz h.1)
        have hU : IsOpen U := hclosed.isOpen_compl
        have hsat (V : Set Complex.ClosedUnitDisc) (hV : V ⊆ U) : q ⁻¹' (q '' V) = V := by
          ext w
          constructor
          · rintro ⟨z,hz,he⟩
            have hw := hfiberq (hV hz) he
            simpa [hw] using hz
          · intro hw
            exact ⟨w,hw,rfl⟩
        have hopen (V : Set Complex.ClosedUnitDisc) (hV : V ⊆ U) (ho : IsOpen V) : IsOpen (q '' V) := by
          apply isQuotientMap_quot_mk.isCoinducing.isOpen_preimage.mp
          rw [hsat V hV]
          exact ho
        have hqU : IsOpen (q '' U) := hopen U subset_rfl hU
        let f : U → q '' U := fun z => ⟨q z,⟨z,z.property,rfl⟩⟩
        have hfc : Continuous f := (continuous_quot_mk.comp continuous_subtype_val).subtype_mk _
        have hfi : Function.Injective f := by
          intro z w he
          apply Subtype.ext
          exact (hfiberq z.property (congrArg Subtype.val he)).symm
        have hfs : Function.Surjective f := by
          rintro ⟨y,⟨z,hz,rfl⟩⟩
          exact ⟨⟨z,hz⟩,rfl⟩
        have hfo : IsOpenMap f := by
          intro V hV
          have ho : IsOpen ((Subtype.val : U → Complex.ClosedUnitDisc) '' V) :=
            hU.isOpenEmbedding_subtypeVal.isOpenMap V hV
          have hs : (Subtype.val : U → Complex.ClosedUnitDisc) '' V ⊆ U := by
            rintro _ ⟨z,_,rfl⟩; exact z.property
          have he : f '' V = (Subtype.val : q '' U → Quot (OrientableRel p n)) ⁻¹'
              (q '' ((Subtype.val : U → Complex.ClosedUnitDisc) '' V)) := by
            ext y
            constructor
            · rintro ⟨z,hz,rfl⟩
              exact ⟨z,⟨z,hz,rfl⟩,rfl⟩
            · rintro ⟨z,⟨u,hu,rfl⟩,he⟩
              exact ⟨u,hu,Subtype.ext he⟩
          rw [he]
          exact (hopen _ hs ho).preimage continuous_subtype_val
        exact ⟨hclosed,hqU,⟨(Equiv.ofBijective f ⟨hfi,hfs⟩).toHomeomorphOfContinuousOpen hfc hfo, fun _ => rfl⟩⟩
      have hcharts (c : Circle) :
        ∃ e : OpenPartialHomeomorph Complex.ClosedUnitDisc (EuclideanHalfSpace 2),
          (⟨(c : ℂ),by simpa [Metric.mem_closedBall,dist_zero_right] using (Circle.norm_coe c).le⟩ : Complex.ClosedUnitDisc) ∈ e.source ∧
          ∀ z : Complex.ClosedUnitDisc, z ∈ e.source → (e z).val 0 = 1 - ‖z.val‖^2 := by
        classical
        have hchart :
          ∃ e : OpenPartialHomeomorph Complex.ClosedUnitDisc (EuclideanHalfSpace 2),
            e.source = {z | 0 < z.val.re} ∧ ∀ z : Complex.ClosedUnitDisc, 0 < z.val.re →
              (e z).val 0 = 1 - ‖z.val‖^2 := by
          classical
          let U : Set Complex.ClosedUnitDisc := {z | 0 < z.val.re}
          let V : Set (EuclideanHalfSpace 2) := {h | h.val 0 + (h.val 1)^2 < 1}
          have hbound (z : Complex.ClosedUnitDisc) : z.val.re^2+z.val.im^2 ≤ 1 := by
            have hn : ‖z.val‖ ≤ 1 := by
              have hz := z.property
              change dist (z : ℂ) 0 ≤ 1 at hz
              rwa [dist_zero_right] at hz
            have hs := Complex.normSq_eq_norm_sq z.val
            simp only [Complex.normSq_apply] at hs
            nlinarith [norm_nonneg z.val]
          let f (z : U) : V := ⟨⟨WithLp.toLp 2
              (fun i : Fin 2 => if i=0 then 1-z.val.val.re^2-z.val.val.im^2 else z.val.val.im), by
                change 0 ≤ 1-z.val.val.re^2-z.val.val.im^2
                linarith [hbound z.val]⟩,by
              change 1-z.val.val.re^2-z.val.val.im^2+z.val.val.im^2 < 1
              nlinarith [show 0 < z.val.val.re from z.property]⟩
          let g (h : V) : U := ⟨⟨⟨Real.sqrt (1-(h.val.val 1)^2-h.val.val 0),h.val.val 1⟩,by
              have hpos : 0 < 1-(h.val.val 1)^2-h.val.val 0 := by linarith [show h.val.val 0 + (h.val.val 1)^2 < 1 from h.property]
              have hs := Real.sq_sqrt hpos.le
              have hn : 0 ≤ h.val.val 0 := h.val.property
              rw [Metric.mem_closedBall,dist_zero_right]
              have he := Complex.normSq_eq_norm_sq
                (⟨Real.sqrt (1-(h.val.val 1)^2-h.val.val 0),h.val.val 1⟩ : ℂ)
              simp only [Complex.normSq_apply] at he
              nlinarith [norm_nonneg (⟨Real.sqrt (1-(h.val.val 1)^2-h.val.val 0),h.val.val 1⟩ : ℂ)]⟩,by
              change 0 < Real.sqrt (1-(h.val.val 1)^2-h.val.val 0)
              exact Real.sqrt_pos.2 (by linarith [show h.val.val 0 + (h.val.val 1)^2 < 1 from h.property])⟩
          have hgf (z : U) : g (f z) = z := by
            apply Subtype.ext
            apply Subtype.ext
            apply Complex.ext
            · change Real.sqrt (1-z.val.val.im^2-(1-z.val.val.re^2-z.val.val.im^2)) = z.val.val.re
              rw [show 1-z.val.val.im^2-(1-z.val.val.re^2-z.val.val.im^2)=z.val.val.re^2 by ring]
              exact Real.sqrt_sq z.property.le
            · rfl
          have hfg (h : V) : f (g h) = h := by
            apply Subtype.ext
            apply Subtype.ext
            apply PiLp.ext
            intro i
            fin_cases i
            · change 1-(Real.sqrt (1-(h.val.val 1)^2-h.val.val 0))^2-(h.val.val 1)^2=h.val.val 0
              rw [Real.sq_sqrt (by linarith [show h.val.val 0 + (h.val.val 1)^2 < 1 from h.property])]
              ring
            · rfl
          have hfc : Continuous f := by
            apply Continuous.subtype_mk
            apply Continuous.subtype_mk
            apply (PiLp.continuous_toLp 2 _).comp
            apply continuous_pi
            intro i
            fin_cases i <;> simp only [Fin.isValue,Fin.zero_eta,↓reduceIte,Fin.mk_one,one_ne_zero] <;> fun_prop
          have hgc : Continuous g := by
            apply Continuous.subtype_mk
            apply Continuous.subtype_mk
            have hc : Continuous (fun h : V =>
              (Real.sqrt (1-(h.val.val 1)^2-h.val.val 0) : ℂ) + (h.val.val 1 : ℂ)*Complex.I) := by fun_prop
            convert hc using 1
            funext h
            apply Complex.ext <;> simp
          have hU : IsOpen U := isOpen_lt continuous_const (Complex.continuous_re.comp continuous_subtype_val)
          have hV : IsOpen V := by
            apply isOpen_lt _ continuous_const
            fun_prop
          let eh : U ≃ₜ V := { toEquiv := ⟨f,g,hgf,hfg⟩, continuous_toFun := hfc, continuous_invFun := hgc }
          letI : Nonempty U := ⟨⟨⟨1,by simp [Metric.mem_closedBall]⟩,by norm_num [U]⟩⟩
          letI : Nonempty V := ⟨eh (Classical.choice (inferInstance : Nonempty U))⟩
          let iu := hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph
            (Subtype.val : U → Complex.ClosedUnitDisc)
          let iv := hV.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph
            (Subtype.val : V → EuclideanHalfSpace 2)
          let e := (iu.symm.transHomeomorph eh).trans iv
          have heu : e.source = U := by
            simp [e,OpenPartialHomeomorph.trans_source,OpenPartialHomeomorph.transHomeomorph,
              iu,iv,Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
          refine ⟨e,heu,?_⟩
          intro z hz
          have hi : iu.symm z = (⟨z,hz⟩ : U) := by
            have hinv := iu.left_inv (show (⟨z,hz⟩ : U) ∈ iu.source by trivial)
            exact hinv
          change (iv (eh (iu.symm z))).val 0 = 1-‖z.val‖^2
          rw [hi]
          change 1-z.val.re^2-z.val.im^2 = 1-‖z.val‖^2
          have hs := Complex.normSq_eq_norm_sq z.val
          simp only [Complex.normSq_apply] at hs
          linarith
        obtain ⟨e,he,heval⟩ := hchart
        let rot : Complex.ClosedUnitDisc ≃ₜ Complex.ClosedUnitDisc := {
          toFun := fun z => ⟨(c⁻¹ : Circle)*(z : ℂ),by
            rw [Metric.mem_closedBall,dist_zero_right,norm_mul,Circle.norm_coe,one_mul]
            simpa only [Metric.mem_closedBall,dist_zero_right] using z.property⟩
          invFun := fun z => ⟨(c : ℂ)*(z : ℂ),by
            rw [Metric.mem_closedBall,dist_zero_right,norm_mul,Circle.norm_coe,one_mul]
            simpa only [Metric.mem_closedBall,dist_zero_right] using z.property⟩
          left_inv := by intro z; apply Subtype.ext; simp [← mul_assoc]
          right_inv := by intro z; apply Subtype.ext; simp [← mul_assoc]
          continuous_toFun := by apply Continuous.subtype_mk; fun_prop
          continuous_invFun := by apply Continuous.subtype_mk; fun_prop }
        let er := rot.toOpenPartialHomeomorph.trans e
        refine ⟨er,?_,?_⟩
        · change _ ∈ Set.univ ∩ rot ⁻¹' e.source
          refine ⟨Set.mem_univ _,?_⟩
          rw [he]
          change 0 < (((c⁻¹ : Circle) : ℂ)*(c : ℂ)).re
          simp
        · intro z hz
          have hz' : rot z ∈ e.source := hz.2
          have hre : 0 < (rot z).val.re := by simpa [he] using hz'
          change (e (rot z)).val 0 = 1-‖z.val‖^2
          rw [heval (rot z) hre]
          simp [rot,norm_mul]
      have hnot :
        ¬ ∃ w : Complex.ClosedUnitDisc,
          OrientableRel p n
            (Complex.ClosedUnitDisc.bdyPtOfReal
              (-(3*(j.val : ℝ)+1+(t : ℝ))/(4*(p : ℝ)+3*(n : ℝ)))) w ∨
          OrientableRel p n w
            (Complex.ClosedUnitDisc.bdyPtOfReal
              (-(3*(j.val : ℝ)+1+(t : ℝ))/(4*(p : ℝ)+3*(n : ℝ)))) := by
        classical
        let N : ℝ := 4*(p : ℝ)+3*(n : ℝ)
        have hN : 0 < N := by
          dsimp [N]
          rcases hadmissible with hp | hn
          · have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
            positivity
          · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
            positivity
        let bp (x : ℝ) := Complex.ClosedUnitDisc.bdyPtOfReal (x/N)
        have hperiod (x y : ℝ) (he : bp x = bp y) :
            ∃ k : ℤ, x=y+(k : ℝ)*N := by
          have hc : Real.fourierChar (x/N) = Real.fourierChar (y/N) := by
            apply Subtype.ext
            exact congrArg (fun z : Complex.ClosedUnitDisc => z.val) he
          rw [Real.fourierChar_apply',Real.fourierChar_apply'] at hc
          obtain ⟨k,hk⟩ := Circle.exp_eq_exp.mp hc
          have hpi : 2*Real.pi ≠ 0 := by positivity
          have hfrac : x/N=y/N+(k : ℝ) := by
            apply mul_left_cancel₀ hpi
            nlinarith [hk]
          have hm := congrArg (fun r : ℝ => r*N) hfrac
          rw [add_mul,div_mul_cancel₀ _ hN.ne',div_mul_cancel₀ _ hN.ne'] at hm
          exact ⟨k,hm⟩
        have hnormalize (x y : ℝ) (hx0 : -3*(n : ℝ)<x) (hx1 : x<4*(p : ℝ))
            (hy0 : -3*(n : ℝ)≤y) (hy1 : y≤4*(p : ℝ)) (he : bp x=bp y) : x=y := by
          obtain ⟨k,hk⟩ := hperiod x y he
          have hlo : -N<x-y := by dsimp [N]; linarith
          have hhi : x-y<N := by dsimp [N]; linarith
          have hk0 : (-1 : ℝ)<(k : ℝ) := by nlinarith
          have hk1 : (k : ℝ)<1 := by nlinarith
          have ki0 : (-1 : ℤ)<k := by exact_mod_cast hk0
          have ki1 : k<(1 : ℤ) := by exact_mod_cast hk1
          have he0 : k=0 := by omega
          simpa [he0] using hk
        let hp (j : Fin n) (t : unitInterval) : Complex.ClosedUnitDisc :=
          bp (-(3*(j.val : ℝ)+1+(t : ℝ)))
        have hpbounds (j : Fin n) (t : unitInterval) :
            -3*(n : ℝ)< -(3*(j.val : ℝ)+1+(t : ℝ)) ∧
            -(3*(j.val : ℝ)+1+(t : ℝ)) < 4*(p : ℝ) := by
          have hj : (j.val : ℝ)+1 ≤ n := by exact_mod_cast j.isLt
          constructor <;> linarith [t.property.1,t.property.2, Nat.cast_nonneg (α := ℝ) j.val,
            Nat.cast_nonneg (α := ℝ) p]
        have hpairedBounds (i : Fin p) (t : unitInterval) (r : ℝ)
            (hr : 0 ≤ r ∧ r ≤ 4) :
            -3*(n : ℝ) ≤ 4*(i.val : ℝ)+r ∧ 4*(i.val : ℝ)+r ≤ 4*(p : ℝ) := by
          have hi : (i.val : ℝ)+1 ≤ p := by exact_mod_cast i.isLt
          constructor <;> linarith [hr.1,hr.2,Nat.cast_nonneg (α := ℝ) i.val,Nat.cast_nonneg (α := ℝ) n]
        have hcBounds (i : Fin n) (t : unitInterval) :
            (-3*(n : ℝ) ≤ -(3*(i.val : ℝ)+(t : ℝ)) ∧
              -(3*(i.val : ℝ)+(t : ℝ)) ≤ 4*(p : ℝ)) ∧
            (-3*(n : ℝ) ≤ -(3*(i.val : ℝ)+3-(t : ℝ)) ∧
              -(3*(i.val : ℝ)+3-(t : ℝ)) ≤ 4*(p : ℝ)) := by
          have hi : (i.val : ℝ)+1 ≤ n := by exact_mod_cast i.isLt
          constructor <;> constructor <;>
            linarith [t.property.1,t.property.2,Nat.cast_nonneg (α := ℝ) i.val,Nat.cast_nonneg (α := ℝ) p]
        have hindex_eq (j k : Fin n) (x y : ℝ)
            (hx : 0≤x ∧ x≤2) (hy : 0≤y ∧ y≤2)
            (he : 3*(j.val : ℝ)+x = 3*(k.val : ℝ)+y) : j=k := by
          have hlo : (-1 : ℝ)<(j.val : ℝ)-(k.val : ℝ) := by linarith
          have hhi : (j.val : ℝ)-(k.val : ℝ)<1 := by linarith
          have hlo' : (-1 : ℤ)<(j.val : ℤ)-(k.val : ℤ) := by exact_mod_cast hlo
          have hhi' : (j.val : ℤ)-(k.val : ℤ)<1 := by exact_mod_cast hhi
          have hv : j.val=k.val := by omega
          exact Fin.ext hv
        have hp_inj (j k : Fin n) (t u : unitInterval) (he : hp j t=hp k u) :
            j=k ∧ t=u := by
          have hj := hpbounds j t
          have hk := hpbounds k u
          have heq := hnormalize _ _ hj.1 hj.2 hk.1.le hk.2.le he
          have hidx : j=k := hindex_eq j k (1+(t : ℝ)) (1+(u : ℝ))
            ⟨by linarith [t.property.1],by linarith [t.property.2]⟩
            ⟨by linarith [u.property.1],by linarith [u.property.2]⟩ (by linarith)
          subst k
          refine ⟨rfl,Subtype.ext ?_⟩
          linarith
        have hp_not_handle (j : Fin n) (t : unitInterval) (i : Fin p) (r : ℝ)
            (hr : 0 ≤ r ∧ r ≤ 4) : hp j t ≠ bp (4*(i.val : ℝ)+r) := by
          intro he
          have hj := hpbounds j t
          have hi := hpairedBounds i t r hr
          have heq := hnormalize _ _ hj.1 hj.2 hi.1 hi.2 he
          linarith [t.property.1,Nat.cast_nonneg (α := ℝ) j.val,Nat.cast_nonneg (α := ℝ) i.val,hr.1]
        have hp_c_left (j i : Fin n) (t x : unitInterval)
            (he : hp j t=bp (-(3*(i.val : ℝ)+(x : ℝ)))) :
            j=i ∧ (t : ℝ)=0 ∧ (x : ℝ)=1 := by
          have hj := hpbounds j t
          have hi := (hcBounds i x).1
          have heq := hnormalize _ _ hj.1 hj.2 hi.1 hi.2 he
          have hidx : j=i := hindex_eq j i (1+(t : ℝ)) x
            ⟨by linarith [t.property.1],by linarith [t.property.2]⟩
            ⟨x.property.1,by linarith [x.property.2]⟩ (by linarith)
          subst i
          refine ⟨rfl,?_,?_⟩ <;> linarith [t.property.1,x.property.2]
        have hp_c_right (j i : Fin n) (t x : unitInterval)
            (he : hp j t=bp (-(3*(i.val : ℝ)+3-(x : ℝ)))) :
            j=i ∧ (t : ℝ)=1 ∧ (x : ℝ)=1 := by
          have hj := hpbounds j t
          have hi := (hcBounds i x).2
          have heq := hnormalize _ _ hj.1 hj.2 hi.1 hi.2 he
          -- Reverse the seam-side offset so both slot offsets lie in [0,2].
          have hidx : j=i := by
            have hlo : (-1 : ℝ)<(j.val : ℝ)-(i.val : ℝ) := by
              linarith [t.property.2,x.property.2]
            have hhi : (j.val : ℝ)-(i.val : ℝ)<1 := by
              linarith [t.property.1,x.property.1]
            have hlo' : (-1 : ℤ)<(j.val : ℤ)-(i.val : ℤ) := by exact_mod_cast hlo
            have hhi' : (j.val : ℤ)-(i.val : ℤ)<1 := by exact_mod_cast hhi
            apply Fin.ext
            omega
          subst i
          refine ⟨rfl,?_,?_⟩ <;> linarith [t.property.2,x.property.2]
        have hrel_src (j : Fin n) (t : unitInterval) {z w : Complex.ClosedUnitDisc}
            (hr : OrientableRel p n z w) (hz : z=hp j t) :
            (t : ℝ)=0 ∧ w=hp j 1 := by
          cases hr with
          | a x i =>
            have he : hp j t=bp (4*(i.val : ℝ)+(x : ℝ)) := hz.symm
            exact False.elim (hp_not_handle j t i x ⟨x.property.1,by linarith [x.property.2]⟩ he)
          | b x i =>
            have he : hp j t=bp (4*(i.val : ℝ)+(1+(x : ℝ))) := by
              convert hz.symm using 1 <;> congr 1 <;> ring
            exact False.elim (hp_not_handle j t i (1+(x : ℝ))
              ⟨by linarith [x.property.1],by linarith [x.property.2]⟩ he)
          | c x i =>
            have he : hp j t=bp (-(3*(i.val : ℝ)+(x : ℝ))) := hz.symm
            obtain ⟨hji,ht,hx⟩ := hp_c_left j i t x he
            subst i
            refine ⟨ht,?_⟩
            change bp (-(3*(j.val : ℝ)+3-(x : ℝ))) = bp (-(3*(j.val : ℝ)+1+(1 : unitInterval)))
            apply congrArg bp
            change -(3*(j.val : ℝ)+3-(x : ℝ)) = -(3*(j.val : ℝ)+1+1)
            linarith
        have hrel_tgt (j : Fin n) (t : unitInterval) {z w : Complex.ClosedUnitDisc}
            (hr : OrientableRel p n z w) (hw : w=hp j t) :
            (t : ℝ)=1 ∧ z=hp j 0 := by
          cases hr with
          | a x i =>
            have he : hp j t=bp (4*(i.val : ℝ)+(3-(x : ℝ))) := by
              convert hw.symm using 1 <;> congr 1 <;> ring
            exact False.elim (hp_not_handle j t i (3-(x : ℝ))
              ⟨by linarith [x.property.2],by linarith [x.property.1]⟩ he)
          | b x i =>
            have he : hp j t=bp (4*(i.val : ℝ)+(4-(x : ℝ))) := by
              convert hw.symm using 1 <;> congr 1 <;> ring
            exact False.elim (hp_not_handle j t i (4-(x : ℝ))
              ⟨by linarith [x.property.2],by linarith [x.property.1]⟩ he)
          | c x i =>
            have he : hp j t=bp (-(3*(i.val : ℝ)+3-(x : ℝ))) := hw.symm
            obtain ⟨hji,ht,hx⟩ := hp_c_right j i t x he
            subst i
            refine ⟨ht,?_⟩
            change bp (-(3*(j.val : ℝ)+(x : ℝ))) = bp (-(3*(j.val : ℝ)+1+(0 : unitInterval)))
            apply congrArg bp
            change -(3*(j.val : ℝ)+(x : ℝ)) = -(3*(j.val : ℝ)+1+0)
            linarith
        rintro ⟨w,hr | hr⟩
        · have ht := (hrel_src j t hr rfl).1
          linarith
        · have ht := (hrel_tgt j t hr rfl).1
          linarith
      let A : Set Complex.ClosedUnitDisc :=
        {z | ∃ w, OrientableRel p n z w ∨ OrientableRel p n w z}
      let U : Set Complex.ClosedUnitDisc := Aᶜ
      let q : Complex.ClosedUnitDisc → Quot (OrientableRel p n) := Quot.mk _
      let z : Complex.ClosedUnitDisc := Complex.ClosedUnitDisc.bdyPtOfReal
        (-(3*(j.val : ℝ)+1+(t : ℝ))/(4*(p : ℝ)+3*(n : ℝ)))
      have hz : z ∈ U := hnot
      obtain ⟨hA,hQU,γ,hγ⟩ := hquot
      let c : Circle := Real.fourierChar
        (-(3*(j.val : ℝ)+1+(t : ℝ))/(4*(p : ℝ)+3*(n : ℝ)))
      obtain ⟨ed,hzd,hed⟩ := hcharts c
      change z ∈ ed.source at hzd
      letI : Nonempty U := ⟨⟨z,hz⟩⟩
      letI : Nonempty (q '' U) := ⟨⟨q z,⟨z,hz,rfl⟩⟩⟩
      let iu := hA.isOpen_compl.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph
        (Subtype.val : U → Complex.ClosedUnitDisc)
      let iq := hQU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph
        (Subtype.val : q '' U → Quot (OrientableRel p n))
      let e := ((iq.symm.transHomeomorph γ.symm).trans iu).trans ed
      have hiq : iq.symm (q z) = γ ⟨z,hz⟩ := by
        have hval : iq (γ ⟨z,hz⟩) = q z := hγ ⟨z,hz⟩
        rw [← hval]
        exact iq.left_inv (by trivial)
      have hev : e (q z) = ed z := by
        change ed (iu (γ.symm (iq.symm (q z)))) = ed z
        rw [hiq,Homeomorph.symm_apply_apply]
        rfl
      have hes : q z ∈ e.source := by
        change q z ∈ (((iq.symm.transHomeomorph γ.symm).trans iu).trans ed).source
        rw [OpenPartialHomeomorph.trans_source]
        constructor
        · rw [OpenPartialHomeomorph.trans_source]
          constructor
          · change q z ∈ iq.target
            simpa [iq,Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target] using
              (show q z ∈ q '' U from ⟨z,hz,rfl⟩)
          · trivial
        · change iu (γ.symm (iq.symm (q z))) ∈ ed.source
          rw [hiq,Homeomorph.symm_apply_apply]
          exact hzd
      rw [InvarianceOfDomain.isBoundaryPoint_iff_any_chart (modelWithCornersEuclideanHalfSpace 2) hes,
        frontier_range_modelWithCornersEuclideanHalfSpace]
      rw [hev]
      change 0 = (ed z).val 0
      rw [hed z hzd]
      simp [z,Complex.ClosedUnitDisc.bdyPtOfReal]
    have hclosed : IsClosed ((modelWithCornersEuclideanHalfSpace 2).boundary
        (Quot (OrientableRel p n))) := by
      let I := modelWithCornersEuclideanHalfSpace 2
      rw [← I.compl_interior,isClosed_compl_iff]
      apply isOpen_iff_forall_mem_open.mpr
      intro x hx
      let c := chartAt (EuclideanHalfSpace 2) x
      let V : Set (Quot (OrientableRel p n)) := c.source ∩ c ⁻¹' {h | 0 < h.val 0}
      have hV : IsOpen V := by
        apply c.continuousOn.isOpen_inter_preimage c.open_source
        exact isOpen_lt continuous_const (by fun_prop)
      have hxsource : x ∈ c.source := mem_chart_source _ x
      have hxpos : 0 < (c x).val 0 := by
        have hn : 0 ≤ (c x).val 0 := (c x).property
        have hb : ¬ I.IsBoundaryPoint x := (I.isInteriorPoint_iff_not_isBoundaryPoint x).mp hx
        have hnot : ¬ (0 = (c x).val 0) := by
          intro he
          apply hb
          rw [InvarianceOfDomain.isBoundaryPoint_iff_any_chart I hxsource,
            frontier_range_modelWithCornersEuclideanHalfSpace]
          exact he
        by_contra hp
        apply hnot
        linarith
      refine ⟨V,?_,hV,⟨hxsource,hxpos⟩⟩
      intro y hy
      apply (I.isInteriorPoint_iff_not_isBoundaryPoint y).mpr
      intro hb
      have he := (InvarianceOfDomain.isBoundaryPoint_iff_any_chart I hy.1).mp hb
      rw [frontier_range_modelWithCornersEuclideanHalfSpace] at he
      change 0 = (c y).val 0 at he
      have hp : 0 < (c y).val 0 := hy.2
      linarith
    rintro x ⟨⟨j,t⟩,rfl⟩
    let h (r : ℝ) := Quot.mk (OrientableRel p n) (Complex.ClosedUnitDisc.bdyPtOfReal
      (-(3*(j.val : ℝ)+1+r)/(4*(p : ℝ)+3*(n : ℝ))))
    have hb : Continuous Complex.ClosedUnitDisc.bdyPtOfReal :=
      (continuous_subtype_val.comp Real.continuous_fourierChar).subtype_mk _
    have hc : Continuous h := continuous_quot_mk.comp (hb.comp (by fun_prop))
    have hp : IsClosed (h ⁻¹' ((modelWithCornersEuclideanHalfSpace 2).boundary
        (Quot (OrientableRel p n)))) := hclosed.preimage hc
    have hsub : Ioo (0 : ℝ) 1 ⊆ h ⁻¹' ((modelWithCornersEuclideanHalfSpace 2).boundary
        (Quot (OrientableRel p n))) := by
      intro r hr
      exact hstrict j ⟨r,⟨hr.1.le,hr.2.le⟩⟩ hr.1 hr.2
    have hall := hp.closure_subset_iff.mpr hsub
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] at hall
    exact hall t.property
  have hdisk (z : Complex.ClosedUnitDisc) (hz : ‖z.val‖ < 1) :
      I.IsInteriorPoint (q z) := by
    classical
    have hinner {U : Set (EuclideanSpace ℝ (Fin 2))} (hU : IsOpen U)
        (f : U → Quot (OrientableRel p n)) (hfcont : Continuous f)
        (hfinj : Function.Injective f) (u : U) :
        (modelWithCornersEuclideanHalfSpace 2).IsInteriorPoint (f u) := by
      let I := modelWithCornersEuclideanHalfSpace 2
      let c : PartialEquiv (Quot (OrientableRel p n)) (EuclideanSpace ℝ (Fin 2)) := extChartAt I (f u)
      let f₀ : (EuclideanSpace ℝ (Fin 2)) → (Quot (OrientableRel p n)) :=
        Function.extend ((↑) : U → (EuclideanSpace ℝ (Fin 2))) f (fun _ ↦ f u)
      have hf₀_eq (x : U) : f₀ x.1 = f x := by
        exact Function.Injective.extend_apply Subtype.val_injective f
          (fun _ ↦ f u) x
      have hf₀_cont : ContinuousOn f₀ U := by
        rw [continuousOn_iff_continuous_restrict]
        convert hfcont using 1
        funext x
        exact hf₀_eq x
      let W : Set (EuclideanSpace ℝ (Fin 2)) := U ∩ f₀ ⁻¹' c.source
      have hWopen : IsOpen W :=
        hf₀_cont.isOpen_inter_preimage hU (isOpen_extChartAt_source (I := I) (f u))
      have huW : u.1 ∈ W := by
        refine ⟨u.2, ?_⟩
        change f₀ u.1 ∈ c.source
        rw [hf₀_eq u]
        exact mem_extChartAt_source (I := I) (f u)
      let g : (EuclideanSpace ℝ (Fin 2)) → (EuclideanSpace ℝ (Fin 2)) := fun x ↦ c (f₀ x)
      have hg_cont : ContinuousOn g W := by
        apply (continuousOn_extChartAt (I := I) (f u)).comp
          (hf₀_cont.mono inter_subset_left)
        exact fun x hx ↦ hx.2
      have hg_inj : Set.InjOn g W := by
        intro x hx y hy hxy
        have hf₀xy : f₀ x = f₀ y :=
          c.injOn hx.2 hy.2 hxy
        have hfx :
            f (⟨x, hx.1⟩ : U) = f (⟨y, hy.1⟩ : U) := by
          rw [← hf₀_eq ⟨x, hx.1⟩, ← hf₀_eq ⟨y, hy.1⟩]
          exact hf₀xy
        exact congrArg Subtype.val (hfinj hfx)
      let φ : PartialEquiv (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) :=
        hg_inj.toPartialEquiv g W
      have hφ_cont : ContinuousOn φ φ.source := by
        change ContinuousOn g W
        exact hg_cont
      have hWnhds : W ∈ nhds u.1 :=
        hWopen.mem_nhds huW
      have himage :
          g '' W ∈ nhds (g u.1) := by
        have h :=
          maps_nhds_to_nhds (EuclideanSpace ℝ (Fin 2)) hφ_cont hWnhds
            (show W ⊆ φ.source by
              change W ⊆ W
              exact subset_rfl)
        change g '' W ∈ nhds (g u.1) at h
        exact h
      have hsub : g '' W ⊆ Set.range I := by
        rintro y ⟨x,hx,rfl⟩
        exact Set.mem_range_self ((chartAt (EuclideanHalfSpace 2) (f u)) (f₀ x))
      have hr : Set.range I ∈ nhds (g u.val) := Filter.mem_of_superset himage hsub
      apply (isInteriorPoint_iff_any_chart I (ChartedSpace.mem_chart_source (f u))).mpr
      change c (f u) ∈ interior (Set.range I)
      rw [mem_interior_iff_mem_nhds]
      convert hr using 1
      congr 1
      change c (f u) = c (f₀ u.val)
      rw [hf₀_eq u]
    classical
    let U : Set Complex.ClosedUnitDisc := {z | ‖z.val‖ < 1}
    let q : Complex.ClosedUnitDisc → Quot (OrientableRel p n) := Quot.mk _
    have hb (r : ℝ) : ‖(Complex.ClosedUnitDisc.bdyPtOfReal r).val‖ = 1 := by
      exact Circle.norm_coe (Real.fourierChar r)
    have hsrc {z w : Complex.ClosedUnitDisc} (h : OrientableRel p n z w) : ‖z.val‖ = 1 := by
      cases h <;> exact hb _
    have htgt {z w : Complex.ClosedUnitDisc} (h : OrientableRel p n z w) : ‖w.val‖ = 1 := by
      cases h <;> exact hb _
    have hnorm {z w : Complex.ClosedUnitDisc}
        (h : Relation.EqvGen (OrientableRel p n) z w) : ‖z.val‖ = ‖w.val‖ := by
      induction h with
      | rel z w h => exact (hsrc h).trans (htgt h).symm
      | refl z => rfl
      | symm z w h ih => exact ih.symm
      | trans z w v h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
    have hfiber {z w : Complex.ClosedUnitDisc} (h : Relation.EqvGen (OrientableRel p n) z w) :
        z ∈ U → w = z := by
      induction h with
      | rel z w h => intro hz; exact False.elim (by have := hsrc h; change ‖z.val‖ < 1 at hz; linarith)
      | refl z => intro _; rfl
      | symm z w h ih =>
        intro hw
        have hz : z ∈ U := by change ‖z.val‖ < 1; rw [hnorm h]; exact hw
        exact (ih hz).symm
      | trans z w v h₁ h₂ ih₁ ih₂ =>
        intro hz
        have hw := ih₁ hz
        subst w
        exact ih₂ hz
    have hfiberq {z w : Complex.ClosedUnitDisc} (hz : z ∈ U) (he : q z = q w) : w=z :=
      hfiber (Quot.eqvGen_exact he) hz
    let L := Complex.orthonormalBasisOneI.repr.symm
    let V : Set (EuclideanSpace ℝ (Fin 2)) := {v | ‖v‖ < 1}
    let f : V → Quot (OrientableRel p n) := fun v =>
      q ⟨L v.val,by
        rw [Metric.mem_closedBall,dist_zero_right,L.norm_map]
        exact v.property.le⟩
    have hfc : Continuous f := by
      apply continuous_quot_mk.comp
      apply Continuous.subtype_mk
      exact L.continuous.comp continuous_subtype_val
    have hfi : Function.Injective f := by
      intro v w he
      have hv : (⟨L v.val,by
          rw [Metric.mem_closedBall,dist_zero_right,L.norm_map]
          exact v.property.le⟩ : Complex.ClosedUnitDisc) ∈ U := by
        change ‖L v.val‖ < 1
        rw [L.norm_map]
        exact v.property
      have hw := hfiberq hv he
      apply Subtype.ext
      apply L.injective
      exact (congrArg Subtype.val hw).symm
    let u : V := ⟨L.symm z.val,by
      change ‖L.symm z.val‖ < 1
      rw [L.symm.norm_map]
      exact hz⟩
    have hi := hinner (isOpen_lt continuous_norm continuous_const) f hfc hfi u
    have hf : f u = q z := by
      apply congrArg q
      apply Subtype.ext
      exact L.apply_symm_apply z.val
    rw [hf] at hi
    exact hi
  have hpairs :
    (∀ (i : Fin p) (t : unitInterval), 0<(t:ℝ) → (t:ℝ)<1 →
      (modelWithCornersEuclideanHalfSpace 2).IsInteriorPoint
        (Quot.mk (OrientableRel p n) (Complex.ClosedUnitDisc.bdyPtOfReal
          ((4*(i.val:ℝ)+(t:ℝ))/(4*(p:ℝ)+3*(n:ℝ)))))) ∧
    (∀ (i : Fin p) (t : unitInterval), 0<(t:ℝ) → (t:ℝ)<1 →
      (modelWithCornersEuclideanHalfSpace 2).IsInteriorPoint
        (Quot.mk (OrientableRel p n) (Complex.ClosedUnitDisc.bdyPtOfReal
          ((4*(i.val:ℝ)+1+(t:ℝ))/(4*(p:ℝ)+3*(n:ℝ)))))) ∧
    (∀ (i : Fin n) (t : unitInterval), 0<(t:ℝ) → (t:ℝ)<1 →
      (modelWithCornersEuclideanHalfSpace 2).IsInteriorPoint
        (Quot.mk (OrientableRel p n) (Complex.ClosedUnitDisc.bdyPtOfReal
          (-(3*(i.val:ℝ)+(t:ℝ))/(4*(p:ℝ)+3*(n:ℝ)))))) := by
    classical
    let N : ℝ := 4*(p : ℝ)+3*(n : ℝ)
    have hN : 0 < N := by
      dsimp [N]
      rcases hadmissible with hp | hn
      · have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
        positivity
      · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
        positivity
    let bp (x : ℝ) := Complex.ClosedUnitDisc.bdyPtOfReal (x/N)
    have hperiod (x y : ℝ) (he : bp x = bp y) :
        ∃ k : ℤ, x=y+(k : ℝ)*N := by
      have hc : Real.fourierChar (x/N) = Real.fourierChar (y/N) := by
        apply Subtype.ext
        exact congrArg (fun z : Complex.ClosedUnitDisc => z.val) he
      rw [Real.fourierChar_apply',Real.fourierChar_apply'] at hc
      obtain ⟨k,hk⟩ := Circle.exp_eq_exp.mp hc
      have hpi : 2*Real.pi ≠ 0 := by positivity
      have hfrac : x/N=y/N+(k : ℝ) := by
        apply mul_left_cancel₀ hpi
        nlinarith [hk]
      have hm := congrArg (fun r : ℝ => r*N) hfrac
      rw [add_mul,div_mul_cancel₀ _ hN.ne',div_mul_cancel₀ _ hN.ne'] at hm
      exact ⟨k,hm⟩
    have hnormalize (x y : ℝ) (hx0 : -3*(n : ℝ)<x) (hx1 : x<4*(p : ℝ))
        (hy0 : -3*(n : ℝ)≤y) (hy1 : y≤4*(p : ℝ)) (he : bp x=bp y) : x=y := by
      obtain ⟨k,hk⟩ := hperiod x y he
      have hlo : -N<x-y := by dsimp [N]; linarith
      have hhi : x-y<N := by dsimp [N]; linarith
      have hk0 : (-1 : ℝ)<(k : ℝ) := by nlinarith
      have hk1 : (k : ℝ)<1 := by nlinarith
      have ki0 : (-1 : ℤ)<k := by exact_mod_cast hk0
      have ki1 : k<(1 : ℤ) := by exact_mod_cast hk1
      have he0 : k=0 := by omega
      simpa [he0] using hk
    have integer_fraction_unique (n m : ℤ) (t x : ℝ)
        (ht0 : 0<t) (ht1 : t<1) (hx0 : 0≤x) (hx1 : x≤1)
        (he : (n:ℝ)+t=(m:ℝ)+x) : n=m ∧ t=x := by
      have hlo : (-1:ℝ)<((n-m:ℤ):ℝ) := by push_cast; linarith
      have hhi : ((n-m:ℤ):ℝ)<1 := by push_cast; linarith
      have hi0 : (-1:ℤ)<n-m := by exact_mod_cast hlo
      have hi1 : n-m<(1:ℤ) := by exact_mod_cast hhi
      have hnm : n=m := by omega
      refine ⟨hnm,?_⟩
      rw [hnm] at he
      linarith
    let J := (Fin p × Bool) ⊕ Fin n
    let rawEdgeSlot (k : J) (e : Bool) : ℤ :=
      match k with
      | .inl (i,b) => 4*(i.val:ℤ)+(if b then 1 else 0)+(if e then 2 else 0)
      | .inr i => -3*(i.val:ℤ)+(if e then -3 else -1)
    let rawEdgeFraction (k : J) (t : unitInterval) (e : Bool) : ℝ :=
      match k with
      | .inl _ => if e then 1-(t:ℝ) else (t:ℝ)
      | .inr _ => if e then (t:ℝ) else 1-(t:ℝ)
    let rawEdgeNumerator (k : J) (t : unitInterval) (e : Bool) : ℝ :=
      (rawEdgeSlot k e:ℝ)+rawEdgeFraction k t e
    let rawEdgePoint (k : J) (t : unitInterval) (e : Bool) : Complex.ClosedUnitDisc :=
      bp (rawEdgeNumerator k t e)
    have rawEdgeSlot_injective (k l : J) (e f : Bool)
        (h : rawEdgeSlot k e=rawEdgeSlot l f) : k=l ∧ e=f := by
      cases k with
      | inl k =>
        rcases k with ⟨i,b⟩
        cases l with
        | inl l =>
          rcases l with ⟨j,c⟩
          cases b <;> cases c <;> cases e <;> cases f <;>
            simp [rawEdgeSlot] at h <;> simp only [Sum.inl.injEq,Sum.inr.injEq,Prod.mk.injEq,Fin.ext_iff, Bool.false_eq_true,Bool.true_eq_false,eq_self_iff_true,and_true,true_and,and_false,false_and] <;> first | omega | (congr 3 <;> omega)
        | inr j =>
          cases b <;> cases e <;> cases f <;> simp [rawEdgeSlot] at h <;> first | omega | (congr 3 <;> omega)
      | inr i =>
        cases l with
        | inl l =>
          rcases l with ⟨j,c⟩
          cases c <;> cases e <;> cases f <;> simp [rawEdgeSlot] at h <;> first | omega | (congr 3 <;> omega)
        | inr j =>
          cases e <;> cases f <;> simp [rawEdgeSlot] at h <;> simp only [Sum.inl.injEq,Sum.inr.injEq,Prod.mk.injEq,Fin.ext_iff, Bool.false_eq_true,Bool.true_eq_false,eq_self_iff_true,and_true,true_and,and_false,false_and] <;> first | omega | (congr 3 <;> omega)
    have rawEdgeSlot_bounds (k : J) (e : Bool) :
        -3*(n:ℤ)≤rawEdgeSlot k e ∧ rawEdgeSlot k e<4*(p:ℤ) := by
      cases k with
      | inl k =>
        rcases k with ⟨i,b⟩
        have hi : (i.val:ℤ)<(p:ℤ) := by exact_mod_cast i.isLt
        cases b <;> cases e <;> simp [rawEdgeSlot] <;> omega
      | inr i =>
        have hi : (i.val:ℤ)<(n:ℤ) := by exact_mod_cast i.isLt
        cases e <;> simp [rawEdgeSlot] <;> omega
    have rawEdgeFraction_bounds (k : J) (t : unitInterval) (e : Bool) :
        0≤rawEdgeFraction k t e ∧ rawEdgeFraction k t e≤1 := by
      have ht0 := t.property.1
      have ht1 := t.property.2
      cases k <;> cases e <;> simp only [rawEdgeFraction,Bool.false_eq_true,Bool.true_eq_false,ite_true,ite_false] <;> constructor <;> linarith
    
    have rawEdgeFraction_strict (k : J) (t : unitInterval)
        (ht0 : 0<(t:ℝ)) (ht1 : (t:ℝ)<1) (e : Bool) :
        0<rawEdgeFraction k t e ∧ rawEdgeFraction k t e<1 := by
      cases k <;> cases e <;> simp only [rawEdgeFraction,Bool.false_eq_true,Bool.true_eq_false,ite_true,ite_false] <;> constructor <;> linarith
    
    have rawEdgeNumerator_bounds (k : J) (t : unitInterval) (e : Bool) :
        -3*(n:ℝ)≤rawEdgeNumerator k t e ∧ rawEdgeNumerator k t e≤4*(p:ℝ) := by
      have hs := rawEdgeSlot_bounds k e
      have h0 : (-3*(n:ℝ))≤(rawEdgeSlot k e:ℝ) := by exact_mod_cast hs.1
      have h1 : (rawEdgeSlot k e:ℝ)+1≤4*(p:ℝ) := by
        exact_mod_cast (show rawEdgeSlot k e+1≤4*(p:ℤ) by omega)
      have ht := rawEdgeFraction_bounds k t e
      unfold rawEdgeNumerator
      constructor <;> linarith
    
    have rawEdgeNumerator_strict (k : J) (t : unitInterval)
        (ht0 : 0<(t:ℝ)) (ht1 : (t:ℝ)<1) (e : Bool) :
        -3*(n:ℝ)<rawEdgeNumerator k t e ∧ rawEdgeNumerator k t e<4*(p:ℝ) := by
      have hs := rawEdgeSlot_bounds k e
      have h0 : (-3*(n:ℝ))≤(rawEdgeSlot k e:ℝ) := by exact_mod_cast hs.1
      have h1 : (rawEdgeSlot k e:ℝ)+1≤4*(p:ℝ) := by
        exact_mod_cast (show rawEdgeSlot k e+1≤4*(p:ℤ) by omega)
      have ht := rawEdgeFraction_strict k t ht0 ht1 e
      unfold rawEdgeNumerator
      constructor <;> linarith
    
    have rawEdgePoint_eq_iff (k l : J) (t x : unitInterval)
        (ht0 : 0<(t:ℝ)) (ht1 : (t:ℝ)<1) (e f : Bool) :
        rawEdgePoint k t e=rawEdgePoint l x f ↔ k=l ∧ t=x ∧ e=f := by
      constructor
      · intro he
        have ht := rawEdgeNumerator_strict k t ht0 ht1 e
        have hx := rawEdgeNumerator_bounds l x f
        have hn := hnormalize _ _ ht.1 ht.2 hx.1 hx.2 he
        have htf := rawEdgeFraction_strict k t ht0 ht1 e
        have hxf := rawEdgeFraction_bounds l x f
        obtain ⟨hslot,hfrac⟩ := integer_fraction_unique (rawEdgeSlot k e) (rawEdgeSlot l f)
          (rawEdgeFraction k t e) (rawEdgeFraction l x f) htf.1 htf.2 hxf.1 hxf.2 hn
        obtain ⟨hkl,hef⟩ := rawEdgeSlot_injective k l e f hslot
        subst l
        subst f
        have htx : t=x := by
          apply Subtype.ext
          cases k <;> cases e <;> simp only [rawEdgeFraction,Bool.false_eq_true,Bool.true_eq_false,ite_true,ite_false] at hfrac <;> linarith
        exact ⟨rfl,htx,rfl⟩
      · rintro ⟨rfl,rfl,rfl⟩
        rfl
    
    let rawInteriorPair (k : J) (t : unitInterval) :
        Set Complex.ClosedUnitDisc := {z | z=rawEdgePoint k t false ∨ z=rawEdgePoint k t true}
    
    have rawEdgePoint_mem_interior_pair_iff (k l : J) (t x : unitInterval)
        (ht0 : 0<(t:ℝ)) (ht1 : (t:ℝ)<1) (f : Bool) :
        rawEdgePoint l x f ∈ rawInteriorPair k t ↔ k=l ∧ t=x := by
      constructor
      · intro he
        rcases he with he|he
        · have h := (rawEdgePoint_eq_iff k l t x ht0 ht1 false f).mp he.symm
          exact ⟨h.1,h.2.1⟩
        · have h := (rawEdgePoint_eq_iff k l t x ht0 ht1 true f).mp he.symm
          exact ⟨h.1,h.2.1⟩
      · rintro ⟨rfl,rfl⟩
        cases f
        · exact Or.inl rfl
        · exact Or.inr rfl
    
    have rawEdgePoint_handle (i : Fin p) (b e : Bool) (t : unitInterval) :
        rawEdgePoint (.inl (i,b)) t e=bp
          (if e then 4*(i:ℝ)+(if b then 4 else 3)-(t:ℝ)
           else 4*(i:ℝ)+(if b then 1 else 0)+(t:ℝ)) := by
      unfold rawEdgePoint
      congr 1
      cases b <;> cases e <;>
        simp [rawEdgeNumerator,rawEdgeSlot,rawEdgeFraction] <;> ring
    
    have rawEdgePoint_seam (i : Fin n) (e : Bool) (t : unitInterval) :
        rawEdgePoint (.inr i) t e=bp
          (if e then -(3*(i.val:ℝ)+3-(t:ℝ)) else -(3*(i.val:ℝ)+(t:ℝ))) := by
      unfold rawEdgePoint
      congr 1
      cases e <;> simp [rawEdgeNumerator,rawEdgeSlot,rawEdgeFraction] <;> ring
    
    have rel_is_raw_edge_pair {z w : Complex.ClosedUnitDisc}
        (h : LeanEval.Topology.ClassificationOfSurfaces.OrientableRel p n z w) :
        ∃ k : J, ∃ x : unitInterval,
          z=rawEdgePoint k x false ∧ w=rawEdgePoint k x true := by
      cases h with
      | a x i =>
        refine ⟨.inl (i,false),x,?_,?_⟩ <;> rw [rawEdgePoint_handle] <;>
          simp [bp,N]
      | b x i =>
        refine ⟨.inl (i,true),x,?_,?_⟩ <;> rw [rawEdgePoint_handle] <;>
          simp [bp,N]
      | c x i =>
        refine ⟨.inr i,x,?_,?_⟩ <;> rw [rawEdgePoint_seam] <;>
          simp [bp,N]
    
    have rawInteriorPair_rel_invariant (k : J) (t : unitInterval)
        (ht0 : 0<(t:ℝ)) (ht1 : (t:ℝ)<1) {z w : Complex.ClosedUnitDisc}
        (h : LeanEval.Topology.ClassificationOfSurfaces.OrientableRel p n z w) :
        z ∈ rawInteriorPair k t ↔ w ∈ rawInteriorPair k t := by
      obtain ⟨l,x,rfl,rfl⟩ := rel_is_raw_edge_pair h
      rw [rawEdgePoint_mem_interior_pair_iff k l t x ht0 ht1 false,
        rawEdgePoint_mem_interior_pair_iff k l t x ht0 ht1 true]
    
    have rawInteriorPair_eqv_invariant (k : J) (t : unitInterval)
        (ht0 : 0<(t:ℝ)) (ht1 : (t:ℝ)<1) {z w : Complex.ClosedUnitDisc}
        (h : Relation.EqvGen (LeanEval.Topology.ClassificationOfSurfaces.OrientableRel p n) z w) :
        z ∈ rawInteriorPair k t ↔ w ∈ rawInteriorPair k t := by
      induction h with
      | rel z w h => exact rawInteriorPair_rel_invariant k t ht0 ht1 h
      | refl z => rfl
      | symm z w h ih => exact ih.symm
      | trans z w u h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
    
    have raw_edge_points_related (k : J) (t : unitInterval) :
        LeanEval.Topology.ClassificationOfSurfaces.OrientableRel p n
          (rawEdgePoint k t false) (rawEdgePoint k t true) := by
      open LeanEval.Topology.ClassificationOfSurfaces in
      cases k with
      | inl k =>
        rcases k with ⟨i,b⟩
        cases b
        · simpa [rawEdgePoint_handle,bp,N] using
            (OrientableRel.a (n:=n) t i)
        · simpa [rawEdgePoint_handle,bp,N] using
            (OrientableRel.b (n:=n) t i)
      | inr u =>
        simpa [rawEdgePoint_seam,bp,N] using
          (OrientableRel.c (n:=n) t u)
    
    have raw_quotient_interior_fiber (k : J) (t : unitInterval)
        (ht0 : 0<(t:ℝ)) (ht1 : (t:ℝ)<1) (w : Complex.ClosedUnitDisc) :
        Quot.mk (LeanEval.Topology.ClassificationOfSurfaces.OrientableRel p n) (rawEdgePoint k t false)=
          Quot.mk (LeanEval.Topology.ClassificationOfSurfaces.OrientableRel p n) w ↔
          w=rawEdgePoint k t false ∨ w=rawEdgePoint k t true := by
      constructor
      · intro h
        exact (rawInteriorPair_eqv_invariant k t ht0 ht1 (Quot.eqvGen_exact h)).mp (Or.inl rfl)
      · rintro (rfl|rfl)
        · rfl
        · exact Quot.sound (raw_edge_points_related k t)
    have hpairedSquare (k : J) (t0 : unitInterval) (ht0 : 0<(t0:ℝ)) (ht1 : (t0:ℝ)<1) :
        ∃ ε : ℝ, ∃ hε : 0<ε,
          ∃ square : Metric.closedBall ((0,0):ℝ×ℝ) ε → Quot (OrientableRel p n),
            Continuous square ∧ Function.Injective square ∧
            square ⟨(0,0),by simpa [Metric.mem_closedBall] using hε.le⟩ =
              Quot.mk (OrientableRel p n) (rawEdgePoint k t0 false) := by
      let ε := min (1/4:ℝ) (min (t0:ℝ) (1-(t0:ℝ)))/2
      have hε : 0<ε := by dsimp [ε]; positivity
      have hε1 : ε<1 := by
        have hh := min_le_left (1/4:ℝ) (min (t0:ℝ) (1-(t0:ℝ)))
        dsimp [ε]; linarith
      have hεt : ε<(t0:ℝ) := by
        have h1 := min_le_right (1/4:ℝ) (min (t0:ℝ) (1-(t0:ℝ)))
        have h2 := min_le_left (t0:ℝ) (1-(t0:ℝ))
        dsimp [ε]; linarith
      have hεt1 : ε<1-(t0:ℝ) := by
        have h1 := min_le_right (1/4:ℝ) (min (t0:ℝ) (1-(t0:ℝ)))
        have h2 := min_le_right (t0:ℝ) (1-(t0:ℝ))
        dsimp [ε]; linarith
      let D := Metric.closedBall ((0,0):ℝ×ℝ) ε
      let q : Complex.ClosedUnitDisc → Quot (OrientableRel p n) := Quot.mk _
      have coords (v : D) : |v.val.1|≤ε ∧ |v.val.2|≤ε := by
        simpa only [D,Metric.mem_closedBall,dist_eq_norm,Prod.norm_def,Prod.fst_sub,
          Prod.snd_sub,Prod.fst_zero,Prod.snd_zero,sub_zero,Real.norm_eq_abs,max_le_iff] using v.property
      have htV (v : D) : 0<(t0:ℝ)+v.val.1 ∧ (t0:ℝ)+v.val.1<1 := by
        have hv := abs_le.mp (coords v).1
        constructor <;> linarith
      let T (v : D) : unitInterval := ⟨(t0:ℝ)+v.val.1,⟨(htV v).1.le,(htV v).2.le⟩⟩
      have hTc : Continuous T := (by fun_prop : Continuous (fun v : D => (t0:ℝ)+v.val.1)).subtype_mk _
      have hpn (e : Bool) (t : unitInterval) : ‖(rawEdgePoint k t e : ℂ)‖=1 := Circle.norm_coe _
      let cap (e : Bool) (v : D) : Complex.ClosedUnitDisc :=
        ⟨((1-|v.val.2|:ℝ):ℂ)*(rawEdgePoint k (T v) e : ℂ),by
          have hr : 0≤1-|v.val.2| := by linarith [(coords v).2]
          rw [Metric.mem_closedBall,dist_zero_right,norm_mul,Complex.norm_real,Real.norm_eq_abs,
            hpn, mul_one,abs_of_nonneg hr]
          linarith [abs_nonneg v.val.2]⟩
      have hb : Continuous Complex.ClosedUnitDisc.bdyPtOfReal :=
        (continuous_subtype_val.comp Real.continuous_fourierChar).subtype_mk _
      have hpc (e : Bool) : Continuous (fun t : unitInterval => rawEdgePoint k t e) := by
        dsimp [rawEdgePoint,bp]
        apply hb.comp
        cases k <;> cases e <;> dsimp [rawEdgeNumerator,rawEdgeFraction] <;> fun_prop
      have hcc (e : Bool) : Continuous (cap e) := by
        apply Continuous.subtype_mk
        exact (by fun_prop : Continuous (fun v : D => ((1-|v.val.2|:ℝ):ℂ))).mul
          (continuous_subtype_val.comp ((hpc e).comp hTc))
      have hcn (e : Bool) (v : D) : ‖(cap e v : ℂ)‖=1-|v.val.2| := by
        have hr : 0≤1-|v.val.2| := by linarith [(coords v).2]
        change ‖((1-|v.val.2|:ℝ):ℂ)*(rawEdgePoint k (T v) e : ℂ)‖=_
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,hpn,mul_one,abs_of_nonneg hr]
      have hcs (e : Bool) (v : D) (hy : v.val.2=0) : cap e v=rawEdgePoint k (T v) e := by
        apply Subtype.ext
        simp [cap,hy]
      have hseam (v : D) (hy : v.val.2=0) : q (cap false v)=q (cap true v) := by
        rw [hcs false v hy,hcs true v hy]
        exact Quot.sound (raw_edge_points_related k (T v))
      have hnormgen {z w : Complex.ClosedUnitDisc}
          (h : Relation.EqvGen (OrientableRel p n) z w) :
          (‖(z:ℂ)‖<1 ∨ ‖(w:ℂ)‖<1) → z=w := by
        induction h with
        | rel z w h =>
          intro hh
          have hn : ‖(z:ℂ)‖=1 ∧ ‖(w:ℂ)‖=1 := by cases h <;> exact ⟨Circle.norm_coe _,Circle.norm_coe _⟩
          rcases hh with hh | hh <;> linarith [hn.1,hn.2]
        | refl z => intro _; rfl
        | symm z w h ih => intro hh; exact (ih hh.symm).symm
        | trans z w v h₁ h₂ ih₁ ih₂ =>
          intro hh
          rcases hh with hz | hv
          · have he := ih₁ (Or.inl hz); subst w; exact ih₂ (Or.inl hz)
          · have he := ih₂ (Or.inr hv); subst w; exact ih₁ (Or.inr hv)
      have hfi0 (v : D) (w : Complex.ClosedUnitDisc) (he : q (cap false v)=q w) :
          w=cap false v ∨ (v.val.2=0 ∧ w=cap true v) := by
        by_cases hy : v.val.2=0
        · have hf := (raw_quotient_interior_fiber k (T v) (htV v).1 (htV v).2 w).mp
            (by simpa [hcs false v hy] using he)
          rcases hf with hf | hf
          · exact Or.inl (hf.trans (hcs false v hy).symm)
          · exact Or.inr ⟨hy,hf.trans (hcs true v hy).symm⟩
        · have hn : ‖(cap false v : ℂ)‖<1 := by rw [hcn]; linarith [abs_pos.mpr hy]
          exact Or.inl (hnormgen (Quot.eqvGen_exact he) (Or.inl hn)).symm
      have hfi1 (v : D) (w : Complex.ClosedUnitDisc) (he : q (cap true v)=q w) :
          w=cap true v ∨ (v.val.2=0 ∧ w=cap false v) := by
        by_cases hy : v.val.2=0
        · rcases hfi0 v w ((hseam v hy).trans he) with hf | ⟨_,hf⟩
          · exact Or.inr ⟨hy,hf⟩
          · exact Or.inl hf
        · have hn : ‖(cap true v : ℂ)‖<1 := by rw [hcn]; linarith [abs_pos.mpr hy]
          exact Or.inl (hnormgen (Quot.eqvGen_exact he) (Or.inl hn)).symm
      have hcxy (e f : Bool) (u v : D) (he : cap e u=cap f v) :
          u.val.1=v.val.1 ∧ |u.val.2|=|v.val.2| ∧ e=f := by
        have hn := congrArg (fun z : Complex.ClosedUnitDisc => ‖(z:ℂ)‖) he
        rw [hcn,hcn] at hn
        have hr : 1-|u.val.2|=1-|v.val.2| := hn
        have hrp : 0<1-|u.val.2| := by linarith [(coords u).2]
        have hec := congrArg (fun z : Complex.ClosedUnitDisc => (z:ℂ)) he
        change ((1-|u.val.2|:ℝ):ℂ)*(rawEdgePoint k (T u) e : ℂ)=
          ((1-|v.val.2|:ℝ):ℂ)*(rawEdgePoint k (T v) f : ℂ) at hec
        rw [← hr] at hec
        have hp := mul_left_cancel₀ (by exact_mod_cast hrp.ne' : ((1-|u.val.2|:ℝ):ℂ)≠0) hec
        have hpt : rawEdgePoint k (T u) e=rawEdgePoint k (T v) f := Subtype.ext hp
        obtain ⟨_,ht,hef⟩ := (rawEdgePoint_eq_iff k k (T u) (T v) (htV u).1 (htV u).2 e f).mp hpt
        have htv := congrArg Subtype.val ht
        change (t0:ℝ)+u.val.1=(t0:ℝ)+v.val.1 at htv
        exact ⟨by linarith,by linarith,hef⟩
      let square : D → Quot (OrientableRel p n) :=
        fun v => if v.val.2≤0 then q (cap true v) else q (cap false v)
      have hsc : Continuous square := by
        apply continuous_if_le (by fun_prop) continuous_const
          (continuous_quot_mk.comp (hcc true)).continuousOn
          (continuous_quot_mk.comp (hcc false)).continuousOn
        intro v hv
        exact (hseam v hv).symm
      have hsi : Function.Injective square := by
        intro u v he
        dsimp [square] at he
        split_ifs at he with hu hv hv
        · rcases hfi1 u (cap true v) he with hec | ⟨hy,hec⟩
          · obtain ⟨hx,hy,_⟩ := hcxy true true u v hec.symm
            apply Subtype.ext
            apply Prod.ext hx
            simpa only [abs_of_nonpos hu,abs_of_nonpos hv,neg_neg] using congrArg Neg.neg hy
          · have hh := (hcxy false true u v hec.symm).2.2
            simp at hh
        · rcases hfi1 u (cap false v) he with hec | ⟨hy,hec⟩
          · have hh := (hcxy true false u v hec.symm).2.2
            simp at hh
          · have hh := (hcxy false false u v hec.symm).2.1
            have hzero : v.val.2=0 := by simpa [hy] using hh.symm
            exact False.elim (hv (by rw [hzero]))
        · rcases hfi0 u (cap true v) he with hec | ⟨hy,hec⟩
          · have hh := (hcxy false true u v hec.symm).2.2
            simp at hh
          · exact False.elim (hu (by rw [hy]))
        · rcases hfi0 u (cap false v) he with hec | ⟨hy,hec⟩
          · obtain ⟨hx,hy,_⟩ := hcxy false false u v hec.symm
            apply Subtype.ext
            apply Prod.ext hx
            simpa only [abs_of_nonneg (not_le.mp hu).le,abs_of_nonneg (not_le.mp hv).le] using hy
          · exact False.elim (hu (by rw [hy]))
      refine ⟨ε,hε,square,hsc,hsi,?_⟩
      have hy : (⟨(0,0),by simpa [D,Metric.mem_closedBall] using hε.le⟩ : D).val.2=0 := rfl
      dsimp only [square]
      rw [if_pos (by norm_num : (0:ℝ)≤0)]
      change q (cap true _) = q (rawEdgePoint k t0 false)
      rw [← hseam _ hy,hcs false _ hy]
      apply congrArg q
      apply congrArg (fun t => rawEdgePoint k t false)
      apply Subtype.ext
      simp [T]
    have hinner {U : Set (EuclideanSpace ℝ (Fin 2))} (hU : IsOpen U)
        (f : U → Quot (OrientableRel p n)) (hfcont : Continuous f)
        (hfinj : Function.Injective f) (u : U) :
        (modelWithCornersEuclideanHalfSpace 2).IsInteriorPoint (f u) := by
      let I := modelWithCornersEuclideanHalfSpace 2
      let c : PartialEquiv (Quot (OrientableRel p n)) (EuclideanSpace ℝ (Fin 2)) := extChartAt I (f u)
      let f₀ : (EuclideanSpace ℝ (Fin 2)) → (Quot (OrientableRel p n)) :=
        Function.extend ((↑) : U → (EuclideanSpace ℝ (Fin 2))) f (fun _ ↦ f u)
      have hf₀_eq (x : U) : f₀ x.1 = f x := by
        exact Function.Injective.extend_apply Subtype.val_injective f
          (fun _ ↦ f u) x
      have hf₀_cont : ContinuousOn f₀ U := by
        rw [continuousOn_iff_continuous_restrict]
        convert hfcont using 1
        funext x
        exact hf₀_eq x
      let W : Set (EuclideanSpace ℝ (Fin 2)) := U ∩ f₀ ⁻¹' c.source
      have hWopen : IsOpen W :=
        hf₀_cont.isOpen_inter_preimage hU (isOpen_extChartAt_source (I := I) (f u))
      have huW : u.1 ∈ W := by
        refine ⟨u.2, ?_⟩
        change f₀ u.1 ∈ c.source
        rw [hf₀_eq u]
        exact mem_extChartAt_source (I := I) (f u)
      let g : (EuclideanSpace ℝ (Fin 2)) → (EuclideanSpace ℝ (Fin 2)) := fun x ↦ c (f₀ x)
      have hg_cont : ContinuousOn g W := by
        apply (continuousOn_extChartAt (I := I) (f u)).comp
          (hf₀_cont.mono inter_subset_left)
        exact fun x hx ↦ hx.2
      have hg_inj : Set.InjOn g W := by
        intro x hx y hy hxy
        have hf₀xy : f₀ x = f₀ y :=
          c.injOn hx.2 hy.2 hxy
        have hfx :
            f (⟨x, hx.1⟩ : U) = f (⟨y, hy.1⟩ : U) := by
          rw [← hf₀_eq ⟨x, hx.1⟩, ← hf₀_eq ⟨y, hy.1⟩]
          exact hf₀xy
        exact congrArg Subtype.val (hfinj hfx)
      let φ : PartialEquiv (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) :=
        hg_inj.toPartialEquiv g W
      have hφ_cont : ContinuousOn φ φ.source := by
        change ContinuousOn g W
        exact hg_cont
      have hWnhds : W ∈ nhds u.1 :=
        hWopen.mem_nhds huW
      have himage :
          g '' W ∈ nhds (g u.1) := by
        have h :=
          maps_nhds_to_nhds (EuclideanSpace ℝ (Fin 2)) hφ_cont hWnhds
            (show W ⊆ φ.source by
              change W ⊆ W
              exact subset_rfl)
        change g '' W ∈ nhds (g u.1) at h
        exact h
      have hsub : g '' W ⊆ Set.range I := by
        rintro y ⟨x,hx,rfl⟩
        exact Set.mem_range_self ((chartAt (EuclideanHalfSpace 2) (f u)) (f₀ x))
      have hr : Set.range I ∈ nhds (g u.val) := Filter.mem_of_superset himage hsub
      apply (isInteriorPoint_iff_any_chart I (ChartedSpace.mem_chart_source (f u))).mpr
      change c (f u) ∈ interior (Set.range I)
      rw [mem_interior_iff_mem_nhds]
      convert hr using 1
      congr 1
      change c (f u) = c (f₀ u.val)
      rw [hf₀_eq u]
    have hpairedInterior (k : J) (t : unitInterval) (ht0 : 0<(t:ℝ)) (ht1 : (t:ℝ)<1) :
        (modelWithCornersEuclideanHalfSpace 2).IsInteriorPoint
          (Quot.mk (OrientableRel p n) (rawEdgePoint k t false)) := by
      obtain ⟨ε,hε,square,hsc,hsi,hs0⟩ := hpairedSquare k t ht0 ht1
      let D := Metric.closedBall ((0,0):ℝ×ℝ) ε
      let L := Complex.orthonormalBasisOneI.repr.symm
      let P (v : EuclideanSpace ℝ (Fin 2)) : ℝ×ℝ := ((L v).re,(L v).im)
      have hPc : Continuous P := (Complex.continuous_re.comp L.continuous).prodMk
        (Complex.continuous_im.comp L.continuous)
      have hPi : Function.Injective P := by
        intro v w he
        apply L.injective
        apply Complex.ext
        · exact congrArg Prod.fst he
        · exact congrArg Prod.snd he
      have hPn (v : EuclideanSpace ℝ (Fin 2)) : ‖P v‖≤‖v‖ := by
        rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs]
        apply max_le_iff.mpr
        rw [← L.norm_map v]
        exact ⟨Complex.abs_re_le_norm _,Complex.abs_im_le_norm _⟩
      let U := Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) ε
      let into (v : U) : D := ⟨P v.val,by
        rw [Metric.mem_closedBall]
        change dist (P v.val) (0 : ℝ×ℝ) ≤ ε
        rw [dist_zero_right]
        have hv : ‖v.val‖<ε := by simpa only [U,Metric.mem_ball,dist_zero_right] using v.property
        exact (hPn v.val).trans hv.le⟩
      have hic : Continuous into := (hPc.comp continuous_subtype_val).subtype_mk _
      let f : U → Quot (OrientableRel p n) := square ∘ into
      have hfc : Continuous f := hsc.comp hic
      have hfi : Function.Injective f := by
        intro v w he
        apply Subtype.ext
        apply hPi
        exact congrArg Subtype.val (hsi he)
      let u0 : U := ⟨0,by simpa [U,Metric.mem_ball] using hε⟩
      have hi := hinner Metric.isOpen_ball f hfc hfi u0
      have hp0 : into u0 = ⟨(0,0),by simpa [D,Metric.mem_closedBall] using hε.le⟩ := by
        apply Subtype.ext
        simp [into,u0,P,L]
      change (modelWithCornersEuclideanHalfSpace 2).IsInteriorPoint (square (into u0)) at hi
      rw [hp0,hs0] at hi
      exact hi
    constructor
    · intro i t ht0 ht1
      have h := hpairedInterior (.inl (i,false)) t ht0 ht1
      rw [rawEdgePoint_handle] at h
      simpa [bp,N] using h
    · constructor
      · intro i t ht0 ht1
        have h := hpairedInterior (.inl (i,true)) t ht0 ht1
        rw [rawEdgePoint_handle] at h
        simpa [bp,N] using h
      · intro i t ht0 ht1
        have h := hpairedInterior (.inr i) t ht0 ht1
        rw [rawEdgePoint_seam] at h
        simpa [bp,N] using h
  have hnormalized (z : Complex.ClosedUnitDisc) (hz : ‖z.val‖=1) :
    ∃ x : ℝ, -3*(n:ℝ)≤x ∧ x≤4*(p:ℝ) ∧
      Complex.ClosedUnitDisc.bdyPtOfReal (x/(4*(p:ℝ)+3*(n:ℝ)))=z := by
    let N : ℝ := 4*(p:ℝ)+3*(n:ℝ)
    have hN : 0<N := by
      dsimp [N]
      rcases hadmissible with hp | hn
      · have hp' : (1:ℝ)≤p := by exact_mod_cast hp
        positivity
      · have hn' : (1:ℝ)≤n := by exact_mod_cast hn
        positivity
    let c : Circle := ⟨z.val,mem_sphere_zero_iff_norm.mpr hz⟩
    obtain ⟨θ,hθ⟩ := Circle.exp_surjective c
    let r := θ/(2*Real.pi)
    have hbd : Complex.ClosedUnitDisc.bdyPtOfReal r=z := by
      apply Subtype.ext
      change (Real.fourierChar r : ℂ)=z.val
      rw [Real.fourierChar_apply']
      have he : 2*Real.pi*r=θ := by dsimp [r]; field_simp
      rw [he]
      exact congrArg (fun c : Circle => (c:ℂ)) hθ
    let s : ℝ := r-(Int.floor r:ℝ)
    have hs0 : 0 ≤ s := Int.fract_nonneg r
    have hs1 : s < 1 := Int.fract_lt_one r
    have hbs : Complex.ClosedUnitDisc.bdyPtOfReal s=z := by
      calc
        _ = Complex.ClosedUnitDisc.bdyPtOfReal (r+(-Int.floor r:ℤ)) := by congr 1; change r-(Int.floor r:ℝ)=r+(-Int.floor r:ℤ); push_cast; ring
        _ = Complex.ClosedUnitDisc.bdyPtOfReal r := Complex.ClosedUnitDisc.bdyPtOfReal_add_int _ _
        _ = z := hbd
    let y := s*N
    have hy0 : 0≤y := mul_nonneg hs0 hN.le
    have hy1 : y<N := by dsimp [y]; nlinarith
    by_cases hyl : y≤4*(p:ℝ)
    · refine ⟨y,?_,hyl,?_⟩
      · linarith [Nat.cast_nonneg (α:=ℝ) n]
      · change Complex.ClosedUnitDisc.bdyPtOfReal (y/N)=z
        have he : y/N=s := by dsimp [y]; field_simp
        rw [he]
        exact hbs
    · refine ⟨y-N,?_,?_,?_⟩
      · dsimp [N] at *
        linarith
      · linarith [Nat.cast_nonneg (α:=ℝ) p]
      · change Complex.ClosedUnitDisc.bdyPtOfReal ((y-N)/N)=z
        have he : (y-N)/N=s+(-1:ℤ) := by dsimp [y]; push_cast; field_simp; ring
        rw [he,Complex.ClosedUnitDisc.bdyPtOfReal_add_int]
        exact hbs
  have hpartition (x : ℝ) (hx0 : -3*(n:ℝ)≤x) (hx1 : x≤4*(p:ℝ)) :
    (∃ m : ℤ, -3*(n:ℤ) ≤ m ∧ m ≤ 4*(p:ℤ) ∧ x = m) ∨
    (∃ (i : Fin p) (t : unitInterval), 0 < (t:ℝ) ∧ (t:ℝ) < 1 ∧
      (x = 4*(i.val:ℝ)+(t:ℝ) ∨ x = 4*(i.val:ℝ)+3-(t:ℝ) ∨
       x = 4*(i.val:ℝ)+1+(t:ℝ) ∨ x = 4*(i.val:ℝ)+4-(t:ℝ))) ∨
    (∃ (i : Fin n) (t : unitInterval), 0 < (t:ℝ) ∧ (t:ℝ) < 1 ∧
      (x = -(3*(i.val:ℝ)+(t:ℝ)) ∨ x = -(3*(i.val:ℝ)+3-(t:ℝ)) ∨
       x = -(3*(i.val:ℝ)+1+(t:ℝ)))) := by
    let m : ℤ := Int.floor x
    let u : ℝ := x-(m:ℝ)
    have hu0 : 0 ≤ u := Int.fract_nonneg x
    have hu1 : u < 1 := Int.fract_lt_one x
    have heq : x = (m:ℝ)+u := by dsimp [u]; ring
    have hm0 : -3*(n:ℤ) ≤ m := by
      apply Int.le_floor.mpr
      simpa only [Int.cast_mul,Int.cast_neg,Int.cast_ofNat,Int.cast_natCast] using hx0
    by_cases hu : u = 0
    · left
      have hxm : x = (m:ℝ) := by linarith
      have hm1 : m ≤ 4*(p:ℤ) := by exact_mod_cast (show (m:ℝ) ≤ 4*(p:ℝ) by linarith)
      exact ⟨m,hm0,hm1,hxm⟩
    · have hup : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hu)
      have hm1 : m < 4*(p:ℤ) := by exact_mod_cast (show (m:ℝ) < 4*(p:ℝ) by linarith)
      let tU : unitInterval := ⟨u,⟨hu0,hu1.le⟩⟩
      let tV : unitInterval := ⟨1-u,⟨by linarith,by linarith⟩⟩
      have htV0 : 0 < (tV:ℝ) := by change 0 < 1-u; linarith
      have htV1 : (tV:ℝ) < 1 := by change 1-u < 1; linarith
      by_cases hmp : 0 ≤ m
      · let q : ℤ := m/4
        have hq0 : 0 ≤ q := by dsimp [q]; omega
        have hq1 : q < (p:ℤ) := by dsimp [q]; omega
        let i : Fin p := ⟨q.toNat,by omega⟩
        have hi : (i.val:ℤ) = q := by exact Int.toNat_of_nonneg hq0
        have hd : m = 4*(i.val:ℤ)+m%4 := by dsimp [i,q]; omega
        have hdR : (m:ℝ)=4*(i.val:ℝ)+((m%4:ℤ):ℝ) := by exact_mod_cast hd
        have hr : m%4 = 0 ∨ m%4 = 1 ∨ m%4 = 2 ∨ m%4 = 3 := by omega
        rcases hr with hr | hr | hr | hr
        · right; left
          refine ⟨i,tU,hup,hu1,Or.inl ?_⟩
          rw [hr] at hdR
          change x = 4*(i.val:ℝ)+u
          push_cast at hdR
          linarith
        · right; left
          refine ⟨i,tU,hup,hu1,Or.inr (Or.inr (Or.inl ?_))⟩
          rw [hr] at hdR
          change x = 4*(i.val:ℝ)+1+u
          push_cast at hdR
          linarith
        · right; left
          refine ⟨i,tV,htV0,htV1,Or.inr (Or.inl ?_)⟩
          rw [hr] at hdR
          change x = 4*(i.val:ℝ)+3-(1-u)
          push_cast at hdR
          linarith
        · right; left
          refine ⟨i,tV,htV0,htV1,Or.inr (Or.inr (Or.inr ?_))⟩
          rw [hr] at hdR
          change x = 4*(i.val:ℝ)+4-(1-u)
          push_cast at hdR
          linarith
      · let a : ℤ := -m-1
        have ha0 : 0 ≤ a := by dsimp [a]; omega
        have ha1 : a < 3*(n:ℤ) := by dsimp [a]; omega
        let q : ℤ := a/3
        have hq0 : 0 ≤ q := by dsimp [q]; omega
        have hq1 : q < (n:ℤ) := by dsimp [q]; omega
        let i : Fin n := ⟨q.toNat,by omega⟩
        have hd : m = -3*(i.val:ℤ)-1-a%3 := by dsimp [i,q,a]; omega
        have hdR : (m:ℝ)=-3*(i.val:ℝ)-1-((a%3:ℤ):ℝ) := by exact_mod_cast hd
        have hr : a%3 = 0 ∨ a%3 = 1 ∨ a%3 = 2 := by omega
        rcases hr with hr | hr | hr
        · right; right
          refine ⟨i,tV,htV0,htV1,Or.inl ?_⟩
          rw [hr] at hdR
          change x = -(3*(i.val:ℝ)+(1-u))
          push_cast at hdR
          linarith
        · right; right
          refine ⟨i,tV,htV0,htV1,Or.inr (Or.inr ?_)⟩
          rw [hr] at hdR
          change x = -(3*(i.val:ℝ)+1+(1-u))
          push_cast at hdR
          linarith
        · right; right
          refine ⟨i,tU,hup,hu1,Or.inr (Or.inl ?_)⟩
          rw [hr] at hdR
          change x = -(3*(i.val:ℝ)+3-u)
          push_cast at hdR
          linarith
  have havoid (x : Quot (OrientableRel p n)) (hx : I.IsBoundaryPoint x)
      (s : Set (Quot (OrientableRel p n))) (hs : IsOpen s) (hxs : x ∈ s)
      (F : Set (Quot (OrientableRel p n))) (hF : F.Finite) :
      ∃ y, y ∉ F ∧ y ∈ s ∧ I.IsBoundaryPoint y := by
    let I := modelWithCornersEuclideanHalfSpace 2
    let c := chartAt (EuclideanHalfSpace 2) x
    have hxc : x ∈ c.source := mem_chart_source _ x
    have hn := (InvarianceOfDomain.isBoundaryPoint_iff_any_chart I hxc).mp hx
    rw [frontier_range_modelWithCornersEuclideanHalfSpace] at hn
    change 0 = (c x).val 0 at hn
    let line (t : ℝ) : EuclideanHalfSpace 2 :=
      ⟨WithLp.toLp 2 (fun i : Fin 2 => if i=0 then 0 else t),by simp⟩
    have hl : Continuous line := by
      apply Continuous.subtype_mk
      apply (PiLp.continuous_toLp 2 _).comp
      apply continuous_pi
      intro i
      fin_cases i <;> simp only [Fin.isValue,Fin.zero_eta,↓reduceIte,Fin.mk_one,one_ne_zero] <;> fun_prop
    let t0 : ℝ := (c x).val 1
    have hline : line t0 = c x := by
      apply Subtype.ext
      apply PiLp.ext
      intro i
      fin_cases i
      · exact hn
      · rfl
    let T : Set ℝ := line ⁻¹' (c.target ∩ c.symm ⁻¹' s)
    have hT : IsOpen T :=
      (c.symm.continuousOn.isOpen_inter_preimage c.open_target hs).preimage hl
    have ht0 : t0 ∈ T := by
      change line t0 ∈ c.target ∧ c.symm (line t0) ∈ s
      rw [hline,c.left_inv hxc]
      exact ⟨c.map_source hxc,hxs⟩
    obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hT t0 ht0
    obtain ⟨t1,htI,htF⟩ := (Set.Ioo_infinite (show t0 < t0+ε by linarith)).exists_notMem_finite
      (hF.image (fun y => (c y).val 1))
    have ht1 : t1 ∈ T := by
      apply hball
      rw [Metric.mem_ball,Real.dist_eq,abs_of_pos (by linarith [htI.1] : 0 < t1-t0)]
      linarith [htI.2]
    have htar : line t1 ∈ c.target := ht1.1
    refine ⟨c.symm (line t1),?_,ht1.2,?_⟩
    · intro hy
      apply htF
      refine ⟨c.symm (line t1),hy,?_⟩
      change (c (c.symm (line t1))).val 1 = t1
      rw [c.right_inv htar]
      rfl
    · rw [InvarianceOfDomain.isBoundaryPoint_iff_any_chart I (c.map_target htar),
        frontier_range_modelWithCornersEuclideanHalfSpace,c.right_inv htar]
      change 0=0
      rfl
  let F : Set (Quot (OrientableRel p n)) :=
    (Set.Icc (-3*(n:ℤ)) (4*(p:ℤ))).image (fun m : ℤ => q (bp (m:ℝ)))
  have hF : F.Finite := (Set.finite_Icc (-3*(n:ℤ)) (4*(p:ℤ))).image _
  have hcover : I.boundary (Quot (OrientableRel p n)) ⊆ B ∪ F := by
    intro y hy
    obtain ⟨z,rfl⟩ := Quot.exists_rep y
    have hzn : ‖z.val‖≤1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using z.property
    by_cases hzi : ‖z.val‖<1
    · exact False.elim ((I.isInteriorPoint_iff_not_isBoundaryPoint (q z)).mp (hdisk z hzi) hy)
    have hzone : ‖z.val‖=1 := by linarith
    obtain ⟨x,hx0,hx1,hxz⟩ := hnormalized z hzone
    rw [← hxz] at hy ⊢
    rcases hpartition x hx0 hx1 with hm | hp | hn
    · right
      obtain ⟨m,hm0,hm1,hxm⟩ := hm
      refine ⟨m,⟨hm0,hm1⟩,?_⟩
      rw [hxm]
    · obtain ⟨i,t,ht0,ht1,he⟩ := hp
      have hint : I.IsInteriorPoint (q (bp x)) := by
        rcases he with he | he | he | he
        · rw [he]
          exact hpairs.1 i t ht0 ht1
        · rw [he]
          have hr := Quot.sound (OrientableRel.a (n:=n) t i)
          change q (bp (4*(i.val:ℝ)+(t:ℝ))) = q (bp (4*(i.val:ℝ)+3-(t:ℝ))) at hr
          rw [← hr]
          exact hpairs.1 i t ht0 ht1
        · rw [he]
          exact hpairs.2.1 i t ht0 ht1
        · rw [he]
          have hr := Quot.sound (OrientableRel.b (n:=n) t i)
          change q (bp (4*(i.val:ℝ)+1+(t:ℝ))) = q (bp (4*(i.val:ℝ)+4-(t:ℝ))) at hr
          rw [← hr]
          exact hpairs.2.1 i t ht0 ht1
      exact False.elim ((I.isInteriorPoint_iff_not_isBoundaryPoint _).mp hint hy)
    · obtain ⟨i,t,ht0,ht1,he⟩ := hn
      rcases he with he | he | he
      · have hint : I.IsInteriorPoint (q (bp x)) := by rw [he]; exact hpairs.2.2 i t ht0 ht1
        exact False.elim ((I.isInteriorPoint_iff_not_isBoundaryPoint _).mp hint hy)
      · have hint : I.IsInteriorPoint (q (bp x)) := by
          rw [he]
          have hr := Quot.sound (OrientableRel.c (p:=p) t i)
          change q (bp (-(3*(i.val:ℝ)+(t:ℝ)))) = q (bp (-(3*(i.val:ℝ)+3-(t:ℝ)))) at hr
          rw [← hr]
          exact hpairs.2.2 i t ht0 ht1
        exact False.elim ((I.isInteriorPoint_iff_not_isBoundaryPoint _).mp hint hy)
      · left
        refine ⟨(i,t),?_⟩
        rw [he]
  have hb : I.boundary (Quot (OrientableRel p n)) = B := by
    apply Set.Subset.antisymm
    · intro x hx
      by_contra hn
      obtain ⟨y,hyF,hyB,hy⟩ := havoid x hx Bᶜ hcircles.2.isOpen_compl hn F hF
      rcases hcover hy with hy' | hy'
      · exact hyB hy'
      · exact hyF hy'
    · exact hincl
  have hn1 (hn : n=1) : B = hn.symm ▸ ActualOneBoundaryOrientableBoundary p := by
    subst n
    ext x
    constructor
    · rintro ⟨⟨j,t⟩,rfl⟩
      have hj : j=0 := Subsingleton.elim _ _
      subst j
      refine ⟨t,?_⟩
      simp [q,bp,N]
    · rintro ⟨t,rfl⟩
      refine ⟨(0,t),?_⟩
      simp [q,bp,N]
  constructor
  · obtain ⟨e⟩ := hcircles.1
    exact ⟨((Homeomorph.refl (Quot (OrientableRel p n))).subtype
      (fun x => Set.ext_iff.mp hb x)).trans e⟩
  · intro hn
    exact hb.trans (hn1 hn)
end CurveComplex.Hyperbolic
