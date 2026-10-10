import CurveComplexGenusTwo.Topology.ActualClosedOrientableHomology.ActualClosedBoundaryDefinitions
import CurveComplexGenusTwo.CWHurewicz.CircleFundamentalCycle
import ClassificationOfSurfaces.LeanEval.ChallengeDeps
open CategoryTheory CategoryTheory.Limits Convexity
open CurveComplexGenusTwo.CWHurewicz
open CurveComplex.Hyperbolic
open LeanEval.Topology.ClassificationOfSurfaces
open scoped Simplicial
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
set_option maxRecDepth 7000
open CircleFundamentalCycle
namespace CurveComplex.Hyperbolic
theorem actual_closed_orientable_attaching_map_homology_one_zero
    (p : ℕ) (hp : 1 ≤ p) :
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).map
        (TopCat.ofHom (actualClosedOrientableAttachingMap p))) = 0 := by
  have hchain (p : ℕ) (hp : 1 ≤ p) :
      (mvAmbientComplex (TopCat.of (ActualClosedOrientableBoundaryGraph p))).pOpcycles 1
        ((singularFinsuppMap (TopCat.ofHom (actualClosedOrientableAttachingMap p))).f 1
          CircleFundamentalCycle.circleBoundaryChain)=0 := by
    have hfull (p : ℕ) (hp : 1 ≤ p) :
        ∃ seg : ℝ → ℝ → (TopCat.toSSet.obj (TopCat.of (ActualClosedOrientableBoundaryGraph p))) _⦋1⦌,
          (∀ a b z, TopCat.toSSetObjEquiv (TopCat.of (ActualClosedOrientableBoundaryGraph p)) (.op ⦋1⦌) (seg a b) z =
            actualClosedOrientableAttachingMap p (Real.fourierChar ((a+(b-a)*z.weights 1)/(4*(p:ℝ))))) ∧
          (∀ a b c, (mvAmbientComplex (TopCat.of (ActualClosedOrientableBoundaryGraph p))).pOpcycles 1 (Finsupp.single (seg a c) (1:ℤ)) =
            (mvAmbientComplex (TopCat.of (ActualClosedOrientableBoundaryGraph p))).pOpcycles 1 (Finsupp.single (seg a b) (1:ℤ)) +
            (mvAmbientComplex (TopCat.of (ActualClosedOrientableBoundaryGraph p))).pOpcycles 1 (Finsupp.single (seg b c) (1:ℤ))) ∧
          (mvAmbientComplex (TopCat.of (ActualClosedOrientableBoundaryGraph p))).pOpcycles 1
            (Finsupp.single (seg 0 (4*(p:ℝ))) (1:ℤ))=0 := by
      have hPaired (p : ℕ) (hp : 1 ≤ p) :
        ∃ seg : ℝ → ℝ → (TopCat.toSSet.obj (TopCat.of (ActualClosedOrientableBoundaryGraph p))) _⦋1⦌,
          (∀ a b z, TopCat.toSSetObjEquiv (TopCat.of (ActualClosedOrientableBoundaryGraph p)) (.op ⦋1⦌) (seg a b) z =
            actualClosedOrientableAttachingMap p (Real.fourierChar ((a+(b-a)*z.weights 1)/(4*(p:ℝ))))) ∧
          (∀ a b c, (mvAmbientComplex (TopCat.of (ActualClosedOrientableBoundaryGraph p))).pOpcycles 1 (Finsupp.single (seg a c) (1:ℤ)) =
            (mvAmbientComplex (TopCat.of (ActualClosedOrientableBoundaryGraph p))).pOpcycles 1 (Finsupp.single (seg a b) (1:ℤ)) +
            (mvAmbientComplex (TopCat.of (ActualClosedOrientableBoundaryGraph p))).pOpcycles 1 (Finsupp.single (seg b c) (1:ℤ))) ∧
          (∀ a, (mvAmbientComplex (TopCat.of (ActualClosedOrientableBoundaryGraph p))).pOpcycles 1 (Finsupp.single (seg a a) (1:ℤ))=0) ∧
          (∀ i : Fin p, seg (4*(i:ℝ)+2) (4*(i:ℝ)+3)=seg (4*(i:ℝ)+1) (4*(i:ℝ))) ∧
          (∀ i : Fin p, seg (4*(i:ℝ)+3) (4*(i:ℝ)+4)=seg (4*(i:ℝ)+2) (4*(i:ℝ)+1)) := by
        have hAffineActual (p : ℕ) (hp : 1 ≤ p) :
          ∃ f : C(ℝ,ActualClosedOrientableBoundaryGraph p),
            (∀ t, f t=actualClosedOrientableAttachingMap p (Real.fourierChar (t/(4*(p:ℝ))))) ∧
            ∃ seg : ℝ → ℝ → (TopCat.toSSet.obj (TopCat.of (ActualClosedOrientableBoundaryGraph p))) _⦋1⦌,
              (∀ a b z, TopCat.toSSetObjEquiv (TopCat.of (ActualClosedOrientableBoundaryGraph p)) (.op ⦋1⦌) (seg a b) z =
                f (a+(b-a)*z.weights 1)) ∧
              ∀ a b c, (mvAmbientComplex (TopCat.of (ActualClosedOrientableBoundaryGraph p))).pOpcycles 1 (Finsupp.single (seg a c) (1:ℤ)) =
                (mvAmbientComplex (TopCat.of (ActualClosedOrientableBoundaryGraph p))).pOpcycles 1 (Finsupp.single (seg a b) (1:ℤ)) +
                (mvAmbientComplex (TopCat.of (ActualClosedOrientableBoundaryGraph p))).pOpcycles 1 (Finsupp.single (seg b c) (1:ℤ)) := by
          have hAffine (X : Type) [TopologicalSpace X] (f : C(ℝ,X)) :
            ∃ seg : ℝ → ℝ → (TopCat.toSSet.obj (TopCat.of X)) _⦋1⦌,
              (∀ a b z, TopCat.toSSetObjEquiv (TopCat.of X) (.op ⦋1⦌) (seg a b) z =
                f (a+(b-a)*z.weights 1)) ∧
              ∀ a b c, (mvAmbientComplex (TopCat.of X)).pOpcycles 1 (Finsupp.single (seg a c) (1:ℤ)) =
                (mvAmbientComplex (TopCat.of X)).pOpcycles 1 (Finsupp.single (seg a b) (1:ℤ)) +
                (mvAmbientComplex (TopCat.of X)).pOpcycles 1 (Finsupp.single (seg b c) (1:ℤ)) := by
            classical
            let T := TopCat.of X
            let C := mvAmbientComplex T
            let Sing (n : ℕ) := (TopCat.toSSet.obj T) _⦋n⦌
            let seg (a b : ℝ) : Sing 1 :=
              (TopCat.toSSetObjEquiv T (.op ⦋1⦌)).symm
                ⟨fun z => f (a+(b-a)*z.weights 1),f.continuous.comp (by fun_prop)⟩
            let tri (a b c : ℝ) : Sing 2 :=
              (TopCat.toSSetObjEquiv T (.op ⦋2⦌)).symm
                ⟨fun z => f (a*z.weights 0+b*z.weights 1+c*z.weights 2),f.continuous.comp (by fun_prop)⟩
            have hsum (z : StdSimplex ℝ (Fin 2)) : z.weights 0+z.weights 1=1 := by
              have hz := z.total
              rw [Finsupp.sum_fintype] at hz <;> try { intro i; rfl }
              change (∑ i : Fin 2, z.weights i)=1 at hz
              simpa [Fin.sum_univ_two] using hz
            have hface0 (a b c : ℝ) : (TopCat.toSSet.obj T).δ 0 (tri a b c)=seg b c := by
              apply (TopCat.toSSetObjEquiv T (.op ⦋1⦌)).injective
              apply ContinuousMap.ext
              intro z
              change f (a*(z.map (0:Fin 3).succAbove).weights 0+
                b*(z.map (0:Fin 3).succAbove).weights 1+c*(z.map (0:Fin 3).succAbove).weights 2)=_
              apply congrArg f
              simp [StdSimplex.weights_map,Finsupp.mapDomain,Finsupp.sum_fintype,Fin.sum_univ_two,Fin.succAbove]
              linear_combination b * hsum z
            have hface1 (a b c : ℝ) : (TopCat.toSSet.obj T).δ 1 (tri a b c)=seg a c := by
              apply (TopCat.toSSetObjEquiv T (.op ⦋1⦌)).injective
              apply ContinuousMap.ext
              intro z
              change f (a*(z.map (1:Fin 3).succAbove).weights 0+
                b*(z.map (1:Fin 3).succAbove).weights 1+c*(z.map (1:Fin 3).succAbove).weights 2)=_
              apply congrArg f
              simp [StdSimplex.weights_map,Finsupp.mapDomain,Finsupp.sum_fintype,Fin.sum_univ_two,Fin.succAbove]
              linear_combination a * hsum z
            have hface2 (a b c : ℝ) : (TopCat.toSSet.obj T).δ 2 (tri a b c)=seg a b := by
              apply (TopCat.toSSetObjEquiv T (.op ⦋1⦌)).injective
              apply ContinuousMap.ext
              intro z
              change f (a*(z.map (2:Fin 3).succAbove).weights 0+
                b*(z.map (2:Fin 3).succAbove).weights 1+c*(z.map (2:Fin 3).succAbove).weights 2)=_
              apply congrArg f
              simp [StdSimplex.weights_map,Finsupp.mapDomain,Finsupp.sum_fintype,Fin.sum_univ_two,Fin.succAbove]
              linear_combination a * hsum z
            have hb (a b c : ℝ) : singularBoundaryFinsupp T 1 (Finsupp.single (tri a b c) (1:ℤ))=
                Finsupp.single (seg b c) 1-Finsupp.single (seg a c) 1+Finsupp.single (seg a b) 1 := by
              rw [singularBoundaryFinsupp_single]
              simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
              norm_num only [Fin.val_zero,Fin.val_succ,pow_zero,pow_one,pow_two]
              simp only [one_smul,neg_one_smul]
              change Finsupp.single ((TopCat.toSSet.obj T).δ 0 (tri a b c)) (1:ℤ)+
                (-(Finsupp.single ((TopCat.toSSet.obj T).δ 1 (tri a b c)) (1:ℤ))+
                  Finsupp.single ((TopCat.toSSet.obj T).δ 2 (tri a b c)) (1:ℤ))=_
              rw [hface0,hface1,hface2]
              abel
            refine ⟨seg,fun _ _ _ => rfl,?_⟩
            intro a b c
            have he := congrArg (fun m => m (Finsupp.single (tri a b c) (1:ℤ))) (C.d_pOpcycles 2 1)
            change C.pOpcycles 1 (singularBoundaryFinsupp T 1 (Finsupp.single (tri a b c) (1:ℤ)))=0 at he
            rw [hb,map_add,map_sub] at he
            apply sub_eq_zero.mp
            calc
              _ = -(C.pOpcycles 1 (Finsupp.single (seg b c) (1:ℤ))-
                C.pOpcycles 1 (Finsupp.single (seg a c) (1:ℤ))+
                  C.pOpcycles 1 (Finsupp.single (seg a b) (1:ℤ))) := by abel
              _ = 0 := by rw [he,neg_zero]
          let f : C(ℝ,ActualClosedOrientableBoundaryGraph p) :=
            (actualClosedOrientableAttachingMap p).comp
              ⟨fun t => Real.fourierChar (t/(4*(p:ℝ))),Real.continuous_fourierChar.comp (continuous_id.div_const _)⟩
          obtain ⟨seg,hseg,hadd⟩ := hAffine (ActualClosedOrientableBoundaryGraph p) f
          exact ⟨f,fun _ => rfl,seg,hseg,hadd⟩
        obtain ⟨f,hf,seg,hseg,hadd⟩ := hAffineActual p hp
        let T := TopCat.of (ActualClosedOrientableBoundaryGraph p)
        let C := mvAmbientComplex T
        let v (a b : ℝ) := C.pOpcycles 1 (Finsupp.single (seg a b) (1:ℤ))
        have hzero (a : ℝ) : v a a=0 := by
          have h := hadd a a a
          change v a a=v a a+v a a at h
          have hz : v a a+0=v a a+v a a := by simpa using h
          exact (add_left_cancel hz).symm
        have hformula (a b : ℝ) (z : StdSimplex ℝ (Fin 2)) :
            TopCat.toSSetObjEquiv T (.op ⦋1⦌) (seg a b) z=
              actualClosedOrientableAttachingMap p (Real.fourierChar ((a+(b-a)*z.weights 1)/(4*(p:ℝ)))) :=
          (hseg a b z).trans (hf _)
        refine ⟨seg,hformula,hadd,hzero,?_,?_⟩
        · intro i
          apply (TopCat.toSSetObjEquiv T (.op ⦋1⦌)).injective
          apply ContinuousMap.ext
          intro z
          rw [hformula,hformula]
          apply Subtype.ext
          let t : unitInterval := ⟨z.weights 1,z.weights_nonneg 1,z.weights_apply_le_one 1⟩
          have h := Quot.sound (OrientableRel.a (p:=p) (n:=0) (unitInterval.symm t) i)
          simp only [Nat.cast_zero,mul_zero,add_zero] at h
          change Quot.mk (OrientableRel p 0) (Complex.ClosedUnitDisc.bdyPtOfReal _)=
            Quot.mk (OrientableRel p 0) (Complex.ClosedUnitDisc.bdyPtOfReal _)
          convert h.symm using 1 <;> congr 2 <;> change _=_ <;> dsimp [t] <;> ring
        · intro i
          apply (TopCat.toSSetObjEquiv T (.op ⦋1⦌)).injective
          apply ContinuousMap.ext
          intro z
          rw [hformula,hformula]
          apply Subtype.ext
          let t : unitInterval := ⟨z.weights 1,z.weights_nonneg 1,z.weights_apply_le_one 1⟩
          have h := Quot.sound (OrientableRel.b (p:=p) (n:=0) (unitInterval.symm t) i)
          simp only [Nat.cast_zero,mul_zero,add_zero] at h
          change Quot.mk (OrientableRel p 0) (Complex.ClosedUnitDisc.bdyPtOfReal _)=
            Quot.mk (OrientableRel p 0) (Complex.ClosedUnitDisc.bdyPtOfReal _)
          convert h.symm using 1 <;> congr 2 <;> change _=_ <;> dsimp [t] <;> ring
      obtain ⟨seg,hformula,hadd,hzero,hpairA,hpairB⟩ := hPaired p hp
      let C := mvAmbientComplex (TopCat.of (ActualClosedOrientableBoundaryGraph p))
      let v (a b : ℝ) := C.pOpcycles 1 (Finsupp.single (seg a b) (1:ℤ))
      have hv (a b c : ℝ) : v a c=v a b+v b c := hadd a b c
      have hreverse (a b : ℝ) : v b a= -v a b := by
        have hh := hv a b a
        change C.pOpcycles 1 (Finsupp.single (seg a a) (1:ℤ))=v a b+v b a at hh
        rw [hzero] at hh
        exact eq_neg_of_add_eq_zero_right hh.symm
      have hblock (i : Fin p) : v (4*(i:ℝ)) (4*(i:ℝ)+4)=0 := by
        let x : ℝ := 4*(i:ℝ)
        have ha : v (x+2) (x+3)= -v x (x+1) := by
          change C.pOpcycles 1 (Finsupp.single (seg (x+2) (x+3)) (1:ℤ))=_
          rw [hpairA]
          exact hreverse x (x+1)
        have hb : v (x+3) (x+4)= -v (x+1) (x+2) := by
          change C.pOpcycles 1 (Finsupp.single (seg (x+3) (x+4)) (1:ℤ))=_
          rw [hpairB]
          exact hreverse (x+1) (x+2)
        rw [hv x (x+1) (x+4),hv (x+1) (x+2) (x+4),hv (x+2) (x+3) (x+4),ha,hb]
        abel
      have htotal (n : ℕ) (hn : n ≤ p) : v 0 (4*(n:ℝ))=0 := by
        induction n with
        | zero => simpa using hzero 0
        | succ n ih =>
          have he := hblock ⟨n,by omega⟩
          have hi := ih (by omega)
          have hh : 4*((n+1:ℕ):ℝ)=4*(n:ℝ)+4 := by push_cast;ring
          rw [hh,hv 0 (4*(n:ℝ)) (4*(n:ℝ)+4),hi,he,zero_add]
      exact ⟨seg,hformula,hadd,htotal p le_rfl⟩
    obtain ⟨seg,hformula,hadd,hfullzero⟩ := hfull p hp
    let T := TopCat.of (ActualClosedOrientableBoundaryGraph p)
    let C := mvAmbientComplex T
    let f := TopCat.ofHom (actualClosedOrientableAttachingMap p)
    have hpR : (p:ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
    have hside (i : Fin 8) :
        (TopCat.toSSet.map f).app (.op ⦋1⦌) (CircleFundamentalCycle.circleSideSimplex i)=
          seg (4*(p:ℝ)*(i:ℝ)/8) (4*(p:ℝ)*((i:ℝ)+1)/8) := by
      apply (TopCat.toSSetObjEquiv T (.op ⦋1⦌)).injective
      apply ContinuousMap.ext
      intro z
      rw [hformula]
      change actualClosedOrientableAttachingMap p (Circle.exp _) =
        actualClosedOrientableAttachingMap p (Real.fourierChar _)
      congr 1
      apply Subtype.ext
      simp only [Circle.coe_exp, Real.fourierChar_apply]
      congr 1
      simp only [CircleFundamentalCycle.coord, ContinuousMap.coe_mk, Homeomorph.apply_symm_apply]
      push_cast
      field_simp [hpR]
      ring_nf
      have hpC : (p:ℂ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
      simp [mul_assoc,hpC]
    rw [singularFinsuppMap_f]
    simp only [CircleFundamentalCycle.circleBoundaryChain,map_sum,Finsupp.mapDomain_single,hside]
    change (∑ i : Fin 8, C.pOpcycles 1
      ((Finsupp.lmapDomain ℤ ℤ ((TopCat.toSSet.map f).app (.op ⦋1⦌)))
        (Finsupp.single (CircleFundamentalCycle.circleSideSimplex i) (1:ℤ))))=0
    simp only [Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]
    simp only [hside]
    let v (a b : ℝ) := C.pOpcycles 1 (Finsupp.single (seg a b) (1:ℤ))
    have hv (a b c : ℝ) : v a c=v a b+v b c := hadd a b c
    have ht : v 0 (4*(p:ℝ))=0 := hfullzero
    simp only [Fin.sum_univ_succ]
    norm_num
    change v 0 (4*(p:ℝ)/8) + (v (4*(p:ℝ)/8) (4*(p:ℝ)*2/8) +
      (v (4*(p:ℝ)*2/8) (4*(p:ℝ)*3/8) + (v (4*(p:ℝ)*3/8) (4*(p:ℝ)*4/8) +
      (v (4*(p:ℝ)*4/8) (4*(p:ℝ)*5/8) + (v (4*(p:ℝ)*5/8) (4*(p:ℝ)*6/8) +
      (v (4*(p:ℝ)*6/8) (4*(p:ℝ)*7/8) + v (4*(p:ℝ)*7/8) (4*(p:ℝ))))))))=0
    repeat rw [← hv]
    exact ht
  let X := TopCat.of (ActualClosedOrientableBoundaryGraph p)
  let f := TopCat.ofHom (actualClosedOrientableAttachingMap p)
  let K := mvAmbientComplex X
  let z := circleBoundaryChain
  have hz : (mvAmbientComplex (TopCat.of Circle)).d 1 0 z=0 := circle_boundary_is_cycle
  have hw : K.d 1 0 ((singularFinsuppMap f).f 1 z)=0 := by
    have h := congrArg (fun m => m z) ((singularFinsuppMap f).comm 1 0)
    simpa [hz] using h
  have hc := cycleClass_map (singularFinsuppMap f) 1 z hz hw
  have hb : cycleClass K 1 ((singularFinsuppMap f).f 1 z) hw=0 := by
    apply (ModuleCat.mono_iff_injective (K.homologyι 1)).mp inferInstance
    have he : K.homologyι 1 (cycleClass K 1 ((singularFinsuppMap f).f 1 z) hw)=
        K.pOpcycles 1 ((singularFinsuppMap f).f 1 z) := by
      dsimp only [cycleClass]
      change (((K.liftCycles (scalar _ ((singularFinsuppMap f).f 1 z)) 0 (by simp) (by
        rw [scalar_naturality,hw,scalar_eq_zero]) ≫ K.homologyπ 1) ≫ K.homologyι 1) (1:ℤ))=_
      rw [Category.assoc,K.homology_π_ι,← Category.assoc,K.liftCycles_i]
      change K.pOpcycles 1 ((1:ℤ) • ((singularFinsuppMap f).f 1 z))=_
      rw [one_smul]
    rw [he,hchain p hp,map_zero]
  rw [hb] at hc
  have hn := congrArg (fun g => g (cycleClass (mvAmbientComplex (TopCat.of Circle)) 1 z hz))
    (singularHomologyRepresentation_naturality f 1)
  change (singularHomologyRepresentation X 1).hom
    (HomologicalComplex.homologyMap (singularFinsuppMap f) 1
      (cycleClass (mvAmbientComplex (TopCat.of Circle)) 1 z hz)) = _ at hn
  rw [hc,map_zero] at hn
  have hf : (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).map f) fundamentalClass=0 := hn.symm
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨n,rfl⟩ := fundamentalClass_generates x
  change (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).map f).hom (n • fundamentalClass)=0
  rw [map_zsmul,hf]
  exact zsmul_zero n
end CurveComplex.Hyperbolic
