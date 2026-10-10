import CurveComplexGenusTwo.CWHurewicz.GeometricContinuation.FiniteSingularCarrier
import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton
import CurveComplexGenusTwo.CWHurewicz.CWBasic

noncomputable section
open CategoryTheory CategoryTheory.Limits Topology
open scoped Simplicial
namespace CurveComplexGenusTwo.CWHurewicz.FiniteSingularCarrier

theorem carrier_finite (S : SSet.{0}) (n : ℕ) (c : S _⦋n⦌ →₀ ℤ) :
    SSet.Finite (carrier S n c) := by
  exact (SSet.finite_iSup_iff _).mpr (fun _ => inferInstance)

theorem carrier_dimension (S : SSet.{0}) (n : ℕ) (c : S _⦋n⦌ →₀ ℤ) :
    SSet.HasDimensionLT (carrier S n c) (n + 1) := by
  apply (SSet.hasDimensionLT_iSup_iff _ _).mpr
  intro a
  exact SSet.hasDimensionLT_of_epi (SSet.Subcomplex.toOfSimplex a.val) (n + 1)

theorem liftChain_push (X : TopCat.{0}) (n : ℕ)
    (c : (TopCat.toSSet.obj X) _⦋n⦌ →₀ ℤ) :
    (SSet.chainComplexMap (carrier (TopCat.toSSet.obj X) n c).ι
      (ModuleCat.of ℤ ℤ)).f n (liftChain (TopCat.toSSet.obj X) n c) =
      (singularChainsFinsuppIso X n).inv c := by
  let S := TopCat.toSSet.obj X
  let A := carrier S n c
  let φ := SSet.chainComplexMap A.ι (ModuleCat.of ℤ ℤ)
  have hb (a : c.support) : φ.f n
      ((A.toSSet.ιChainComplex (R := ModuleCat.of ℤ ℤ) (liftSimplex S n c a)).hom 1) =
      (S.ιChainComplex (R := ModuleCat.of ℤ ℤ) a.val).hom 1 := by
    exact congrArg (fun q : ModuleCat.of ℤ ℤ ⟶ _ => q.hom 1)
      (SSet.ι_chainComplexMap_f A.toSSet S A.ι (ModuleCat.of ℤ ℤ) (liftSimplex S n c a))
  change (φ.f n).hom (liftChain S n c) = _
  unfold liftChain
  rw [map_sum]
  simp only [map_zsmul]
  change (∑ a : c.support, c a.val • φ.f n
    ((A.toSSet.ιChainComplex (R := ModuleCat.of ℤ ℤ) (liftSimplex S n c a)).hom 1)) = _
  simp_rw [hb]
  apply (ModuleCat.mono_iff_injective (singularChainsFinsuppIso X n).hom).mp inferInstance
  change (singularChainsFinsuppIso X n).hom.hom _ =
    (singularChainsFinsuppIso X n).hom ((singularChainsFinsuppIso X n).inv c)
  rw [Iso.inv_hom_id_apply, map_sum]
  simp only [map_zsmul]
  change (∑ a : c.support, c a.val • (singularChainsFinsuppIso X n).hom
    ((S.ιChainComplex (R := ModuleCat.of ℤ ℤ) a.val).hom 1)) = c
  have hgen (a : c.support) : (singularChainsFinsuppIso X n).hom
      ((S.ιChainComplex (R := ModuleCat.of ℤ ℤ) a.val).hom 1) =
      Finsupp.single a.val 1 := singularChainsFinsuppIso_generator X n a.val
  simp_rw [hgen, Finsupp.smul_single, smul_eq_mul, mul_one]
  exact (Finset.sum_coe_sort c.support (fun a => Finsupp.single a (c a))).trans
    (Finsupp.sum_single c)

theorem inclusion_component_injective (S : SSet.{0}) (A : S.Subcomplex) (m : ℕ) :
    Function.Injective
      ((SSet.chainComplexMap A.ι (ModuleCat.of ℤ ℤ)).f m) := by
  classical
  let r : (S.chainComplex (ModuleCat.of ℤ ℤ)).X m ⟶
      (A.toSSet.chainComplex (ModuleCat.of ℤ ℤ)).X m :=
    Sigma.desc (fun a : S _⦋m⦌ => if h : a ∈ A.obj _ then
      A.toSSet.ιChainComplex (R := ModuleCat.of ℤ ℤ) ⟨a,h⟩ else 0)
  have hr : (SSet.chainComplexMap A.ι (ModuleCat.of ℤ ℤ)).f m ≫ r = 𝟙 _ := by
    apply SSet.chainComplex_hom_ext
    intro a
    rw [SSet.ι_chainComplexMap_f_assoc]
    simp [r, SSet.ιChainComplex, a.property]
  apply Function.LeftInverse.injective (g := fun a => r a)
  intro a
  exact congrArg (fun q => q a) hr

theorem finite_cycle_carrier (X : TopCat.{0}) (n : ℕ) (z : (singularChains X).cycles n) :
    ∃ A : (TopCat.toSSet.obj X).Subcomplex,
      SSet.Finite A ∧ SSet.HasDimensionLT A (n + 1) ∧
      ∃ w : (A.toSSet.chainComplex (ModuleCat.of ℤ ℤ)).cycles n,
        (SSet.chainComplexMap A.ι (ModuleCat.of ℤ ℤ)).f n
          ((A.toSSet.chainComplex (ModuleCat.of ℤ ℤ)).iCycles n w) =
          (singularChains X).iCycles n z := by
  classical
  let S := TopCat.toSSet.obj X
  let K := singularChains X
  let c := (singularChainsFinsuppIso X n).hom (K.iCycles n z)
  let A := carrier S n c
  let L := A.toSSet.chainComplex (ModuleCat.of ℤ ℤ)
  let φ := SSet.chainComplexMap A.ι (ModuleCat.of ℤ ℤ)
  let a := liftChain S n c
  have hpush : φ.f n a = K.iCycles n z := by
    have hb (b : c.support) : φ.f n
        ((A.toSSet.ιChainComplex (R := ModuleCat.of ℤ ℤ) (liftSimplex S n c b)).hom 1) =
        (S.ιChainComplex (R := ModuleCat.of ℤ ℤ) b.val).hom 1 := by
      exact congrArg (fun q : ModuleCat.of ℤ ℤ ⟶ _ => q.hom 1)
        (SSet.ι_chainComplexMap_f A.toSSet S A.ι (ModuleCat.of ℤ ℤ) (liftSimplex S n c b))
    apply (ModuleCat.mono_iff_injective (singularChainsFinsuppIso X n).hom).mp inferInstance
    change (singularChainsFinsuppIso X n).hom.hom ((φ.f n).hom a) = c
    dsimp [a]
    unfold liftChain
    rw [map_sum]
    simp only [map_zsmul]
    change (singularChainsFinsuppIso X n).hom.hom
      (∑ b : c.support, c b.val • φ.f n
        ((A.toSSet.ιChainComplex (R := ModuleCat.of ℤ ℤ) (liftSimplex S n c b)).hom 1)) = c
    simp_rw [hb]
    rw [map_sum]
    simp only [map_zsmul]
    change (∑ b : c.support, c b.val • (singularChainsFinsuppIso X n).hom
      ((S.ιChainComplex (R := ModuleCat.of ℤ ℤ) b.val).hom 1)) = c
    have hgen (b : c.support) : (singularChainsFinsuppIso X n).hom
        ((S.ιChainComplex (R := ModuleCat.of ℤ ℤ) b.val).hom 1) =
        Finsupp.single b.val 1 := singularChainsFinsuppIso_generator X n b.val
    simp_rw [hgen, Finsupp.smul_single, smul_eq_mul, mul_one]
    exact (Finset.sum_coe_sort c.support (fun b => Finsupp.single b (c b))).trans
      (Finsupp.sum_single c)
  have hinj (m : ℕ) : Function.Injective (φ.f m) := by
    let r : K.X m ⟶ L.X m :=
      Sigma.desc (fun b : S _⦋m⦌ => if h : b ∈ A.obj _ then
        A.toSSet.ιChainComplex (R := ModuleCat.of ℤ ℤ) ⟨b,h⟩ else 0)
    have hr : φ.f m ≫ r = 𝟙 _ := by
      apply SSet.chainComplex_hom_ext
      intro b
      rw [SSet.ι_chainComplexMap_f_assoc]
      change S.ιChainComplex (R := ModuleCat.of ℤ ℤ) b.val ≫ r =
        A.toSSet.ιChainComplex (R := ModuleCat.of ℤ ℤ) b ≫ 𝟙 _
      dsimp [r, SSet.ιChainComplex]
      rw [Sigma.ι_comp_desc]
      rw [dite_eq_left b.property, Category.comp_id]
      rfl
    apply Function.LeftInverse.injective (g := fun b => r b)
    intro b
    exact congrArg (fun q => q b) hr
  have ha : L.d n ((ComplexShape.down ℕ).next n) a = 0 := by
    apply hinj ((ComplexShape.down ℕ).next n)
    have hcomm := congrArg (fun q => q a) (φ.comm n ((ComplexShape.down ℕ).next n)).symm
    change φ.f ((ComplexShape.down ℕ).next n)
      (L.d n ((ComplexShape.down ℕ).next n) a) =
      K.d n ((ComplexShape.down ℕ).next n) (φ.f n a) at hcomm
    rw [hpush] at hcomm
    have hz := congrArg (fun q => q z) (K.iCycles_d n ((ComplexShape.down ℕ).next n))
    change K.d n ((ComplexShape.down ℕ).next n) (K.iCycles n z) = 0 at hz
    rw [hz] at hcomm
    change _ = (φ.f ((ComplexShape.down ℕ).next n)).hom 0
    rw [map_zero]
    exact hcomm
  let v : LinearMap.ker (L.sc n).g.hom := ⟨a, ha⟩
  let w : L.cycles n := (L.sc n).moduleCatCyclesIso.inv v
  have hw : L.iCycles n w = a :=
    congrArg (fun q => q v) ((L.sc n).moduleCatCyclesIso_inv_iCycles)
  refine ⟨A, ?_, ?_, w, ?_⟩
  · exact (SSet.finite_iSup_iff _).mpr (fun _ => inferInstance)
  · apply (SSet.hasDimensionLT_iSup_iff _ _).mpr
    intro b
    exact SSet.hasDimensionLT_of_epi (SSet.Subcomplex.toOfSimplex b.val) (n + 1)
  · change φ.f n (L.iCycles n w) = _
    rw [hw]
    exact hpush

theorem cycle_realization_push (X : TopCat.{0})
    (A : (TopCat.toSSet.obj X).Subcomplex) (n : ℕ)
    (w : (A.toSSet.chainComplex (ModuleCat.of ℤ ℤ)).cycles n) :
    ∃ u : (singularChains (SSet.toTop.obj A.toSSet)).cycles n,
      (actualSingularFunctor.map
        (SSet.toTop.map A.ι ≫ sSetTopAdj.counit.app X)).f n
        ((singularChains (SSet.toTop.obj A.toSSet)).iCycles n u) =
      (SSet.chainComplexMap A.ι (ModuleCat.of ℤ ℤ)).f n
        ((A.toSSet.chainComplex (ModuleCat.of ℤ ℤ)).iCycles n w) := by
  let F := (SSet.chainComplexFunctor (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)
  let μ := SSet.chainComplexMap (sSetTopAdj.unit.app A.toSSet) (ModuleCat.of ℤ ℤ)
  let p := SSet.toTop.map A.ι ≫ sSetTopAdj.counit.app X
  have hcomp : sSetTopAdj.unit.app A.toSSet ≫ TopCat.toSSet.map p = A.ι := by
    have hnat := sSetTopAdj.unit.naturality A.ι
    change A.ι ≫ sSetTopAdj.unit.app (TopCat.toSSet.obj X) =
      sSetTopAdj.unit.app A.toSSet ≫ TopCat.toSSet.map (SSet.toTop.map A.ι) at hnat
    dsimp [p]
    rw [Functor.map_comp, ← Category.assoc, ← hnat, Category.assoc,
      sSetTopAdj.right_triangle_components, Category.comp_id]
  have hmaps : μ ≫ actualSingularFunctor.map p =
      SSet.chainComplexMap A.ι (ModuleCat.of ℤ ℤ) := by
    change F.map (sSetTopAdj.unit.app A.toSSet) ≫ F.map (TopCat.toSSet.map p) = F.map A.ι
    rw [← F.map_comp, hcomp]
  let u := HomologicalComplex.cyclesMap μ n w
  refine ⟨u, ?_⟩
  have hi := congrArg (fun q => q w) (HomologicalComplex.cyclesMap_i μ n)
  change (singularChains (SSet.toTop.obj A.toSSet)).iCycles n u =
    μ.f n ((A.toSSet.chainComplex (ModuleCat.of ℤ ℤ)).iCycles n w) at hi
  rw [hi]
  exact congrArg (fun q => q.f n ((A.toSSet.chainComplex (ModuleCat.of ℤ ℤ)).iCycles n w)) hmaps

end CurveComplexGenusTwo.CWHurewicz.FiniteSingularCarrier
