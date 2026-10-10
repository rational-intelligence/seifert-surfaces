import CurveComplexGenusTwo.CWHurewicz.AbsolutePacket.MapLaws
import CurveComplexGenusTwo.CWHurewicz.SingularRepresentation
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

noncomputable section
open CategoryTheory CategoryTheory.Limits Topology
namespace CurveComplexGenusTwo.CWHurewicz.CWGeometricChains

abbrev C (X : Type) [TopologicalSpace X] := singularChains (TopCat.of X)

def cycleClass {X : Type} [TopologicalSpace X] (n : ℕ) (z : (C X).cycles n) : H X n :=
  (C X).homologyπ n z

theorem fundamentalCycle_exists (k : ℕ) :
    ∃ s : (C (CubeSphere (k + 2))).cycles (k + 2),
      cycleClass (k + 2) s = AbsolutePacket.fundamentalClass k := by
  exact (ModuleCat.epi_iff_surjective _).mp
    (inferInstance : Epi ((C (CubeSphere (k + 2))).homologyπ (k + 2)))
    (AbsolutePacket.fundamentalClass k)

theorem cycleClass_surjective {X : Type} [TopologicalSpace X] (n : ℕ) :
    Function.Surjective (cycleClass (X := X) n) := by
  exact (ModuleCat.epi_iff_surjective _).mp inferInstance

theorem cycleClass_zero_iff_boundary {X : Type} [TopologicalSpace X]
    (n : ℕ) (z : (C X).cycles n) :
    cycleClass n z = 0 ↔
      ∃ b : (C X).X (n + 1), (C X).d (n + 1) n b = (C X).iCycles n z := by
  have hi := (ModuleCat.mono_iff_injective ((C X).homologyι n)).mp inferInstance
  have he := congrArg (fun q => q z) ((C X).homology_π_ι n)
  change (C X).homologyι n (cycleClass n z) =
    (C X).pOpcycles n ((C X).iCycles n z) at he
  have hz : cycleClass n z = 0 ↔
      (C X).pOpcycles n ((C X).iCycles n z) = 0 := by
    constructor
    · intro h
      rw [← he, h]
      exact map_zero _
    · intro h
      apply hi
      rw [he, h]
      change 0 = ((C X).homologyι n).hom 0
      simp
  rw [hz]
  have h := ((C X).sc n).moduleCat_pOpcycles_eq_zero_iff ((C X).iCycles n z)
  change (C X).pOpcycles n ((C X).iCycles n z) = 0 ↔
    ∃ b : (C X).X ((ComplexShape.down ℕ).prev n),
      (C X).d ((ComplexShape.down ℕ).prev n) n b = (C X).iCycles n z at h
  rw [ChainComplex.prev ℕ n] at h
  exact h

theorem pushed_fundamental_cycle_class {X : Type} [TopologicalSpace X]
    (k : ℕ) (x : X) (f : GenLoop (Fin (k + 2)) X x)
    (s : (C (CubeSphere (k + 2))).cycles (k + 2))
    (hs : cycleClass (k + 2) s = AbsolutePacket.fundamentalClass k) :
    (C X).homologyπ (k + 2)
      (HomologicalComplex.cyclesMap
        (actualSingularFunctor.map (TopCat.ofHom (loopSphereMap (k + 2) x f)))
        (k + 2) s) = AbsolutePacket.value k x f := by
  have hn := congrArg (fun q => q s)
    (HomologicalComplex.homologyπ_naturality
      (actualSingularFunctor.map (TopCat.ofHom (loopSphereMap (k + 2) x f)))
      (k + 2))
  change HomologicalComplex.homologyMap
      (actualSingularFunctor.map (TopCat.ofHom (loopSphereMap (k + 2) x f)))
      (k + 2) (cycleClass (k + 2) s) = _ at hn
  rw [hs] at hn
  exact hn.symm

theorem coherent_homotopy_cycle_prism
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    (n : ℕ) (f g : C(P, X)) (F : ContinuousMap.Homotopy f g)
    (z : (C P).cycles n) :
    ∃ b : (C X).X (n + 1),
      (C X).d (n + 1) n b =
        (actualSingularFunctor.map (TopCat.ofHom f)).f n ((C P).iCycles n z) -
        (actualSingularFunctor.map (TopCat.ofHom g)).f n ((C P).iCycles n z) := by
  let K := C P
  let L := C X
  let φ := actualSingularFunctor.map (TopCat.ofHom f)
  let ψ := actualSingularFunctor.map (TopCat.ofHom g)
  let H := (show TopCat.Homotopy (TopCat.ofHom f) (TopCat.ofHom g) from F).singularChainComplexFunctorObjMap (ModuleCat.of ℤ ℤ)
  let c := K.iCycles n z
  have hc : K.d n ((ComplexShape.down ℕ).next n) c = 0 := by
    exact congrArg (fun q => q z) (K.iCycles_d n ((ComplexShape.down ℕ).next n))
  have h := congrArg (fun q => q c) (H.comm n)
  change φ.f n c =
    H.hom ((ComplexShape.down ℕ).next n) n (K.d n ((ComplexShape.down ℕ).next n) c) +
    L.d ((ComplexShape.down ℕ).prev n) n (H.hom n ((ComplexShape.down ℕ).prev n) c) +
    ψ.f n c at h
  rw [hc] at h
  change φ.f n c =
    (H.hom ((ComplexShape.down ℕ).next n) n).hom 0 +
    L.d ((ComplexShape.down ℕ).prev n) n (H.hom n ((ComplexShape.down ℕ).prev n) c) +
    ψ.f n c at h
  rw [map_zero, zero_add, ChainComplex.prev ℕ n] at h
  exact ⟨H.hom n (n + 1) c, eq_sub_of_add_eq h.symm⟩

end CurveComplexGenusTwo.CWHurewicz.CWGeometricChains
