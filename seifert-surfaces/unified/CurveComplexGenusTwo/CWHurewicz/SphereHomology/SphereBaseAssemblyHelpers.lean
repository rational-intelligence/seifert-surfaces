import CurveComplexGenusTwo.CWHurewicz.SingularRepresentation
import CurveComplexGenusTwo.CWHurewicz.SphereHomology.SphereBaseHZero

noncomputable section
open CategoryTheory CategoryTheory.Limits
open CurveComplexGenusTwo.CWHurewicz
namespace CircleHomologyComputation

def ordinaryHomologyIso (X : TopCat) (U : Set X) (n : ℕ) :
    (mvOrdinaryComplex X U).homology n ≅ H U n :=
  singularHomologyRepresentation (TopCat.of U) n

lemma subsetMap_eq (X : TopCat) (A B : Set X) (h : A ⊆ B) :
    mvSubsetMap X A B h = singularFinsuppMap
      (TopCat.ofHom ⟨fun x : A => (⟨x.val, h x.property⟩ : B), by fun_prop⟩) := by
  apply HomologicalComplex.Hom.ext
  funext n
  rw [singularFinsuppMap_f]
  rfl

lemma ordinaryHomologyIso_naturality (X : TopCat) (A B : Set X) (h : A ⊆ B) (n : ℕ) :
    HomologicalComplex.homologyMap (mvSubsetMap X A B h) n ≫
      (ordinaryHomologyIso X B n).hom =
        (ordinaryHomologyIso X A n).hom ≫
          ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj RZ).map
            (TopCat.ofHom ⟨fun x : A => (⟨x.val, h x.property⟩ : B), by fun_prop⟩) := by
  rw [subsetMap_eq]
  exact singularHomologyRepresentation_naturality _ n

lemma pairHomology_zero (X : TopCat) (U V : Set X) (n : ℕ)
    (hU : IsZero (H U n)) (hV : IsZero (H V n)) :
    IsZero ((mvPairComplex X U V).homology n) := by
  letI := ModuleCat.subsingleton_of_isZero (hU.of_iso (ordinaryHomologyIso X U n))
  letI := ModuleCat.subsingleton_of_isZero (hV.of_iso (ordinaryHomologyIso X V n))
  letI : Subsingleton ((mvPairComplex X U V).homology n) :=
    (mvPairHomologyEquiv X U V n).injective.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

/-- A monomorphism onto the coordinate-sum kernel identifies its source with ℤ. -/
def isoOfSumKernel {A B C : ModuleCat ℤ} (f : A ⟶ B) (g : B ⟶ C)
    (hfg : f ≫ g = 0) (hex : (ShortComplex.mk f g hfg).Exact)
    (hinj : Function.Injective f) (e : B ≃ₗ[ℤ] (ℤ × ℤ))
    (hker : ∀ x : B, g x = 0 ↔ (e x).1 + (e x).2 = 0) : A ≅ RZ := by
  let l : A →ₗ[ℤ] ℤ := (LinearMap.fst ℤ ℤ ℤ).comp (e.toLinearMap.comp f.hom)
  have hz (x : A) : (e (f x)).1 + (e (f x)).2 = 0 :=
    (hker (f x)).mp (congrArg (fun m => m x) hfg)
  have hi : Function.Injective l := by
    intro x y h
    apply hinj
    apply e.injective
    apply Prod.ext
    · exact h
    · have hx := hz x
      have hy := hz y
      change (e (f x)).1 = (e (f y)).1 at h
      omega
  have hs : Function.Surjective l := by
    intro z
    let b := e.symm (z,-z)
    have hb : g b = 0 := (hker b).mpr (by simp [b])
    obtain ⟨a, ha⟩ := (ShortComplex.moduleCat_exact_iff _).mp hex b hb
    refine ⟨a, ?_⟩
    change (e (f a)).1 = z
    rw [ha]
    simp [b]
  exact (LinearEquiv.ofBijective l ⟨hi,hs⟩).toModuleIso

end CircleHomologyComputation
