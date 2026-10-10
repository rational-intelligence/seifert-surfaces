import CurveComplexGenusTwo.CWHurewicz.PairExactnessInterface

namespace CurveComplexGenusTwo.CWHurewicz

open CategoryTheory CategoryTheory.Limits Topology

/-- In degree one, surjectivity of absolute-to-relative homology needs only
injectivity of the degree-zero inclusion.  The subspace's `H₀` need not vanish. -/
theorem homologyToRelative_one_epi_of_H0_mono
    (X : Type) [TopologicalSpace X] (A : Set X)
    [Mono (homologyInclusion X A 0)] :
    Epi (homologyToRelative X A 1) := by
  obtain ⟨hcomp, _⟩ := pairHomology_exact_at_subspace X A 0
  have hδ : relativeConnecting X A 0 = 0 := by
    apply (cancel_mono (homologyInclusion X A 0)).mp
    simpa using hcomp
  obtain ⟨_, hexact⟩ := pairHomology_exact_at_relative X A 0
  exact hexact.epi_f hδ

/-- A retraction onto the subspace makes its degree-zero homology inclusion
injective, so the degree-one absolute-to-relative map is onto. -/
theorem homologyToRelative_one_epi_of_retraction
    (X : Type) [TopologicalSpace X] (A : Set X)
    (r : TopCat.of X ⟶ TopCat.of ↥A)
    (hr : pairInclusion X A ≫ r = 𝟙 (TopCat.of ↥A)) :
    Epi (homologyToRelative X A 1) := by
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 0).obj
    (ModuleCat.of ℤ ℤ)
  have hF : homologyInclusion X A 0 ≫ F.map r = 𝟙 (H ↥A 0) := by
    change F.map (pairInclusion X A) ≫ F.map r = 𝟙 _
    rw [← F.map_comp, hr, F.map_id]
  have : Mono (homologyInclusion X A 0 ≫ F.map r) := by
    rw [hF]
    infer_instance
  have : Mono (homologyInclusion X A 0) :=
    mono_of_mono (homologyInclusion X A 0) (F.map r)
  exact homologyToRelative_one_epi_of_H0_mono X A

/-- The singleton basepoint always has the degree-zero injection needed for
degree-one relative homology, independently of connectivity of `X`. -/
theorem homologyToRelative_one_epi_singleton
    (X : Type) [TopologicalSpace X] (x : X) :
    Epi (homologyToRelative X ({x} : Set X) 1) := by
  let r : TopCat.of X ⟶ TopCat.of ↥({x} : Set X) :=
    TopCat.ofHom ⟨fun _ => (⟨x, Set.mem_singleton x⟩ : ↥({x} : Set X)), continuous_const⟩
  apply homologyToRelative_one_epi_of_retraction X {x} r
  ext y
  change x = y.val
  exact y.property.symm

theorem homologyToRelative_one_surjective_singleton
    (X : Type) [TopologicalSpace X] (x : X) :
    Function.Surjective (homologyToRelative X ({x} : Set X) 1) :=
  (ModuleCat.epi_iff_surjective _).mp
    (homologyToRelative_one_epi_singleton X x)

/-- The degree-one kernel of the quotient map is exactly the image of the
subspace inclusion.  This is the absolute term in the pair exact sequence. -/
theorem homologyToRelative_one_kernel_image
    (X : Type) [TopologicalSpace X] (A : Set X)
    (w : H X 1) (hw : homologyToRelative X A 1 w = 0) :
    ∃ a : H ↥A 1, homologyInclusion X A 1 a = w := by
  obtain ⟨_, hexact⟩ := pairHomology_exact_at_absolute X A 1
  exact (ShortComplex.exact_iff_of_hasForget _).mp hexact w hw

/-- First homology equals homology relative to a chosen point.  The proof
uses vanishing of the point's positive-degree homology and the split injection
in degree zero, without assuming that the point's `H₀` vanishes. -/
theorem homologyToRelative_one_isIso_singleton
    (X : Type) [TopologicalSpace X] (x : X) :
    IsIso (homologyToRelative X ({x} : Set X) 1) := by
  have : Subsingleton ↥({x} : Set X) :=
    ⟨fun a b => Subtype.ext (a.property.trans b.property.symm)⟩
  have : TotallyDisconnectedSpace ↥({x} : Set X) :=
    ⟨fun s _ _ => by
      intro a _ b _
      exact Subsingleton.elim a b⟩
  have hzero : IsZero (H ↥({x} : Set X) 1) :=
    AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat.{0} ℤ) 1 (ModuleCat.of ℤ ℤ)
      (TopCat.of ↥({x} : Set X)) (by omega)
  obtain ⟨_, hexact⟩ := pairHomology_exact_at_absolute X {x} 1
  have hmono : Mono (homologyToRelative X ({x} : Set X) 1) :=
    hexact.mono_g (hzero.eq_of_src _ _)
  have hepi : Epi (homologyToRelative X ({x} : Set X) 1) :=
    homologyToRelative_one_epi_singleton X x
  exact isIso_of_mono_of_epi _

/-- Algebraic projection criterion for a wedge in degree one.  The maps model
the two inclusions, two projections, and the absolute-to-relative maps in an
excision diagram.  In particular, the second absolute-to-relative map is only
required to be onto, as supplied by `homologyToRelative_one_epi_of_H0_mono`. -/
theorem wedgeHOne_projection_injective_of_relative_diagram
    {A W R S QR QW : Type} [AddCommGroup A] [AddCommGroup W]
    [AddCommGroup R] [AddCommGroup S] [AddCommGroup QR] [AddCommGroup QW]
    (j : A →+ W) (p₁ p₂ : W →+ S) (qW : W →+ QW)
    (qR : R →+ QR) (e : QR →+ QW) (s : R →+ S) (p₂rel : QW →+ S)
    (hexact : ∀ w, qW w = 0 → ∃ a, j a = w)
    (ha_inj : Function.Injective (p₁.comp j))
    (hqW : p₂rel.comp qW = p₂)
    (he_surj : Function.Surjective e)
    (hqR_surj : Function.Surjective qR)
    (hs_inj : Function.Injective s)
    (hrel : p₂rel.comp (e.comp qR) = s) :
    Function.Injective (fun w => (p₁ w, p₂ w)) := by
  intro w w' hpair
  have h₁ : p₁ w = p₁ w' := congrArg Prod.fst hpair
  have h₂ : p₂ w = p₂ w' := congrArg Prod.snd hpair
  have hkernel (v : W) (hv : p₂ v = 0) : qW v = 0 := by
    obtain ⟨z, hz⟩ := he_surj (qW v)
    obtain ⟨r, hr⟩ := hqR_surj z
    have hs0 : s r = 0 := by
      have hrelr := congrArg (fun f : R →+ S => f r) hrel
      have hqWr := congrArg (fun f : W →+ S => f v) hqW
      calc
        s r = p₂rel (e (qR r)) := hrelr.symm
        _ = p₂rel (e z) := by rw [hr]
        _ = p₂rel (qW v) := by rw [hz]
        _ = p₂ v := hqWr
        _ = 0 := hv
    have hr0 : r = 0 := hs_inj (by simp [hs0])
    rw [← hz, ← hr, hr0]
    simp
  have hqzero : qW (w - w') = 0 := by
    apply hkernel
    rw [map_sub, h₂, sub_self]
  obtain ⟨a, ha⟩ := hexact (w - w') hqzero
  have hpa : p₁ (j a) = 0 := by
    rw [ha, map_sub, h₁, sub_self]
  have ha0 : a = 0 := by
    apply ha_inj
    simpa using hpa
  have hww : w - w' = 0 := by simpa [ha0] using ha.symm
  exact sub_eq_zero.mp hww

#print axioms homologyToRelative_one_epi_of_H0_mono
#print axioms homologyToRelative_one_epi_of_retraction
#print axioms homologyToRelative_one_epi_singleton
#print axioms homologyToRelative_one_surjective_singleton
#print axioms homologyToRelative_one_kernel_image
#print axioms homologyToRelative_one_isIso_singleton
#print axioms wedgeHOne_projection_injective_of_relative_diagram

end CurveComplexGenusTwo.CWHurewicz
