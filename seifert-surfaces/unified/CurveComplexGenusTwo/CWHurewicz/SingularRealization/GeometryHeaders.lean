import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.AlgebraicTopology.SimplicialSet.NonDegenerateSimplicesColimit
import Mathlib.Topology.Category.TopCat.Limits.Basic
open CategoryTheory CategoryTheory.Limits Opposite Topology
open scoped Simplicial
noncomputable section
namespace CurveComplexGenusTwo.CWHurewicz.SingularApproximation
/-- Every actual realization point has a characteristic-simplex representative. -/
theorem realization_simplex_representation (S : SSet.{0}) (x : SSet.toTop.obj S) :
    ∃ (n : SimplexCategory) (s : S.obj (op n)) (t : SSet.toTop.obj (SSet.stdSimplex.obj n)),
      SSet.toTop.map (SSet.yonedaEquiv.symm s) t = x := by
  obtain ⟨j, t, ht⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget TopCat)
      (isColimitOfPreserves SSet.toTop (Presheaf.colimitOfRepresentable S))) x
  exact ⟨j.unop.1.unop, j.unop.2, t, ht⟩
/-- Closedness for the actual Kan-extension topology is detected on characteristic simplices. -/
theorem realization_isClosed_iff (S : SSet.{0}) (A : Set (SSet.toTop.obj S)) :
    IsClosed A ↔ ∀ (n : SimplexCategory) (s : S.obj (op n)),
      IsClosed (SSet.toTop.map (SSet.yonedaEquiv.symm s) ⁻¹' A) := by
  have H := TopCat.isClosed_iff_of_isColimit _
    (isColimitOfPreserves SSet.toTop (Presheaf.colimitOfRepresentable S)) A
  constructor
  · intro h n s
    exact H.mp h (op {obj := op n, val := s})
  · intro h
    apply H.mpr
    intro j
    exact h j.unop.1.unop j.unop.2
/-- Degenerate representatives can be replaced by nondegenerate ones. -/
theorem realization_nondegenerate_representation (S : SSet.{0}) (x : SSet.toTop.obj S) :
    ∃ (n : ℕ) (s : S.nonDegenerate n) (t : SSet.toTop.obj (SSet.stdSimplex.obj ⦋n⦌)),
      SSet.toTop.map (SSet.yonedaEquiv.symm s.val) t = x := by
  obtain ⟨j, t, ht⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget TopCat)
      (isColimitOfPreserves SSet.toTop (Presheaf.colimitOfRepresentable S))) x
  let n := j.unop.1.unop
  let s : S.obj (op n) := j.unop.2
  change SSet.toTop.map (SSet.yonedaEquiv.symm s) t = x at ht
  change |SSet.stdSimplex.obj ⦋n.len⦌| at t
  obtain ⟨m, f, hf, y, hy⟩ := S.exists_nonDegenerate s
  have he : SSet.yonedaEquiv.symm (S.map f.op y.val) =
      SSet.stdSimplex.map f ≫ SSet.yonedaEquiv.symm y.val :=
    uliftYonedaEquiv_symm_map f.op y.val
  refine ⟨m, y, SSet.toTop.map (SSet.stdSimplex.map f) t, ?_⟩
  change (SSet.toTop.map (SSet.stdSimplex.map f) ≫
    SSet.toTop.map (SSet.yonedaEquiv.symm y.val)) t = x
  rw [← SSet.toTop.map_comp, ← he, ← hy]
  exact ht
/-- Nondegenerate characteristic simplices suffice to test closedness. -/
theorem realization_isClosed_iff_nondegenerate (S : SSet.{0}) (A : Set (SSet.toTop.obj S)) :
    IsClosed A ↔ ∀ (n : ℕ) (s : S.nonDegenerate n),
      IsClosed (SSet.toTop.map (SSet.yonedaEquiv.symm s.val) ⁻¹' A) := by
  have H := TopCat.isClosed_iff_of_isColimit _
    (isColimitOfPreserves SSet.toTop (Presheaf.colimitOfRepresentable S)) A
  constructor
  · intro h n s
    exact h.preimage (SSet.toTop.map (SSet.yonedaEquiv.symm s.val)).hom.continuous
  · intro h
    apply H.mpr
    intro j
    let n := j.unop.1.unop
    let s : S.obj (op n) := j.unop.2
    change IsClosed (SSet.toTop.map (SSet.yonedaEquiv.symm s) ⁻¹' A)
    obtain ⟨m, f, hf, y, hy⟩ := S.exists_nonDegenerate s
    have he : SSet.yonedaEquiv.symm (S.map f.op y.val) =
        SSet.stdSimplex.map f ≫ SSet.yonedaEquiv.symm y.val :=
      uliftYonedaEquiv_symm_map f.op y.val
    rw [hy, he, SSet.toTop.map_comp]
    change IsClosed (SSet.toTop.map (SSet.stdSimplex.map f) ⁻¹'
      (SSet.toTop.map (SSet.yonedaEquiv.symm y.val) ⁻¹' A))
    exact (h m y).preimage (SSet.toTop.map (SSet.stdSimplex.map f)).hom.continuous
/-- The disjoint union of nondegenerate closed simplices maps by a genuine quotient map
onto the actual Kan-extension realization. No change of realization topology is made. -/
theorem realization_nondegenerate_quotient (S : SSet.{0}) :
    IsQuotientMap
      (fun z : (Σ ns : (Σ n : ℕ, S.nonDegenerate n),
          SSet.toTop.obj (SSet.stdSimplex.obj ⦋ns.1⦌)) =>
        SSet.toTop.map (SSet.yonedaEquiv.symm z.1.2.val) z.2) := by
  have hrep (x : SSet.toTop.obj S) :
      ∃ (n : ℕ) (s : S.nonDegenerate n) (t : SSet.toTop.obj (SSet.stdSimplex.obj ⦋n⦌)),
        SSet.toTop.map (SSet.yonedaEquiv.symm s.val) t = x := by
    obtain ⟨j, t, ht⟩ := Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves (forget TopCat)
        (isColimitOfPreserves SSet.toTop (Presheaf.colimitOfRepresentable S))) x
    let n := j.unop.1.unop
    let s : S.obj (op n) := j.unop.2
    change SSet.toTop.map (SSet.yonedaEquiv.symm s) t = x at ht
    change |SSet.stdSimplex.obj ⦋n.len⦌| at t
    obtain ⟨m, f, hf, y, hy⟩ := S.exists_nonDegenerate s
    have he : SSet.yonedaEquiv.symm (S.map f.op y.val) =
        SSet.stdSimplex.map f ≫ SSet.yonedaEquiv.symm y.val :=
      uliftYonedaEquiv_symm_map f.op y.val
    refine ⟨m, y, SSet.toTop.map (SSet.stdSimplex.map f) t, ?_⟩
    change (SSet.toTop.map (SSet.stdSimplex.map f) ≫
      SSet.toTop.map (SSet.yonedaEquiv.symm y.val)) t = x
    rw [← SSet.toTop.map_comp, ← he, ← hy]
    exact ht
  have hclosed (A : Set (SSet.toTop.obj S)) :
      IsClosed A ↔ ∀ (n : ℕ) (s : S.nonDegenerate n),
        IsClosed (SSet.toTop.map (SSet.yonedaEquiv.symm s.val) ⁻¹' A) := by
    have H := TopCat.isClosed_iff_of_isColimit _
      (isColimitOfPreserves SSet.toTop (Presheaf.colimitOfRepresentable S)) A
    constructor
    · intro h n s
      exact h.preimage (SSet.toTop.map (SSet.yonedaEquiv.symm s.val)).hom.continuous
    · intro h
      apply H.mpr
      intro j
      let n := j.unop.1.unop
      let s : S.obj (op n) := j.unop.2
      change IsClosed (SSet.toTop.map (SSet.yonedaEquiv.symm s) ⁻¹' A)
      obtain ⟨m, f, hf, y, hy⟩ := S.exists_nonDegenerate s
      have he : SSet.yonedaEquiv.symm (S.map f.op y.val) =
          SSet.stdSimplex.map f ≫ SSet.yonedaEquiv.symm y.val :=
        uliftYonedaEquiv_symm_map f.op y.val
      rw [hy, he, SSet.toTop.map_comp]
      change IsClosed (SSet.toTop.map (SSet.stdSimplex.map f) ⁻¹'
        (SSet.toTop.map (SSet.yonedaEquiv.symm y.val) ⁻¹' A))
      exact (h m y).preimage (SSet.toTop.map (SSet.stdSimplex.map f)).hom.continuous
  apply isQuotientMap_iff_isClosed.mpr
  constructor
  · intro x
    obtain ⟨n, s, t, ht⟩ := hrep x
    exact ⟨⟨⟨n, s⟩, t⟩, ht⟩
  · intro A
    rw [isClosed_sigma_iff]
    exact (hclosed A).trans ⟨fun h ns => h ns.1 ns.2, fun h n s => h ⟨n, s⟩⟩
/-- Characteristic representatives in the actual realization are identified exactly
by the equivalence relation generated by simplex morphisms. -/
theorem realization_simplex_eq_iff (S : SSet.{0}) (j k : S.Elementsᵒᵖ)
    (t : SSet.toTop.obj (SSet.stdSimplex.obj j.unop.obj.unop))
    (u : SSet.toTop.obj (SSet.stdSimplex.obj k.unop.obj.unop)) :
    SSet.toTop.map (SSet.yonedaEquiv.symm j.unop.val) t =
      SSet.toTop.map (SSet.yonedaEquiv.symm k.unop.val) u ↔
    Relation.EqvGen
      (Presheaf.functorToRepresentables S ⋙ SSet.toTop ⋙ forget TopCat).ColimitTypeRel
      ⟨j, t⟩ ⟨k, u⟩ := by
  let F := Presheaf.functorToRepresentables S ⋙ SSet.toTop ⋙ forget TopCat
  let c := (forget TopCat).mapCocone
    (SSet.toTop.mapCocone (Presheaf.coconeOfRepresentable S))
  have hc : (F.coconeTypesEquiv.symm c).IsColimit :=
    (Types.isColimit_iff_coconeTypesIsColimit c).mp
      ⟨isColimitOfPreserves (forget TopCat)
        (isColimitOfPreserves SSet.toTop (Presheaf.colimitOfRepresentable S))⟩
  change F.obj j at t
  change F.obj k at u
  change (F.coconeTypesEquiv.symm c).ι j t =
    (F.coconeTypesEquiv.symm c).ι k u ↔ Relation.EqvGen F.ColimitTypeRel ⟨j, t⟩ ⟨k, u⟩
  rw [← F.ιColimitType_eq_iff t u]
  constructor
  · intro h
    have he := congrArg hc.equiv.symm h
    simpa only [Functor.CoconeTypes.IsColimit.equiv_symm_ι_apply] using he
  · intro h
    have he := congrArg hc.equiv h
    simpa only [Functor.CoconeTypes.IsColimit.equiv_apply,
      Functor.descColimitType_ιColimitType_apply] using he
end CurveComplexGenusTwo.CWHurewicz.SingularApproximation
