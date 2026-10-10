import Section2.WeakRealization
import WhiteheadSupport.PointWhitehead
import TopologyAdapters.WeakBridge

namespace SeifertSurfaces.WhiteheadSupport

universe u

private theorem pi_subsingleton_across_homeomorph
    {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z]
    (e : Y ≃ₜ Z) (n : ℕ)
    (hpi : ∀ y : Y, Subsingleton (HomotopyGroup.Pi n Y y)) :
    ∀ z : Z, Subsingleton (HomotopyGroup.Pi n Z z) := by
  intro z
  constructor
  intro a b
  induction a using Quotient.inductionOn with
  | h f =>
    induction b using Quotient.inductionOn with
    | h g =>
      let fY : GenLoop (Fin n) Y (e.symm z) :=
        ⟨(⟨e.symm, e.symm.continuous⟩ : C(Z, Y)).comp f.val,
          fun a ha => congrArg e.symm (GenLoop.boundary f a ha)⟩
      let gY : GenLoop (Fin n) Y (e.symm z) :=
        ⟨(⟨e.symm, e.symm.continuous⟩ : C(Z, Y)).comp g.val,
          fun a ha => congrArg e.symm (GenLoop.boundary g a ha)⟩
      have heq : (⟦fY⟧ : HomotopyGroup.Pi n Y (e.symm z)) = ⟦gY⟧ :=
        @Subsingleton.elim (HomotopyGroup.Pi n Y (e.symm z)) (hpi (e.symm z)) _ _
      obtain ⟨K⟩ := Quotient.exact heq
      apply Quotient.sound
      refine ⟨{
        toFun := fun ta => e (K ta)
        continuous_toFun := e.continuous.comp K.continuous
        map_zero_left := ?_
        map_one_left := ?_
        prop' := ?_ }⟩
      · intro a
        exact (congrArg e (K.apply_zero a)).trans (e.apply_symm_apply (f a))
      · intro a
        exact (congrArg e (K.apply_one a)).trans (e.apply_symm_apply (g a))
      · intro t a ha
        exact (congrArg e (K.prop t a ha)).trans (e.apply_symm_apply (f a))

/-- Point Whitehead for the actual Section 2 weak realization in any universe.
The CW and Hausdorff properties must be proved by the realization adapter
package; they are not supplied as hypotheses to this consumer. -/
theorem contractible_weak_realization_of_all_pi_subsingleton
    {V : Type u} (X : AbstractSimplicialComplex V)
    [PathConnectedSpace (RealizationPoint X)]
    (hpi : ∀ n : ℕ, 1 ≤ n → ∀ x : RealizationPoint X,
      Subsingleton (HomotopyGroup.Pi n (RealizationPoint X) x)) :
    ContractibleSpace (RealizationPoint X) := by
  let e := TopologyAdapters.weakRealizationHomeomorph X
  let : PathConnectedSpace (CurveComplex.RealizationPoint X) := e.pathConnectedSpace
  have hcurve : ∀ n : ℕ, 1 ≤ n → ∀ x : CurveComplex.RealizationPoint X,
      Subsingleton (HomotopyGroup.Pi n (CurveComplex.RealizationPoint X) x) := by
    intro n hn
    exact pi_subsingleton_across_homeomorph e n (hpi n hn)
  let : ContractibleSpace (CurveComplex.RealizationPoint X) :=
    contractible_of_cw_all_pi_subsingleton_t2 hcurve
  exact e.contractibleSpace

end SeifertSurfaces.WhiteheadSupport
