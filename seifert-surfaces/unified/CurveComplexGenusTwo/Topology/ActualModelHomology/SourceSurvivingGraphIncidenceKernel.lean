import CurveComplexGenusTwo.Topology.ActualModelHomology.ActualOneBoundaryHandleEdges
import CurveComplexGenusTwo.Topology.ActualModelHomology.ActualOneBoundaryRawInteriorFibers
import CurveComplexGenusTwo.Topology.ActualModelHomology.ActualOneBoundarySurvivingArcNormalization
import CurveComplexGenusTwo.CWHurewicz.SingularRepresentation
namespace CurveComplex.Hyperbolic.OneBoundaryRay
open Set Topology CategoryTheory CategoryTheory.Limits
open CurveComplexGenusTwo.CWHurewicz
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
theorem source_surviving_graph_incidence_kernel (p : ℕ) : ∃ D : (Fin (2*p) × Bool → ℤ) →ₗ[ℤ] (ℤ × (Fin (2*p) → ℤ)),
    (∀ c, D c=(∑ i, (c (i,false)+c (i,true)),fun i => c (i,false)+c (i,true))) ∧
    Nonempty (LinearMap.ker D ≃ₗ[ℤ] (Fin (2*p) → ℤ)) := by
  classical
  let difference : (Fin (2*p) × Bool → ℤ) →ₗ[ℤ] (ℤ × (Fin (2*p) → ℤ)) := {
    toFun := fun c => (∑ i : Fin (2*p), (c (i, false) + c (i, true)),
      fun i => c (i, false) + c (i, true))
    map_add' := by
      intro c d
      apply Prod.ext
      · change (∑ i : Fin (2*p), ((c (i, false) + d (i, false)) +
            (c (i, true) + d (i, true)))) =
          (∑ i : Fin (2*p), (c (i, false) + c (i, true))) +
            (∑ i : Fin (2*p), (d (i, false) + d (i, true)))
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        abel
      · funext i
        change (c (i, false) + d (i, false)) + (c (i, true) + d (i, true)) =
          (c (i, false) + c (i, true)) + (d (i, false) + d (i, true))
        abel
    map_smul' := by
      intro r c
      apply Prod.ext
      · change (∑ i : Fin (2*p), (r * c (i, false) + r * c (i, true))) =
          r * (∑ i : Fin (2*p), (c (i, false) + c (i, true)))
        simp_rw [← mul_add]
        calc
          (∑ i : Fin (2*p), r * (c (i, false) + c (i, true))) =
              ∑ i : Fin (2*p), r • (c (i, false) + c (i, true)) := by simp
          _ = r • (∑ i : Fin (2*p), (c (i, false) + c (i, true))) := Finset.smul_sum.symm
          _ = r * (∑ i : Fin (2*p), (c (i, false) + c (i, true))) := by simp
      · funext i
        change r * c (i, false) + r * c (i, true) =
          r * (c (i, false) + c (i, true))
        ring
  }
  let read : LinearMap.ker difference →ₗ[ℤ] (Fin (2*p) → ℤ) := {
    toFun := fun c i => c.val (i,false)
    map_add' := by intro c d; funext i; rfl
    map_smul' := by intro r c; funext i; rfl
  }
  have hend (c : LinearMap.ker difference) (i : Fin (2*p)) :
      c.val (i,true)= -c.val (i,false) := by
    have h := congrArg (fun q : ℤ × (Fin (2*p) → ℤ) => q.2 i) c.property
    change c.val (i,false)+c.val (i,true)=0 at h
    exact eq_neg_of_add_eq_zero_right h
  have hb : Function.Bijective read := by
    constructor
    · intro c d h
      apply Subtype.ext
      funext q
      rcases q with ⟨i,b⟩
      cases b
      · exact congrFun h i
      · rw [hend c i,hend d i]
        exact congrArg Neg.neg (congrFun h i)
    · intro f
      let c : Fin (2*p) × Bool → ℤ := fun q => if q.2 then -f q.1 else f q.1
      have hc : difference c=0 := by
        apply Prod.ext
        · change (∑ i, (c (i,false)+c (i,true)))=0
          simp [c]
        · funext i
          change c (i,false)+c (i,true)=0
          simp [c]
      exact ⟨⟨c,hc⟩,by funext i; rfl⟩
  exact ⟨difference,fun _ => rfl,⟨LinearEquiv.ofBijective read hb⟩⟩
end CurveComplex.Hyperbolic.OneBoundaryRay
