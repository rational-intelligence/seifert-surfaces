import CurveComplexGenusTwo.CWHurewicz.PublicExport.FiniteAvoidance

namespace CurveComplexGenusTwo.CWHurewicz
open Topology
open scoped unitInterval

/-- A finite-support map from a source of dimension below the selected cell
dimension deforms into the preceding skeleton. The center avoidance is
produced by perturbing the given map, and the entire deformation fixes source
points originally in the lower skeleton. -/
theorem finiteCellDimensionReductionAfterAvoidance
    {X : Type} [TopologicalSpace X] [Topology.CWComplex (Set.univ : Set X)] [T2Space X]
    {S : Type*} [TopologicalSpace S] {k n : ℕ}
    (e : S → (Fin k → ℝ)) (he : IsClosedEmbedding e) (hkn : k < n)
    (F : Finset (StageCellIndex X n)) (hF : ∀ a ∈ F, a.1.val = n)
    (f : C(S, ↥(skeletonBelow X (n+1))))
    (hsupp : ∀ z, (f z).val ∈ finiteTopCellSupport n F) :
    ∃ g : C(S, ↥(skeletonBelow X n)),
      Nonempty (ContinuousMap.HomotopyRel
        ((⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(skeletonBelow X (n+1)), X)).comp f)
        ((⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(skeletonBelow X n), X)).comp g)
        {z | (f z).val ∈ skeletonBelow X n}) := by
  obtain ⟨u, H₁, hmiss, hsupp'⟩ :=
    finiteCellPointAvoidance e he hkn F hF f hsupp
  obtain ⟨g, ⟨H₂⟩⟩ := finiteCellDimensionReduction n F hF u hmiss
    (fun z => by simpa using hsupp' 1 z)
  let v : C(↥(skeletonBelow X (n+1)), X) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  have H₂' : ContinuousMap.HomotopyRel (v.comp u)
      ((⟨Subtype.val, continuous_subtype_val⟩ :
        C(↥(skeletonBelow X n), X)).comp g)
      {z | (f z).val ∈ skeletonBelow X n} := {
    toHomotopy := H₂.toHomotopy
    prop' := by
      intro t z hz
      apply H₂.prop t z
      have heq : u z = f z := by simpa using H₁.prop 1 z hz
      change (u z).val ∈ skeletonBelow X n
      rw [heq]
      exact hz }
  exact ⟨g, ⟨(H₁.compContinuousMap v).trans H₂'⟩⟩

end CurveComplexGenusTwo.CWHurewicz
