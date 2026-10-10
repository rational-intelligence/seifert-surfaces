import CurveComplexGenusTwo.CWHurewicz.PublicExport.FiniteAvoidanceComposition

namespace CurveComplexGenusTwo.CWHurewicz
open Topology
open scoped unitInterval

/-- Iterate finite-support dimension reduction from an upper successor stage
down to the stage just above the source embedding dimension. Finite support
for each intermediate map is an explicit hypothesis. -/
theorem finiteCellDimensionReductionIterated
    {X : Type} [TopologicalSpace X] [Topology.CWComplex (Set.univ : Set X)] [T2Space X]
    {S : Type*} [TopologicalSpace S] {k n : ℕ}
    (e : S → (Fin k → ℝ)) (he : IsClosedEmbedding e) (hkn : k < n)
    (hsupport : ∀ m, k < m → m ≤ n →
      ∀ u : C(S, ↥(skeletonBelow X (m+1))),
        ∃ F : Finset (StageCellIndex X m),
          (∀ a ∈ F, a.1.val = m) ∧
          ∀ z, (u z).val ∈ finiteTopCellSupport m F)
    (f : C(S, ↥(skeletonBelow X (n+1)))) :
    ∃ g : C(S, ↥(skeletonBelow X (k+1))),
      Nonempty (ContinuousMap.HomotopyRel
        ((⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(skeletonBelow X (n+1)), X)).comp f)
        ((⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(skeletonBelow X (k+1)), X)).comp g)
        {z | (f z).val ∈ skeletonBelow X (k+1)}) := by
  have hmain : ∀ (m : ℕ), k < m → m ≤ n →
      ∀ u : C(S, ↥(skeletonBelow X (m+1))),
        ∃ g : C(S, ↥(skeletonBelow X (k+1))),
          Nonempty (ContinuousMap.HomotopyRel
            ((⟨Subtype.val, continuous_subtype_val⟩ :
              C(↥(skeletonBelow X (m+1)), X)).comp u)
            ((⟨Subtype.val, continuous_subtype_val⟩ :
              C(↥(skeletonBelow X (k+1)), X)).comp g)
            {z | (u z).val ∈ skeletonBelow X (k+1)}) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro hkm hmn u
        cases m with
        | zero => omega
        | succ p =>
            obtain ⟨F,hF,hsupp⟩ := hsupport (p+1) hkm hmn u
            obtain ⟨v,⟨H₁⟩⟩ :=
              finiteCellDimensionReductionAfterAvoidance e he hkm F hF u hsupp
            by_cases hpk : p = k
            · subst p
              exact ⟨v,⟨H₁⟩⟩
            · have hkp : k < p := by omega
              obtain ⟨w,⟨H₂⟩⟩ := ih p (by omega) hkp (by omega) v
              let P : Set S := {z | (u z).val ∈ skeletonBelow X (k+1)}
              have hfix (z : S) (hz : z ∈ P) : (v z).val = (u z).val := by
                have hz' : (u z).val ∈ skeletonBelow X (p+1) :=
                  skeletonBelow_mono (by omega : k+1 ≤ p+1) hz
                simpa using H₁.prop 1 z hz'
              have H₁' : ContinuousMap.HomotopyRel
                  ((⟨Subtype.val, continuous_subtype_val⟩ :
                    C(↥(skeletonBelow X (p+2)), X)).comp u)
                  ((⟨Subtype.val, continuous_subtype_val⟩ :
                    C(↥(skeletonBelow X (p+1)), X)).comp v) P := {
                toHomotopy := H₁.toHomotopy
                prop' := by
                  intro t z hz
                  apply H₁.prop t z
                  exact skeletonBelow_mono (by omega : k+1 ≤ p+1) hz }
              have H₂' : ContinuousMap.HomotopyRel
                  ((⟨Subtype.val, continuous_subtype_val⟩ :
                    C(↥(skeletonBelow X (p+1)), X)).comp v)
                  ((⟨Subtype.val, continuous_subtype_val⟩ :
                    C(↥(skeletonBelow X (k+1)), X)).comp w) P := {
                toHomotopy := H₂.toHomotopy
                prop' := by
                  intro t z hz
                  apply H₂.prop t z
                  change (v z).val ∈ skeletonBelow X (k+1)
                  rw [hfix z hz]
                  exact hz }
              exact ⟨w, ⟨H₁'.trans H₂'⟩⟩
  exact hmain n hkn le_rfl f

end CurveComplexGenusTwo.CWHurewicz
