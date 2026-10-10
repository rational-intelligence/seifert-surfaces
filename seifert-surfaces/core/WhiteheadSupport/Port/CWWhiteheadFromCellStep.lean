import WhiteheadSupport.Port.CWCylinderStep
import WhiteheadSupport.Port.CWWhiteheadConditional
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.Homotopy.Contractible

namespace SeifertSurfaces.WhiteheadSupport.Port.CW

universe u v

open _root_.Topology
open scoped ContinuousMap

/-- Full point-map Whitehead conclusion, using the proved Hausdorff cellular
extension step rather than a separately supplied step hypothesis. -/
theorem cwPointWhiteheadT2_from_hpi
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] [PathConnectedSpace X]
    (hpi : ∀ n : ℕ, 1 ≤ n → ∀ x : X,
      Subsingleton (HomotopyGroup.Pi n X x)) :
    Nonempty (X ≃ₕ Unit) := by
  apply cwPointWhiteheadT2_of_step hpi
  intro x₀ n Hn
  exact cwExtendNullhomotopyStepT2 x₀ n hpi Hn

/-- Contractibility follows from the actual point-map Whitehead equivalence. -/
theorem contractibleOfCWAllPiSubsingletonT2_actual
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] [PathConnectedSpace X]
    (hpi : ∀ n : ℕ, 1 ≤ n → ∀ x : X,
      Subsingleton (HomotopyGroup.Pi n X x)) :
    ContractibleSpace X := by
  exact (Classical.choice (cwPointWhiteheadT2_from_hpi hpi)).contractibleSpace

end SeifertSurfaces.WhiteheadSupport.Port.CW
