import NativeBoundaryConvexRetraction
import NativeBoundaryTangentialSchauderHolder

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization

/-- The literal closed cap used by the native local Holder gains. -/
def nativeClosedBoundaryCap (c : E2) (r : ℝ) : Set E2 :=
  Metric.closedBall c r ∩ {x : E2 | 0 ≤ x 0}

theorem nativeClosedBoundaryCap_isClosed (c : E2) (r : ℝ) :
    IsClosed (nativeClosedBoundaryCap c r) :=
  Metric.isClosed_closedBall.inter
    (isClosed_le continuous_const (EuclideanSpace.proj (0 : Fin 2)).continuous)

theorem nativeClosedBoundaryCap_convex (c : E2) (r : ℝ) :
    Convex ℝ (nativeClosedBoundaryCap c r) :=
  (convex_closedBall c r).inter
    ((convex_Ici (0 : ℝ)).linear_preimage
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).toLinearMap)

theorem nativeClosedBoundaryCap_nonempty (c : E2) (r : ℝ)
    (hr : 0 ≤ r) (hc : 0 ≤ c 0) : (nativeClosedBoundaryCap c r).Nonempty :=
  ⟨c, Metric.mem_closedBall_self hr, hc⟩

/-- Native cap specialization, preserving the original matrix coercivity,
entrywise bound, and Holder constant everywhere. -/
theorem native_holder_matrix_extension_on_cap
    (c : E2) (r : ℝ) (hr : 0 ≤ r) (hc : 0 ≤ c 0)
    (a : E2 → Matrix (Fin 2) (Fin 2) ℝ) (H α : ℝ≥0) (κ M : ℝ)
    (hholder : ∀ i j, HolderOnWith H α (fun x => a x i j) (nativeClosedBoundaryCap c r))
    (hbound : ∀ x ∈ nativeClosedBoundaryCap c r, ∀ ξ : E2,
      κ * ‖ξ‖ ^ 2 ≤ inner ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2) (a x) ξ) ξ ∧
        ∀ i j, |a x i j| ≤ M) :
    ∃ A : E2 → Matrix (Fin 2) (Fin 2) ℝ,
      EqOn A a (nativeClosedBoundaryCap c r) ∧
      (∀ i j, HolderWith H α (fun x => A x i j)) ∧
      (∀ x : E2, ∀ ξ : E2,
        κ * ‖ξ‖ ^ 2 ≤ inner ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2) (A x) ξ) ξ ∧
          ∀ i j, |A x i j| ≤ M) :=
  native_holder_matrix_extension (nativeClosedBoundaryCap c r)
    (nativeClosedBoundaryCap_isClosed c r) (nativeClosedBoundaryCap_convex c r)
    (nativeClosedBoundaryCap_nonempty c r hr hc) a H α κ M hholder hbound

/-- Vector or scalar forcing on the same cap extends through the same
nonexpansive retraction, preserving its Holder constant and norm bound. -/
theorem native_holder_field_extension_on_cap
    {F : Type*} [NormedAddCommGroup F]
    (c : E2) (r : ℝ) (hr : 0 ≤ r) (hc : 0 ≤ c 0)
    (f : E2 → F) (H α : ℝ≥0) (B : ℝ)
    (hholder : HolderOnWith H α f (nativeClosedBoundaryCap c r))
    (hbound : ∀ x ∈ nativeClosedBoundaryCap c r, ‖f x‖ ≤ B) :
    ∃ fbar : E2 → F, EqOn fbar f (nativeClosedBoundaryCap c r) ∧
      HolderWith H α fbar ∧ ∀ x, ‖fbar x‖ ≤ B := by
  obtain ⟨P, hP, heq, hL⟩ := native_closed_convex_lipschitz_retraction
    (nativeClosedBoundaryCap c r) (nativeClosedBoundaryCap_isClosed c r)
    (nativeClosedBoundaryCap_convex c r) (nativeClosedBoundaryCap_nonempty c r hr hc)
  refine ⟨fun x => f (P x), ?_, ?_, ?_⟩
  · intro x hx
    change f (P x) = f x
    rw [heq hx, id_eq]
  · have hh := hholder.comp_holderWith hL.holderWith hP
    convert hh using 1 <;> simp [Function.comp_def]
  · intro x
    exact hbound (P x) (hP x)

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
