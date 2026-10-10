import NativeBoundaryLinearNormalReconstruction

set_option autoImplicit false
set_option maxHeartbeats 100000
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization

/-- Full C2 and Hessian Holder gain for the same native linear solution. -/
theorem native_linear_C2_holder_gain
    (r κ M0 : ℝ) (hr : 0 < r) (hκ : 0 < κ) (hM0 : 0 < M0)
    (C : LinearizedCoefficients) (v : E2 → ℝ) (α : ℝ≥0)
    (hα : 0 < α) (hα1 : α < 1)
    (hv : ContDiffOn ℝ 1 v (closedHalfDisc (4 * r)))
    (ha : ContDiffOn ℝ 1 C.a (closedHalfDisc (4 * r)))
    (hd : ContDiffOn ℝ 1 C.d (closedHalfDisc (4 * r)))
    (hDa : ∃ A, HolderOnWith A α (fderivWithin ℝ C.a (closedHalfDisc (4 * r))) (closedHalfDisc (4 * r)))
    (hDd : ∃ A, HolderOnWith A α (fderivWithin ℝ C.d (closedHalfDisc (4 * r))) (closedHalfDisc (4 * r)))
    (hDv : ∃ A, HolderOnWith A α (fderivWithin ℝ v (closedHalfDisc (4 * r))) (closedHalfDisc (4 * r)))
    (hvi : ContDiffOn ℝ 2 v (openHalfDisc (4 * r)))
    (hz : ∀ x ∈ flatBoundary (4 * r), v x = 0)
    (hc : C.c = 0) (hb : C.b = 0) (hq : C.q = 0) (hf : C.f = 0)
    (hprincipal : ∀ x ∈ closedHalfDisc (4 * r),
      (∀ ξ : E2, κ * ‖ξ‖ ^ 2 ≤ inner ℝ (C.a x ξ) ξ) ∧ ‖C.a x‖ ≤ M0)
    (hw : LinearWeakEquation (openHalfDisc (4 * r)) C v (planarGradient v)) :
    ContDiffOn ℝ 2 v (closedHalfDisc (r / 64)) ∧
      ∀ j : Fin 2,
        ContDiffOn ℝ 1 (fun x => fderivWithin ℝ v (closedHalfDisc (4 * r)) x (coordinateVector 2 j))
          (closedHalfDisc (r / 64)) ∧
        ∃ A, HolderOnWith A α
          (fderivWithin ℝ (fun x => fderivWithin ℝ v (closedHalfDisc (4 * r)) x (coordinateVector 2 j))
            (closedHalfDisc (r / 64))) (closedHalfDisc (r / 64)) := by
  obtain ⟨ht, htH⟩ := native_linear_tangential_C1_holder_gain r κ M0 hr hκ hM0 C v α hα hα1
    hv ha hd hDa hDd hDv hvi hz hc hb hq hf hprincipal hw
  have hgain := native_linear_normal_C1_holder_reconstruction (4 * r) (r / 32) κ
    (by positivity) (by linarith) hκ C v α hα hα1.le hv ha hd hDa hDd hDv hvi hc hb hq hf
    (fun x hx => (hprincipal x hx).1) hw ht htH
  simpa only [show r / 32 / 2 = r / 64 by ring] using hgain

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
