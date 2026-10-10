import QuotientBasic

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology BigOperators ContDiff
namespace SeifertSurfaces.QuasilinearLocalization.QuotientHelpers
open SeifertSurfaces.AppendixACoordinates

lemma coordinate_norm (k : Fin 2) : ‖coordinateVector 2 k‖ = 1 := by
  simp [coordinateVector, PiLp.norm_single]

lemma shift_distance (k : Fin 2) (h : ℝ) (x : E2) : dist (shift k h x) x = |h| := by
  simp [dist_eq_norm, shift, norm_smul, coordinate_norm]

lemma shift_mem_closedBall (x₀ x : E2) (r : ℝ) (hr : 0 < r)
    (hx : x ∈ Metric.closedBall x₀ (3 * r)) (k : Fin 2) (h : ℝ) (hh : |h| < r) :
    shift k h x ∈ Metric.closedBall x₀ (4 * r) := by
  apply Metric.mem_closedBall.mpr
  calc
    dist (shift k h x) x₀ ≤ dist (shift k h x) x + dist x x₀ := dist_triangle _ _ _
    _ ≤ |h| + 3 * r := by rw [shift_distance]; exact add_le_add_right (Metric.mem_closedBall.mp hx) _
    _ ≤ 4 * r := by linarith

lemma ball_two_subset_closed_three (x₀ : E2) (r : ℝ) (hr : 0 < r) :
    Metric.ball x₀ (2 * r) ⊆ Metric.closedBall x₀ (3 * r) :=
  Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))

lemma jetSegment_mem (u : E2 → ℝ) (x₀ : E2) (r : ℝ) (hr : 0 < r)
    (T : Set Jet) (hT : Convex ℝ T)
    (hjetsT : ∀ x ∈ Metric.closedBall x₀ (4 * r), firstJet u x ∈ T)
    (k : Fin 2) (h : ℝ) (hh : |h| < r) (x : E2)
    (hx : x ∈ Metric.closedBall x₀ (3 * r)) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    jetSegment u k h x t ∈ T := by
  apply hT (hjetsT x (Metric.closedBall_subset_closedBall (by linarith) hx))
    (hjetsT (shift k h x) (shift_mem_closedBall x₀ x r hr hx k h hh))
    (by linarith [ht.2]) ht.1
  ring

lemma quotient_contDiffOn (Ω : Set E2) (hΩ : IsOpen Ω) (u : E2 → ℝ)
    (hC1 : ContDiffOn ℝ 1 u Ω) (x₀ : E2) (r : ℝ) (hr : 0 < r)
    (hball : Metric.closedBall x₀ (4 * r) ⊆ Ω) (k : Fin 2) (h : ℝ) (hh : |h| < r) :
    ContDiffOn ℝ 1 (differenceQuotient u k h) (Metric.ball x₀ (2 * r)) := by
  have hxΩ : Metric.ball x₀ (2 * r) ⊆ Ω :=
    (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))).trans hball
  have hsΩ : MapsTo (shift k h) (Metric.ball x₀ (2 * r)) Ω := by
    intro x hx
    exact hball (shift_mem_closedBall x₀ x r hr (ball_two_subset_closed_three x₀ r hr hx) k h hh)
  have hs : ContDiff ℝ 1 (shift k h) := by unfold shift; fun_prop
  have hu := (hC1.comp hs.contDiffOn hsΩ).sub (hC1.mono hxΩ)
  have heq : differenceQuotient u k h = h⁻¹ • (u ∘ shift k h - u) := by
    funext x
    simp [differenceQuotient, div_eq_mul_inv, mul_comm]
  rw [heq]
  exact hu.const_smul h⁻¹

lemma gradient_fderiv_norm (u : E2 → ℝ) (x : E2) :
    ‖fderiv ℝ u x‖ = ‖planarGradient u x‖ := by
  rw [← Helpers.gradient_dual, (InnerProductSpace.toDual ℝ E2).norm_map]

lemma quotient_bound (Ω : Set E2) (hΩ : IsOpen Ω) (u : E2 → ℝ)
    (hC1 : ContDiffOn ℝ 1 u Ω) (x₀ : E2) (r M : ℝ) (hr : 0 < r)
    (hball : Metric.closedBall x₀ (4 * r) ⊆ Ω)
    (hgrad : ∀ x ∈ Metric.closedBall x₀ (4 * r), ‖planarGradient u x‖ ≤ M)
    (k : Fin 2) (h : ℝ) (hh : 0 < |h|) (hhr : |h| < r)
    (x : E2) (hx : x ∈ Metric.ball x₀ (2 * r)) : |differenceQuotient u k h x| ≤ M := by
  have hx4 : x ∈ Metric.closedBall x₀ (4 * r) :=
    (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))) hx
  have hs4 := shift_mem_closedBall x₀ x r hr (ball_two_subset_closed_three x₀ r hr hx) k h hhr
  have hle := (convex_closedBall x₀ (4 * r)).norm_image_sub_le_of_norm_fderiv_le
    (fun y hy => (hC1.contDiffAt (hΩ.mem_nhds (hball hy))).differentiableAt (by simp))
    (fun y hy => (gradient_fderiv_norm u y).trans_le (hgrad y hy)) hx4 hs4
  rw [show ‖shift k h x - x‖ = |h| by simpa [dist_eq_norm] using shift_distance k h x] at hle
  rw [differenceQuotient, abs_div]
  exact (div_le_iff₀ hh).mpr (by simpa [Real.norm_eq_abs] using hle)

end SeifertSurfaces.QuasilinearLocalization.QuotientHelpers
