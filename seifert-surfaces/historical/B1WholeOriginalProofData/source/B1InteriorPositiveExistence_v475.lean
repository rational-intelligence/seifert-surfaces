import B1InteriorSmallDomain_v475
import B1InteriorNativeClassical_v475
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Restriction of the internal analytic window keeps exactly the original
coefficient functions. -/
def InteriorCoefficientWindow_v475.restrict (W : InteriorCoefficientWindow_v475)
    (r : ℝ) (hr : 0 < r) (hrR : r ≤ W.R) : InteriorCoefficientWindow_v475 where
  R := r
  R_pos := hr
  O := W.O
  isOpen_O := W.isOpen_O
  closed_subset := fun x hx => W.closed_subset
    ⟨Metric.closedBall_subset_closedBall hrR hx.1,hx.2⟩
  a := W.a
  b := W.b
  c := W.c
  smooth_a := W.smooth_a
  smooth_b := W.smooth_b
  smooth_c := W.smooth_c
  symmetric := fun x hx => W.symmetric x
    ⟨Metric.closedBall_subset_closedBall hrR hx.1,hx.2⟩
  ell := W.ell
  ell_pos := W.ell_pos
  coercive := fun x hx => W.coercive x
    ⟨Metric.closedBall_subset_closedBall hrR hx.1,hx.2⟩

/-- Arbitrary smooth symmetric elliptic coefficients have a genuinely constructed
smooth positive classical solution on a small half-disc.  The boundary is
artificial; only the smooth interior representative is used later. -/
theorem interior_window_positive_classical_exists_v475
    (W : InteriorCoefficientWindow_v475) :
    ∃ r : ℝ, 0 < r ∧ r < W.R ∧ ∃ h : E2 → ℝ,
      ContDiffOn ℝ ∞ h (halfDisc r) ∧
      (∀ x ∈ halfDisc r, (1/2 : ℝ) ≤ h x) ∧
      (∀ x ∈ halfDisc r, classicalL W.a W.b W.c h x = 0) := by
  obtain ⟨r₀,κ,hr₀,hr₀R,hκ,htest⟩ := interior_window_small_test_coercivity_v475 W
  obtain ⟨r₁,hr₁,hr₁R,v,hv,hvb,hvL⟩ := interior_window_positive_barrier_v475 W
  let r := min r₀ r₁
  have hr : 0 < r := lt_min hr₀ hr₁
  have hrR : r < W.R := lt_of_le_of_lt (min_le_left _ _) hr₀R
  let V := W.restrict r hr hrR.le
  have hcoer := halfdisc_test_coercivity_mono_v468 r₀ r κ (min_le_left _ _)
    W.a W.b W.c htest
  have hclosed : closedHalfDisc r ⊆ closedHalfDisc r₁ := fun x hx =>
    ⟨Metric.closedBall_subset_closedBall (min_le_right _ _) hx.1,hx.2⟩
  have hopen : halfDisc r ⊆ halfDisc r₁ := fun x hx =>
    ⟨Metric.ball_subset_ball (min_le_right _ _) hx.1,hx.2⟩
  obtain ⟨u,du,hu,h10,heq,hpos⟩ := interior_window_native_positive_solution_v475 V κ hκ
    hcoer v hv (fun x hx => hvb x (hclosed hx))
    (fun x hx => le_trans (by norm_num : (0:ℝ) ≤ 1) (hvL x (hopen hx)))
  obtain ⟨h,hh,-,-,-,hp,he⟩ := interior_window_classical_positive_v475 V u du hu h10 heq hpos
  exact ⟨r,hr,hrR,h,hh,hp,he⟩

#print axioms interior_window_positive_classical_exists_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
