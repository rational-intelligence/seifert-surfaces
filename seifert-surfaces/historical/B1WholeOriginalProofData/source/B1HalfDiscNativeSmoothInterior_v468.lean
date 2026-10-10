import B1NativeSmoothRepresentative_v468
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
set_option maxHeartbeats 0

private theorem leOn_of_ae_le_v468 (U : Set E2) (hU : IsOpen U) (f : E2 → ℝ) (C : ℝ)
    (hf : ContinuousOn f U) (hae : ∀ᵐ x ∂volume.restrict U, f x ≤ C) :
    ∀ x ∈ U, f x ≤ C := by
  have he : (fun x => min (f x) C) =ᵐ[volume.restrict U] f :=
    hae.mono fun x hx => min_eq_left hx
  have hp := Measure.eqOn_open_of_ae_eq he hU (hf.inf continuousOn_const) hf
  intro x hx
  exact min_eq_left_iff.mp (hp hx)

/-- The literal original weak solution now has a smooth positive interior representative;
all H1/H10/equation fields are transported across the checked a.e. representative. -/
theorem actual_halfdisc_native_smooth_positive_interior_v468
    (D : B1OriginalData (g := g) J) (s : Circle) (W : CollarWindow D s) :
    ∃ R : ℝ, 0 < R ∧ R < W.R ∧ ∃ f : E2 → ℝ, ∃ df : E2 → E2,
      ContDiffOn ℝ ∞ f (halfDisc R) ∧
      H1On (halfDisc R) f df ∧
      H10On (halfDisc R) (fun x => f x - 1) df ∧
      WeakLinearEquationOn (halfDisc R) W.a W.b W.c f df ∧
      (∀ x ∈ halfDisc R, (1/2 : ℝ) ≤ f x) := by
  obtain ⟨R,hR,hRW,u,du,hu,h10,heq,hpos⟩ := actual_halfdisc_native_positive_solution_v468 D s W
  obtain ⟨f,hf,hae⟩ := actual_halfdisc_native_smooth_interior_v468 D s W R hRW u du hu heq
  have hdf : du =ᵐ[volume.restrict (halfDisc R)] planarGradient f :=
    native_smooth_gradient_ae_v468 (halfDisc R)
      (Metric.isOpen_ball.inter (isOpen_lt continuous_const
        (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous)) u f du hu hf hae
  have h1f := native_h1_congr_ae_v468 (halfDisc R) u f du (planarGradient f) hu hae hdf
  have h10f := native_h10_congr_ae_v468 (halfDisc R) (fun x => u x - 1)
    (fun x => f x - 1) du (planarGradient f) h10
    (hae.mono fun x hx => by dsimp only; rw [hx]) hdf
  have heqf := native_linear_congr_ae_v468 (halfDisc R) W.a W.b W.c u f du
    (planarGradient f) hu heq hae hdf
  have hposf : ∀ᵐ x ∂volume.restrict (halfDisc R), (1/2 : ℝ) ≤ f x := by
    filter_upwards [hpos,hae] with x hx he
    rw [← he]
    exact hx
  have hpoint : ∀ x ∈ halfDisc R, (1/2 : ℝ) ≤ f x := by
    intro x hx
    have hn := leOn_of_ae_le_v468 (halfDisc R)
      (Metric.isOpen_ball.inter (isOpen_lt continuous_const
        (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous))
      (fun y => -f y) (-(1/2 : ℝ))
      (hf.continuousOn.neg) (hposf.mono fun y hy => by linarith)
    have hh := hn x hx
    linarith
  exact ⟨R,hR,hRW,f,planarGradient f,hf,h1f,h10f,heqf,hpoint⟩

end SeifertSurfaces.OriginalEndpoints.B1Tangency
