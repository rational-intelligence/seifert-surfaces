import B1ActualNativeBoundaryBounds_v468
import B1ClosedContinuousRepresentative_v468
import B1NativeClassicalAtRadius_v468
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- The original inputs yield a continuous positive classical Dirichlet representative
on the entire closed half-disc. Boundary datum 1, literal native H1/H10 and the
exact full weak equation are constructed, without assuming boundary regularity. -/
theorem actual_halfdisc_native_closed_classical_positive_v468
    (D : B1OriginalData (g := g) J) (s : Circle) (W : CollarWindow D s) :
    ∃ R : ℝ, 0 < R ∧ R < W.R ∧ ∃ h : E2 → ℝ,
      ContinuousOn h (closedHalfDisc R) ∧
      (∀ x ∈ frontier (halfDisc R), h x = 1) ∧
      (∀ x ∈ closedHalfDisc R, (1/2 : ℝ) ≤ h x) ∧
      ContDiffOn ℝ ∞ h (halfDisc R) ∧
      H1On (halfDisc R) h (planarGradient h) ∧
      H10On (halfDisc R) (fun x => h x-1) (planarGradient h) ∧
      WeakLinearEquationOn (halfDisc R) W.a W.b W.c h (planarGradient h) ∧
      (∀ x ∈ halfDisc R, classicalL W.a W.b W.c h x = 0) := by
  classical
  obtain ⟨R,S,M,N,hR,hRS,hSW,hM,hN,f,hf,h1,h10,heq,hpos,hbound,hcircleBound⟩ :=
    actual_halfdisc_native_two_boundary_bounds_v468 D s W
  let U := halfDisc R
  let h := U.piecewise f (fun _ => 1)
  have hU : IsOpen U := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous)
  obtain ⟨hhc,hhfrontier,hhf⟩ := halfdisc_closed_continuous_representative_v468 R S M N hR hM.le hN.le
    ((hR.le).trans hRS) f hf.continuousOn hbound hcircleBound
  have hae : f =ᵐ[volume.restrict U] h := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    exact (hhf x hx).symm
  have h1h := native_h1_congr_ae_v468 U f h (planarGradient f) (planarGradient f) h1 hae EventuallyEq.rfl
  have h10h := native_h10_congr_ae_v468 U (fun x => f x-1) (fun x => h x-1)
    (planarGradient f) (planarGradient f) h10 (hae.mono fun x hx => by dsimp only; rw [hx]) EventuallyEq.rfl
  have heqh := native_linear_congr_ae_v468 U W.a W.b W.c f h
    (planarGradient f) (planarGradient f) h1 heq hae EventuallyEq.rfl
  have hhsm : ContDiffOn ℝ ∞ h U := hf.congr (fun x hx => hhf x hx)
  have hhpos : ∀ x ∈ closedHalfDisc R, (1/2 : ℝ) ≤ h x := by
    intro x hx
    by_cases hxp : x ∈ U
    · change (1/2 : ℝ) ≤ (halfDisc R).piecewise f (fun _ => 1) x
      rw [hhf x hxp]
      exact hpos x hxp
    · have hh : h x = 1 := by simp only [h,Set.piecewise,ite_eq_right hxp]
      rw [hh]; norm_num
  have hgrad : ∀ x ∈ U, planarGradient f x = planarGradient h x := by
    intro x hx
    have he : h =ᶠ[𝓝 x] f := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact hhf y hy
    simp only [planarGradient,he.fderiv_eq]
  have hdfae : planarGradient f =ᵐ[volume.restrict U] planarGradient h := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    exact hgrad x hx
  have h1exact := native_h1_congr_ae_v468 U h h (planarGradient f) (planarGradient h)
    h1h EventuallyEq.rfl hdfae
  have h10exact := native_h10_congr_ae_v468 U (fun x => h x-1) (fun x => h x-1)
    (planarGradient f) (planarGradient h) h10h EventuallyEq.rfl hdfae
  have heqexact := native_linear_congr_ae_v468 U W.a W.b W.c h h
    (planarGradient f) (planarGradient h) h1h heqh EventuallyEq.rfl hdfae
  have hclass := actual_halfdisc_native_weak_classical_at_radius_v468 D s W R (hRS.trans_lt hSW) h hhsm heqexact
  exact ⟨R,hR,hRS.trans_lt hSW,h,hhc,hhfrontier,hhpos,hhsm,h1exact,h10exact,heqexact,hclass⟩

end SeifertSurfaces.OriginalEndpoints.B1Tangency
