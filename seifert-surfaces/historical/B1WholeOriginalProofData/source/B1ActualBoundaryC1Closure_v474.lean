import B1NativeBoundaryGradientContinuous_v468
import Mathlib.Analysis.Calculus.FDeriv.Extend
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open DifferentialGeometry.Analysis.Sobolev.Euclidean
set_option maxHeartbeats 40000
set_option maxRecDepth 1000
set_option backward.isDefEq.respectTransparency false


private theorem halfdisc_closure_eq_v474 (R : ℝ) (hR : 0<R) :
    closure (halfDisc R) = closedHalfDisc R := by
  letI : IsBoundedSMul ℝ E2 := NormedSpace.toIsBoundedSMul
  letI : ContinuousSMul ℝ E2 := IsBoundedSMul.continuousSMul
  have hc : Convex ℝ (closedHalfDisc R) :=
    (convex_closedBall (0:E2) R).inter
      (convex_halfSpace_ge (f := fun x : E2 => x 1) ⟨by intros; rfl,by intros; rfl⟩ 0)
  have hint : interior (closedHalfDisc R) = halfDisc R := by
    change interior (Metric.closedBall (0:E2) R ∩ {x : E2 | 0≤x 1}) = _
    rw [interior_inter,interior_closedBall _ hR.ne',interior_halfSpace]
    rfl
  have hne : (interior (closedHalfDisc R)).Nonempty := by
    change (interior (closedHalfDisc R)).Nonempty
    rw [hint]
    refine ⟨(R/2) • coordinateVector 2 1,?_,?_⟩
    · apply Metric.mem_ball.mpr
      rw [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (half_pos hR)]
      have hn : ‖coordinateVector 2 (1:Fin 2)‖ = 1 := by simp [coordinateVector]
      rw [hn,mul_one]
      linarith
    · simpa [coordinateVector] using half_pos hR
  have hclosed : IsClosed (closedHalfDisc R) := Metric.isClosed_closedBall.inter
    (isClosed_le continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)
  rw [←hint,hc.closure_interior_eq_closure_of_nonempty_interior hne,hclosed.closure_eq]

/-- A continuous ambient gradient representative gives the literal C1
within-closure regularity on the flat edge. -/
theorem native_halfdisc_C1_closure_v474 (R : ℝ) (hR : 0<R) (u : E2 → ℝ)
    (hs : ContDiffOn ℝ ∞ u (halfDisc R))
    (hc : ContinuousOn u (closedHalfDisc R))
    (G : Fin 2 → E2 → ℝ) (hG : ∀ i, Continuous (G i))
    (heq : ∀ i, EqOn (G i) (fun x => planarGradient u x i) (halfDisc R)) :
    ContDiffOn ℝ 1 u (closedHalfDisc R) := by
  let L : E2 → (E2 →L[ℝ] ℝ) := fun x =>
    G 0 x • (EuclideanSpace.proj (𝕜:=ℝ) (0:Fin 2)) +
      G 1 x • (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2))
  have hL : Continuous L := ((hG 0).smul continuous_const).add
    ((hG 1).smul continuous_const)
  have hL_apply (x : E2) (i : Fin 2) : L x (coordinateVector 2 i)=G i x := by
    fin_cases i <;> simp [L,coordinateVector]
  have hd (x : E2) (hx : x∈halfDisc R) (i : Fin 2) :
      fderiv ℝ u x (coordinateVector 2 i)=G i x :=
    (QuasilinearLocalization.Helpers.gradient_apply u x i).symm.trans (heq i hx).symm
  have hdeq (x : E2) (hx : x∈halfDisc R) : fderiv ℝ u x=L x := by
    apply ContinuousLinearMap.ext
    intro v
    have hv : v=v 0 • coordinateVector 2 0+v 1 • coordinateVector 2 1 := by
      ext i
      fin_cases i <;> simp [coordinateVector]
    rw [hv,map_add,map_smul,map_smul,map_add,map_smul,map_smul,
      hd x hx 0,hd x hx 1,hL_apply,hL_apply]
  have hU : IsOpen (halfDisc R) := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)
  have hconv : Convex ℝ (halfDisc R) := (convex_ball (0:E2) R).inter
    (convex_halfSpace_gt (f:=fun x : E2 => x 1) ⟨by intros; rfl,by intros; rfl⟩ 0)
  have hclosure := halfdisc_closure_eq_v474 R hR
  have hcont : ∀ y ∈ closure (halfDisc R), ContinuousWithinAt u (halfDisc R) y := by
    intro y hy
    apply (hc y (hclosure ▸ hy)).mono
    intro z hz
    exact ⟨Metric.ball_subset_closedBall hz.1,hz.2.le⟩
  have hderiv (x : E2) : HasFDerivWithinAt u (L x) (closedHalfDisc R) x := by
    rw [←hclosure]
    apply hasFDerivWithinAt_closure_of_tendsto_fderiv
      (hs.differentiableOn (by simp)) hconv hU hcont
    have hev : (fun y => fderiv ℝ u y)=ᶠ[𝓝[halfDisc R] x] L := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact hdeq y hy
    exact hL.continuousAt.continuousWithinAt.congr' hev.symm
  have huniq : UniqueDiffOn ℝ (closedHalfDisc R) := by
    apply uniqueDiffOn_convex
      ((convex_closedBall (0:E2) R).inter
        (convex_halfSpace_ge (f:=fun x : E2 => x 1) ⟨by intros; rfl,by intros; rfl⟩ 0))
    have hint : interior (closedHalfDisc R)=halfDisc R := by
      change interior (Metric.closedBall (0:E2) R ∩ {x : E2 | 0≤x 1}) = _
      rw [interior_inter,interior_closedBall _ hR.ne',interior_halfSpace]
      rfl
    change (interior (closedHalfDisc R)).Nonempty
    rw [hint]
    refine ⟨(R/2) • coordinateVector 2 1,?_,?_⟩
    · apply Metric.mem_ball.mpr
      rw [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (half_pos hR)]
      have hn : ‖coordinateVector 2 (1:Fin 2)‖=1 := by simp [coordinateVector]
      rw [hn,mul_one]
      linarith
    · simpa [coordinateVector] using half_pos hR
  rw [show (1:ℕ∞ω)=0+1 by norm_num,
    contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn huniq]
  refine ⟨by simp, L, ?_,fun x hx => hderiv x⟩
  exact contDiffOn_zero.mpr hL.continuousOn

/-- Boundary C1 is derived for the same original-input positive solution;
all original weak, classical, trace, and positivity properties are retained. -/
theorem actual_positive_boundary_C1_closure_v474
    (D : B1OriginalData (g:=g) J) (s : Circle) (W : CollarWindow D s) :
    ∃ R : ℝ, 0<R ∧ R<W.R ∧ ∃ h : E2 → ℝ,
      ContinuousOn h (closedHalfDisc R) ∧
      (∀ x ∈ frontier (halfDisc R), h x=1) ∧
      (∀ x ∈ closedHalfDisc R, (1/2 : ℝ)≤h x) ∧
      ContDiffOn ℝ ∞ h (halfDisc R) ∧
      H1On (halfDisc R) h (planarGradient h) ∧
      H10On (halfDisc R) (fun x => h x-1) (planarGradient h) ∧
      WeakLinearEquationOn (halfDisc R) W.a W.b W.c h (planarGradient h) ∧
      (∀ x ∈ halfDisc R, classicalL W.a W.b W.c h x=0) ∧
      ContDiffOn ℝ 1 h (closedHalfDisc (R/256)) := by
  obtain ⟨R,hR,hRW,h,hhc,hfront,hpos,hs,h1,h0,heq,hcl,hgrad⟩ :=
    actual_positive_boundary_gradient_continuous_v468 D s W
  choose G hG heqG using hgrad
  have hq : 0<R/256 := by positivity
  have hsub : halfDisc (R/256) ⊆ halfDisc R :=
    fun x hx => ⟨Metric.ball_subset_ball (by linarith : R/256≤R) hx.1,hx.2⟩
  have hcsub : closedHalfDisc (R/256) ⊆ closedHalfDisc R :=
    fun x hx => ⟨Metric.closedBall_subset_closedBall (by linarith : R/256≤R) hx.1,hx.2⟩
  exact ⟨R,hR,hRW,h,hhc,hfront,hpos,hs,h1,h0,heq,hcl,
    native_halfdisc_C1_closure_v474 (R/256) hq h (hs.mono hsub) (hhc.mono hcsub) G hG heqG⟩
end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.actual_positive_boundary_C1_closure_v474
