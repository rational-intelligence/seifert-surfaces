import B1BoundaryH3Step_v468
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open ChartMetricProvider.Variational.DirectWeak.BoundaryContinuation
set_option maxHeartbeats 1000000

/-- Full boundary H3 for a positive solution constructed from the exact
original D,s,W data. Every derivative gain applies to that same solution. -/
theorem actual_positive_boundary_full_H3_v468
    (D : B1OriginalData (g := g) J) (s : Circle) (W : CollarWindow D s) :
    ∃ R : ℝ, 0<R ∧ R<W.R ∧ ∃ h : E2 → ℝ,
      ContinuousOn h (closedHalfDisc R) ∧
      (∀ x ∈ frontier (halfDisc R), h x=1) ∧
      (∀ x ∈ closedHalfDisc R, (1/2 : ℝ)≤h x) ∧
      ContDiffOn ℝ ∞ h (halfDisc R) ∧
      H1On (halfDisc R) h (planarGradient h) ∧
      H10On (halfDisc R) (fun x => h x-1) (planarGradient h) ∧
      WeakLinearEquationOn (halfDisc R) W.a W.b W.c h (planarGradient h) ∧
      (∀ x ∈ halfDisc R, classicalL W.a W.b W.c h x=0) ∧
      MemWkp 3 2 h (halfDisc (R/64)) := by
  obtain ⟨R,hR,hRW,h,hhc,hfront,hpos,hs,h1,h0,heq,hcl,hH2,hcut⟩ :=
    actual_positive_boundary_tangent_cutoff_H2_v468 D s W
  have hsmall : 0<R/64 := by positivity
  have hsR : R/64<R := by linarith
  have hsub : halfDisc (R/64) ⊆ halfDisc R :=
    fun x hx => ⟨Metric.ball_subset_ball hsR.le hx.1,hx.2⟩
  have hU : IsOpen (halfDisc (R/64)) := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)
  have hUc : IsCompact (closure (halfDisc (R/64))) := (isCompact_closedBall (0:E2) (R/64)).of_isClosed_subset
    isClosed_closure (closure_minimal (fun x hx => Metric.ball_subset_closedBall hx.1) Metric.isClosed_closedBall)
  have hball : Metric.closedBall (0:E2) (R/32) ⊆ Metric.ball 0 (R/8) := by
    intro x hx
    exact Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hx) (by linarith))
  obtain ⟨chi,hchi,hchic,hchione,hchisub,hchirange⟩ :=
    DifferentialGeometry.Analysis.exists_bump_compact (isCompact_closedBall (0:E2) (R/32))
      Metric.isOpen_ball hball
  have ht := hcut (R/8) (by positivity) (by linarith) chi hchi hchic hchisub
    (R/64) hsmall (by linarith)
  have ht' : MemWkp 2 2 (fun x => planarGradient h x 0) (halfDisc (R/64)) := by
    apply (MemWkp_congr_ae (by norm_num) hU _).mp ht
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    rw [hchione.self_of_nhdsSet (Metric.closedBall_subset_closedBall
      (by linarith : R/64≤R/32) (Metric.ball_subset_closedBall hx.1))]
    simp only [Pi.one_apply,one_mul]
  have hH2' := hH2 (R/64) hsmall (by linarith)
  have hclosed : closure (halfDisc (R/64)) ⊆ closedHalfDisc W.R := by
    apply closure_minimal
    · intro x hx
      exact ⟨Metric.ball_subset_closedBall
        (Metric.ball_subset_ball (hsR.trans hRW).le hx.1),hx.2.le⟩
    · exact Metric.isClosed_closedBall.inter
        (isClosed_le continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)
  have hS := actual_halfdisc_boundary_lower_source_tower_v468 D s W R hRW h
    (planarGradient h) h1 _ hU hUc hsub hclosed 1 hH2'
  have hP : IsCompact (closedHalfDisc R) := (isCompact_closedBall (0:E2) R).inter_right
    (isClosed_le continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)
  have hPW : closedHalfDisc R ⊆ closedHalfDisc W.R :=
    fun x hx => ⟨Metric.closedBall_subset_closedBall hRW.le hx.1,hx.2⟩
  obtain ⟨B,hBa⟩ := actual_closed_halfdisc_smooth_elliptic_extension_v468 D s W
    (closedHalfDisc R) hP hPW
  refine ⟨R,hR,hRW,h,hhc,hfront,hpos,hs,h1,h0,heq,hcl,?_⟩
  apply native_boundary_full_H3_step_v468 (R/64) h (hs.mono hsub) hH2' ht' B
    (fun x => inner ℝ (W.b x) (planarGradient h x)+W.c x*h x) hS
  intro x hx
  have hcoeff : (fun y => B.a y)=ᶠ[𝓝 x] W.a := by
    filter_upwards [(show IsOpen (halfDisc R) from Metric.isOpen_ball.inter
      (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)).mem_nhds
        (hsub hx)] with y hy
    exact hBa y ⟨Metric.ball_subset_closedBall hy.1,hy.2.le⟩
  have he := hcl x (hsub hx)
  change (∑ i : Fin 2, fderiv ℝ
    (fun y => matrixAction (B.a y) (planarGradient h y) i) x (coordinateVector 2 i))+
    (inner ℝ (W.b x) (planarGradient h x)+W.c x*h x)=0
  have he' : (∑ i : Fin 2, fderiv ℝ
    (fun y => matrixAction (W.a y) (planarGradient h y) i) x (coordinateVector 2 i))+
    (inner ℝ (W.b x) (planarGradient h x)+W.c x*h x)=0 := by
      simpa only [classicalL,add_assoc] using he
  convert he' using 1
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  exact congrArg (fun L : E2 →L[ℝ] ℝ => L (coordinateVector 2 i))
    (EventuallyEq.fderiv_eq (hcoeff.mono (fun y hy => by
      change B.a y=W.a y at hy
      change matrixAction (B.a y) (planarGradient h y) i=matrixAction (W.a y) (planarGradient h y) i
      rw [hy])))
end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.actual_positive_boundary_full_H3_v468
