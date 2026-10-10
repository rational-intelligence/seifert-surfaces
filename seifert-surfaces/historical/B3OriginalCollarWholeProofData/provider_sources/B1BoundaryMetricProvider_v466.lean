import VM03ExactCaller_v464
import B1GlobalInverseMetric
import B1SimultaneousMetricMinimizer
import Lean
noncomputable section
open Set Topology Function MeasureTheory
open scoped Manifold ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider
open SeifertSurfaces.AppendixACoordinates
open Variational
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- The original H02 consumer, assembled from the same internally chosen minimizer. -/
theorem boundary_metric_conformal_provider (R : ℝ) (A : E2 → Mat2)
    (G : InverseMetricData R A) (Ω : SmoothFlatJordanDomain R) :
    Nonempty (MetricDiscParametrization G Ω) := by
  have package :
      (∃ tau : PartialHomeomorph E2 E2,
      tau.source = closedDisc 1 ∧ tau.target = closure Ω.domain ∧
      tau '' disc 1 = Ω.domain ∧
      tau '' Metric.sphere (0 : E2) 1 = frontier Ω.domain ∧
      ContDiffOn ℝ 1 tau (closedDisc 1) ∧
      ContDiffOn ℝ 1 tau.symm (closure Ω.domain) ∧
      (∀ z ∈ closedDisc 1, Matrix.det (jacobianWithin tau (closedDisc 1) z) ≠ 0) ∧
      (∀ x ∈ closure Ω.domain,
        Matrix.det (jacobianWithin tau.symm (closure Ω.domain) x) ≠ 0) ∧
      (∀ i j, ∃ C : ℝ≥0, HolderOnWith C G.alpha
        (fun z => jacobianWithin tau (closedDisc 1) z i j) (closedDisc 1)) ∧
      (∀ i j, ∃ C : ℝ≥0, HolderOnWith C G.alpha
        (fun x => jacobianWithin tau.symm (closure Ω.domain) x i j) (closure Ω.domain)) ∧
      (∀ᵐ z ∂volume.restrict (disc 1),
        let M := inverseMetric A (tau z)
        let D := jacobianWithin tau (closedDisc 1) z
        D 0 1 = -(M 0 1 * D 0 0 + M 1 1 * D 1 0) ∧
        D 1 1 = M 0 0 * D 0 0 + M 0 1 * D 1 0)) → Nonempty (MetricDiscParametrization G Ω) := by
    have closeSystem :
        ∀ (tau : PartialHomeomorph E2 E2),
        tau.source = closedDisc 1 → tau.target = closure Ω.domain →
        (∀ i j, ∃ C : ℝ≥0, HolderOnWith C G.alpha
          (fun z => jacobianWithin tau (closedDisc 1) z i j) (closedDisc 1)) →
        (∀ᵐ z ∂volume.restrict (disc 1),
          let M := inverseMetric A (tau z)
          let D := jacobianWithin tau (closedDisc 1) z
          D 0 1 = -(M 0 1 * D 0 0 + M 1 1 * D 1 0) ∧
          D 1 1 = M 0 0 * D 0 0 + M 0 1 * D 1 0) →
        ∀ z ∈ closedDisc 1,
          let M := inverseMetric A (tau z)
          let D := jacobianWithin tau (closedDisc 1) z
          D 0 1 = -(M 0 1 * D 0 0 + M 1 1 * D 1 0) ∧
          D 1 1 = M 0 0 * D 0 0 + M 0 1 * D 1 0
        := by
      intro tau hs ht hfh heq
      have hc (i j : Fin 2) : ContinuousOn
          (fun z => jacobianWithin tau (closedDisc 1) z i j) (closedDisc 1) := by
        obtain ⟨C,hC⟩ := hfh i j
        exact hC.continuousOn G.alpha_pos
      have hm (i j : Fin 2) : ContinuousOn
          (fun z => inverseMetric A (tau z) i j) (closedDisc 1) := by
        obtain ⟨C,hC⟩ := G.holder i j
        have hm0 : ContinuousOn (fun x => inverseMetric A x i j) (closedHalfDisc R) :=
          hC.continuousOn G.alpha_pos
        have htc : ContinuousOn (fun z => tau z) (closedDisc 1) := by
          rw [← hs]
          exact tau.continuousOn_toFun
        apply hm0.comp htc
        · intro z hz
          apply Ω.closure_inside
          have hz' : z ∈ tau.source := by rwa [hs]
          simpa only [ht] using tau.map_source hz'
      have extend (f g : E2 → ℝ) (hf : ContinuousOn f (closedDisc 1))
          (hg : ContinuousOn g (closedDisc 1)) (he : f =ᵐ[volume.restrict (disc 1)] g) :
          EqOn f g (closedDisc 1) := by
        have hi : EqOn f g (disc 1) := Measure.eqOn_open_of_ae_eq he Metric.isOpen_ball
          (hf.mono Metric.ball_subset_closedBall) (hg.mono Metric.ball_subset_closedBall)
        apply hi.of_subset_closure hf hg Metric.ball_subset_closedBall
        rw [disc,closure_ball (0 : E2) (by norm_num : (1 : ℝ) ≠ 0)]
        exact Subset.rfl
      have h0 : ∀ z ∈ closedDisc 1,
          jacobianWithin tau (closedDisc 1) z 0 1 =
          -(inverseMetric A (tau z) 0 1 * jacobianWithin tau (closedDisc 1) z 0 0 +
            inverseMetric A (tau z) 1 1 * jacobianWithin tau (closedDisc 1) z 1 0) := by
        apply extend _ _ (hc 0 1)
        · intro z hz
          exact (((hm 0 1 z hz).mul (hc 0 0 z hz)).add
            ((hm 1 1 z hz).mul (hc 1 0 z hz))).neg
        · filter_upwards [heq] with z hz using hz.1
      have h1 : ∀ z ∈ closedDisc 1,
          jacobianWithin tau (closedDisc 1) z 1 1 =
          inverseMetric A (tau z) 0 0 * jacobianWithin tau (closedDisc 1) z 0 0 +
            inverseMetric A (tau z) 0 1 * jacobianWithin tau (closedDisc 1) z 1 0 := by
        apply extend _ _ (hc 1 1)
        · intro z hz
          exact ((hm 0 0 z hz).mul (hc 0 0 z hz)).add
            ((hm 0 1 z hz).mul (hc 1 0 z hz))
        · filter_upwards [heq] with z hz using hz.2
      exact fun z hz => ⟨h0 z hz,h1 z hz⟩
    have packageFields :
        ∀ (tau : PartialHomeomorph E2 E2),
        tau.source = closedDisc 1 → tau.target = closure Ω.domain →
        tau '' disc 1 = Ω.domain →
        tau '' Metric.sphere (0 : E2) 1 = frontier Ω.domain →
        ContDiffOn ℝ 1 tau (closedDisc 1) →
        ContDiffOn ℝ 1 tau.symm (closure Ω.domain) →
        (∀ z ∈ closedDisc 1, Matrix.det (jacobianWithin tau (closedDisc 1) z) ≠ 0) →
        (∀ x ∈ closure Ω.domain,
          Matrix.det (jacobianWithin tau.symm (closure Ω.domain) x) ≠ 0) →
        (∀ i j, ∃ C : ℝ≥0, HolderOnWith C G.alpha
          (fun z => jacobianWithin tau (closedDisc 1) z i j) (closedDisc 1)) →
        (∀ i j, ∃ C : ℝ≥0, HolderOnWith C G.alpha
          (fun x => jacobianWithin tau.symm (closure Ω.domain) x i j) (closure Ω.domain)) →
        (∀ z ∈ closedDisc 1,
          let M := inverseMetric A (tau z)
          let D := jacobianWithin tau (closedDisc 1) z
          D 0 1 = -(M 0 1 * D 0 0 + M 1 1 * D 1 0) ∧
          D 1 1 = M 0 0 * D 0 0 + M 0 1 * D 1 0) →
        Nonempty (MetricDiscParametrization G Ω)
        := by
      intro tau hs ht hi hb hf hg hfd hgd hfh hgh hcr
      have source_mem (z : E2) (hz : z ∈ closedDisc 1) : z ∈ tau.source := by
        rwa [hs]
      have target_mem (z : E2) (hz : z ∈ closedDisc 1) : tau z ∈ closure Ω.domain := by
        simpa only [ht] using tau.map_source (source_mem z hz)
      have inverse_image (S : Set E2) (hS : S ⊆ closedDisc 1) :
          tau.symm '' (tau '' S) = S := by
        ext z
        constructor
        · rintro ⟨x, ⟨y, hy, rfl⟩, rfl⟩
          simpa only [tau.left_inv (source_mem y (hS hy))] using hy
        · intro hz
          exact ⟨tau z, ⟨z, hz, rfl⟩, tau.left_inv (source_mem z (hS hz))⟩
      have his : tau.symm '' Ω.domain = disc 1 := by
        rw [← hi]
        exact inverse_image _ Metric.ball_subset_closedBall
      have hbs : tau.symm '' frontier Ω.domain = Metric.sphere (0 : E2) 1 := by
        rw [← hb]
        exact inverse_image _ Metric.sphere_subset_closedBall
      obtain ⟨base, hbase, hbzero⟩ := (show (0 : E2) ∈ tau '' Metric.sphere (0 : E2) 1 by
        rw [hb]; exact Ω.base_boundary)
      have hbaseinv : tau.symm 0 = base := by
        rw [← hbzero]
        exact tau.left_inv (source_mem base (Metric.sphere_subset_closedBall hbase))
      let lam : E2 → ℝ := fun z => Matrix.det (jacobianWithin tau (closedDisc 1) z)
      have hcont : ContinuousOn lam (closedDisc 1) := by
        have hc (i j : Fin 2) : ContinuousOn
            (fun z => jacobianWithin tau (closedDisc 1) z i j) (closedDisc 1) := by
          obtain ⟨C, hC⟩ := hfh i j
          exact hC.continuousOn G.alpha_pos
        intro z hz
        simp only [lam, Matrix.det_fin_two]
        exact ((hc 0 0 z hz).mul (hc 1 1 z hz)).sub ((hc 0 1 z hz).mul (hc 1 0 z hz))
      have halgebra (z : E2) (hz : z ∈ closedDisc 1) :
          0 < lam z ∧
          (jacobianWithin tau (closedDisc 1) z).transpose * inverseMetric A (tau z) *
            jacobianWithin tau (closedDisc 1) z = lam z • (1 : Mat2) := by
        let M := inverseMetric A (tau z)
        let D := jacobianWithin tau (closedDisc 1) z
        let a := M 0 0
        let b := M 0 1
        let c := M 1 1
        let u := D 0 0
        let v := D 1 0
        have hx := Ω.closure_inside (target_mem z hz)
        have hsym : M 1 0 = b := G.symmetric (tau z) hx 1 0
        have hm : M = !![a,b;b,c] := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp [a,b,c, hsym]
        have hd : D = !![u,-(b*u+c*v);v,a*u+b*v] := by
          obtain ⟨h0,h1⟩ := hcr z hz
          ext i j
          fin_cases i <;> fin_cases j <;> simp [u,v,a,b,c,D,M] at *
          all_goals assumption
        have hdet : a*c-b^2=1 := by
          have he := G.det_one (tau z) hx
          change Matrix.det M = 1 at he
          rw [hm,Matrix.det_fin_two] at he
          simpa [pow_two] using he
        have hdetD : lam z = a*u^2+2*b*u*v+c*v^2 := by
          change Matrix.det D = _
          rw [hd,Matrix.det_fin_two]
          simp
          ring
        have hform : D.transpose * M * D = (a*u^2+2*b*u*v+c*v^2) • (1 : Mat2) := by
          rw [hd,hm]
          ext i j
          fin_cases i <;> fin_cases j
          all_goals simp [Matrix.mul_apply,Fin.sum_univ_two,Matrix.transpose_apply]
          · ring
          · ring
          · ring
          · linear_combination (a*u^2+2*b*u*v+c*v^2)*hdet
        have ha : 0 < a := by
          have h := G.positive_definite (tau z) hx (coordinateVector 2 0) (by
            intro he
            have hz0 := congrArg (fun q : E2 => q 0) he
            simpa [coordinateVector,EuclideanSpace.single] using hz0)
          simpa [a,M,coordinateVector,matrixAction,EuclideanSpace.inner_eq_star_dotProduct,
            dotProduct,Fin.sum_univ_two] using h
        have hnonneg : 0 ≤ lam z := by
          have hid : a * (a*u^2+2*b*u*v+c*v^2) = (a*u+b*v)^2+v^2 := by
            nlinarith [hdet]
          rw [hdetD]
          apply nonneg_of_mul_nonneg_right (show 0 ≤ a * (a*u^2+2*b*u*v+c*v^2) by
            rw [hid]; positivity) ha
        refine ⟨lt_of_le_of_ne hnonneg (Ne.symm (hfd z hz)), ?_⟩
        change D.transpose * M * D = lam z • (1 : Mat2)
        rw [hdetD]
        exact hform
      exact ⟨{
        tau := tau
        source_eq := hs
        target_eq := ht
        interior_image := hi
        boundary_image := hb
        inverse_interior_image := his
        inverse_boundary_image := hbs
        forward_C1 := hf
        inverse_C1 := hg
        forward_det := hfd
        inverse_det := hgd
        forward_holder := hfh
        inverse_holder := hgh
        base := base
        base_on_circle := hbase
        base_image := hbzero
        inverse_base := hbaseinv
        lambda := lam
        lambda_continuous := hcont
        lambda_pos := fun z hz => (halgebra z hz).1
        conformal := fun z hz => (halgebra z hz).2 }⟩
    rintro ⟨tau,hs,ht,hi,hb,hf,hg,hfd,hgd,hfh,hgh,hcr⟩
    exact packageFields tau hs ht hi hb hf hg hfd hgd hfh hgh
      (closeSystem tau hs ht hfh hcr)
  obtain ⟨M, agreement, symmetric, elliptic, holder, identity_at_infinity⟩ :=
    global_inverse_metric_extension R A G Ω
  obtain ⟨f, d, minimum⟩ := simultaneous_metric_minimizer R A G Ω M
    agreement symmetric elliptic holder identity_at_infinity
  have regular : Nonempty (ClosedMetricRepresentative G Ω f d) := by
    run_tac Lean.Elab.Tactic.withMainContext do
      let pn := (Lean.Name.num `_private.VM03ExactCaller_v464 0) ++
        `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.same_minimizer_regular_representative_v464
      let names := [`R, `A, `G, `Ω, `M, `agreement, `symmetric, `elliptic, `holder,
        `identity_at_infinity, `f, `d, `minimum]
      let args ← names.toArray.mapM fun n => Lean.Elab.Term.elabTerm (Lean.mkIdent n) none
      Lean.Elab.Tactic.closeMainGoal `whole_original (Lean.mkAppN (Lean.mkConst pn) args)
  obtain ⟨Q⟩ := regular
  obtain ⟨orientation, horientation, P, hforward, hinverse, hweighted⟩ :=
    positive_system_of_same_regular_minimizer R A G Ω M agreement symmetric elliptic
      holder identity_at_infinity f d minimum Q
  apply package
  refine ⟨P.tau, P.source_eq, P.target_eq, P.interior_image, P.boundary_image,
    P.forward_C1, P.inverse_C1, P.forward_det, P.inverse_det,
    P.forward_holder, P.inverse_holder, ?_⟩
  have hdet (x : E2) (hx : x ∈ closure Ω.domain) : Real.sqrt (Matrix.det (M x)) = 1 := by
    rw [agreement x hx, G.det_one x (Ω.closure_inside hx), Real.sqrt_one]
  filter_upwards [hweighted, ae_restrict_mem
    (show MeasurableSet (disc 1) from Metric.isOpen_ball.measurableSet)] with z hz hzin
  have hzs : z ∈ P.tau.source := by
    rw [P.source_eq]
    exact Metric.ball_subset_closedBall hzin
  have hzt : P.tau z ∈ closure Ω.domain := by
    simpa only [P.target_eq] using P.tau.map_source hzs
  dsimp only at hz ⊢
  rw [hdet (P.tau z) hzt, one_mul, one_mul, agreement (P.tau z) hzt] at hz
  exact hz
end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.boundary_metric_conformal_provider
