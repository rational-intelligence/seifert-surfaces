import B1HalfDiscBarrierWeak_v468
noncomputable section
open Set Topology Function MeasureTheory
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1GraphCoefficients
universe v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- The classical positive barrier is a weak supersolution on every nonnegative
compactly supported smooth test, with the literal original coefficients. -/
theorem actual_halfdisc_positive_barrier_weak_test_v468
    (D : B1OriginalData g J) (s : Circle) (W : CollarWindow D s) :
    ∃ R : ℝ, 0 < R ∧ R < W.R ∧ ∃ v : E2 → ℝ,
      ContDiff ℝ ∞ v ∧
      (∀ x ∈ closedHalfDisc R, (1/2 : ℝ) ≤ v x ∧ v x ≤ 1) ∧
      (∀ x ∈ halfDisc R, 1 ≤ classicalL W.a W.b W.c v x) ∧
      (∀ φ : E2 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
        tsupport φ ⊆ halfDisc R → (∀ x, 0 ≤ φ x) →
        (∫ x in halfDisc R,
          inner ℝ (matrixAction (W.a x) (planarGradient v x)) (planarGradient φ x) -
          (inner ℝ (W.b x) (planarGradient v x) + W.c x * v x) * φ x) ≤
        -(∫ x in halfDisc R, φ x)) := by
  obtain ⟨R,hR,hRW,v,hv,hvb,hvL⟩ := actual_halfdisc_positive_barrier_v468 D s W
  obtain ⟨O,hO,hWO,hOU,hjets,hf,hdf,ha,hq,hlg,hlh,hb,hc⟩ :=
    actual_coefficient_open_tube D s W
  refine ⟨R,hR,hRW,v,hv,hvb,hvL,?_⟩
  intro φ hs hcφ ht hnonneg
  have hUO : halfDisc R ⊆ O := fun x hx =>
    hWO ⟨Metric.ball_subset_closedBall (Metric.ball_subset_ball hRW.le hx.1),hx.2.le⟩
  have hform := halfdisc_classical_form_identity_v468 R O hO hUO W.a W.b W.c v
    ha hb hc hv φ hs hcφ ht
  have hphi : IntegrableOn φ (halfDisc R) :=
    (hs.continuous.integrable_of_hasCompactSupport hcφ).integrableOn
  have hLphi : IntegrableOn (fun x => classicalL W.a W.b W.c v x * φ x) (halfDisc R) := hform.2.1
  have hmono : (∫ x in halfDisc R, φ x) ≤
      ∫ x in halfDisc R, classicalL W.a W.b W.c v x * φ x := by
    apply integral_mono_ae hphi hLphi
    filter_upwards [ae_restrict_mem (show MeasurableSet (halfDisc R) by
      change MeasurableSet (Metric.ball (0 : E2) R ∩ {x : E2 | 0 < x 1})
      exact (Metric.isOpen_ball.inter (isOpen_lt continuous_const
        (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous)).measurableSet)] with x hx
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hvL x hx) (hnonneg x)
  rw [hform.2.2]
  linarith

end SeifertSurfaces.OriginalEndpoints.B1Tangency
