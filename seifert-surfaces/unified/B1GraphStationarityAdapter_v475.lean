import B1ActualCompactGraphVariation_v475

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped Manifold ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
universe v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- Analytic end of the relative-minimum argument on the exact support of each
graph test.  The geometric realization of the local minimum is a separate debt. -/
theorem actual_graph_weak_stationarity_adapter_v475
    (D : B1OriginalData g J) (s : Circle) (W : CollarWindow D s)
    (u : E2 → ℝ) (hu : ContDiffOn ℝ ∞ u W.U)
    (hjets : ∀ x ∈ halfDisc W.R, jetPoint (x,u x,planarGradient u x) ∈ W.V)
    (hminimum : ∀ φ : E2 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ halfDisc W.R →
      IsLocalMin (fun t => ∫ x in tsupport φ,
        W.density (x,u x+t*φ x,planarGradient u x+t • planarGradient φ x)) 0) :
    ∀ φ : E2 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ halfDisc W.R →
      (∫ x in halfDisc W.R, inner ℝ (W.flux (x,u x,planarGradient u x)) (planarGradient φ x) -
        W.lower (x,u x,planarGradient u x) * φ x) = 0 := by
  intro φ hφ hφc ht
  have hhalfU : halfDisc W.R ⊆ W.U := fun x hx =>
    W.U_contains ⟨Metric.ball_subset_closedBall hx.1,hx.2.le⟩
  obtain ⟨Q,O,hQ,h0,hO,hAO,hOU,hvaried⟩ := actual_compact_graph_jet_tube_v475 D s W
    (tsupport φ) W.U hφc W.U_open (ht.trans hhalfU) u φ hu hφ
    (fun x hx => hjets x (ht hx))
  have hvar := actual_compact_graph_density_variation_v475 D s W (tsupport φ) O
    hφc hO hAO Q hQ h0 u φ (hu.mono hOU) hφ hvaried
  have hderiv := (hminimum φ hφ hφc ht).hasDerivAt_eq_zero hvar.2
  let F := fun x => inner ℝ (W.flux (x,u x,planarGradient u x)) (planarGradient φ x) -
    W.lower (x,u x,planarGradient u x) * φ x
  have hz : ∀ x ∉ tsupport φ, F x = 0 := by
    intro x hx
    have hzero : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
    have hgradzero : planarGradient φ x = 0 := by
      unfold planarGradient
      rw [fderiv_of_notMem_tsupport ℝ hx]
      simp
    simp [F,hzero,hgradzero]
  change (∫ x in tsupport φ, F x) = 0 at hderiv
  change (∫ x in halfDisc W.R, F x) = 0
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => hz x (fun hh => hx (ht hh))),
    ← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  exact hderiv

/-- Once the actual geometric minimum is expressed in graph density, both
protected graph equations follow using the supplied W calculus. -/
theorem actual_minimal_graph_equations_from_compact_minima_v475
    (D : B1OriginalData g J) (s : Circle) (W : CollarWindow D s)
    (hheight : ∀ φ : E2 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ halfDisc W.R →
      IsLocalMin (fun t => ∫ x in tsupport φ,
        W.density (x,localHeight D s x+t*φ x,
          planarGradient (localHeight D s) x+t • planarGradient φ x)) 0)
    (hzero : ∀ φ : E2 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ halfDisc W.R →
      IsLocalMin (fun t => ∫ x in tsupport φ,
        W.density (x,t*φ x,t • planarGradient φ x)) 0) :
    (∀ x ∈ halfDisc W.R, W.residual (localHeight D s) x = 0) ∧
    (∀ x ∈ halfDisc W.R, W.residual (fun _ => 0) x = 0) := by
  have hclosed : halfDisc W.R ⊆ closedHalfDisc W.R := fun x hx =>
    ⟨Metric.ball_subset_closedBall hx.1,hx.2.le⟩
  have hhalfU : halfDisc W.R ⊆ W.U := hclosed.trans W.U_contains
  have hO : IsOpen (halfDisc W.R) := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous)
  have hjheight : ∀ x ∈ halfDisc W.R,
      jetPoint (x,localHeight D s x,planarGradient (localHeight D s) x) ∈ W.V := by
    intro x hx
    simpa using W.jets_inside x (hclosed hx) 1 (by simp)
  have hjzero : ∀ x ∈ halfDisc W.R, jetPoint (x,0,planarGradient (fun _ => 0) x) ∈ W.V := by
    intro x hx
    simpa [planarGradient] using W.jets_inside x (hclosed hx) 0 (by simp)
  have hh := actual_graph_weak_stationarity_adapter_v475 D s W
    (localHeight D s) W.height_smooth hjheight hheight
  have hz := actual_graph_weak_stationarity_adapter_v475 D s W
    (fun _ => 0) contDiffOn_const hjzero (by simpa [planarGradient] using hzero)
  exact ⟨actual_graph_residual_of_tests_v475 D s W (halfDisc W.R) hO
      (localHeight D s) (W.height_smooth.mono hhalfU) hjheight hh,
    actual_graph_residual_of_tests_v475 D s W (halfDisc W.R) hO
      (fun _ => 0) contDiffOn_const hjzero hz⟩

#print axioms actual_graph_weak_stationarity_adapter_v475
#print axioms actual_minimal_graph_equations_from_compact_minima_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
