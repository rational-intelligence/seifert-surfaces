import B1ActualCompactLocalGraphMinimum_v475

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped Manifold ContDiff BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.MetricFoundations.AreaAnalysis
open SeifertSurfaces.AppendixACoordinates
universe u v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

theorem actual_local_graph_tests_of_minima_v475
    (D : B1OriginalData g J) (s : Circle) (W : CollarWindow D s)
    (u : E2 → ℝ) (hu : ContDiffOn ℝ ∞ u W.U)
    (hjets : ∀ x ∈ halfDisc W.R, jetPoint (x,u x,planarGradient u x) ∈ W.V)
    (O : Set E2) (hOhalf : O ⊆ halfDisc W.R)
    (hminimum : ∀ φ : E2 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
      IsLocalMin (fun t => ∫ x in tsupport φ,
        W.density (x,u x+t*φ x,planarGradient u x+t • planarGradient φ x)) 0) :
    ∀ φ : E2 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
      (∫ x in O, inner ℝ (W.flux (x,u x,planarGradient u x)) (planarGradient φ x) -
        W.lower (x,u x,planarGradient u x) * φ x) = 0 := by
  intro φ hφ hφc ht
  have hhalfU : halfDisc W.R ⊆ W.U := fun x hx =>
    W.U_contains ⟨Metric.ball_subset_closedBall hx.1,hx.2.le⟩
  obtain ⟨Q,N,hQ,h0,hN,hAN,hNU,hvaried⟩ := actual_compact_graph_jet_tube_v475 D s W
    (tsupport φ) W.U hφc W.U_open (ht.trans (hOhalf.trans hhalfU)) u φ hu hφ
    (fun x hx => hjets x (hOhalf (ht hx)))
  obtain ⟨hi,hd⟩ := actual_compact_graph_density_variation_v475 D s W (tsupport φ) N
    hφc hN hAN Q hQ h0 u φ (hu.mono hNU) hφ hvaried
  have hz := (hminimum φ hφ hφc ht).hasDerivAt_eq_zero hd
  let F := fun x => inner ℝ (W.flux (x,u x,planarGradient u x)) (planarGradient φ x) -
    W.lower (x,u x,planarGradient u x) * φ x
  have hzero : ∀ x ∉ tsupport φ, F x = 0 := by
    intro x hx
    have hφz : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
    have hgradz : planarGradient φ x = 0 := by
      unfold planarGradient
      rw [fderiv_of_notMem_tsupport ℝ hx]
      simp
    simp [F,hφz,hgradz]
  change (∫ x in tsupport φ, F x) = 0 at hz
  change (∫ x in O, F x) = 0
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => hzero x (fun hh => hx (ht hh))),
    ← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  exact hz

/-- The genuine flow minimum and the recovered embedded graph parameter give
the pointwise classical equation throughout the original half-disc. -/
theorem actual_graph_pde_from_native_flow_v475
    (D : B1OriginalData g J) (s : Circle) (W : CollarWindow D s)
    {S : CompactOrientedSurface.{u}} (f : ProperSmoothEmbedding S E.Carrier)
    (hmin : ∀ X : NativeInteriorSmoothVectorField_v475 E,
      IsLocalMin (fun t => area g (native_actual_exterior_flow_v475 X t ∘ f.toFun)) 0)
    (u : E2 → ℝ) (hu : ContDiffOn ℝ ∞ u W.U)
    (hheight : ∀ x ∈ halfDisc W.R, |u x| < D.eta)
    (hjets : ∀ x ∈ halfDisc W.R, jetPoint (x,u x,planarGradient u x) ∈ W.V)
    (q : E2 → S) (hq : ContMDiffOn 𝓘(ℝ,E2) (𝓡∂ 2) ∞ q (halfDisc W.R))
    (hqgraph : ∀ x ∈ halfDisc W.R, f.toFun (q x) = localCollar D s (jetPoint (x,u x,0)))
    (hqi : ∀ x ∈ halfDisc W.R, q x ∉ S.boundary)
    (hgraph : ∀ y ∈ collarDomain D W.R, localCollar D s y ∈ f.image →
      y 2 = u (native_collar_base_v475 y)) :
    ∀ x ∈ halfDisc W.R, W.residual u x = 0 := by
  have hhalf : IsOpen (halfDisc W.R) := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous)
  have hhalfU : halfDisc W.R ⊆ W.U := fun x hx =>
    W.U_contains ⟨Metric.ball_subset_closedBall hx.1,hx.2.le⟩
  intro x hx
  let p := q x
  let O := halfDisc W.R ∩ q ⁻¹' (surfaceChart p).source
  have hO : IsOpen O := hq.continuousOn.isOpen_inter_preimage hhalf (isOpen_extChartAt_source p)
  have hxO : x ∈ O := ⟨hx,mem_extChartAt_source p⟩
  have hOhalf : O ⊆ halfDisc W.R := inter_subset_left
  have hqs : MapsTo q O (surfaceChart p).source := fun z hz => hz.2
  have hminimum := fun φ hφ hφc ht => actual_compact_local_graph_minimum_v475 D s W f
    hmin u hu hheight hjets q hq hqgraph hqi hgraph p O hO hOhalf hqs φ hφ hφc ht
  have hweak := actual_local_graph_tests_of_minima_v475 D s W u hu hjets O hOhalf hminimum
  exact actual_graph_residual_of_tests_v475 D s W O hO u (hu.mono (hOhalf.trans hhalfU))
    (fun z hz => hjets z (hOhalf hz)) hweak x hxO

#print axioms actual_local_graph_tests_of_minima_v475
#print axioms actual_graph_pde_from_native_flow_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
