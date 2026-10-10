import B1ActualGraphAreaFlowVariation_v475

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped Manifold ContDiff BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
universe v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

/-- The exact bridge from an actual ambient-flow local minimum to the graph
stationarity adapter. All geometric hypotheses are explicit graph identities;
no area or regularity oracle is hidden in this bridge. -/
theorem actual_surface_flow_stationarity_v475
    (D : B1OriginalData g J) (s : Circle) (W : CollarWindow D s)
    (u φ : E2 → ℝ) (hu : ContDiffOn ℝ ∞ u W.U) (hφ : ContDiff ℝ ∞ φ)
    (A O : Set E2) (hA : IsCompact A) (hO : IsOpen O) (hAO : A ⊆ O) (hOU : O ⊆ W.U)
    (hhalf : A ⊆ halfDisc W.R) (hφA : tsupport φ ⊆ A)
    (Q : Set ℝ) (hQ : IsOpen Q) (h0Q : (0 : ℝ) ∈ Q)
    (hjets : ∀ t ∈ Q, ∀ x ∈ O,
      jetPoint (x,u x+t*φ x,planarGradient u x+t • planarGradient φ x) ∈ W.V)
    (L : ℝ → ℝ) (hL : ∀ t ∈ Q, L t = ∫ x in A,
      W.density (x,u x+t*φ x,planarGradient u x+t • planarGradient φ x))
    (hmin : IsLocalMin L 0) :
    (∫ x in halfDisc W.R,
      inner ℝ (W.flux (x,u x,planarGradient u x)) (planarGradient φ x) -
        W.lower (x,u x,planarGradient u x) * φ x) = 0 := by
  have hv := actual_compact_graph_density_variation_v475 D s W A O hA hO hAO Q hQ h0Q
    u φ (hu.mono hOU) hφ hjets
  have heq : L =ᶠ[𝓝 (0 : ℝ)] (fun t => ∫ x in A,
      W.density (x,u x+t*φ x,planarGradient u x+t • planarGradient φ x)) :=
    Filter.eventuallyEq_of_mem (hQ.mem_nhds h0Q) hL
  have hd := hv.2.congr_of_eventuallyEq heq
  have hz := hmin.hasDerivAt_eq_zero hd
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
  change (∫ x in A, F x) = 0 at hz
  change (∫ x in halfDisc W.R, F x) = 0
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => hzero x (fun h => hx (hhalf (hφA h)))),
    ← setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => hzero x (fun h => hx (hφA h)))]
  exact hz

#print axioms actual_surface_flow_stationarity_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
