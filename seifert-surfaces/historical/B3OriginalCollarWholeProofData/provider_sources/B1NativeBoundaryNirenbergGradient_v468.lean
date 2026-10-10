import B1ActualBoundaryNirenbergEquation_v468
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open ChartMetricProvider.Variational.DirectWeak.BoundaryContinuation
open SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction
set_option maxHeartbeats 0

/-- The native boundary test has the explicit Nirenberg gradient. The equality
is established by weak-derivative uniqueness, using the actual zero extension. -/
theorem native_boundary_nirenberg_explicit_gradient_v468
    (R r t : ℝ) (hroom : r+|t|<R) (htne : t≠0)
    (eta : E2 → ℝ) (hs : ContDiff ℝ ∞ eta) (hc : HasCompactSupport eta)
    (ht : tsupport eta ⊆ Metric.ball 0 r)
    (u : E2 → ℝ) (du : E2 → E2) (hu : H10On (halfDisc R) u du) :
    ∃ G : E2 → E2, H10On (halfDisc R)
      (nirenbergTestFunction 0 t eta ((halfDisc R).indicator u)) G ∧
      ∀ j : Fin 2, (fun x => G x j) =ᵐ[volume.restrict (halfDisc R)]
        diffQuot 0 (-t) (fun y => eta y^2 *
          diffQuot 0 t (fun z => (halfDisc R).indicator du z j) y+
            2*eta y*fderiv ℝ eta y (coordinateVector 2 j)*
              diffQuot 0 t ((halfDisc R).indicator u) y) := by
  have hU : IsOpen (halfDisc R) := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous)
  have hz := zero_extension (halfDisc R) hU.measurableSet u du hu
  let hw := native_regular_witness_v468 univ ((halfDisc R).indicator u)
    ((halfDisc R).indicator du) hz.1
  let hv := hw.nirenbergTestFunction isOpen_univ hs hc 0 t (subset_univ _)
  obtain ⟨G,hG⟩ := native_boundary_nirenberg_test_h10_v468 R r t hroom htne eta hs hc ht u du hu
  refine ⟨G,hG,?_⟩
  intro j
  have hder := (hv.isWeakGrad j).restrict hU (subset_univ _)
  have heq := DeGiorgi.HasWeakPartialDeriv.ae_eq hU
    ((native_regular_witness_v468 _ _ G hG.1).isWeakGrad j) hder
    ((hG.1.2.2.eval_piLp j).locallyIntegrable (by norm_num))
    ((hv.weakGrad_component_memLp j).mono_measure
      (Measure.restrict_mono_set _ (subset_univ (halfDisc R))) |>.locallyIntegrable (by norm_num))
  convert heq using 1 <;> rfl

end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.native_boundary_nirenberg_explicit_gradient_v468
