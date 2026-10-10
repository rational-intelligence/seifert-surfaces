import B1NativeBoundaryTangentialEnergy_v468
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction
set_option maxHeartbeats 0

/-- The original B1 data supply a single positive classical Dirichlet solution
and its actual flat-edge tangential energy estimates. The smooth elliptic
extension is constructed from the same W, and introduces no original premise. -/
theorem actual_positive_boundary_tangential_energy_v468
    (D : B1OriginalData (g := g) J) (s : Circle) (W : CollarWindow D s) :
    ∃ R : ℝ, 0 < R ∧ R < W.R ∧ ∃ h : E2 → ℝ,
      ContinuousOn h (closedHalfDisc R) ∧
      (∀ x ∈ frontier (halfDisc R), h x=1) ∧
      (∀ x ∈ closedHalfDisc R, (1/2 : ℝ) ≤ h x) ∧
      ContDiffOn ℝ ∞ h (halfDisc R) ∧
      H1On (halfDisc R) h (planarGradient h) ∧
      H10On (halfDisc R) (fun x => h x-1) (planarGradient h) ∧
      WeakLinearEquationOn (halfDisc R) W.a W.b W.c h (planarGradient h) ∧
      (∀ x ∈ halfDisc R, classicalL W.a W.b W.c h x=0) ∧
      ∃ B : SmoothEllipticBilinearForm 2 univ,
        (∀ x ∈ closedHalfDisc R, B.a x=W.a x) ∧
        ∀ r t : ℝ, r+|t|<R → t≠0 → ∀ eta : E2 → ℝ,
          ContDiff ℝ ∞ eta → HasCompactSupport eta → tsupport eta ⊆ Metric.ball 0 r →
          B.lam * (∫ x, eta x^2 * ∑ i : Fin 2,
            (diffQuot 0 t (fun y => (halfDisc R).indicator (planarGradient h) y i) x)^2) ≤
            |∫ x, (halfDisc R).indicator
                (fun y => inner ℝ (W.b y) (planarGradient h y)+W.c y*h y) x *
              nirenbergTestFunction 0 t eta ((halfDisc R).indicator (fun y => h y-1)) x|+
            |∫ x, boundaryTangentialCross_v468 B eta t
              ((halfDisc R).indicator (fun y => h y-1))
              ((halfDisc R).indicator (planarGradient h)) x| := by
  obtain ⟨R,hR,hRW,h,hhc,hfront,hpos,hs,h1,h0,heq,hcl⟩ :=
    actual_halfdisc_native_closed_classical_positive_v468 D s W
  have hP : IsCompact (closedHalfDisc R) := (isCompact_closedBall (0 : E2) R).inter_right
    (isClosed_le continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous)
  have hPW : closedHalfDisc R ⊆ closedHalfDisc W.R :=
    fun x hx => ⟨Metric.closedBall_subset_closedBall hRW.le hx.1,hx.2⟩
  obtain ⟨B,hBa⟩ := actual_closed_halfdisc_smooth_elliptic_extension_v468 D s W
    (closedHalfDisc R) hP hPW
  obtain ⟨hF,hS⟩ := actual_halfdisc_flux_source_L2_v468 D s W R hRW h (planarGradient h) h1
  refine ⟨R,hR,hRW,h,hhc,hfront,hpos,hs,h1,h0,heq,hcl,B,hBa,?_⟩
  intro r t hroom ht eta heta hetac hetas
  apply native_boundary_tangential_energy_v468 R r t hroom ht eta heta hetac hetas
    (fun y => h y-1) (planarGradient h) h0
    (fun y => matrixAction (W.a y) (planarGradient h y))
    (fun y => inner ℝ (W.b y) (planarGradient h y)+W.c y*h y) hF hS
    (fun phi hphi hphic hphis => (heq.2 phi hphi hphic hphis).2) B
  intro x hx
  rw [hBa x ⟨Metric.ball_subset_closedBall hx.1,hx.2.le⟩]

end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.actual_positive_boundary_tangential_energy_v468
