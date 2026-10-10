import B1ActualNativeClosedDirichlet_v468
import B1NativeBoundaryNirenbergEquation_v468
import B1ClosedHalfDiscEllipticExtension_v468
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction
set_option maxHeartbeats 0

/-- Both actual terms of the collar's native weak equation are in L2. -/
theorem actual_halfdisc_flux_source_L2_v468
    (D : B1OriginalData (g := g) J) (s : Circle) (W : CollarWindow D s)
    (R : ℝ) (hRW : R < W.R) (u : E2 → ℝ) (du : E2 → E2)
    (hu : H1On (halfDisc R) u du) :
    MemLp (fun x => matrixAction (W.a x) (du x)) 2 (volume.restrict (halfDisc R)) ∧
    MemLp (fun x => inner ℝ (W.b x) (du x)+W.c x*u x) 2 (volume.restrict (halfDisc R)) := by
  obtain ⟨ha,hb,hc,A,B,C,hA,hB,hC,haBound,hbBound,hcBound⟩ :=
    actual_halfdisc_full_form_bounds_v468 D s W R hRW
  have hUm : MeasurableSet (halfDisc R) := (Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous)).measurableSet
  refine ⟨?_,native_lower_source_L2_v468 (halfDisc R) u du W.b W.c hu hb hc B C
    (by filter_upwards [ae_restrict_mem hUm] with x hx; exact hbBound x hx)
    (by filter_upwards [ae_restrict_mem hUm] with x hx; exact hcBound x hx)⟩
  have hmeas : AEStronglyMeasurable (fun x => matrixAction (W.a x) (du x))
      (volume.restrict (halfDisc R)) := by
    have hcoord (i : Fin 2) : AEStronglyMeasurable
        (fun x => ∑ j : Fin 2, W.a x i j * du x j) (volume.restrict (halfDisc R)) := by
      convert ((ha i 0).mul (hu.2.2.eval_piLp 0).aestronglyMeasurable).add
          ((ha i 1).mul (hu.2.2.eval_piLp 1).aestronglyMeasurable) using 1
      funext x
      simp [Fin.sum_univ_two, matrixAction]
    exact ((PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).measurable.comp_aemeasurable
      (AEMeasurable.of_eval fun i => (hcoord i).aemeasurable)).aestronglyMeasurable
  apply hu.2.2.of_le_mul hmeas
  filter_upwards [ae_restrict_mem hUm] with x hx
  exact haBound x hx (du x)

/-- The positive classical solution constructed from the original data admits
every flat-edge tangential Nirenberg test. Its equation, flux, source and test
all use the same W and the same native solution h. -/
theorem actual_positive_boundary_nirenberg_equation_v468
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
      ∀ r t : ℝ, r+|t|<R → t≠0 → ∀ eta : E2 → ℝ,
        ContDiff ℝ ∞ eta → HasCompactSupport eta → tsupport eta ⊆ Metric.ball 0 r →
        ∃ G : E2 → E2,
          H10On (halfDisc R)
            (nirenbergTestFunction 0 t eta ((halfDisc R).indicator (fun x => h x-1))) G ∧
          (∫ x in halfDisc R,
            inner ℝ (matrixAction (W.a x) (planarGradient h x)) (G x)-
              (inner ℝ (W.b x) (planarGradient h x)+W.c x*h x)*
                nirenbergTestFunction 0 t eta ((halfDisc R).indicator (fun x => h x-1)) x)=0 := by
  obtain ⟨R,hR,hRW,h,hhc,hfront,hpos,hs,h1,h0,heq,hcl⟩ :=
    actual_halfdisc_native_closed_classical_positive_v468 D s W
  obtain ⟨hF,hS⟩ := actual_halfdisc_flux_source_L2_v468 D s W R hRW h (planarGradient h) h1
  refine ⟨R,hR,hRW,h,hhc,hfront,hpos,hs,h1,h0,heq,hcl,?_⟩
  intro r t hroom ht eta heta hetac hetas
  exact native_boundary_nirenberg_equation_v468 R r t hroom ht eta heta hetac hetas _ _ h0
    _ _ hF hS (fun phi hphi hphic hphis => (heq.2 phi hphi hphic hphis).2)

end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.actual_halfdisc_flux_source_L2_v468
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.actual_positive_boundary_nirenberg_equation_v468
