import B1ActualBoundaryFullH2_v468
import NativeH1Sum
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open DifferentialGeometry.Analysis.Sobolev
open ChartMetricProvider.Variational.DirectWeak.BoundaryContinuation
set_option maxHeartbeats 800000

/-- Commutation of native weak mixed partials, including across the flat edge,
proved directly by testing with the two derivatives of a smooth test. -/
theorem native_mixed_weak_partial_v468
    (U : Set E2) (u d0 d1 w : E2 → ℝ)
    (h0 : DeGiorgi.HasWeakPartialDeriv 0 d0 u U)
    (h1 : DeGiorgi.HasWeakPartialDeriv 1 d1 u U)
    (hw : DeGiorgi.HasWeakPartialDeriv 0 w d1 U) :
    DeGiorgi.HasWeakPartialDeriv 1 w d0 U := by
  intro phi hs hc ht
  let p0 : E2 → ℝ := fun x => fderiv ℝ phi x (coordinateVector 2 0)
  let p1 : E2 → ℝ := fun x => fderiv ℝ phi x (coordinateVector 2 1)
  have hps (i : Fin 2) : ContDiff ℝ ∞ (fun x => fderiv ℝ phi x (coordinateVector 2 i)) :=
    (hs.fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const
  have e0 := h0 p1 (hps 1) (hc.fderiv_apply ℝ _) ((tsupport_fderiv_apply_subset ℝ _).trans ht)
  have e1 := h1 p0 (hps 0) (hc.fderiv_apply ℝ _) ((tsupport_fderiv_apply_subset ℝ _).trans ht)
  have em : (fun x => fderiv ℝ p1 x (coordinateVector 2 0))=
      (fun x => fderiv ℝ p0 x (coordinateVector 2 1)) := by
    funext x
    have he (i j : Fin 2) :
        fderiv ℝ (fun y => fderiv ℝ phi y (coordinateVector 2 j)) x (coordinateVector 2 i)=
          fderiv ℝ (fderiv ℝ phi) x (coordinateVector 2 i) (coordinateVector 2 j) := by
      let e := ContinuousLinearMap.apply ℝ ℝ (coordinateVector 2 j)
      have he := e.hasFDerivAt.comp x
        ((hs.fderiv_right (m:=1) (by simp)).differentiable (by simp) x).hasFDerivAt
      exact congrArg (fun L : E2 →L[ℝ] ℝ => L (coordinateVector 2 i)) he.fderiv
    exact (he 0 1).trans (((hs.of_le (by simp : (2:ℕ∞ω)≤(∞:ℕ∞ω))).contDiffAt.isSymmSndFDerivAt
      (by norm_num)).eq _ _ |>.trans (he 1 0).symm)
  have el : (∫ x in U, u x*fderiv ℝ p1 x (EuclideanSpace.single 0 1))=
      ∫ x in U, u x*fderiv ℝ p0 x (EuclideanSpace.single 1 1) := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => congrArg (fun z => u x*z) (congrFun em x)
  have ew := hw phi hs hc ht
  change (∫ x in U, d0 x * fderiv ℝ phi x (EuclideanSpace.single 1 1))=
    -(∫ x in U, w x*phi x)
  change (∫ x in U, d1 x * fderiv ℝ phi x (EuclideanSpace.single 0 1))=
    -(∫ x in U, w x*phi x) at ew
  dsimp only [p0,p1] at e0 e1 el
  simp only [coordinateVector] at e0 e1 el
  linarith only [e0,e1,el,ew]

/-- Native H1 of the zero-extended tangential gradient, constructed from the
uniform quotient witnesses and the original H10 extension. -/
theorem native_zero_extended_tangent_H1_v468
    (R q : ℝ) (hq : 0<q) (u : E2 → ℝ) (du : E2 → E2)
    (hu : H10On (halfDisc R) u du)
    (w0 w1 : E2 → ℝ)
    (hw0 : MemLp w0 2 (volume.restrict (Metric.ball (0:E2) q)))
    (hw1 : MemLp w1 2 (volume.restrict (Metric.ball (0:E2) q)))
    (hd0 : DeGiorgi.HasWeakPartialDeriv 0 w0 (fun y => (halfDisc R).indicator du y 0) (Metric.ball 0 q))
    (hd1 : DeGiorgi.HasWeakPartialDeriv 0 w1 (fun y => (halfDisc R).indicator du y 1) (Metric.ball 0 q)) :
    H1On (Metric.ball 0 q) (fun y => (halfDisc R).indicator du y 0)
      (fun y => w0 y • coordinateVector 2 0+w1 y • coordinateVector 2 1) := by
  let V : Set E2 := Metric.ball 0 q
  have hUm : MeasurableSet (halfDisc R) := (Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)).measurableSet
  have hz := zero_extension (halfDisc R) hUm u du hu
  let hw : DeGiorgi.MemW1pWitness 2 ((halfDisc R).indicator u) univ :=
    native_regular_witness_v468 univ ((halfDisc R).indicator u) ((halfDisc R).indicator du) hz.1
  have hf : MemLp (fun y => (halfDisc R).indicator du y 0) 2 (volume.restrict V) :=
    by simpa only [Measure.restrict_univ] using (hz.1.2.2.eval_piLp 0).restrict V
  have hg : MemLp (fun y => w0 y • coordinateVector 2 0+w1 y • coordinateVector 2 1) 2 (volume.restrict V) :=
    (hw0.continuousLinearMap_comp (ContinuousLinearMap.toSpanSingleton ℝ (coordinateVector 2 0))).add
      (hw1.continuousLinearMap_comp (ContinuousLinearMap.toSpanSingleton ℝ (coordinateVector 2 1)))
  have hn := native_mixed_weak_partial_v468 V _ _ _ w1
    ((hw.isWeakGrad 0).restrict Metric.isOpen_ball (subset_univ _))
    ((hw.isWeakGrad 1).restrict Metric.isOpen_ball (subset_univ _)) hd1
  refine ⟨⟨locallyIntegrableOn_of_locallyIntegrable_restrict (hf.locallyIntegrable (by norm_num)),
    locallyIntegrableOn_of_locallyIntegrable_restrict (hg.locallyIntegrable (by norm_num)),?_⟩,hf,hg⟩
  intro phi hs hc ht i
  fin_cases i
  · simpa [coordinateVector] using hd0 phi hs hc ht
  · simpa [hw,native_regular_witness_v468,coordinateVector] using hn phi hs hc ht
end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.native_mixed_weak_partial_v468
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.native_zero_extended_tangent_H1_v468
