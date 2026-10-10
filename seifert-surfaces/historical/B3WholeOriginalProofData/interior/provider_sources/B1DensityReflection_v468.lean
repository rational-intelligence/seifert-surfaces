import B1NormalizedCoefficients_v468
import B1WeakTransportReflection
noncomputable section
open Set Topology Function MeasureTheory
open scoped Manifold ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates WeakTransport
universe v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}
set_option maxHeartbeats 0
theorem same_difference_density_equation (D : B1OriginalData g J) (s : Circle)
    (W : CollarWindow D s) (N : PositiveNormalization W) (F : BoundaryIsothermalPatch N) :
    (∀ z ∈ closedHalfDisc F.targetR,
      densityLeading N.normalizedA F.chart (F.chart.symm z) = 1) ∧
    BoundedOn F.bhat (halfDisc F.targetR) ∧
    MemLp F.bhat ⊤ (volume.restrict (halfDisc F.targetR)) ∧
    (∀ z ∈ flatArc F.targetR, F.vhat z = 0) ∧
    H1On (halfDisc F.targetR) F.vhat (planarGradient F.vhat) ∧
    WeakLinearEquationOn (halfDisc F.targetR) (fun _ => 1) F.bhat (fun _ => 0)
      F.vhat (planarGradient F.vhat) := by
  obtain ⟨hfirst,heq,hell,hlip,hb,hdet,htrace⟩ := same_difference_positive_normalization D s W N
  obtain ⟨hU,himage,hjets,hdetF,htests,hleading,hbc,hbb,hblp,hflat,hweak⟩ :=
    same_density_test_transport D s W N F heq hell hb hdet htrace
  have hjet := same_chart_first_jets_H1 D s W N F
  refine ⟨hleading, ?_, hblp, hflat, hjet.2.2.2.2.2.2.2.2.2.2.2, hweak⟩
  exact ⟨hbb.choose,hbb.choose_spec.1,fun x hx => hbb.choose_spec.2 x
    ⟨Metric.ball_subset_closedBall hx.1,hx.2.le⟩⟩

theorem same_boundary_odd_reflected_weak_equation (D : B1OriginalData g J)
    (s : Circle) (W : CollarWindow D s) (N : PositiveNormalization W)
    (F : BoundaryIsothermalPatch N) :
    ContDiffOn ℝ 1 F.reflectedV (disc F.targetR) ∧
    H1On (disc F.targetR) F.reflectedV (planarGradient F.reflectedV) ∧
    BoundedOn F.reflectedB (disc F.targetR) ∧
    MemLp F.reflectedB ⊤ (volume.restrict (disc F.targetR)) ∧
    WeakLinearEquationOn (disc F.targetR) (fun _ => 1) F.reflectedB (fun _ => 0)
      F.reflectedV (planarGradient F.reflectedV) := by
  obtain ⟨hfirst,heq,hell,hlip,hb,hdet,htrace⟩ := same_difference_positive_normalization D s W N
  obtain ⟨hU,himage,hjets,hdetF,htests,hleading,hbc,hbb,hblp,hflat,hweak⟩ :=
    same_density_test_transport D s W N F heq hell hb hdet htrace
  obtain ⟨hNv,hNvb,hNdb,hFd,hFi,hvd,hvg,hvc,hgc,hvb,hgb,hH1⟩ :=
    same_chart_first_jets_H1 D s W N F
  have hmeas : MeasurableSet (closedHalfDisc F.targetR) := by
    change MeasurableSet (Metric.closedBall (0 : E2) F.targetR ∩ {x : E2 | 0 ≤ x 1})
    exact (Metric.isClosed_closedBall.inter
      (isClosed_le continuous_const (EuclideanSpace.proj (1 : Fin 2)).continuous)).measurableSet
  have hm : AEStronglyMeasurable F.bhat (volume.restrict (closedHalfDisc F.targetR)) :=
    hbc.aestronglyMeasurable hmeas
  obtain ⟨hflatjet,hoddjet,hC1,hoddH1,hob,hod,hdb,hdLp⟩ :=
    odd_first_jet_paste_H1 F.targetR F.targetR_pos F.vhat F.bhat hvc hgc hvd
      hflat hvb hgb hbb hm
  have hhalf : halfDisc F.targetR ⊆ closedHalfDisc F.targetR :=
    fun x hx => ⟨Metric.ball_subset_closedBall hx.1,hx.2.le⟩
  have hlocal : ∀ K' : Set E2, IsCompact K' → K' ⊆ disc F.targetR →
      BoundedOn (planarGradient F.vhat) (K' ∩ closedHalfDisc F.targetR) ∧
      BoundedOn F.bhat (K' ∩ closedHalfDisc F.targetR) := by
    intro K' hK hKsub
    exact ⟨⟨hgb.choose,hgb.choose_spec.1,fun x hx => hgb.choose_spec.2 x hx.2⟩,
      ⟨hbb.choose,hbb.choose_spec.1,fun x hx => hbb.choose_spec.2 x hx.2⟩⟩
  have href := (reflected_weak_test_assembly F.targetR F.targetR_pos F.vhat F.bhat
    hweak hoddH1 hoddjet (hm.mono_measure (Measure.restrict_mono hhalf le_rfl)) hlocal).2
  exact ⟨hC1,hoddH1,hdb,hdLp,href⟩


/-- Distributional ∂bar w=A*w+B*conj(w), w=∂1v-i∂2v, using the actual
reflected drift, including all Lp preconditions for every finite p>2. -/
theorem same_reflected_gradient_vekua_equation (D : B1OriginalData g J)
    (s : Circle) (W : CollarWindow D s) (N : PositiveNormalization W)
    (F : BoundaryIsothermalPatch N) :
    ContinuousOn F.w (Metric.ball (0 : ℂ) F.targetR) ∧
    WeakVekuaOn (Metric.ball (0 : ℂ) F.targetR) F.w
      (vekuaA F.reflectedB) (vekuaB F.reflectedB) ∧
    ∀ p : ℝ, 2 < p →
      MemLp (vekuaA F.reflectedB) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : ℂ) F.targetR)) ∧
      MemLp (vekuaB F.reflectedB) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : ℂ) F.targetR)) := by
  obtain ⟨hu,hH1,hb,hbLp,heq⟩ := same_boundary_odd_reflected_weak_equation D s W N F
  obtain ⟨hw,hvekua,hid,hlp⟩ := C1_real_weak_to_vekua F.targetR F.targetR_pos
    F.reflectedV F.reflectedB hu heq hb hbLp
  exact ⟨hw,hvekua,hlp⟩


end SeifertSurfaces.OriginalEndpoints.B1Tangency
