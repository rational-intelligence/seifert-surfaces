import B1NativeBoundaryGradientContinuous_v468
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Localization
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open DifferentialGeometry.Analysis.Sobolev.Euclidean
set_option maxHeartbeats 300000
set_option maxRecDepth 1500
set_option backward.isDefEq.respectTransparency false

theorem native_halfdisc_H2_continuous_radius_v474 (R q : ℝ) (hq : 0<q) (hqR : q<R)
    (u : E2 → ℝ) (hs : ContDiffOn ℝ ∞ u (halfDisc R))
    (hu : MemWkp 2 2 u (halfDisc R)) :
    ∃ f : E2 → ℝ, Continuous f ∧ EqOn f u (halfDisc q) := by
  have hR : 0<R := hq.trans hqR
  have he := native_halfdisc_even_W14_v468 R hR u hs hu
  obtain ⟨U,hU,hUc,hUsub,hUeq,hUgradeq⟩ :=
    he.someWitness.exists_compactly_supported_extension (by norm_num) Metric.isOpen_ball
      (isCompact_closedBall (0:E2) q) (by
        intro x hx
        exact Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hx) hqR))
  have hUb := hU.restrict Metric.isOpen_ball (subset_univ (Metric.ball (0:E2) (4*q)))
  obtain ⟨f,C,hfc,hC,hae,hHolder⟩ :=
    DifferentialGeometry.Analysis.Sobolev.EuclideanMorrey.morrey_holder_representative
      (by norm_num : (2:ℝ)<4) (by positivity : 0<4*q)
      (show DeGiorgi.MemW1pWitness (ENNReal.ofReal (4:ℝ)) U (Metric.ball 0 (4*q)) from by
        simpa using hUb)
  have hUq : IsOpen (halfDisc q) := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)
  have hsub : halfDisc q ⊆ halfDisc R :=
    fun x hx => ⟨Metric.ball_subset_ball hqR.le hx.1,hx.2⟩
  have hae' : f =ᵐ[volume.restrict (halfDisc q)] u := by
    have hh := ae_restrict_of_ae_restrict_of_subset
      (fun x (hx : x∈halfDisc q) => by
        change x∈Metric.ball (0:E2) ((4*q)/4)
        rw [show (4*q)/4=q by ring]
        exact hx.1) hae
    filter_upwards [hh,ae_restrict_mem hUq.measurableSet] with x hx hxU
    rw [hx,hUeq (Metric.ball_subset_closedBall hxU.1)]
    exact if_pos hxU.2.le
  exact ⟨f,hfc,MeasureTheory.Measure.eqOn_open_of_ae_eq hae' hUq
    hfc.continuousOn (hs.mono hsub).continuousOn⟩

end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.native_halfdisc_H2_continuous_radius_v474
