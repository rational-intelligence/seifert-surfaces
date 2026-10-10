import B1ActualBoundaryFullH3_v468
import B1NativeHalfDiscEvenW14_v468
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.Morrey.Basic
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open DifferentialGeometry.Analysis.Sobolev.Euclidean
set_option maxHeartbeats 1000000

/-- Native boundary H2 supplies an actual continuous extension across the
flat edge by even H1 reflection, a supercritical Sobolev gain, and Morrey. -/
theorem native_halfdisc_H2_continuous_extension_v468 (R : ℝ) (hR : 0<R) (u : E2 → ℝ)
    (hs : ContDiffOn ℝ ∞ u (halfDisc R)) (hu : MemWkp 2 2 u (halfDisc R)) :
    ∃ f : E2 → ℝ, Continuous f ∧ EqOn f u (halfDisc (R/4)) := by
  have he := native_halfdisc_even_W14_v468 R hR u hs hu
  obtain ⟨f,C,hfc,hC,hae,hHolder⟩ :=
    DifferentialGeometry.Analysis.Sobolev.EuclideanMorrey.morrey_holder_representative
      (by norm_num : (2:ℝ)<4) hR (show DeGiorgi.MemW1pWitness (ENNReal.ofReal (4:ℝ))
        (fun x => if 0≤x 1 then u x else u (ChartMetricProvider.Variational.DirectWeak.BoundarySupport.reflect x))
        (Metric.ball 0 R) from by simpa using he.someWitness)
  refine ⟨f,hfc,?_⟩
  have hsub : halfDisc (R/4) ⊆ halfDisc R :=
    fun x hx => ⟨Metric.ball_subset_ball (by linarith : R/4≤R) hx.1,hx.2⟩
  have hU : IsOpen (halfDisc (R/4)) := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)
  have heq : f =ᵐ[volume.restrict (halfDisc (R/4))] u := by
    have hh := ae_restrict_of_ae_restrict_of_subset (fun x (hx : x∈halfDisc (R/4)) => hx.1) hae
    filter_upwards [hh,ae_restrict_mem hU.measurableSet] with x hx hxU
    simpa only [if_pos hxU.2.le] using hx
  exact MeasureTheory.Measure.eqOn_open_of_ae_eq heq hU hfc.continuousOn ((hs.mono hsub).continuousOn)

/-- The same original positive Dirichlet solution has continuous extensions
of both literal interior gradient components, obtained from its native H3. -/
theorem actual_positive_boundary_gradient_continuous_v468
    (D : B1OriginalData (g := g) J) (s : Circle) (W : CollarWindow D s) :
    ∃ R : ℝ, 0<R ∧ R<W.R ∧ ∃ h : E2 → ℝ,
      ContinuousOn h (closedHalfDisc R) ∧
      (∀ x ∈ frontier (halfDisc R), h x=1) ∧
      (∀ x ∈ closedHalfDisc R, (1/2 : ℝ)≤h x) ∧
      ContDiffOn ℝ ∞ h (halfDisc R) ∧
      H1On (halfDisc R) h (planarGradient h) ∧
      H10On (halfDisc R) (fun x => h x-1) (planarGradient h) ∧
      WeakLinearEquationOn (halfDisc R) W.a W.b W.c h (planarGradient h) ∧
      (∀ x ∈ halfDisc R, classicalL W.a W.b W.c h x=0) ∧
      ∀ i : Fin 2, ∃ f : E2 → ℝ, Continuous f ∧
        EqOn f (fun x => planarGradient h x i) (halfDisc (R/256)) := by
  obtain ⟨R,hR,hRW,h,hhc,hfront,hpos,hs,h1,h0,heq,hcl,hH3⟩ :=
    actual_positive_boundary_full_H3_v468 D s W
  refine ⟨R,hR,hRW,h,hhc,hfront,hpos,hs,h1,h0,heq,hcl,?_⟩
  intro i
  have hU : IsOpen (halfDisc (R/64)) := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)
  have hsub : halfDisc (R/64) ⊆ halfDisc R :=
    fun x hx => ⟨Metric.ball_subset_ball (by linarith : R/64≤R) hx.1,hx.2⟩
  have hgs : ContDiffOn ℝ ∞ (fun x => planarGradient h x i) (halfDisc (R/64)) := by
    have he : (fun x => planarGradient h x i)=fun x => fderiv ℝ h x (coordinateVector 2 i) := by
      funext x
      exact QuasilinearLocalization.Helpers.gradient_apply h x i
    rw [he]
    exact ((hs.fderiv_of_isOpen (Metric.isOpen_ball.inter
      (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous))
      (m:=∞) (by simp)).clm_apply contDiffOn_const).mono hsub
  have hp := native_smooth_partial_memWkp_v468 _ hU h (hs.mono hsub) 2 hH3 i
  simpa only [div_div,show (64:ℝ)*4=256 by norm_num] using
    native_halfdisc_H2_continuous_extension_v468 (R/64) (by positivity) _ hgs hp
end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.native_halfdisc_H2_continuous_extension_v468
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.actual_positive_boundary_gradient_continuous_v468
