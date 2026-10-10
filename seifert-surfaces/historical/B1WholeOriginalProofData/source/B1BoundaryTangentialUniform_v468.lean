import B1BoundaryCrossSplit_v468
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.TestFunction.IntegralBound
import DifferentialGeometry.Analysis.Sobolev.Tools.DifferenceQuotient.WeakDerivativeBound
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open ChartMetricProvider.Variational.DirectWeak.BoundaryContinuation
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction
open DifferentialGeometry.Analysis.Sobolev.NirenbergCrossBoundsNonSmooth
set_option maxHeartbeats 800000

/-- A uniform L2 bound on the full tangential gradient quotient at the flat
edge follows from the native equation and H10, without a C1 boundary premise. -/
theorem native_boundary_tangential_uniform_v468
    (R r rho : ℝ) (hrho : 0<rho) (hroom : r+rho<R)
    (eta : E2 → ℝ) (hs : ContDiff ℝ ∞ eta) (hc : HasCompactSupport eta)
    (ht : tsupport eta ⊆ Metric.ball 0 r) (hrange : range eta ⊆ Icc (0:ℝ) 1)
    (N : ℝ) (hN : 0≤N) (hder : ∀ x, ‖fderiv ℝ eta x‖≤N)
    (V : Set E2) (hV : MeasurableSet V) (hVone : ∀ x∈V, eta x=1)
    (u : E2 → ℝ) (du : E2 → E2) (hu : H10On (halfDisc R) u du)
    (F : E2 → E2) (S : E2 → ℝ)
    (hF : MemLp F 2 (volume.restrict (halfDisc R)))
    (hS : MemLp S 2 (volume.restrict (halfDisc R)))
    (hweak : ∀ phi : E2 → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ halfDisc R →
        (∫ x in halfDisc R, inner ℝ (F x) (planarGradient phi x)-S x*phi x)=0)
    (B : SmoothEllipticBilinearForm 2 univ)
    (hBF : ∀ x∈halfDisc R, matrixAction (B.a x) (du x)=F x) :
    ∃ M : ℝ, 0≤M ∧ ∀ t : ℝ, t≠0 → |t|≤rho →
      (∫ x in V, ∑ i : Fin 2,
        (diffQuot 0 t (fun y => (halfDisc R).indicator du y i) x)^2) ≤ M := by
  classical
  let U := halfDisc R
  let u0 := U.indicator u
  let d0 := U.indicator du
  let s0 := U.indicator S
  let O : Set E2 := Metric.ball 0 R
  have hUm : MeasurableSet U := (Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous)).measurableSet
  have hz := zero_extension U hUm u du hu
  have hu0 : MemLp u0 2 volume := by simpa using hz.1.2.1
  have hd0 : MemLp d0 2 volume := by simpa using hz.1.2.2
  have hs0 : MemLp s0 2 volume := (memLp_indicator_iff_restrict hUm.nullMeasurableSet).mpr hS
  let hw := native_regular_witness_v468 univ u0 d0 hz.1
  have hthick : ∀ {t : ℝ}, |t|≤rho → Metric.cthickening |t| (tsupport eta) ⊆ O := by
    intro t htr x hx
    rw [hc.isCompact.cthickening_eq_biUnion_closedBall (abs_nonneg t)] at hx
    obtain ⟨y,hxy⟩ := mem_iUnion.mp hx
    obtain ⟨hyeta,hxy⟩ := mem_iUnion.mp hxy
    have hyn : ‖y‖<r := by simpa [dist_zero_right] using ht hyeta
    have hdist : dist x y≤|t| := hxy
    change dist x (0:E2)<R
    rw [dist_zero_right]
    have htri := dist_triangle x y (0:E2)
    rw [dist_zero_right,dist_zero_right] at htri
    linarith
  have hFk : ∀ {t : ℝ}, t≠0 → |t|≤rho →
      (∫ x in tsupport eta, (diffQuot 0 t u0 x)^2) ≤
        ∫ x in O, ∑ i : Fin 2, (d0 x i)^2 := by
    intro t htne htr
    have ht0 : Metric.cthickening rho (closure (tsupport eta)) ⊆ O := by
      rw [(isClosed_tsupport eta).closure_eq]
      simpa only [abs_of_pos hrho] using (hthick (t := rho) (by rw [abs_of_pos hrho]))
    have hb := integral_sq_diffQuot_le_integral_sq_weakPartial_meas hu0 (hd0.eval_piLp 0) 0
      (hw.isWeakGrad 0) measurableSet_ball (isClosed_tsupport eta).measurableSet
      (by simpa only [(isClosed_tsupport eta).closure_eq] using hc.isCompact) hrho ht0 htne htr
    refine hb.trans ?_
    have hi (i : Fin 2) : Integrable (fun x => (d0 x i)^2) volume := by
      simpa only [Real.norm_eq_abs,sq_abs] using
        (hd0.eval_piLp i).integrable_norm_pow (by decide : (2:ℕ)≠0)
    apply integral_mono_ae (hi 0).restrict (integrable_finsetSum _ (fun i _ => hi i)).restrict
    exact Eventually.of_forall fun x => Finset.single_le_sum (fun i _ => sq_nonneg (d0 x i)) (Finset.mem_univ 0)
  have hvbound : ∀ {t : ℝ}, t≠0 → |t|≤rho →
      (∫ x, (nirenbergTestFunction 0 t eta u0 x)^2) ≤
        8*N^2*(∫ x in tsupport eta, (diffQuot 0 t u0 x)^2)+
          2*(∫ x, eta x^2*(diffQuot 0 t (fun y => d0 y 0) x)^2) := by
    intro t htne htr
    apply integral_sq_nirenbergTestFunction_le hu0 (hd0.eval_piLp 0) 0 (hw.isWeakGrad 0) hs hc
    · intro x
      obtain ⟨hlo,hhi⟩ := hrange (mem_range_self x)
      simpa only [abs_of_nonneg hlo] using hhi
    · intro x
      calc
        _ ≤ ‖fderiv ℝ eta x‖ * ‖(EuclideanSpace.single 0 1 : E2)‖ :=
          (fderiv ℝ eta x).le_opNorm _
        _ ≤ N := by simpa using hder x
  obtain ⟨C,hC,hbound⟩ := nirenberg_diffQuot_g_localL2_bound B hu0
    (fun {_} _ => hs0.restrict _) (fun i => hd0.eval_piLp i) hs hc hrange hN hder
    (Ω' := O) Metric.isOpen_ball (subset_univ _)
    (isCompact_closedBall (0:E2) R |>.of_isClosed_subset isClosed_closure
      (closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall))
    hthick hVone hV 0 hFk hvbound (by
      intro t htne htr
      have he := native_boundary_tangential_energy_v468 R r t (by linarith only [hroom,htr]) htne eta hs hc ht
        u du hu F S hF hS hweak B hBF
      have hcros := boundary_tangential_cross_abs_le_v468 B eta hs hc t u0 d0 hu0 hd0
      simp only [Measure.restrict_univ]
      dsimp only [u0,d0,s0,U] at hcros ⊢
      simp only [coordinateVector] at hcros
      linarith only [he,hcros,abs_nonneg (∫ x, B.c x*u0 x*nirenbergTestFunction 0 t eta u0 x)])
  let E := (∫ x in O, ∑ i : Fin 2, (d0 x i)^2)+
    (∫ x in O, (u0 x)^2)+(∫ x in O, (s0 x)^2)
  have hE : 0≤E := by
    apply add_nonneg
    · apply add_nonneg
      · exact integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
      · exact integral_nonneg fun x => sq_nonneg _
    · exact integral_nonneg fun x => sq_nonneg _
  refine ⟨C*E/(B.lam/2),div_nonneg (mul_nonneg hC hE) (half_pos B.ellipticity_pos).le,?_⟩
  intro t htne htr
  apply (le_div_iff₀ (half_pos B.ellipticity_pos)).mpr
  simpa only [mul_comm] using hbound htne htr

end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.native_boundary_tangential_uniform_v468
