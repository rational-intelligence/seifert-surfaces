import B1NativeBoundaryNirenbergGradient_v468
import DifferentialGeometry.Analysis.Sobolev.Tools.DifferenceQuotient.IntegrationByParts
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

/-- Difference quotients of the actual flux test against the derivative of the
cutoff quotient. This is the boundary integration-by-parts identity; all fields
are extended by zero from the actual half-disc. -/
theorem native_boundary_tangential_flux_identity_v468
    (R r t : ℝ) (hroom : r+|t|<R) (htne : t≠0)
    (eta : E2 → ℝ) (hs : ContDiff ℝ ∞ eta) (hc : HasCompactSupport eta)
    (ht : tsupport eta ⊆ Metric.ball 0 r)
    (u : E2 → ℝ) (du : E2 → E2) (hu : H10On (halfDisc R) u du)
    (F : E2 → E2) (S : E2 → ℝ)
    (hF : MemLp F 2 (volume.restrict (halfDisc R)))
    (hS : MemLp S 2 (volume.restrict (halfDisc R)))
    (hweak : ∀ phi : E2 → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ halfDisc R →
        (∫ x in halfDisc R, inner ℝ (F x) (planarGradient phi x)-S x*phi x)=0) :
    (∫ x, ∑ i : Fin 2,
      diffQuot 0 t (fun y => (halfDisc R).indicator F y i) x *
        (eta x^2 * diffQuot 0 t (fun y => (halfDisc R).indicator du y i) x+
          2*eta x*fderiv ℝ eta x (coordinateVector 2 i)*
            diffQuot 0 t ((halfDisc R).indicator u) x)) =
      -(∫ x, (halfDisc R).indicator S x *
        nirenbergTestFunction 0 t eta ((halfDisc R).indicator u) x) := by
  classical
  let U := halfDisc R
  let V := nirenbergTestFunction 0 t eta (U.indicator u)
  let Q : Fin 2 → E2 → ℝ := fun i x => eta x^2 * diffQuot 0 t (fun y => U.indicator du y i) x+
    2*eta x*fderiv ℝ eta x (coordinateVector 2 i)*diffQuot 0 t (U.indicator u) x
  have hUm : MeasurableSet U := (Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous)).measurableSet
  have hF0 : MemLp (U.indicator F) 2 volume := (memLp_indicator_iff_restrict hUm.nullMeasurableSet).mpr hF
  have hS0 : MemLp (U.indicator S) 2 volume := (memLp_indicator_iff_restrict hUm.nullMeasurableSet).mpr hS
  have hzero := zero_extension U hUm u du hu
  have hu0 : MemLp (U.indicator u) 2 volume := by simpa using hzero.1.2.1
  have hdu0 : MemLp (U.indicator du) 2 volume := by simpa using hzero.1.2.2
  have hQ (i : Fin 2) : MemLp (Q i) 2 volume := by
    have he : HasCompactSupport (fun x : E2 => eta x^2) := by
      simpa only [pow_two,Pi.mul_def] using hc.mul_right (f' := eta)
    have hfirst := ((hs.continuous.pow 2).memLp_top_of_hasCompactSupport he volume).fun_mul
      (r := 2) (memLp_diffQuot 0 t (hdu0.eval_piLp i))
    have hcoef : Continuous (fun x : E2 => 2*eta x*fderiv ℝ eta x (coordinateVector 2 i)) :=
      (continuous_const.mul hs.continuous).mul
        ((hs.continuous_fderiv (by simp)).clm_apply continuous_const)
    have hcoefc : HasCompactSupport (fun x : E2 => 2*eta x*fderiv ℝ eta x (coordinateVector 2 i)) := by
      apply HasCompactSupport.intro' hc.isCompact (isClosed_tsupport eta)
      intro x hx
      simp only [image_eq_zero_of_notMem_tsupport hx,mul_zero,zero_mul]
    have hsecond := (hcoef.memLp_top_of_hasCompactSupport hcoefc volume).fun_mul
      (r := 2) (memLp_diffQuot 0 t hu0)
    exact hfirst.add hsecond
  obtain ⟨G,hG,hGeq⟩ := native_boundary_nirenberg_explicit_gradient_v468
    R r t hroom htne eta hs hc ht u du hu
  obtain ⟨hFG,hSV,heq⟩ := native_h10_flux_source_testing U F S hF hS hweak V G hG
  have hpair : (∫ x in U, inner ℝ (F x) (G x)) = ∫ x in U, S x*V x := by
    rw [integral_sub hFG hSV] at heq
    exact sub_eq_zero.mp heq
  have hpoint : (fun x => inner ℝ (F x) (G x)) =ᵐ[volume.restrict U]
      fun x => ∑ i : Fin 2, F x i * diffQuot 0 (-t) (Q i) x := by
    filter_upwards [hGeq 0,hGeq 1] with x h0 h1
    simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_two,
      star_trivial,h0,h1,Q]
    ring
  have hglobal : (∫ x, ∑ i : Fin 2, U.indicator F x i * diffQuot 0 (-t) (Q i) x) =
      ∫ x, U.indicator S x*V x := by
    have hl : (∫ x in U, ∑ i : Fin 2, U.indicator F x i * diffQuot 0 (-t) (Q i) x) =
        ∫ x in U, inner ℝ (F x) (G x) := by
      apply integral_congr_ae
      filter_upwards [hpoint,ae_restrict_mem hUm] with x hh hx
      rw [indicator_of_mem hx]
      exact hh.symm
    have hr : (∫ x in U, U.indicator S x*V x)=∫ x in U, S x*V x := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hUm] with x hx
      rw [indicator_of_mem hx]
    calc
      _ = ∫ x in U, ∑ i : Fin 2, U.indicator F x i * diffQuot 0 (-t) (Q i) x :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun x hx => by simp [indicator_of_notMem hx])).symm
      _ = ∫ x in U, inner ℝ (F x) (G x) := hl
      _ = ∫ x in U, S x*V x := hpair
      _ = ∫ x in U, U.indicator S x*V x := hr.symm
      _ = ∫ x, U.indicator S x*V x :=
        setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun x hx => by simp [indicator_of_notMem hx])
  have hip (i : Fin 2) : Integrable (fun x => U.indicator F x i * diffQuot 0 (-t) (Q i) x) volume :=
    (hF0.eval_piLp i).integrable_mul (memLp_diffQuot 0 (-t) (hQ i))
  have hiq (i : Fin 2) : Integrable (fun x => diffQuot 0 t (fun y => U.indicator F y i) x*Q i x) volume :=
    (memLp_diffQuot 0 t (hF0.eval_piLp i)).integrable_mul (hQ i)
  have hibp (i : Fin 2) : (∫ x, U.indicator F x i*diffQuot 0 (-t) (Q i) x) =
      -(∫ x, diffQuot 0 t (fun y => U.indicator F y i) x*Q i x) := by
    have hi := integral_diffQuot_mul_eq_neg_integral_mul_diffQuot 0 htne (hF0.eval_piLp i) (hQ i)
    linarith
  have he : (∫ x, ∑ i : Fin 2, U.indicator F x i*diffQuot 0 (-t) (Q i) x) =
      -(∫ x, ∑ i : Fin 2, diffQuot 0 t (fun y => U.indicator F y i) x*Q i x) := by
    rw [integral_finsetSum _ (fun i _ => hip i), integral_finsetSum _ (fun i _ => hiq i)]
    simp_rw [hibp]
    rw [Finset.sum_neg_distrib]
  rw [he] at hglobal
  exact (neg_eq_iff_eq_neg.mp hglobal)

end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.native_boundary_tangential_flux_identity_v468
