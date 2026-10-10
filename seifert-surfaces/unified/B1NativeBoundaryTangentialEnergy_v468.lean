import B1NativeBoundaryTangentialIdentity_v468
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.SubstitutionIdentity.SubstitutionNonSmooth
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open ChartMetricProvider.Variational.DirectWeak.BoundaryContinuation
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction
set_option maxHeartbeats 0

def boundaryTangentialCross_v468 (B : SmoothEllipticBilinearForm 2 univ)
    (eta : E2 → ℝ) (t : ℝ) (u : E2 → ℝ) (du : E2 → E2) (x : E2) : ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 2,
    (2*translate 0 t (fun y => B.a y i j) x*eta x*
        fderiv ℝ eta x (coordinateVector 2 j)*diffQuot 0 t (fun y => du y i) x*diffQuot 0 t u x+
      diffQuot 0 t (fun y => B.a y i j) x*eta x^2*du x i*diffQuot 0 t (fun y => du y j) x+
      2*diffQuot 0 t (fun y => B.a y i j) x*eta x*
        fderiv ℝ eta x (coordinateVector 2 j)*du x i*diffQuot 0 t u x)

/-- Coercive tangential boundary energy for the native H10 solution, with all
three coefficient/cutoff errors retained explicitly. -/
theorem native_boundary_tangential_energy_v468
    (R r t : ℝ) (hroom : r+|t|<R) (htne : t≠0)
    (eta : E2 → ℝ) (hs : ContDiff ℝ ∞ eta) (hc : HasCompactSupport eta)
    (ht : tsupport eta ⊆ Metric.ball 0 r)
    (u : E2 → ℝ) (du : E2 → E2) (hu : H10On (halfDisc R) u du)
    (F : E2 → E2) (S : E2 → ℝ)
    (hF : MemLp F 2 (volume.restrict (halfDisc R)))
    (hS : MemLp S 2 (volume.restrict (halfDisc R)))
    (hweak : ∀ phi : E2 → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ halfDisc R →
        (∫ x in halfDisc R, inner ℝ (F x) (planarGradient phi x)-S x*phi x)=0)
    (B : SmoothEllipticBilinearForm 2 univ)
    (hBF : ∀ x∈halfDisc R, matrixAction (B.a x) (du x)=F x) :
    B.lam * (∫ x, eta x^2 * ∑ i : Fin 2,
      (diffQuot 0 t (fun y => (halfDisc R).indicator du y i) x)^2) ≤
      |∫ x, (halfDisc R).indicator S x *
        nirenbergTestFunction 0 t eta ((halfDisc R).indicator u) x|+
      |∫ x, boundaryTangentialCross_v468 B eta t
        ((halfDisc R).indicator u) ((halfDisc R).indicator du) x| := by
  classical
  let U := halfDisc R
  let u0 := U.indicator u
  let d0 := U.indicator du
  let F0 := U.indicator F
  let Q : Fin 2 → E2 → ℝ := fun i x => eta x^2*diffQuot 0 t (fun y => d0 y i) x+
    2*eta x*fderiv ℝ eta x (coordinateVector 2 i)*diffQuot 0 t u0 x
  let P : E2 → ℝ := fun x => ∑ i : Fin 2, ∑ j : Fin 2,
    translate 0 t (fun y => B.a y i j) x*eta x^2*
      diffQuot 0 t (fun y => d0 y i) x*diffQuot 0 t (fun y => d0 y j) x
  let I : E2 → ℝ := fun x => ∑ i : Fin 2,
    diffQuot 0 t (fun y => F0 y i) x*Q i x
  have hUm : MeasurableSet U := (Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous)).measurableSet
  have hzero := zero_extension U hUm u du hu
  have hu0 : MemLp u0 2 volume := by simpa using hzero.1.2.1
  have hd0 : MemLp d0 2 volume := by simpa using hzero.1.2.2
  have hF0 : MemLp F0 2 volume := (memLp_indicator_iff_restrict hUm.nullMeasurableSet).mpr hF
  have hact (x : E2) : matrixAction (B.a x) (d0 x)=F0 x := by
    by_cases hx : x∈U
    · simpa only [d0,F0,indicator_of_mem hx] using hBF x hx
    · ext i
      simp [d0,F0,indicator_of_notMem hx,matrixAction]
  have hQ (i : Fin 2) : MemLp (Q i) 2 volume := by
    have he : HasCompactSupport (fun x : E2 => eta x^2) := by
      simpa only [pow_two,Pi.mul_def] using hc.mul_right (f' := eta)
    have hfirst := ((hs.continuous.pow 2).memLp_top_of_hasCompactSupport he volume).fun_mul
      (r := 2) (memLp_diffQuot 0 t (hd0.eval_piLp i))
    have hcoef : Continuous (fun x : E2 => 2*eta x*fderiv ℝ eta x (coordinateVector 2 i)) :=
      (continuous_const.mul hs.continuous).mul
        ((hs.continuous_fderiv (by simp)).clm_apply continuous_const)
    have hcoefc : HasCompactSupport (fun x : E2 => 2*eta x*fderiv ℝ eta x (coordinateVector 2 i)) := by
      apply HasCompactSupport.intro' hc.isCompact (isClosed_tsupport eta)
      intro x hx
      simp only [image_eq_zero_of_notMem_tsupport hx,mul_zero,zero_mul]
    exact hfirst.add ((hcoef.memLp_top_of_hasCompactSupport hcoefc volume).fun_mul
      (r := 2) (memLp_diffQuot 0 t hu0))
  have hI : Integrable I volume :=
    integrable_finsetSum _ (fun i _ =>
      (memLp_diffQuot 0 t (hF0.eval_piLp i)).integrable_mul (hQ i))
  have hP : Integrable P volume := by
    apply integrable_finsetSum
    intro i hi
    apply integrable_finsetSum
    intro j hj
    have hcoef : Continuous (fun x => translate 0 t (fun y => B.a y i j) x*eta x^2) :=
      ((B.continuous_a i j).comp (continuous_id.add continuous_const)).mul (hs.continuous.pow 2)
    have hcoefc : HasCompactSupport (fun x => translate 0 t (fun y => B.a y i j) x*eta x^2) := by
      apply HasCompactSupport.intro' hc.isCompact (isClosed_tsupport eta)
      intro x hx
      simp only [image_eq_zero_of_notMem_tsupport hx,zero_pow (by norm_num : (2:ℕ)≠0),mul_zero]
    exact ((hcoef.memLp_top_of_hasCompactSupport hcoefc volume).fun_mul
      (r := 2) (memLp_diffQuot 0 t (hd0.eval_piLp i))).integrable_mul
        (memLp_diffQuot 0 t (hd0.eval_piLp j))
  have hpoint (x : E2) : I x = P x+boundaryTangentialCross_v468 B eta t u0 d0 x := by
    have hFcoord (i : Fin 2) : (fun y => F0 y i)=(fun y => ∑ j : Fin 2, B.a y i j*d0 y j) := by
      funext y
      exact (congrArg (fun v : E2 => v i) (hact y)).symm
    simp only [I,hFcoord,Fin.sum_univ_two,P,Q,boundaryTangentialCross_v468]
    simp only [diffQuot_apply_of_ne 0 htne,DifferentialGeometry.Analysis.Sobolev.translate]
    rw [B.symm x 1 0,B.symm (x+t • EuclideanSpace.single 0 1) 1 0]
    ring
  have hC : Integrable (fun x => boundaryTangentialCross_v468 B eta t u0 d0 x) volume := by
    apply (hI.sub hP).congr
    exact Eventually.of_forall fun x => by dsimp only [Pi.sub_apply]; rw [hpoint]; ring
  have he : (∫ x, I x) = (∫ x, P x)+(∫ x, boundaryTangentialCross_v468 B eta t u0 d0 x) := by
    simp_rw [hpoint]
    exact integral_add hP hC
  have hidentity := native_boundary_tangential_flux_identity_v468 R r t hroom htne eta hs hc ht
    u du hu F S hF hS hweak
  change (∫ x, I x) = -(∫ x, U.indicator S x*nirenbergTestFunction 0 t eta u0 x) at hidentity
  rw [he] at hidentity
  have hprincipal :=
    DifferentialGeometry.Analysis.Sobolev.NirenbergSubstitutionNonSmooth.principal_term_ge_lambda_norm_sq_nonsmooth
      B (fun i => hd0.eval_piLp i) hs hc (Ω' := univ) (subset_univ _) (R₀ := |t|)
      (fun {_} _ => subset_univ _) 0 (le_refl |t|)
  change B.lam*(∫ x, eta x^2*∑ i : Fin 2, (diffQuot 0 t (fun y => d0 y i) x)^2) ≤ ∫ x, P x at hprincipal
  exact hprincipal.trans (by
    linarith [neg_le_abs (∫ x, U.indicator S x*nirenbergTestFunction 0 t eta u0 x),
      neg_le_abs (∫ x, boundaryTangentialCross_v468 B eta t u0 d0 x)])

end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.native_boundary_tangential_energy_v468
