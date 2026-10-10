import B1BoundaryTangentialUniform_v468
import DifferentialGeometry.Analysis.Sobolev.Tools.DifferenceQuotient.LocalWeakLimit
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open ChartMetricProvider.Variational.DirectWeak.BoundaryContinuation
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
set_option maxHeartbeats 800000

/-- Convert the native integrated quotient bound into a genuine L2 weak
partial derivative; the open patch may cross the flat boundary. -/
theorem native_tangential_weakDerivative_of_uniform_v468
    (d : E2 → E2) (hd : MemLp d 2 volume)
    (V : Set E2) (hV : IsOpen V) (hVc : IsCompact (closure V))
    (rho : ℝ) (hrho : 0<rho) (M : ℝ) (hM : 0≤M)
    (hbound : ∀ t : ℝ, t≠0 → |t|≤rho →
      (∫ x in V, ∑ i : Fin 2, (diffQuot 0 t (fun y => d y i) x)^2)≤M) :
    ∀ i : Fin 2, ∃ w : E2 → ℝ,
      MemLp w 2 (volume.restrict V) ∧
      DeGiorgi.HasWeakPartialDeriv 0 w (fun y => d y i) V := by
  intro i
  have hnorm (t : ℝ) (ht : 0 < |t|) (htr : |t|≤rho) :
      eLpNorm (diffQuot 0 t (fun y => d y i)) 2 (volume.restrict V)≤
        ENNReal.ofReal (M ^ (1/2 : ℝ)) := by
    have hq (j : Fin 2) := memLp_diffQuot 0 t (hd.eval_piLp j)
    have hi (j : Fin 2) : Integrable (fun x => (diffQuot 0 t (fun y => d y j) x)^2) volume := by
      simpa only [Real.norm_eq_abs,sq_abs] using
        (hq j).integrable_norm_pow (by decide : (2:ℕ)≠0)
    have hb : (∫ x in V, (diffQuot 0 t (fun y => d y i) x)^2)≤M := by
      refine (integral_mono_ae (hi i).restrict
        (integrable_finsetSum _ (fun j _ => hi j)).restrict ?_).trans
          (hbound t (abs_pos.mp ht) htr)
      exact Eventually.of_forall fun x =>
        Finset.single_le_sum (fun j _ => sq_nonneg (diffQuot 0 t (fun y => d y j) x)) (Finset.mem_univ i)
    rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num : (2:ℝ≥0∞)≠0)
      (by norm_num : (2:ℝ≥0∞)≠⊤) ((hq i).restrict V)]
    simp only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs]
    apply ENNReal.ofReal_le_ofReal
    have hn : 0≤∫ x in V, (diffQuot 0 t (fun y => d y i) x)^2 :=
      integral_nonneg fun x => sq_nonneg _
    convert Real.rpow_le_rpow hn hb (by norm_num : (0:ℝ)≤1/2) using 1 <;> norm_num
  obtain ⟨w,hw,hwder,-⟩ := hasWeakPartialDeriv_of_diffQuot_uniform_bound_local
    isOpen_univ hV hVc hrho (subset_univ _) (by simpa using (hd.eval_piLp i)) 0
    (Real.rpow_nonneg hM _) hnorm
  exact ⟨w,hw,hwder⟩

end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.native_tangential_weakDerivative_of_uniform_v468
