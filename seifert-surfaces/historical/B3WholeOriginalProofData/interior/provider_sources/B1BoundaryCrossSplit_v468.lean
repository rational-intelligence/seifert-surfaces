import B1ActualBoundaryTangentialEnergy_v468
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
set_option maxHeartbeats 0

/-- The three actual boundary cross terms are integrable and separate under
the integral, allowing the existing Nirenberg Young bounds to be consumed. -/
theorem boundary_tangential_cross_abs_le_v468
    (B : SmoothEllipticBilinearForm 2 univ) (eta : E2 → ℝ)
    (hs : ContDiff ℝ ∞ eta) (hc : HasCompactSupport eta)
    (t : ℝ) (u : E2 → ℝ) (du : E2 → E2)
    (hu : MemLp u 2 volume) (hd : MemLp du 2 volume) :
    |∫ x, boundaryTangentialCross_v468 B eta t u du x| ≤
      |∑ i : Fin 2, ∑ j : Fin 2, ∫ x,
        2*translate 0 t (fun y => B.a y i j) x*eta x*
          fderiv ℝ eta x (coordinateVector 2 j)*diffQuot 0 t (fun y => du y i) x*diffQuot 0 t u x|+
      |∑ i : Fin 2, ∑ j : Fin 2, ∫ x,
        diffQuot 0 t (fun y => B.a y i j) x*eta x^2*du x i*diffQuot 0 t (fun y => du y j) x|+
      |∑ i : Fin 2, ∑ j : Fin 2, ∫ x,
        2*diffQuot 0 t (fun y => B.a y i j) x*eta x*
          fderiv ℝ eta x (coordinateVector 2 j)*du x i*diffQuot 0 t u x| := by
  classical
  let C1 : Fin 2 → Fin 2 → E2 → ℝ := fun i j x =>
    2*translate 0 t (fun y => B.a y i j) x*eta x*fderiv ℝ eta x (coordinateVector 2 j)*
      diffQuot 0 t (fun y => du y i) x*diffQuot 0 t u x
  let C2 : Fin 2 → Fin 2 → E2 → ℝ := fun i j x =>
    diffQuot 0 t (fun y => B.a y i j) x*eta x^2*du x i*diffQuot 0 t (fun y => du y j) x
  let C3 : Fin 2 → Fin 2 → E2 → ℝ := fun i j x =>
    2*diffQuot 0 t (fun y => B.a y i j) x*eta x*fderiv ℝ eta x (coordinateVector 2 j)*
      du x i*diffQuot 0 t u x
  have hpair (c f q : E2 → ℝ) (hcs : Continuous c) (hcc : HasCompactSupport c)
      (hf : MemLp f 2 volume) (hq : MemLp q 2 volume) :
      Integrable (fun x => c x*f x*q x) volume :=
    ((hcs.memLp_top_of_hasCompactSupport hcc volume).fun_mul (r := 2) hf).integrable_mul hq
  have htranslate (i j : Fin 2) : Continuous (translate 0 t (fun y => B.a y i j)) :=
    (B.continuous_a i j).comp (continuous_id.add continuous_const)
  have hdqa (i j : Fin 2) : Continuous (diffQuot 0 t (fun y => B.a y i j)) :=
    continuous_diffQuot_of_continuous 0 t (B.continuous_a i j)
  have hder (j : Fin 2) : Continuous (fun x => fderiv ℝ eta x (coordinateVector 2 j)) :=
    (hs.continuous_fderiv (by simp)).clm_apply continuous_const
  have hsupp (c : E2 → ℝ) (hz : ∀ x∉tsupport eta, c x=0) : HasCompactSupport c :=
    HasCompactSupport.intro' hc.isCompact (isClosed_tsupport eta) hz
  have h1 (i j : Fin 2) : Integrable (C1 i j) volume := by
    apply hpair _ _ _ (((continuous_const.mul (htranslate i j)).mul hs.continuous).mul (hder j))
      (hsupp _ (fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx]))
      (memLp_diffQuot 0 t (hd.eval_piLp i)) (memLp_diffQuot 0 t hu)
  have h2 (i j : Fin 2) : Integrable (C2 i j) volume := by
    apply hpair _ _ _ ((hdqa i j).mul (hs.continuous.pow 2))
      (hsupp _ (fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx]))
      (hd.eval_piLp i) (memLp_diffQuot 0 t (hd.eval_piLp j))
  have h3 (i j : Fin 2) : Integrable (C3 i j) volume := by
    apply hpair _ _ _ (((continuous_const.mul (hdqa i j)).mul hs.continuous).mul (hder j))
      (hsupp _ (fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx]))
      (hd.eval_piLp i) (memLp_diffQuot 0 t hu)
  have he : (∫ x, boundaryTangentialCross_v468 B eta t u du x)=
      (∑ i : Fin 2, ∑ j : Fin 2, ∫ x, C1 i j x)+
      (∑ i : Fin 2, ∑ j : Fin 2, ∫ x, C2 i j x)+
      (∑ i : Fin 2, ∑ j : Fin 2, ∫ x, C3 i j x) := by
    have hj (i j : Fin 2) : (∫ x, C1 i j x+C2 i j x+C3 i j x)=
        (∫ x, C1 i j x)+(∫ x, C2 i j x)+(∫ x, C3 i j x) := by
      exact (integral_add ((h1 i j).add (h2 i j)) (h3 i j)).trans
        (congrArg (fun z => z+∫ x, C3 i j x) (integral_add (h1 i j) (h2 i j)))
    calc
      _ = ∑ i : Fin 2, ∫ x, ∑ j : Fin 2, (C1 i j x+C2 i j x+C3 i j x) :=
        integral_finsetSum _ (fun i _ => integrable_finsetSum _
          (fun j _ => ((h1 i j).add (h2 i j)).add (h3 i j)))
      _ = ∑ i : Fin 2, ∑ j : Fin 2, ∫ x, C1 i j x+C2 i j x+C3 i j x := by
        apply Finset.sum_congr rfl
        intro i hi
        exact integral_finsetSum _ (fun j _ => ((h1 i j).add (h2 i j)).add (h3 i j))
      _ = _ := by simp_rw [hj,Finset.sum_add_distrib]
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)

end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.boundary_tangential_cross_abs_le_v468
