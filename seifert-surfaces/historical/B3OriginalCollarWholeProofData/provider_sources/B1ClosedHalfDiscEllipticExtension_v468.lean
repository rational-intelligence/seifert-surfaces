import B1HalfDiscEllipticExtension_v468
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.OriginalEndpoints.B1GraphCoefficients
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
set_option maxHeartbeats 0

/-- A compact patch reaching the flat boundary has a global smooth symmetric
elliptic extension of its actual principal coefficients. Positivity in an ambient
neighborhood is derived from the original uniform bound on the closed half-disc. -/
theorem actual_closed_halfdisc_smooth_elliptic_extension_v468
    (D : B1OriginalData (g := g) J) (s : Circle) (W : CollarWindow D s)
    (P : Set E2) (hP : IsCompact P) (hPH : P ⊆ closedHalfDisc W.R) :
    ∃ B : SmoothEllipticBilinearForm 2 univ, ∀ x ∈ P, B.a x=W.a x := by
  classical
  obtain ⟨O,hO,hWO,hOU,hjets,hf,hdf,ha,hq,hlg,hlh,hb,hc⟩ := actual_coefficient_open_tube D s W
  obtain ⟨-,hsym,ell,C,hell,hC,hbounds⟩ := actual_slope_hessian_uniform_bounds D s W
  let A : E2 → Mat2 := fun x i j => (W.a x i j+W.a x j i)/2
  have hAs (i j : Fin 2) : ContDiffOn ℝ ∞ (fun x => A x i j) O :=
    ((ha i j).add (ha j i)).div_const 2
  have hAeq (x : E2) (hx : x∈closedHalfDisc W.R) : A x=W.a x := by
    ext i j
    dsimp [A]
    rw [hsym x hx j i]
    ring
  let N : Set E2 := ⋃ z : E2, ⋃ (_hz : z∈closedHalfDisc W.R),
    ⋂ i : Fin 2, ⋂ j : Fin 2,
      O ∩ {x : E2 | |A x i j-W.a z i j|<ell/8}
  have hN : IsOpen N := by
    dsimp [N]
    apply isOpen_iUnion
    intro z
    apply isOpen_iUnion
    intro hz
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro j
    exact ((hAs i j).continuousOn.sub continuousOn_const |>.abs).isOpen_inter_preimage hO isOpen_Iio
  have hHN : closedHalfDisc W.R ⊆ N := by
    intro x hx
    simp only [N,mem_iUnion,mem_iInter]
    refine ⟨x,hx,?_⟩
    intro i j
    refine ⟨hWO hx,?_⟩
    change |A x i j-W.a x i j| < ell/8
    rw [hAeq x hx]
    simpa using div_pos hell (by norm_num : (0:ℝ)<8)
  have hAcoer : ∀ x∈N, ∀ p : E2, (ell/2)*‖p‖^2 ≤ inner ℝ p (matrixAction (A x) p) := by
    intro x hx p
    simp only [N,mem_iUnion,mem_iInter] at hx
    obtain ⟨z,hz,hclose⟩ := hx
    have hdiff (i j : Fin 2) :
        |(A x i j-W.a z i j)*p i*p j| ≤ (ell/8)*‖p‖^2 := by
      rw [abs_mul,abs_mul]
      have hp (k : Fin 2) : |p k|≤‖p‖ := by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le p k (p:=2)
      have he := mul_le_mul (hclose i j).2.le (hp i) (abs_nonneg _) (by positivity : (0:ℝ)≤ell/8)
      have hh := mul_le_mul he (hp j) (abs_nonneg _) (by positivity : (0:ℝ)≤ell/8*‖p‖)
      simpa only [pow_two,mul_assoc] using hh
    have hquad : inner ℝ p (matrixAction (A x) p)-inner ℝ p (matrixAction (W.a z) p)=
        ∑ i : Fin 2, ∑ j : Fin 2, (A x i j-W.a z i j)*p i*p j := by
      simp [matrixAction,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_two]
      ring
    have hestimate : |inner ℝ p (matrixAction (A x) p)-inner ℝ p (matrixAction (W.a z) p)| ≤
        ell/2*‖p‖^2 := by
      rw [hquad]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hh : (∑ i : Fin 2, |∑ j : Fin 2, (A x i j-W.a z i j)*p i*p j|) ≤
          ∑ i : Fin 2, ∑ j : Fin 2, (ell/8)*‖p‖^2 :=
        Finset.sum_le_sum (fun i (_ : i∈(Finset.univ:Finset (Fin 2))) =>
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => hdiff i j)))
      convert hh using 1 <;> simp only [Fin.sum_univ_two] <;> ring
    have hlow := (hbounds z hz p).1
    linarith [(abs_le.mp hestimate).1]
  obtain ⟨chi,hchis,hchic,hchione,hchiN,hchiRange⟩ :=
    DifferentialGeometry.Analysis.exists_bump_compact hP hN (hPH.trans hHN)
  let a : E2 → Mat2 := fun x => chi x • A x+(1-chi x) • (1:Mat2)
  let lam := min (ell/2) 1
  have hlam : 0<lam := lt_min (half_pos hell) zero_lt_one
  have has (i j : Fin 2) : ContDiff ℝ ∞ (fun x => a x i j) := by
    change ContDiff ℝ ∞ (fun x => chi x*A x i j+(1-chi x)*(1:Mat2) i j)
    exact (DifferentialGeometry.Analysis.contDiff_cutoff_smul hN hchis hchiN
      ((hAs i j).mono (by
        intro x hx
        simp only [N,mem_iUnion,mem_iInter] at hx
        obtain ⟨z,hz,hh⟩ := hx
        exact (hh 0 0).1))).add ((contDiff_const.sub hchis).mul contDiff_const)
  have hact (x p : E2) : matrixAction (a x) p=chi x • matrixAction (A x) p+(1-chi x) • p := by
    ext i
    simp only [a,matrixAction,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,add_mul,
      Finset.sum_add_distrib,mul_assoc,← Finset.mul_sum,PiLp.add_apply,PiLp.smul_apply]
    simp [Matrix.one_apply]
  let B : SmoothEllipticBilinearForm 2 univ :=
    { a := a
      c := 0
      symm := by
        intro x i j
        change chi x*((W.a x i j+W.a x j i)/2)+(1-chi x)*(1:Mat2) i j =
          chi x*((W.a x j i+W.a x i j)/2)+(1-chi x)*(1:Mat2) j i
        simp only [add_comm (W.a x i j) (W.a x j i),Matrix.one_apply,eq_comm]
      smooth_a := has
      smooth_c := contDiff_const
      lam := lam
      capLam := lam
      ellipticity_pos := hlam
      ellipticity_le_upper := le_rfl
      coercive := by
        intro x _ p
        change lam * ‖p‖^2 ≤ inner ℝ p (matrixAction (a x) p)
        rw [hact,inner_add_right,real_inner_smul_right,real_inner_smul_right,real_inner_self_eq_norm_sq]
        have hchi := hchiRange (mem_range_self x)
        have hlo := mul_le_mul_of_nonneg_right (min_le_left (ell/2) 1) (sq_nonneg ‖p‖)
        have hhi := mul_le_mul_of_nonneg_right (min_le_right (ell/2) 1) (sq_nonneg ‖p‖)
        by_cases hx : x∈N
        · have hc := mul_le_mul_of_nonneg_left (hAcoer x hx p) hchi.1
          have he0 := mul_le_mul_of_nonneg_left hlo hchi.1
          have he1 := mul_le_mul_of_nonneg_left hhi (sub_nonneg.mpr hchi.2)
          dsimp only [lam] at *
          nlinarith
        · have hz : chi x=0 := image_eq_zero_of_notMem_tsupport (fun hh => hx (hchiN hh))
          simpa only [hz,zero_mul,sub_zero,one_mul,zero_add] using hhi }
  refine ⟨B,?_⟩
  intro x hx
  change a x=W.a x
  simp only [a,hchione.self_of_nhdsSet hx,Pi.one_apply,one_smul,sub_self,zero_smul,add_zero]
  exact hAeq x (hPH hx)

end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.actual_closed_halfdisc_smooth_elliptic_extension_v468
