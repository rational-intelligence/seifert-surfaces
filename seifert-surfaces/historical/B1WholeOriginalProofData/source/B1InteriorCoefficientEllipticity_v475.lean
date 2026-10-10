import B1InteriorCoefficientData_v475
import A3MetricVariationBridges
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped Manifold ContDiff BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.A3MetricVariationBridges
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
theorem native_interior_slope_hessian_uniform_bounds_v475 (W : NativeInteriorGraphWindow_v475) :
    (∀ j : Jet, jetPoint j ∈ W.V → ∀ i k : Fin 2,
      fderiv ℝ (fun p : E2 => W.flux (j.1, j.2.1, p) i) j.2.2
          (coordinateVector 2 k) =
        Matrix.det (W.metric.tensor (jetPoint j)) / W.density j *
          (W.gram j)⁻¹ i k) ∧
    (∀ x ∈ W.compactBase, ∀ i j : Fin 2, W.a x i j = W.a x j i) ∧
    (∃ ell C : ℝ, 0 < ell ∧ 0 < C ∧
      ∀ x ∈ W.compactBase, ∀ p : E2,
        ell * ‖p‖ ^ 2 ≤ inner ℝ p (matrixAction (W.a x) p) ∧
        inner ℝ p (matrixAction (W.a x) p) ≤ C * ‖p‖ ^ 2) := by
  classical
  let L : E2 →L[ℝ] E3 :=
    (EuclideanSpace.proj 0).smulRight (coordinateVector 3 0) +
      (EuclideanSpace.proj 1).smulRight (coordinateVector 3 1)
  let n : E3 := coordinateVector 3 2
  have hL (i : Fin 2) : L (coordinateVector 2 i) = coordinateVector 3 (Fin.castSucc i) := by
    fin_cases i <;> ext k <;> fin_cases k <;>
      simp [L, coordinateVector, EuclideanSpace.single]
  have hsplit : Function.Bijective (fun z : E2 × ℝ => L z.1 + z.2 • n) := by
    constructor
    · intro z w h
      have h0 := congrArg (fun y : E3 => y 0) h
      have h1 := congrArg (fun y : E3 => y 1) h
      have h2 := congrArg (fun y : E3 => y 2) h
      simp [L,n,coordinateVector,EuclideanSpace.single] at h0 h1 h2
      apply Prod.ext
      · ext i
        fin_cases i
        · exact h0
        · exact h1
      · exact h2
    · intro y
      refine ⟨((EuclideanSpace.equiv (Fin 2) ℝ).symm ![y 0,y 1],y 2),?_⟩
      ext k
      fin_cases k <;> simp [L,n,coordinateVector,EuclideanSpace.single]
  have hsplitGram (B : Matrix (Fin 3) (Fin 3) ℝ) : splittingGram B L n = B := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [splittingGram,coordinateInner,L,n,coordinateVector,EuclideanSpace.single,
        Fin.sum_univ_three]
  have hmetric (y : E3) (hy : y ∈ W.V) : (W.metric.tensor y).PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · ext a c
      exact W.metric.symmetric y hy c a
    · intro x hx
      let w : E3 := WithLp.toLp 2 x
      have hw : w ≠ 0 := by
        intro he
        apply hx
        exact congrArg WithLp.ofLp he
      have hp := W.metric.positive y hy w hw
      convert hp using 1
      simp only [coordinateInner,dotProduct,Matrix.mulVec,Fin.sum_univ_three,
        Pi.star_apply,star_trivial]
      dsimp [w]
      ring
  have hgram_eq (x : E2) (z : ℝ) (p : E2) :
      slopeGram (W.metric.tensor (jetPoint (x,z,p))) L n p = W.gram (x,z,p) := by
    ext i k
    dsimp [slopeGram,NativeInteriorGraphWindow_v475.gram,jetTangent]
    rw [hL i,hL k]
    rfl
  have harea_eq (x : E2) (z : ℝ) :
      slopeArea (W.metric.tensor (jetPoint (x,z,0))) L n =
        (fun p : E2 => W.density (x,z,p)) := by
    funext p
    exact congrArg (fun A : Mat2 => Real.sqrt (Matrix.det A)) (hgram_eq x z p)
  have hflux_eq (x : E2) (z : ℝ) :
      slopeFlux (W.metric.tensor (jetPoint (x,z,0))) L n =
        (fun p : E2 => W.flux (x,z,p)) := by
    change planarGradient (slopeArea (W.metric.tensor (jetPoint (x,z,0))) L n) =
      (fun p => planarGradient (fun q => W.density (x,z,q)) p)
    rw [harea_eq]
  have hhessian_eq (j : Jet) :
      slopeHessian (W.metric.tensor (jetPoint j)) L n j.2.2 =
        (Matrix.of fun i k => fderiv ℝ (fun p : E2 => W.flux (j.1,j.2.1,p) i)
          j.2.2 (coordinateVector 2 k)) := by
    rcases j with ⟨x,z,p⟩
    ext i k
    dsimp [slopeHessian]
    change fderiv ℝ (fun q : E2 => slopeFlux (W.metric.tensor (jetPoint (x,z,0))) L n q i)
      p (coordinateVector 2 k) = _
    rw [hflux_eq x z]
  have hformula (j : Jet) (hj : jetPoint j ∈ W.V) (i k : Fin 2) :
      fderiv ℝ (fun p : E2 => W.flux (j.1,j.2.1,p) i) j.2.2
        (coordinateVector 2 k) = Matrix.det (W.metric.tensor (jetPoint j)) / W.density j *
          (W.gram j)⁻¹ i k := by
    have h := slope_area_hessian_formula (W.metric.tensor (jetPoint j))
      (hmetric _ hj) L n hsplit j.2.2 i k
    rw [hsplitGram, hhessian_eq] at h
    change _ = Matrix.det (W.metric.tensor (jetPoint j)) / Real.sqrt (Matrix.det (W.gram j)) *
      (W.gram j)⁻¹ i k
    simpa only [slopeArea,hgram_eq,Prod.eta,Matrix.of_apply] using h
  have hsym (j : Jet) (hj : jetPoint j ∈ W.V) (i k : Fin 2) :
      fderiv ℝ (fun p : E2 => W.flux (j.1,j.2.1,p) i) j.2.2
        (coordinateVector 2 k) =
      fderiv ℝ (fun p : E2 => W.flux (j.1,j.2.1,p) k) j.2.2
        (coordinateVector 2 i) := by
    have h := (slope_area_hessian_posDef (W.metric.tensor (jetPoint j))
      (hmetric _ hj) L n hsplit j.2.2).isHermitian.apply k i
    rw [hhessian_eq] at h
    simpa only [star_trivial,Matrix.of_apply] using h
  have hgrampos (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.PosDef) (q : E2) : (slopeGram B L n q).PosDef := by
    let v : Fin 2 → E3 := fun i => L (coordinateVector 2 i) + q i • n
    have hli : LinearIndependent ℝ v := by
      apply Fintype.linearIndependent_iff.mpr
      intro a ha
      have hs : L (∑ i : Fin 2, a i • coordinateVector 2 i) +
          (∑ i : Fin 2, a i * q i) • n = 0 := by
        simpa only [v, smul_add, Finset.sum_add_distrib,
          map_sum, map_smul, mul_smul, Finset.sum_smul] using ha
      have he : ((∑ i : Fin 2, a i • coordinateVector 2 i), ∑ i : Fin 2, a i * q i) =
          ((0 : E2), (0 : ℝ)) := by
        apply hsplit.injective
        simpa only [map_zero, zero_smul, add_zero] using hs
      have hz := congrArg Prod.fst he
      intro i
      have heval := congrArg (fun z : E2 => z i) hz
      fin_cases i <;> simpa [coordinateVector, EuclideanSpace.single, Pi.single_apply] using heval
    let V : Matrix (Fin 3) (Fin 2) ℝ := fun a i => v i a
    have hV : Function.Injective V.mulVec := by
      intro x y hxy
      have hsum : ∑ i, (x i - y i) • v i = 0 := by
        ext a
        have hh := congrFun hxy a
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hh
        simpa only [Fin.sum_univ_two, PiLp.add_apply, PiLp.smul_apply,
          smul_eq_mul, sub_mul, PiLp.zero_apply] using (by
            dsimp [V] at hh
            nlinarith [hh] : (x 0 - y 0) * v 0 a + (x 1 - y 1) * v 1 a = 0)
      have he := Fintype.linearIndependent_iff.mp hli _ hsum
      funext i
      exact sub_eq_zero.mp (he i)
    have heq : slopeGram B L n q = V.conjTranspose * B * V := by
      ext i j
      change (∑ a : Fin 3, ∑ b : Fin 3, B a b * v i a * v j b) =
        ∑ b : Fin 3, (∑ a : Fin 3, v i a * B a b) * v j b
      simp only [Fin.sum_univ_three]
      ring
    rw [heq]
    exact hB.conjTranspose_mul_mul_same hV
  have hinner (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.PosDef)
    (L : E2 →L[ℝ] E3) (n : E3)
    (hsplit : Function.Bijective (fun z : E2 × ℝ => L z.1 + z.2 • n))
    (p ξ : E2) :
    inner ℝ (fderiv ℝ (slopeFlux B L n) p ξ) ξ =
      ∑ i : Fin 2, ∑ j : Fin 2, slopeHessian B L n p i j * ξ i * ξ j := by
    classical
    have hc (i : Fin 2) : DifferentiableAt ℝ (fun q : E2 => slopeFlux B L n q i) p := by
      by_contra hn
      have hp : 0 < slopeHessian B L n p i i :=
        (slope_area_hessian_posDef B hB L n hsplit p).diag_pos
      change 0 < (fderiv ℝ (fun q : E2 => slopeFlux B L n q i) p) (coordinateVector 2 i) at hp
      rw [fderiv_zero_of_not_differentiableAt hn, ContinuousLinearMap.zero_apply] at hp
      exact (lt_irrefl 0) hp
    have hf : DifferentiableAt ℝ (slopeFlux B L n) p :=
      (differentiableAt_piLp 2).mpr hc
    have hi (i : Fin 2) : fderiv ℝ (fun q : E2 => slopeFlux B L n q i) p =
        (EuclideanSpace.proj i).comp (fderiv ℝ (slopeFlux B L n) p) := by
      exact ((EuclideanSpace.proj i).hasFDerivAt.comp p hf.hasFDerivAt).fderiv
    have hx : ξ = ∑ j : Fin 2, ξ j • coordinateVector 2 j := by
      ext i
      fin_cases i <;> simp [coordinateVector, EuclideanSpace.single]
    rw [PiLp.inner_apply, Fin.sum_univ_two]
    simp only [RCLike.inner_apply, conj_trivial]
    have hh (i : Fin 2) : (fderiv ℝ (slopeFlux B L n) p ξ) i =
        ∑ j : Fin 2, ξ j * slopeHessian B L n p i j := by
      change (EuclideanSpace.proj i) (fderiv ℝ (slopeFlux B L n) p ξ) = _
      rw [← ContinuousLinearMap.comp_apply, ← hi]
      conv_lhs => rw [hx]
      simp only [map_sum, map_smul, smul_eq_mul]
      rfl
    rw [hh 0, hh 1]
    simp only [Fin.sum_univ_two]
    ring
  have hclosed : IsCompact W.compactBase := W.compactBase_compact
  have hgradU : ContinuousOn (planarGradient (W.height)) W.U := by
    have hdu : ContinuousOn (fderiv ℝ (W.height)) W.U := by
      intro x hx
      exact (((W.height_smooth x hx).contDiffAt (W.U_open.mem_nhds hx)).fderiv_right
        (m := 0) (by simp)).continuousAt.continuousWithinAt
    unfold planarGradient
    apply continuousOn_finsetSum
    intro i hi
    exact (hdu.clm_apply continuousOn_const).smul continuousOn_const
  let X : Set (E2 × ℝ) := W.compactBase ×ˢ Icc (0 : ℝ) 1
  have hX : IsCompact X := hclosed.prod isCompact_Icc
  let jmap : E2 × ℝ → Jet := fun z => W.segmentJet z.1 z.2
  have hjmap : ContinuousOn jmap X := by
    exact continuousOn_fst.prodMk
      ((continuousOn_snd.mul (W.height_smooth.continuousOn.comp continuousOn_fst
        (fun z hz => W.U_contains hz.1))).prodMk
        (continuousOn_snd.smul (hgradU.comp continuousOn_fst
          (fun z hz => W.U_contains hz.1))))
  have hjV (z : E2 × ℝ) (hz : z ∈ X) : jetPoint (jmap z) ∈ W.V :=
    W.jets_inside z.1 hz.1 z.2 hz.2
  have hjpoint : Continuous jetPoint := by unfold jetPoint; fun_prop
  let B : E2 × ℝ → Matrix (Fin 3) (Fin 3) ℝ := fun z => W.metric.tensor (jetPoint (jmap z))
  have hBcont : ContinuousOn B X := by
    apply continuousOn_pi.mpr; intro i
    apply continuousOn_pi.mpr; intro k
    exact (W.metric.smooth i k).continuousOn.comp
      (hjpoint.continuousOn.comp hjmap (fun z hz => mem_univ _)) hjV
  have hBpositive : ∀ b ∈ B '' X, b.PosDef := by
    rintro b ⟨z,hz,rfl⟩
    exact hmetric _ (hjV z hz)
  let P : Set E2 := (fun z : E2 × ℝ => (jmap z).2.2) '' X
  have hP : IsCompact P := hX.image_of_continuousOn (continuousOn_snd.comp
    (continuousOn_snd.comp hjmap (fun z hz => mem_univ _)) (fun z hz => mem_univ _))
  obtain ⟨d,a₀,l₀,hd,ha₀,hl₀,hdet,hbound⟩ :=
    compact_metric_slope_hessian_lower_bound (B '' X) (hX.image_of_continuousOn hBcont)
      hBpositive P hP L n hsplit
  let ell : ℝ := d / (a₀*l₀)
  have hell : 0 < ell := div_pos hd (mul_pos ha₀ hl₀)
  let A : E2 × ℝ → Mat2 := fun z => slopeGram (B z) L n (jmap z).2.2
  let H : E2 × ℝ → Mat2 := fun z => slopeHessian (B z) L n (jmap z).2.2
  have hApositive (z : E2 × ℝ) (hz : z ∈ X) : (A z).PosDef :=
    hgrampos (B z) (hmetric _ (hjV z hz)) _
  have hAcont : ContinuousOn A X := by
    have hg : Continuous (fun z : Matrix (Fin 3) (Fin 3) ℝ × E2 => slopeGram z.1 L n z.2) := by
      apply continuous_pi; intro i
      apply continuous_pi; intro k
      unfold slopeGram coordinateInner
      simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
      fun_prop
    exact hg.continuousOn.comp (hBcont.prodMk (continuousOn_snd.comp
      (continuousOn_snd.comp hjmap (fun z hz => mem_univ _)) (fun z hz => mem_univ _)))
      (fun z hz => mem_univ _)
  have hinvcont : ContinuousOn (fun z => (A z)⁻¹) X := by
    intro z hz
    apply (continuousAt_matrix_inv (A z) ?_).comp_continuousWithinAt (hAcont z hz)
    have heq : (Ring.inverse : ℝ → ℝ) = Inv.inv := by
      funext r
      exact Ring.inverse_eq_inv r
    rw [heq]
    exact continuousAt_inv₀ (hApositive z hz).det_pos.ne'
  have hcoefcont : ContinuousOn (fun z => Matrix.det (B z) / Real.sqrt (Matrix.det (A z))) X :=
    (continuous_id.matrix_det.continuousOn.comp hBcont (fun z hz => mem_univ _)).div
      (Real.continuous_sqrt.continuousOn.comp
        (continuous_id.matrix_det.continuousOn.comp hAcont (fun z hz => mem_univ _))
      (fun z hz => mem_univ _)) (fun z hz => (Real.sqrt_pos.mpr (hApositive z hz).det_pos).ne')
  have hHcont : ContinuousOn H X := by
    apply (hcoefcont.smul hinvcont).congr
    intro z hz
    ext i k
    exact slope_area_hessian_formula (B z) (hmetric _ (hjV z hz)) L n hsplit
      (jmap z).2.2 i k |>.trans (by rw [hsplitGram]; rfl)
  let sumAbs : E2 × ℝ → ℝ := fun z => ∑ i : Fin 2, ∑ k : Fin 2, |H z i k|
  have hsumcont : ContinuousOn sumAbs X := by
    apply continuousOn_finsetSum
    intro i hi
    apply continuousOn_finsetSum
    intro k hk
    exact ((continuous_apply k).comp_continuousOn
      ((continuous_apply i).comp_continuousOn hHcont)).abs
  obtain ⟨C₀,hC₀⟩ := hX.bddAbove_image hsumcont
  let C : ℝ := max C₀ 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hquad (M : Mat2) (p : E2) :
      inner ℝ p (matrixAction M p) = ∑ i : Fin 2, ∑ k : Fin 2, M i k * p i * p k := by
    change inner ℝ p ((EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i => ∑ k, M i k * p k)) = _
    simp [PiLp.inner_apply,Fin.sum_univ_two,RCLike.inner_apply]
    ring
  have hpointwise (z : E2 × ℝ) (hz : z ∈ X) (p : E2) :
      ell*‖p‖^2 ≤ inner ℝ p (matrixAction (H z) p) ∧
        inner ℝ p (matrixAction (H z) p) ≤ C*‖p‖^2 := by
    constructor
    · have h := ((hbound (B z) (mem_image_of_mem B hz) (jmap z).2.2
        (mem_image_of_mem (fun z : E2 × ℝ => (jmap z).2.2) hz)).2 p).2
      rw [hinner (B z) (hmetric _ (hjV z hz)) L n hsplit, ← hquad] at h
      exact h
    · have hnorm (i : Fin 2) : |p i| ≤ ‖p‖ := by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le p i
      have hterm (i k : Fin 2) : H z i k * p i * p k ≤ |H z i k| * ‖p‖^2 := by
        calc
          _ ≤ |H z i k * p i * p k| := le_abs_self _
          _ = |H z i k| * (|p i| * |p k|) := by rw [abs_mul,abs_mul]; ring
          _ ≤ |H z i k| * (‖p‖*‖p‖) := mul_le_mul_of_nonneg_left
            (mul_le_mul (hnorm i) (hnorm k) (abs_nonneg _) (norm_nonneg _)) (abs_nonneg _)
          _ = _ := by ring
      rw [hquad]
      calc
        _ ≤ ∑ i : Fin 2, ∑ k : Fin 2, |H z i k| * ‖p‖^2 :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => hterm i k
        _ = sumAbs z * ‖p‖^2 := by simp only [sumAbs,Finset.sum_mul]
        _ ≤ C*‖p‖^2 := mul_le_mul_of_nonneg_right
          ((hC₀ (mem_image_of_mem sumAbs hz)).trans (le_max_left _ _)) (sq_nonneg _)
  refine ⟨hformula, ?_, ell,C,hell,hC,?_⟩
  · intro x hx i j
    apply intervalIntegral.integral_congr
    intro t ht
    exact hsym (W.segmentJet x t) (W.jets_inside x hx t (by simpa using ht)) i j
  · intro x hx p
    have htmap : Continuous (fun t : ℝ => (x,t)) := continuous_const.prodMk continuous_id
    have hentrycont (i k : Fin 2) : ContinuousOn (fun t : ℝ => H (x,t) i k) (Icc (0 : ℝ) 1) :=
      ((continuous_apply k).comp_continuousOn ((continuous_apply i).comp_continuousOn hHcont)).comp
        htmap.continuousOn (fun t ht => ⟨hx,ht⟩)
    have hint (i k : Fin 2) : IntervalIntegrable (fun t : ℝ => H (x,t) i k) volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      simpa only [uIcc_of_le zero_le_one] using hentrycont i k
    have hQint : IntervalIntegrable
        (fun t : ℝ => inner ℝ p (matrixAction (H (x,t)) p)) volume 0 1 := by
      simp_rw [hquad]
      exact IntervalIntegrable.sum Finset.univ fun i _ => IntervalIntegrable.sum Finset.univ fun k _ =>
        ((hint i k).mul_const (p i)).mul_const (p k)
    have haeq (i k : Fin 2) : W.a x i k = ∫ t in (0 : ℝ)..1, H (x,t) i k := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact (congrFun (congrFun (hhessian_eq (W.segmentJet x t)) i) k).symm
    have hQeq : inner ℝ p (matrixAction (W.a x) p) =
        ∫ t in (0 : ℝ)..1, inner ℝ p (matrixAction (H (x,t)) p) := by
      simp_rw [hquad,haeq]
      rw [intervalIntegral.integral_finsetSum (s := Finset.univ)
        (f := fun i t => ∑ k : Fin 2, H (x,t) i k * p i * p k)
        (fun i _ => IntervalIntegrable.sum Finset.univ fun k _ =>
          ((hint i k).mul_const (p i)).mul_const (p k))]
      apply Finset.sum_congr rfl
      intro i hi
      rw [intervalIntegral.integral_finsetSum (s := Finset.univ)
        (f := fun k t => H (x,t) i k * p i * p k)
        (fun k _ => ((hint i k).mul_const (p i)).mul_const (p k))]
      simp_rw [intervalIntegral.integral_mul_const]
    rw [hQeq]
    constructor
    · have h := intervalIntegral.integral_mono_on zero_le_one
        (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => ell*‖p‖^2) volume 0 1)
        hQint (fun t ht => (hpointwise (x,t) ⟨hx,ht⟩ p).1)
      simpa only [intervalIntegral.integral_const,sub_zero,one_smul] using h
    · have h := intervalIntegral.integral_mono_on zero_le_one hQint
        (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => C*‖p‖^2) volume 0 1)
        (fun t ht => (hpointwise (x,t) ⟨hx,ht⟩ p).2)
      simpa only [intervalIntegral.integral_const,sub_zero,one_smul] using h

#print axioms native_interior_slope_hessian_uniform_bounds_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
