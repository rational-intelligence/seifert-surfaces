import A3MetricPDE
import A3FirstVariationIdentity

set_option autoImplicit false
noncomputable section
open Set Topology Function
open scoped Manifold ContDiff BigOperators

namespace SeifertSurfaces.OriginalEndpoints.A3MetricVariationBridges
open SeifertSurfaces.OriginalEndpoints
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC

/-- The actual Gram matrix of the two graph jet tangent vectors in a fixed
symmetric positive metric coefficient matrix, with no orthogonal splitting
assumption. -/
def slopeGram (B : Matrix (Fin 3) (Fin 3) ℝ) (L : E2 →L[ℝ] E3)
    (n : E3) (p : E2) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => coordinateInner (fun _ => B) 0
    (L (coordinateVector 2 i) + p i • n)
    (L (coordinateVector 2 j) + p j • n)

/-- The full metric Gram determinant uses the original splitting basis
L(e0), L(e1), n in that order. -/
def splittingGram (B : Matrix (Fin 3) (Fin 3) ℝ) (L : E2 →L[ℝ] E3)
    (n : E3) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => coordinateInner (fun _ => B) 0
    (if i = 0 then L (coordinateVector 2 0)
      else if i = 1 then L (coordinateVector 2 1) else n)
    (if j = 0 then L (coordinateVector 2 0)
      else if j = 1 then L (coordinateVector 2 1) else n)

def slopeArea (B : Matrix (Fin 3) (Fin 3) ℝ) (L : E2 →L[ℝ] E3)
    (n : E3) (p : E2) : ℝ :=
  Real.sqrt (Matrix.det (slopeGram B L n p))

def slopeFlux (B : Matrix (Fin 3) (Fin 3) ℝ) (L : E2 →L[ℝ] E3)
    (n : E3) (p : E2) : E2 :=
  planarGradient (slopeArea B L n) p

/-- Entry i,j differentiates flux component i in slope direction e_j. -/
def slopeHessian (B : Matrix (Fin 3) (Fin 3) ℝ) (L : E2 →L[ℝ] E3)
    (n : E3) (p : E2) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => fderiv ℝ (fun q : E2 => slopeFlux B L n q i) p
    (coordinateVector 2 j)

/-- Exact slope Hessian formula for the metric area integrand. -/
theorem slope_area_hessian_formula
    (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.PosDef)
    (L : E2 →L[ℝ] E3) (n : E3)
    (hsplit : Function.Bijective (fun z : E2 × ℝ => L z.1 + z.2 • n))
    (p : E2) (i j : Fin 2) :
    slopeHessian B L n p i j =
      Matrix.det (splittingGram B L n) / slopeArea B L n p *
        (slopeGram B L n p)⁻¹ i j := by
  classical
  have hgram (q : E2) : (slopeGram B L n q).PosDef := by
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
  let ci : E3 → E3 → ℝ := coordinateInner (fun _ => B) 0
  have hsym (v w : E3) : ci v w = ci w v := by
    dsimp [ci, coordinateInner]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    have hb : B b a = B a b := hB.isHermitian.apply a b
    rw [hb]
    ring
  have hbil (v w : E3) (s t : ℝ) :
      ci (v + s • n) (w + t • n) = ci v w + s * ci n w +
        t * ci v n + s*t*ci n n := by
    simp only [ci, coordinateInner, Fin.sum_univ_three, PiLp.add_apply,
      PiLp.smul_apply, smul_eq_mul]
    ring
  let a := ci (L (coordinateVector 2 0)) (L (coordinateVector 2 0))
  let b := ci (L (coordinateVector 2 0)) (L (coordinateVector 2 1))
  let c := ci (L (coordinateVector 2 1)) (L (coordinateVector 2 1))
  let d := ci (L (coordinateVector 2 0)) n
  let e := ci (L (coordinateVector 2 1)) n
  let f := ci n n
  have g00 (q : E2) : slopeGram B L n q 0 0 = a + 2*d*q 0 + f*(q 0)^2 := by
    change ci _ _ = _
    rw [hbil, hsym n (L (coordinateVector 2 0))]
    dsimp [a, d, f]
    ring
  have g01 (q : E2) : slopeGram B L n q 0 1 = b+e*q 0+d*q 1+f*q 0*q 1 := by
    change ci _ _ = _
    rw [hbil, hsym n (L (coordinateVector 2 1))]
    dsimp [b, d, e, f]
    ring
  have g10 (q : E2) : slopeGram B L n q 1 0 = b+e*q 0+d*q 1+f*q 0*q 1 := by
    change ci _ _ = _
    rw [hsym]
    exact g01 q
  have g11 (q : E2) : slopeGram B L n q 1 1 = c + 2*e*q 1 + f*(q 1)^2 := by
    change ci _ _ = _
    rw [hbil, hsym n (L (coordinateVector 2 1))]
    dsimp [c, e, f]
    ring
  let Q : E2 → ℝ := fun q => Matrix.det (slopeGram B L n q)
  have hQpos (q : E2) : 0 < Q q := (hgram q).det_pos
  have hQdef (q : E2) : Q q = (c*f-e^2)*(q 0)^2 +
      2*(d*e-b*f)*q 0*q 1+(a*f-d^2)*(q 1)^2+
      2*(c*d-b*e)*q 0+2*(a*e-b*d)*q 1+(a*c-b^2) := by
    dsimp [Q]
    rw [Matrix.det_fin_two, g00, g01, g10, g11]
    ring
  have hsplitdet : Matrix.det (splittingGram B L n) =
      a*c*f-a*e^2-b^2*f+2*b*d*e-c*d^2 := by
    rw [Matrix.det_fin_three]
    change a*c*f-a*e*ci n (L (coordinateVector 2 1))-
      b*ci (L (coordinateVector 2 1)) (L (coordinateVector 2 0))*f+
      b*e*ci n (L (coordinateVector 2 0))+
      d*ci (L (coordinateVector 2 1)) (L (coordinateVector 2 0))*ci n (L (coordinateVector 2 1))-
      d*c*ci n (L (coordinateVector 2 0)) = _
    rw [hsym n (L (coordinateVector 2 0)), hsym n (L (coordinateVector 2 1)),
      hsym (L (coordinateVector 2 1)) (L (coordinateVector 2 0))]
    change a*c*f-a*e*e-b*b*f+b*e*d+d*b*e-d*c*d = _
    ring
  have hquad (a b c d e f : ℝ) (Q : E2 → ℝ)
      (hQdef : ∀ x, Q x = a * (x 0)^2 + 2*b*x 0*x 1 + c*(x 1)^2 + 2*d*x 0 + 2*e*x 1+f)
      (hpos : ∀ x, 0 < Q x) (p : E2) (i j : Fin 2) :
      fderiv ℝ (fun q : E2 => planarGradient (fun x => Real.sqrt (Q x)) q i) p
        (coordinateVector 2 j) =
      (if i = j then (if i = 0 then a else c) else b) / Real.sqrt (Q p) -
        (if i = 0 then a*p 0+b*p 1+d else b*p 0+c*p 1+e) *
        (if j = 0 then a*p 0+b*p 1+d else b*p 0+c*p 1+e) / (Real.sqrt (Q p))^3 := by
    let π0 : E2 →L[ℝ] ℝ := EuclideanSpace.proj 0
    let π1 : E2 →L[ℝ] ℝ := EuclideanSpace.proj 1
    let N0 := fun x : E2 => a*x 0+b*x 1+d
    let N1 := fun x : E2 => b*x 0+c*x 1+e
    have hQ (x : E2) : HasFDerivAt Q ((2*N0 x) • π0 + (2*N1 x) • π1) x := by
      have h0 : HasFDerivAt (fun x : E2 => x 0) π0 x := π0.hasFDerivAt
      have h1 : HasFDerivAt (fun x : E2 => x 1) π1 x := π1.hasFDerivAt
      have h := (((((h0.mul h0).const_mul a).add (((h0.const_mul (2*b)).mul h1))).add
        ((h1.mul h1).const_mul c)).add (h0.const_mul (2*d))).add (h1.const_mul (2*e))
      convert h.add_const f using 1
      · funext y
        rw [hQdef]
        simp only [Pi.add_apply, Pi.mul_apply]
        ring
      · ext v
        simp [N0, N1, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.smulRight_apply, smul_eq_mul]
        <;> ring
    have hF (x : E2) := (hQ x).sqrt (ne_of_gt (hpos x))
    have hsqrt (x : E2) : Real.sqrt (Q x) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (hpos x))
    have hgrad (x : E2) (k : Fin 2) :
        planarGradient (fun x => Real.sqrt (Q x)) x k =
          (if k = 0 then N0 x else N1 x) / Real.sqrt (Q x) := by
      unfold planarGradient
      rw [(hF x).fderiv]
      fin_cases k <;>
        simp [Fin.sum_univ_two, coordinateVector, EuclideanSpace.single, π0, π1,
          Pi.single_apply, N0, N1] <;> field_simp (disch := first | exact hsqrt _ | exact ne_of_gt (hpos _) | positivity | norm_num) <;> ring
    have hN0 (x : E2) : HasFDerivAt N0 (a • π0 + b • π1) x := by
      exact ((π0.hasFDerivAt.const_mul a).add (π1.hasFDerivAt.const_mul b)).add_const d
    have hN1 (x : E2) : HasFDerivAt N1 (b • π0 + c • π1) x := by
      exact ((π0.hasFDerivAt.const_mul b).add (π1.hasFDerivAt.const_mul c)).add_const e
    have hi := (hasDerivAt_inv (hsqrt p)).comp_hasFDerivAt p (hF p)
    have h0 := (hN0 p).mul hi
    have h1 := (hN1 p).mul hi
    change HasFDerivAt (fun q : E2 => N0 q * (Real.sqrt (Q q))⁻¹) _ p at h0
    change HasFDerivAt (fun q : E2 => N1 q * (Real.sqrt (Q q))⁻¹) _ p at h1
    have heq : (fun q : E2 => planarGradient (fun x => Real.sqrt (Q x)) q i) =
        (fun q => (if i = 0 then N0 q else N1 q) * (Real.sqrt (Q q))⁻¹) := by
      funext q
      rw [hgrad, div_eq_mul_inv]
    rw [heq]
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceEq, ite_true, ite_false] <;>
      first | rw [h0.fderiv] | rw [h1.fderiv]
    all_goals
      simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
        coordinateVector, π0, π1, EuclideanSpace.single, Pi.single_apply, N0, N1]
      <;> field_simp (disch := first | exact hsqrt _ | exact ne_of_gt (hpos _) | positivity | norm_num) <;> ring
  have h := hquad (c*f-e^2) (d*e-b*f) (a*f-d^2) (c*d-b*e) (a*e-b*d)
    (a*c-b^2) Q hQdef hQpos p i j
  change slopeHessian B L n p i j = _
  change fderiv ℝ (fun q : E2 => planarGradient (fun x => Real.sqrt (Q x)) q i) p
    (coordinateVector 2 j) = _
  rw [h, Matrix.inv_def, Matrix.adjugate_fin_two, hsplitdet]
  have hs : Real.sqrt (Q p) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (hQpos p))
  have hsq : Real.sqrt (Q p)^2 = Q p := Real.sq_sqrt (hQpos p).le
  have hpow : Real.sqrt (Q p)^3 = Real.sqrt (Q p) * Q p := by
    rw [pow_succ, hsq]
    ring
  change _ = (a*c*f-a*e^2-b^2*f+2*b*d*e-c*d^2) / Real.sqrt (Q p) *
    ((Ring.inverse (Q p)) • !![slopeGram B L n p 1 1, -slopeGram B L n p 0 1;
      -slopeGram B L n p 1 0, slopeGram B L n p 0 0]) i j
  rw [Ring.inverse_eq_inv, hpow]
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ite_true, ite_false,
      Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, g00, g01, g10, g11]
  all_goals
    field_simp (disch := first | assumption | exact ne_of_gt (hQpos p) | positivity | norm_num)
    rw [hQdef]
    ring

/-- Positive definiteness holds for every finite slope in the same metric. -/
theorem slope_area_hessian_posDef
    (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.PosDef)
    (L : E2 →L[ℝ] E3) (n : E3)
    (hsplit : Function.Bijective (fun z : E2 × ℝ => L z.1 + z.2 • n))
    (p : E2) :
    (slopeHessian B L n p).PosDef := by
  classical
  have hgram (q : E2) : (slopeGram B L n q).PosDef := by
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
  let v : Fin 3 → E3 := fun i => if i = 0 then L (coordinateVector 2 0)
    else if i = 1 then L (coordinateVector 2 1) else n
  let V : Matrix (Fin 3) (Fin 3) ℝ := fun a i => v i a
  have hV : Function.Injective V.mulVec := by
    intro x y hxy
    have hs : L ((x 0-y 0) • coordinateVector 2 0 + (x 1-y 1) • coordinateVector 2 1) +
        (x 2-y 2) • n = 0 := by
      ext a
      have hh := congrFun hxy a
      simp [Matrix.mulVec, dotProduct, V, v, Fin.sum_univ_three] at hh
      simp only [map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.zero_apply]
      nlinarith [hh]
    have he : (((x 0-y 0) • coordinateVector 2 0 + (x 1-y 1) • coordinateVector 2 1), x 2-y 2) =
        ((0 : E2), (0 : ℝ)) := by
      apply hsplit.injective
      simpa only [map_zero, zero_smul, add_zero] using hs
    have h0 := congrArg (fun z : E2 × ℝ => z.1 0) he
    have h1 := congrArg (fun z : E2 × ℝ => z.1 1) he
    have h2 := congrArg Prod.snd he
    simp [coordinateVector, EuclideanSpace.single, Pi.single_apply] at h0 h1
    funext i
    fin_cases i
    · exact sub_eq_zero.mp h0
    · exact sub_eq_zero.mp h1
    · exact sub_eq_zero.mp h2
  have heq : splittingGram B L n = V.conjTranspose * B * V := by
    ext i j
    change (∑ a : Fin 3, ∑ b : Fin 3, B a b * v i a * v j b) =
      ∑ b : Fin 3, (∑ a : Fin 3, v i a * B a b) * v j b
    simp only [Fin.sum_univ_three]
    ring
  have hf : (splittingGram B L n).PosDef := by
    rw [heq]
    exact hB.conjTranspose_mul_mul_same hV
  have ha : 0 < slopeArea B L n p := Real.sqrt_pos.mpr (hgram p).det_pos
  have hh : slopeHessian B L n p =
      (Matrix.det (splittingGram B L n) / slopeArea B L n p) • (slopeGram B L n p)⁻¹ := by
    ext i j
    exact slope_area_hessian_formula B hB L n hsplit p i j
  rw [hh]
  exact (hgram p).inv.smul (div_pos hf.det_pos ha)

/-- One strictly positive coercivity constant works simultaneously for a
compact positive metric family and a compact slope set. -/
theorem compact_metric_slope_hessian_lower_bound
    (K : Set (Matrix (Fin 3) (Fin 3) ℝ)) (hK : IsCompact K)
    (hpositive : ∀ B ∈ K, B.PosDef)
    (P : Set E2) (hP : IsCompact P)
    (L : E2 →L[ℝ] E3) (n : E3)
    (hsplit : Function.Bijective (fun z : E2 × ℝ => L z.1 + z.2 • n)) :
    ∃ d a ℓ : ℝ, 0 < d ∧ 0 < a ∧ 0 < ℓ ∧
      (∀ B ∈ K, d ≤ Matrix.det (splittingGram B L n)) ∧
      (∀ B ∈ K, ∀ p ∈ P, slopeArea B L n p ≤ a ∧
        ∀ ξ : E2,
          (∑ i : Fin 2, ∑ j : Fin 2,
            slopeGram B L n p i j * ξ i * ξ j) ≤ ℓ * ‖ξ‖ ^ 2 ∧
          d / (a * ℓ) * ‖ξ‖ ^ 2 ≤
            inner ℝ (fderiv ℝ (slopeFlux B L n) p ξ) ξ) := by
  classical
  have hgeom (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.PosDef) :
      (splittingGram B L n).PosDef ∧ ∀ p, (slopeGram B L n p).PosDef := by
    have hgram (q : E2) : (slopeGram B L n q).PosDef := by
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
    let v : Fin 3 → E3 := fun i => if i = 0 then L (coordinateVector 2 0)
      else if i = 1 then L (coordinateVector 2 1) else n
    let V : Matrix (Fin 3) (Fin 3) ℝ := fun a i => v i a
    have hV : Function.Injective V.mulVec := by
      intro x y hxy
      have hs : L ((x 0-y 0) • coordinateVector 2 0 + (x 1-y 1) • coordinateVector 2 1) +
          (x 2-y 2) • n = 0 := by
        ext a
        have hh := congrFun hxy a
        simp [Matrix.mulVec, dotProduct, V, v, Fin.sum_univ_three] at hh
        simp only [map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.zero_apply]
        nlinarith [hh]
      have he : (((x 0-y 0) • coordinateVector 2 0 + (x 1-y 1) • coordinateVector 2 1), x 2-y 2) =
          ((0 : E2), (0 : ℝ)) := by
        apply hsplit.injective
        simpa only [map_zero, zero_smul, add_zero] using hs
      have h0 := congrArg (fun z : E2 × ℝ => z.1 0) he
      have h1 := congrArg (fun z : E2 × ℝ => z.1 1) he
      have h2 := congrArg Prod.snd he
      simp [coordinateVector, EuclideanSpace.single, Pi.single_apply] at h0 h1
      funext i
      fin_cases i
      · exact sub_eq_zero.mp h0
      · exact sub_eq_zero.mp h1
      · exact sub_eq_zero.mp h2
    have heq : splittingGram B L n = V.conjTranspose * B * V := by
      ext i j
      change (∑ a : Fin 3, ∑ b : Fin 3, B a b * v i a * v j b) =
        ∑ b : Fin 3, (∑ a : Fin 3, v i a * B a b) * v j b
      simp only [Fin.sum_univ_three]
      ring
    have hf : (splittingGram B L n).PosDef := by
      rw [heq]
      exact hB.conjTranspose_mul_mul_same hV
    exact ⟨hf, hgram⟩
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
  have hinv (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : A.PosDef)
    (ℓ : ℝ) (hℓ : 0 < ℓ)
    (hbound : ∀ ξ : E2, (∑ i : Fin 2, ∑ j : Fin 2, A i j * ξ i * ξ j) ≤ ℓ * ‖ξ‖^2)
    (ξ : E2) : ‖ξ‖^2 / ℓ ≤ ∑ i : Fin 2, ∑ j : Fin 2, A⁻¹ i j * ξ i * ξ j := by
    classical
    have hn : ‖ξ‖^2 = ξ 0 * ξ 0 + ξ 1 * ξ 1 := by
      rw [← real_inner_self_eq_norm_sq ξ, PiLp.inner_apply]
      simp [Fin.sum_univ_two, RCLike.inner_apply, pow_two]
    have hq (M : Matrix (Fin 2) (Fin 2) ℝ) :
        (∑ i : Fin 2, ∑ j : Fin 2, M i j * ξ i * ξ j) =
          dotProduct (star (WithLp.ofLp ξ)) (Matrix.mulVec M (WithLp.ofLp ξ)) := by
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
      ring
    have hc := hA.star_dotProduct_mulVec_mul_le (WithLp.ofLp ξ) (Matrix.mulVec A⁻¹ (WithLp.ofLp ξ))
    have he : Matrix.mulVec A (Matrix.mulVec A⁻¹ (WithLp.ofLp ξ)) = WithLp.ofLp ξ := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA.det_pos.ne'), Matrix.one_mulVec]
    rw [he] at hc
    have hs : dotProduct (star (Matrix.mulVec A⁻¹ (WithLp.ofLp ξ))) (WithLp.ofLp ξ) =
        dotProduct (star (WithLp.ofLp ξ)) (Matrix.mulVec A⁻¹ (WithLp.ofLp ξ)) := by
      simp only [star_trivial]
      exact dotProduct_comm _ _
    rw [hs, ← hq A, ← hq A⁻¹] at hc
    have hd : dotProduct (star (WithLp.ofLp ξ)) (WithLp.ofLp ξ) = ‖ξ‖^2 := by
      simp only [dotProduct, Fin.sum_univ_two, Pi.star_apply, star_trivial, hn]
    rw [hd, star_trivial] at hc
    have hp : 0 ≤ ∑ i : Fin 2, ∑ j : Fin 2, A⁻¹ i j * ξ i * ξ j := by
      rw [hq]
      exact hA.inv.posSemidef.dotProduct_mulVec_nonneg _
    have hc' := hc.trans (mul_le_mul_of_nonneg_right (hbound ξ) hp)
    by_cases hx : ξ = 0
    · simp [hx]
    · have hnorm : 0 < ‖ξ‖^2 := pow_pos (norm_pos_iff.mpr hx) _
      apply (div_le_iff₀ hℓ).mpr
      nlinarith
  have hbounds :
      ∃ d a ℓ : ℝ, 0 < d ∧ 0 < a ∧ 0 < ℓ ∧
        (∀ B ∈ K, d ≤ Matrix.det (splittingGram B L n)) ∧
        (∀ B ∈ K, ∀ p ∈ P, slopeArea B L n p ≤ a ∧
          ∀ ξ : E2, (∑ i : Fin 2, ∑ j : Fin 2,
            slopeGram B L n p i j * ξ i * ξ j) ≤ ℓ * ‖ξ‖ ^ 2)
      := by
    have hdcont : Continuous (fun B => Matrix.det (splittingGram B L n)) := by
      apply Continuous.matrix_det
      apply continuous_pi; intro i
      apply continuous_pi; intro j
      change Continuous (fun B : Matrix (Fin 3) (Fin 3) ℝ => ∑ a : Fin 3, ∑ b : Fin 3, B a b *
        (if i = 0 then L (coordinateVector 2 0) else if i = 1 then L (coordinateVector 2 1) else n) a *
        (if j = 0 then L (coordinateVector 2 0) else if j = 1 then L (coordinateVector 2 1) else n) b)
      fun_prop
    obtain ⟨d, hd, hdb⟩ := hK.exists_forall_le' hdcont.continuousOn
      (fun B hB => (hgeom B (hpositive B hB)).1.det_pos)
    have hacont : Continuous (fun z : Matrix (Fin 3) (Fin 3) ℝ × E2 => slopeArea z.1 L n z.2) := by
      apply Real.continuous_sqrt.comp
      apply Continuous.matrix_det
      apply continuous_pi; intro i
      apply continuous_pi; intro j
      unfold slopeGram coordinateInner
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      fun_prop
    obtain ⟨a₀, ha₀⟩ := (hK.prod hP).bddAbove_image hacont.continuousOn
    let c := fun z : Matrix (Fin 3) (Fin 3) ℝ × E2 =>
      ∑ i : Fin 2, ∑ j : Fin 2, |slopeGram z.1 L n z.2 i j|
    have hccont : Continuous c := by
      unfold c slopeGram coordinateInner
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      fun_prop
    obtain ⟨ℓ₀, hℓ₀⟩ := (hK.prod hP).bddAbove_image hccont.continuousOn
    refine ⟨d, max a₀ 1, max ℓ₀ 1, hd, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
      lt_of_lt_of_le zero_lt_one (le_max_right _ _), hdb, ?_⟩
    intro B hB p hp
    refine ⟨(ha₀ ⟨(B,p), ⟨hB,hp⟩, rfl⟩).trans (le_max_left _ _), ?_⟩
    intro ξ
    have hnorm (i : Fin 2) : |ξ i| ≤ ‖ξ‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le ξ i
    have hterm (i j : Fin 2) : slopeGram B L n p i j * ξ i * ξ j ≤
        |slopeGram B L n p i j| * ‖ξ‖^2 := by
      calc
        _ ≤ |slopeGram B L n p i j * ξ i * ξ j| := le_abs_self _
        _ = |slopeGram B L n p i j| * (|ξ i| * |ξ j|) := by rw [abs_mul,abs_mul];ring
        _ ≤ |slopeGram B L n p i j| * (‖ξ‖ * ‖ξ‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul (hnorm i) (hnorm j) (abs_nonneg _) (norm_nonneg _)) (abs_nonneg _)
        _ = _ := by ring
    calc
      _ ≤ ∑ i : Fin 2, ∑ j : Fin 2, |slopeGram B L n p i j| * ‖ξ‖^2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
      _ = c (B,p) * ‖ξ‖^2 := by simp only [c,Finset.sum_mul]
      _ ≤ max ℓ₀ 1 * ‖ξ‖^2 := mul_le_mul_of_nonneg_right
        ((hℓ₀ ⟨(B,p), ⟨hB,hp⟩, rfl⟩).trans (le_max_left _ _)) (sq_nonneg _)
  obtain ⟨d,a,ℓ,hd,ha,hℓ,hdet,hbounds⟩ := hbounds
  refine ⟨d,a,ℓ,hd,ha,hℓ,hdet,?_⟩
  intro B hB p hp
  refine ⟨(hbounds B hB p hp).1, ?_⟩
  intro ξ
  refine ⟨(hbounds B hB p hp).2 ξ, ?_⟩
  have hA := hgeom B (hpositive B hB)
  have harea : 0 < slopeArea B L n p := Real.sqrt_pos.mpr (hA.2 p).det_pos
  have hratio : d/a ≤ (Matrix.det (splittingGram B L n))/slopeArea B L n p := by
    apply (div_le_div_iff₀ ha harea).mpr
    exact (mul_le_mul_of_nonneg_left (hbounds B hB p hp).1 hd.le).trans
      (mul_le_mul_of_nonneg_right (hdet B hB) ha.le)
  rw [hinner B (hpositive B hB) L n hsplit p ξ]
  have hsum : (∑ i : Fin 2, ∑ j : Fin 2, slopeHessian B L n p i j * ξ i * ξ j) =
      (Matrix.det (splittingGram B L n)/slopeArea B L n p) *
        (∑ i : Fin 2, ∑ j : Fin 2, (slopeGram B L n p)⁻¹ i j * ξ i * ξ j) := by
    simp_rw [slope_area_hessian_formula B (hpositive B hB) L n hsplit p]
    simp only [Fin.sum_univ_two]
    ring
  rw [hsum]
  calc
    d/(a*ℓ)*‖ξ‖^2 = (d/a)*(‖ξ‖^2/ℓ) := by ring
    _ ≤ (Matrix.det (splittingGram B L n)/slopeArea B L n p)*(‖ξ‖^2/ℓ) :=
      mul_le_mul_of_nonneg_right hratio (div_nonneg (sq_nonneg _) hℓ.le)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (hinv (slopeGram B L n p) (hA.2 p) ℓ hℓ (hbounds B hB p hp).2 ξ)
      (div_nonneg hA.1.det_pos.le harea.le)

universe u v
variable {N : Type u} [TopologicalSpace N] [ChartedSpace E3 N]
  [IsManifold 𝓘(ℝ, E3) ∞ N]
variable {h : AmbientMetric N} {M : Set N} {D : A3OriginalData.{u,v} h M}

/-- Compact actual jet control yields uniform ellipticity of the literal
actual-metric flux, before constructing OperatorControl. -/
theorem actual_metric_flux_uniformly_elliptic_on_compact
    (G : A3SharedGraph D) (K : Set Jet) (hK : IsCompact K)
    (hchart : MapsTo G.jetPoint K G.coordinates.chart.target) :
    UniformlyEllipticOn K G.metricFlux := by
  classical
  have hmetric :
      (∀ i j, ContDiffOn ℝ ∞ (fun y => actualChartTensor h G.coordinates y i j)
        G.coordinates.chart.target) ∧
      (∀ y ∈ G.coordinates.chart.target, ∀ i j,
        actualChartTensor h G.coordinates y i j = actualChartTensor h G.coordinates y j i) ∧
      (∀ y ∈ G.coordinates.chart.target, ∀ w : E3, w ≠ 0 →
        0 < coordinateInner (actualChartTensor h G.coordinates) y w w) := by
    let c := G.coordinates
    refine ⟨?_, ?_, ?_⟩
    · intro i j
      letI : Bundle.RiemannianBundle (fun p : N => TangentSpace 𝓘(ℝ, E3) p) :=
        ⟨h.toRiemannianMetric⟩
      have hv (k : Fin 3) : ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, E3).tangent ∞
          (fun y => (⟨c.chart.symm y, inverseChartDifferential c y (coordinateVector 3 k)⟩ :
            TangentBundle 𝓘(ℝ, E3) N)) c.chart.target := by
        have hs : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, E3).tangent ∞
            (fun y => (⟨y, (NormedSpace.fromTangentSpace y).symm (coordinateVector 3 k)⟩ :
              TangentBundle 𝓘(ℝ, E3) E3)) :=
          contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
        have ht := c.inverse_smooth.contMDiffOn_tangentMapWithin
          (m := ∞) (by simp) c.chart.open_target.uniqueMDiffOn
        have hc := ht.comp hs.contMDiffOn (by intro y hy; exact hy)
        apply hc.congr
        intro y hy
        change (⟨c.chart.symm y, (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) c.chart.symm y)
          ((NormedSpace.fromTangentSpace y).symm (coordinateVector 3 k))⟩ : TangentBundle 𝓘(ℝ, E3) N) =
            ⟨c.chart.symm y, (mfderivWithin 𝓘(ℝ, E3) 𝓘(ℝ, E3) c.chart.symm c.chart.target y)
              ((NormedSpace.fromTangentSpace y).symm (coordinateVector 3 k))⟩
        rw [mfderivWithin_eq_mfderiv (c.chart.open_target.uniqueMDiffOn y hy)
          (((c.inverse_smooth y hy).mdifferentiableWithinAt (by simp)).mdifferentiableAt
            (c.chart.open_target.mem_nhds hy))]
      exact (open scoped Bundle in (hv i |>.inner_bundle (hv j)).contDiffOn)
    · intro y hy i j
      exact h.symm _ _ _
    · intro y hy w hw
      have he : c.chart.MDifferentiable 𝓘(ℝ, E3) 𝓘(ℝ, E3) :=
        ⟨c.smooth.mdifferentiableOn (by simp), c.inverse_smooth.mdifferentiableOn (by simp)⟩
      have hinj : Function.Injective (inverseChartDifferential c y) :=
        (he.symm.mfderiv_injective hy).comp (NormedSpace.fromTangentSpace y).symm.injective
      have hn : inverseChartDifferential c y w ≠ 0 := by
        intro hh
        apply hw
        apply hinj
        simpa only [map_zero] using hh
      have hid (v w : E3) : coordinateInner (actualChartTensor h c) y v w =
          h.inner (c.chart.symm y) (inverseChartDifferential c y v)
            (inverseChartDifferential c y w) := by
        have hsum (v : E3) : (∑ i : Fin 3, v i • coordinateVector 3 i) = v := by
          ext j
          simp [coordinateVector, EuclideanSpace.single, Pi.single_apply]
        have hdiff (v : E3) : inverseChartDifferential c y v =
            ∑ i : Fin 3, v i • inverseChartDifferential c y (coordinateVector 3 i) := by
          simpa only [map_sum, map_smul] using congrArg (inverseChartDifferential c y) (hsum v).symm
        unfold coordinateInner actualChartTensor
        rw [hdiff v, hdiff w, map_sum]
        simp only [map_smul, _root_.sum_apply, _root_.smul_apply, map_sum, smul_eq_mul]
        simp only [Finset.mul_sum]
        conv_rhs => rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        ring
      rw [hid]
      exact h.pos _ _ hn
  let B := fun j : Jet => actualChartTensor h G.coordinates (G.jetPoint j)
  have hjcont : Continuous G.jetPoint := by
    unfold A3SharedGraph.jetPoint
    fun_prop
  have hBcont : ContinuousOn B K := by
    apply continuousOn_pi.mpr; intro i
    apply continuousOn_pi.mpr; intro j
    exact ((hmetric.1 i j).continuousOn).comp hjcont.continuousOn hchart
  have hBpos : ∀ b ∈ B '' K, b.PosDef := by
    rintro b ⟨j,hj,rfl⟩
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · ext a c
      exact (hmetric.2.1 (G.jetPoint j) (hchart hj) c a)
    · intro x hx
      let w : E3 := WithLp.toLp 2 x
      have hw : w ≠ 0 := by
        intro he
        apply hx
        exact congrArg WithLp.ofLp he
      have hp := hmetric.2.2 (G.jetPoint j) (hchart hj) w hw
      convert hp using 1
      simp only [coordinateInner, dotProduct, Matrix.mulVec, Fin.sum_univ_three,
        Pi.star_apply, star_trivial]
      dsimp [B,w]
      ring
  have hP : IsCompact ((fun j : Jet => j.2.2) '' K) :=
    hK.image (continuous_snd.comp continuous_snd)
  obtain ⟨d,a,ℓ,hd,ha,hℓ,hdet,hbound⟩ :=
    compact_metric_slope_hessian_lower_bound (B '' K) (hK.image_of_continuousOn hBcont)
      hBpos ((fun j : Jet => j.2.2) '' K) hP G.plane G.normal G.splitting
  refine ⟨d/(a*ℓ), div_pos hd (mul_pos ha hℓ), ?_⟩
  intro x z p ξ hj
  have hh := (hbound (B (x,z,p)) (mem_image_of_mem B hj) p
    (mem_image_of_mem (fun j : Jet => j.2.2) hj)).2 ξ |>.2
  convert hh using 1
  rfl

/-- Forward geometric bridge on an actual open graph domain. Tangency of the
same covariant trace implies div(d_p F)-d_z F=0 for the literal metric area
integrand; no ellipticity/control or classical-equation certificate is assumed. -/
theorem actual_graph_covariant_trace_implies_area_residual
    (G : A3SharedGraph D) (Ω : Set E2) (hΩ : IsOpen Ω)
    (hΩdisc : Ω ⊆ G.disc)
    (hsmooth : ContDiffOn ℝ ∞ G.height Ω)
    (htrace : ∀ x ∈ Ω,
      tracedAcceleration (actualChartTensor h G.coordinates)
        (graphMap (G.coordinates.chart (D.edge D.pointParameter))
          G.plane G.normal G.height) x ∈
      LinearMap.range
        (fderiv ℝ (graphMap (G.coordinates.chart (D.edge D.pointParameter))
          G.plane G.normal G.height) x).toLinearMap) :
    ∀ x ∈ Ω, G.classicalResidual x = 0 := by
  classical
  have hmetric :
      (∀ i j, ContDiffOn ℝ ∞ (fun y => actualChartTensor h G.coordinates y i j)
        G.coordinates.chart.target) ∧
      (∀ y ∈ G.coordinates.chart.target, ∀ i j,
        actualChartTensor h G.coordinates y i j = actualChartTensor h G.coordinates y j i) ∧
      (∀ y ∈ G.coordinates.chart.target, ∀ w : E3, w ≠ 0 →
        0 < coordinateInner (actualChartTensor h G.coordinates) y w w) := by
    let c := G.coordinates
    refine ⟨?_, ?_, ?_⟩
    · intro i j
      letI : Bundle.RiemannianBundle (fun p : N => TangentSpace 𝓘(ℝ, E3) p) :=
        ⟨h.toRiemannianMetric⟩
      have hv (k : Fin 3) : ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, E3).tangent ∞
          (fun y => (⟨c.chart.symm y, inverseChartDifferential c y (coordinateVector 3 k)⟩ :
            TangentBundle 𝓘(ℝ, E3) N)) c.chart.target := by
        have hs : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, E3).tangent ∞
            (fun y => (⟨y, (NormedSpace.fromTangentSpace y).symm (coordinateVector 3 k)⟩ :
              TangentBundle 𝓘(ℝ, E3) E3)) :=
          contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
        have ht := c.inverse_smooth.contMDiffOn_tangentMapWithin
          (m := ∞) (by simp) c.chart.open_target.uniqueMDiffOn
        have hc := ht.comp hs.contMDiffOn (by intro y hy; exact hy)
        apply hc.congr
        intro y hy
        change (⟨c.chart.symm y, (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) c.chart.symm y)
          ((NormedSpace.fromTangentSpace y).symm (coordinateVector 3 k))⟩ : TangentBundle 𝓘(ℝ, E3) N) =
            ⟨c.chart.symm y, (mfderivWithin 𝓘(ℝ, E3) 𝓘(ℝ, E3) c.chart.symm c.chart.target y)
              ((NormedSpace.fromTangentSpace y).symm (coordinateVector 3 k))⟩
        rw [mfderivWithin_eq_mfderiv (c.chart.open_target.uniqueMDiffOn y hy)
          (((c.inverse_smooth y hy).mdifferentiableWithinAt (by simp)).mdifferentiableAt
            (c.chart.open_target.mem_nhds hy))]
      exact (open scoped Bundle in (hv i |>.inner_bundle (hv j)).contDiffOn)
    · intro y hy i j
      exact h.symm _ _ _
    · intro y hy w hw
      have he : c.chart.MDifferentiable 𝓘(ℝ, E3) 𝓘(ℝ, E3) :=
        ⟨c.smooth.mdifferentiableOn (by simp), c.inverse_smooth.mdifferentiableOn (by simp)⟩
      have hinj : Function.Injective (inverseChartDifferential c y) :=
        (he.symm.mfderiv_injective hy).comp (NormedSpace.fromTangentSpace y).symm.injective
      have hn : inverseChartDifferential c y w ≠ 0 := by
        intro hh
        apply hw
        apply hinj
        simpa only [map_zero] using hh
      have hid (v w : E3) : coordinateInner (actualChartTensor h c) y v w =
          h.inner (c.chart.symm y) (inverseChartDifferential c y v)
            (inverseChartDifferential c y w) := by
        have hsum (v : E3) : (∑ i : Fin 3, v i • coordinateVector 3 i) = v := by
          ext j
          simp [coordinateVector, EuclideanSpace.single, Pi.single_apply]
        have hdiff (v : E3) : inverseChartDifferential c y v =
            ∑ i : Fin 3, v i • inverseChartDifferential c y (coordinateVector 3 i) := by
          simpa only [map_sum, map_smul] using congrArg (inverseChartDifferential c y) (hsum v).symm
        unfold coordinateInner actualChartTensor
        rw [hdiff v, hdiff w, map_sum]
        simp only [map_smul, _root_.sum_apply, _root_.smul_apply, map_sum, smul_eq_mul]
        simp only [Finset.mul_sum]
        conv_rhs => rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        ring
      rw [hid]
      exact h.pos _ _ hn
  have hann (B : Matrix (Fin 3) (Fin 3) ℝ) (T : E2 →L[ℝ] E3)
    (n : E3) (v : E2)
    (hG : Matrix.PosDef (fun i j : Fin 2 => coordinateInner (fun _ => B) 0
      (T (coordinateVector 2 i)) (T (coordinateVector 2 j)))) :
    coordinateInner (fun _ => B) 0 (T v) n -
      ∑ i : Fin 2, ∑ j : Fin 2,
        (@Inv.inv (Matrix (Fin 2) (Fin 2) ℝ) Matrix.inv (fun i j : Fin 2 => coordinateInner (fun _ => B) 0
          (T (coordinateVector 2 i)) (T (coordinateVector 2 j)))) i j *
        coordinateInner (fun _ => B) 0 (T v) (T (coordinateVector 2 i)) *
        coordinateInner (fun _ => B) 0 (T (coordinateVector 2 j)) n = 0 := by
    classical
    let A : Matrix (Fin 2) (Fin 2) ℝ := fun i j => coordinateInner (fun _ => B) 0
      (T (coordinateVector 2 i)) (T (coordinateVector 2 j))
    have hv : v = v 0 • coordinateVector 2 0 + v 1 • coordinateVector 2 1 := by
      ext i
      fin_cases i <;> simp [coordinateVector,EuclideanSpace.single]
    have hlin (w : E3) : coordinateInner (fun _ => B) 0 (T v) w =
        ∑ k : Fin 2, v k * coordinateInner (fun _ => B) 0 (T (coordinateVector 2 k)) w := by
      conv_lhs => rw [hv,map_add,map_smul,map_smul]
      simp only [coordinateInner,Fin.sum_univ_two,Fin.sum_univ_three,PiLp.add_apply,
        PiLp.smul_apply,smul_eq_mul]
      ring
    rw [hlin]
    simp_rw [hlin]
    change (∑ k : Fin 2, v k * coordinateInner (fun _ => B) 0 (T (coordinateVector 2 k)) n) -
      (∑ i : Fin 2, ∑ j : Fin 2, A⁻¹ i j * (∑ k : Fin 2, v k * A k i) *
        coordinateInner (fun _ => B) 0 (T (coordinateVector 2 j)) n) = 0
    have heq : (∑ i : Fin 2, ∑ j : Fin 2, A⁻¹ i j * (∑ k : Fin 2, v k * A k i) *
        coordinateInner (fun _ => B) 0 (T (coordinateVector 2 j)) n) =
        ∑ k : Fin 2, ∑ j : Fin 2, v k * (A*A⁻¹) k j *
          coordinateInner (fun _ => B) 0 (T (coordinateVector 2 j)) n := by
      simp only [Matrix.mul_apply,Fin.sum_univ_two]
      ring
    rw [heq, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hG.det_pos.ne')]
    simp
  let g := actualChartTensor h G.coordinates
  let Φ := graphMap (G.coordinates.chart (D.edge D.pointParameter)) G.plane G.normal G.height
  have hvariation (x : E2) (hx : x ∈ Ω) :
      G.classicalResidual x = G.areaDensity (G.attainedJet x) *
        (coordinateInner g (Φ x) (tracedAcceleration g Φ x) G.normal -
          ∑ i : Fin 2, ∑ j : Fin 2, (inducedMetric g Φ x)⁻¹ i j *
            coordinateInner g (Φ x) (tracedAcceleration g Φ x) (graphTangent Φ x i) *
            coordinateInner g (Φ x) (graphTangent Φ x j) G.normal) := by
    exact A3FirstVariation.actual_graph_first_variation_identity G Ω hΩ hΩdisc hsmooth x hx
  intro x hx
  have hu : DifferentiableAt ℝ G.height x :=
    ((hsmooth x hx).contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)
  have hΦ : HasFDerivAt Φ (G.plane + (fderiv ℝ G.height x).smulRight G.normal) x := by
    exact (G.plane.hasFDerivAt.const_add _).add (hu.hasFDerivAt.smul_const G.normal)
  have hpg (i : Fin 2) : planarGradient G.height x i =
      fderiv ℝ G.height x (coordinateVector 2 i) := by
    unfold planarGradient
    fin_cases i <;> simp [coordinateVector,EuclideanSpace.single]
  have ht (i : Fin 2) : graphTangent Φ x i =
      G.plane (coordinateVector 2 i) + planarGradient G.height x i • G.normal := by
    rw [graphTangent,hΦ.fderiv,hpg]
    rfl
  have hchartx : Φ x ∈ G.coordinates.chart.target := by
    apply G.graph_in_chart
    have hxdisc := hΩdisc hx
    change dist x 0 < G.radius at hxdisc
    change dist x 0 ≤ 2*G.radius
    linarith [G.radius_pos]
  have hB : (g (Φ x)).PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · ext i j
      exact hmetric.2.1 (Φ x) hchartx j i
    · intro w hw
      have hp := hmetric.2.2 (Φ x) hchartx (WithLp.toLp 2 w) (by
        intro he;apply hw;exact congrArg WithLp.ofLp he)
      convert hp using 1
      simp only [coordinateInner,dotProduct,Matrix.mulVec,Fin.sum_univ_three,
        Pi.star_apply,star_trivial]
      dsimp [g]
      ring
  have hgram : (inducedMetric g Φ x).PosDef := by
    let B := g (Φ x)
    let L := G.plane
    let n := G.normal
    have hsplit := G.splitting
    have hgram (q : E2) : (slopeGram B L n q).PosDef := by
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
    have heq : inducedMetric g Φ x = slopeGram B L n (planarGradient G.height x) := by
      ext i j
      rw [inducedMetric, ht i, ht j]
      rfl
    rw [heq]
    exact hgram _
  obtain ⟨v,hv⟩ := htrace x hx
  rw [hvariation x hx]
  have hh := hann (g (Φ x)) (fderiv ℝ Φ x) G.normal v hgram
  change (fderiv ℝ Φ x) v = tracedAcceleration g Φ x at hv
  rw [← hv]
  change G.areaDensity (G.attainedJet x) * _ = 0
  exact mul_eq_zero_of_right _ hh


end SeifertSurfaces.OriginalEndpoints.A3MetricVariationBridges
