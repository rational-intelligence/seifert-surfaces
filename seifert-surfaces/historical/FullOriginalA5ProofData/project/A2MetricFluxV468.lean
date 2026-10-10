import A2NativeNormalProjection
import CurvedGaussGreenHelpers

noncomputable section
open Set Topology MeasureTheory Function
open scoped BigOperators ContDiff
namespace SeifertSurfaces.OriginalEndpoints.A2MetricFlux
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.A2NativeNormalProjection
open SeifertSurfaces.OriginalEndpoints.CurvedDivergence
open SeifertSurfaces.OriginalEndpoints.CurvedDivergence.GaussGreen

/-- The coordinate Levi-Civita connection of the actual supplied tensor. -/
def metricConnection (g : MetricTensor) (y v w : E3) : E3 :=
  ∑ k : Fin 3, (∑ a : Fin 3, ∑ b : Fin 3,
    christoffel g y a b k * v a * w b) • coordinateVector 3 k

def covariantFieldDerivative (g : MetricTensor) (W : E3 → E3)
    (y v : E3) : E3 :=
  fderiv ℝ W y v + metricConnection g y v (W y)

def metricGram (g : MetricTensor) (y : E3) (L : E2 →L[ℝ] E3) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  fun a b => coordinateInner g y (L (coordinateVector 2 a)) (L (coordinateVector 2 b))

def metricDensity (g : MetricTensor) (y : E3) (L : E2 →L[ℝ] E3) : ℝ :=
  Real.sqrt (metricGram g y L).det

def metricTangentialDivergence (g : MetricTensor) (W : E3 → E3)
    (y : E3) (L : E2 →L[ℝ] E3) : ℝ :=
  ∑ a : Fin 2, ∑ b : Fin 2, (metricGram g y L)⁻¹ a b *
    coordinateInner g y (covariantFieldDerivative g W y (L (coordinateVector 2 a)))
      (L (coordinateVector 2 b))

/-- Density-weighted contravariant tangential flux, using this same Gram matrix. -/
def metricFlux (g : MetricTensor) (W : E3 → E3)
    (y : E3) (L : E2 →L[ℝ] E3) : E2 :=
  WithLp.toLp 2 (fun a : Fin 2 => metricDensity g y L *
    ∑ b : Fin 2, (metricGram g y L)⁻¹ a b *
      coordinateInner g y (W y) (L (coordinateVector 2 b)))

/-- Reuse the paid metric projection of the actual traced acceleration. -/
def normalTrace (g : MetricTensor) (f : E2 → E3) (x : E2) : E3 :=
  normalProjection g (f x) (fderiv ℝ f x) (tracedAcceleration g f x)

private theorem inner_symmetric (g : MetricTensor) (y : E3)
    (hs : ∀ a b, g y a b = g y b a) (v w : E3) :
    coordinateInner g y v w = coordinateInner g y w v := by
  simp only [coordinateInner, Fin.sum_univ_three, hs]
  ring
private theorem basis_sum (v : E2) : (∑ i : Fin 2, v i • coordinateVector 2 i) = v := by
  ext i
  fin_cases i <;> simp [coordinateVector, EuclideanSpace.single]
private theorem gram_positive (g : MetricTensor) (y : E3) (L : E2 →L[ℝ] E3)
    (hs : ∀ a b, g y a b = g y b a)
    (hp : ∀ v : E3, v ≠ 0 → 0 < coordinateInner g y v v)
    (hL : Function.Injective L) : (metricGram g y L).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · apply Matrix.IsHermitian.ext
    intro i j
    simpa only [Matrix.conjTranspose_apply, star_trivial, metricGram] using
      inner_symmetric g y hs (L (coordinateVector 2 j)) (L (coordinateVector 2 i))
  · intro ξ hξ
    let w : E2 := WithLp.toLp 2 ξ
    have hw : w ≠ 0 := fun he => hξ (WithLp.toLp_injective 2 he)
    have hLw : L w ≠ 0 := fun hz => hw (hL (hz.trans L.map_zero.symm))
    have hpos := hp (L w) hLw
    have hsum : L w = ∑ i : Fin 2, ξ i • L (coordinateVector 2 i) := by
      rw [← basis_sum w, map_sum]
      simp only [map_smul]
      rfl
    rw [hsum] at hpos
    convert! hpos using 1
    simp only [dotProduct, Matrix.mulVec, star_trivial, metricGram, coordinateInner,
      Fin.sum_univ_two, Fin.sum_univ_three, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul]
    ring

private theorem inner_continuousOn {X : Type*} [TopologicalSpace X]
    (S : Set X) (g : MetricTensor) (F V W : X → E3)
    (hF : ContinuousOn F S) (hV : ContinuousOn V S) (hW : ContinuousOn W S)
    (hg : ∀ a b, ContinuousOn (fun x => g (F x) a b) S) :
    ContinuousOn (fun x => coordinateInner g (F x) (V x) (W x)) S := by
  apply continuousOn_finsetSum
  intro a ha
  apply continuousOn_finsetSum
  intro b hb
  exact ((hg a b).mul ((EuclideanSpace.proj a).continuous.comp_continuousOn hV)).mul
    ((EuclideanSpace.proj b).continuous.comp_continuousOn hW)
private theorem flux_continuousOn {X : Type*} [TopologicalSpace X]
    (S : Set X) (g : MetricTensor) (F : X → E3) (L : X → E2 →L[ℝ] E3)
    (W : E3 → E3) (hF : ContinuousOn F S) (hL : ContinuousOn L S)
    (hW : ContinuousOn (fun x => W (F x)) S)
    (hg : ∀ a b, ContinuousOn (fun x => g (F x) a b) S)
    (hp : ∀ x ∈ S, (metricGram g (F x) (L x)).PosDef) :
    ContinuousOn (fun x => metricFlux g W (F x) (L x)) S := by
  have hv (i : Fin 2) : ContinuousOn (fun x => L x (coordinateVector 2 i)) S :=
    hL.clm_apply continuousOn_const
  have hq (i j : Fin 2) : ContinuousOn (fun x => metricGram g (F x) (L x) i j) S :=
    inner_continuousOn S g F _ _ hF (hv i) (hv j) hg
  have hdet : ContinuousOn (fun x => (metricGram g (F x) (L x)).det) S := by
    simp only [Matrix.det_fin_two]
    exact ((hq 0 0).mul (hq 1 1)).sub ((hq 0 1).mul (hq 1 0))
  have hinv (i j : Fin 2) : ContinuousOn (fun x => (metricGram g (F x) (L x))⁻¹ i j) S := by
    have hi : ContinuousOn (fun x => ((metricGram g (F x) (L x)).det)⁻¹) S :=
      hdet.inv₀ (fun x hx => (hp x hx).det_pos.ne')
    simp only [Matrix.inv_def, Matrix.adjugate_fin_two, Ring.inverse_eq_inv,
      Matrix.smul_apply, smul_eq_mul]
    fin_cases i <;> fin_cases j <;> dsimp <;> fun_prop
  have hb (j : Fin 2) : ContinuousOn (fun x => coordinateInner g (F x) (W (F x))
      (L x (coordinateVector 2 j))) S :=
    inner_continuousOn S g F _ _ hF hW (hv j) hg
  have hd : ContinuousOn (fun x => metricDensity g (F x) (L x)) S := hdet.sqrt
  unfold metricFlux
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.continuous.comp_continuousOn
  apply continuousOn_pi.mpr
  intro i
  exact hd.mul (continuousOn_finsetSum _ (fun j _ => (hinv i j).mul (hb j)))
private theorem inner_differentiableAt (g : MetricTensor) (F V W : E2 → E3) (x : E2)
    (hV : DifferentiableAt ℝ V x) (hW : DifferentiableAt ℝ W x)
    (hg : ∀ a b, DifferentiableAt ℝ (fun x => g (F x) a b) x) :
    DifferentiableAt ℝ (fun x => coordinateInner g (F x) (V x) (W x)) x := by
  apply DifferentiableAt.fun_sum
  intro a ha
  apply DifferentiableAt.fun_sum
  intro b hb
  exact ((hg a b).mul ((EuclideanSpace.proj a).differentiableAt.comp x hV)).mul
    ((EuclideanSpace.proj b).differentiableAt.comp x hW)
private theorem flux_differentiableAt (g : MetricTensor) (F : E2 → E3)
    (L : E2 → E2 →L[ℝ] E3) (W : E3 → E3) (x : E2)
    (hL : DifferentiableAt ℝ L x) (hW : DifferentiableAt ℝ (fun x => W (F x)) x)
    (hg : ∀ a b, DifferentiableAt ℝ (fun x => g (F x) a b) x)
    (hp : (metricGram g (F x) (L x)).PosDef) :
    DifferentiableAt ℝ (fun x => metricFlux g W (F x) (L x)) x := by
  have hv (i : Fin 2) : DifferentiableAt ℝ (fun x => L x (coordinateVector 2 i)) x :=
    hL.clm_apply (differentiableAt_const _)
  have hq (i j : Fin 2) : DifferentiableAt ℝ (fun x => metricGram g (F x) (L x) i j) x :=
    inner_differentiableAt g F _ _ x (hv i) (hv j) hg
  have hdet : DifferentiableAt ℝ (fun x => (metricGram g (F x) (L x)).det) x := by
    simp only [Matrix.det_fin_two]
    exact ((hq 0 0).mul (hq 1 1)).sub ((hq 0 1).mul (hq 1 0))
  have hinv (i j : Fin 2) : DifferentiableAt ℝ (fun x => (metricGram g (F x) (L x))⁻¹ i j) x := by
    have hi : DifferentiableAt ℝ (fun x => ((metricGram g (F x) (L x)).det)⁻¹) x :=
      hdet.inv hp.det_pos.ne'
    simp only [Matrix.inv_def, Matrix.adjugate_fin_two, Ring.inverse_eq_inv,
      Matrix.smul_apply, smul_eq_mul]
    fin_cases i <;> fin_cases j <;> dsimp <;> fun_prop
  have hb (j : Fin 2) : DifferentiableAt ℝ (fun x => coordinateInner g (F x) (W (F x))
      (L x (coordinateVector 2 j))) x :=
    inner_differentiableAt g F _ _ x hW (hv j) hg
  have hd : DifferentiableAt ℝ (fun x => metricDensity g (F x) (L x)) x :=
    hdet.sqrt hp.det_pos.ne'
  unfold metricFlux
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.differentiableAt.comp x
  apply differentiableAt_pi.mpr
  intro i
  exact hd.mul (DifferentiableAt.fun_sum (fun j _ => (hinv i j).mul (hb j)))
private theorem matrix_inverse_hasDerivAt
    (A : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (B : Matrix (Fin 2) (Fin 2) ℝ)
    (hu : IsUnit (A 0).det) (hB : ∀ i j, HasDerivAt (fun t => A t i j) (B i j) 0) :
    ∀ i j, HasDerivAt (fun t => (A t)⁻¹ i j)
      (-(∑ a : Fin 2, ∑ b : Fin 2, (A 0)⁻¹ i a * B a b * (A 0)⁻¹ b j)) 0 := by
  have hdet : HasDerivAt (fun t => (A t).det)
      (B 0 0 * A 0 1 1 + A 0 0 0 * B 1 1 -
        (B 0 1 * A 0 1 0 + A 0 0 1 * B 1 0)) 0 := by
    convert! ((hB 0 0).mul (hB 1 1)).sub ((hB 0 1).mul (hB 1 0)) using 1
    ext t
    exact Matrix.det_fin_two (A t)
  have hAdj (i j : Fin 2) : HasDerivAt (fun t => (A t).adjugate i j) (B.adjugate i j) 0 := by
    fin_cases i <;> fin_cases j <;> simp only [Matrix.adjugate_fin_two] <;> dsimp
    · exact hB 1 1
    · exact (hB 0 1).neg
    · exact (hB 1 0).neg
    · exact hB 0 0
  intro i j
  have hd := (hdet.inv (isUnit_iff_ne_zero.mp hu)).mul (hAdj i j)
  convert! hd using 1
  · simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
    rfl
  · simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.adjugate_fin_two,
      Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> dsimp
    all_goals field_simp [isUnit_iff_ne_zero.mp hu]
    all_goals simp only [Matrix.det_fin_two]
    all_goals ring
private theorem gram_density_hasDerivAt
    (A : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (B : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : (A 0).PosDef) (hB : ∀ i j, HasDerivAt (fun t => A t i j) (B i j) 0) :
    HasDerivAt (fun t => Real.sqrt (A t).det)
      ((1 / 2 : ℝ) * Real.sqrt (A 0).det *
        (∑ i : Fin 2, ∑ j : Fin 2, (A 0)⁻¹ i j * B j i)) 0 := by
  have hdet : HasDerivAt (fun t => (A t).det)
      (B 0 0 * A 0 1 1 + A 0 0 0 * B 1 1 -
        (B 0 1 * A 0 1 0 + A 0 0 1 * B 1 0)) 0 := by
    convert! ((hB 0 0).mul (hB 1 1)).sub ((hB 0 1).mul (hB 1 0)) using 1
    ext t
    exact Matrix.det_fin_two (A t)
  have hs := hdet.sqrt (ne_of_gt hA.det_pos)
  convert hs using 1
  have hroot : 0 < Real.sqrt (A 0).det := Real.sqrt_pos.2 hA.det_pos
  have hsq : Real.sqrt (A 0).det ^ 2 = (A 0).det := Real.sq_sqrt hA.det_pos.le
  rw [Matrix.inv_def, Matrix.adjugate_fin_two]
  simp only [Ring.inverse_eq_inv, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.head_fin_const]
  field_simp [ne_of_gt hroot, ne_of_gt hA.det_pos]
  rw [hsq]
  ring
private theorem flux_curve_hasDerivAt
    (A : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (B : Matrix (Fin 2) (Fin 2) ℝ)
    (P : ℝ → Fin 2 → ℝ) (D : Fin 2 → ℝ)
    (hA : (A 0).PosDef) (hB : ∀ i j, HasDerivAt (fun t => A t i j) (B i j) 0)
    (hP : ∀ i, HasDerivAt (fun t => P t i) (D i) 0) (i : Fin 2) :
    HasDerivAt (fun t => Real.sqrt (A t).det * ∑ j : Fin 2, (A t)⁻¹ i j * P t j)
      (Real.sqrt (A 0).det *
        ((1 / 2 : ℝ) * (∑ a : Fin 2, ∑ b : Fin 2, (A 0)⁻¹ a b * B b a) *
          (∑ j : Fin 2, (A 0)⁻¹ i j * P 0 j) +
          (∑ j : Fin 2, ((-(∑ a : Fin 2, ∑ b : Fin 2,
            (A 0)⁻¹ i a * B a b * (A 0)⁻¹ b j)) * P 0 j + (A 0)⁻¹ i j * D j)))) 0 := by
  have hi := matrix_inverse_hasDerivAt A B (isUnit_iff_ne_zero.mpr hA.det_pos.ne') hB
  have hp := HasDerivAt.sum (u := Finset.univ) (fun j _ => (hi i j).mul (hP j))
  convert (gram_density_hasDerivAt A B hA hB).mul hp using 1
  · rfl
  · simp only [Finset.sum_apply, Pi.mul_apply, Fin.sum_univ_two]
    ring
private theorem flux_trace_algebra
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (T : Fin 2 → Fin 2 → Fin 2 → ℝ)
    (P : Fin 2 → ℝ) (R S : Fin 2 → Fin 2 → ℝ)
    (hQ : ∀ i j, Q i j = Q j i) (hT : ∀ i j k, T i j k = T j i k) :
    (∑ i : Fin 2,
      ((1 / 2 : ℝ) * (∑ a : Fin 2, ∑ b : Fin 2, Q a b * (T i b a + T i a b)) *
        (∑ j : Fin 2, Q i j * P j) +
      (∑ j : Fin 2, ((-(∑ a : Fin 2, ∑ b : Fin 2,
        Q i a * (T i a b + T i b a) * Q b j)) * P j + Q i j * (R i j + S i j))))) =
      (∑ i : Fin 2, ∑ j : Fin 2, Q i j * R i j) +
      (∑ i : Fin 2, ∑ j : Fin 2, Q i j * S i j) -
      (∑ a : Fin 2, ∑ b : Fin 2, Q a b * (∑ i : Fin 2, ∑ j : Fin 2,
        Q i j * T i j a) * P b) := by
  simp only [Fin.sum_univ_two, hQ 1 0, hT 1 0]
  ring
private theorem lowered_christoffel_formula (g : MetricTensor) (y : E3) (hg : IsUnit (g y).det)
    (hsym : ∀ a b, g y a b = g y b a)
    (hdsym : ∀ a b, fderiv ℝ (fun z => g z a b) y = fderiv ℝ (fun z => g z b a) y) (u v w : E3) :
    coordinateInner g y
      (∑ k : Fin 3, (∑ a : Fin 3, ∑ b : Fin 3,
        christoffel g y a b k * u a * v b) • coordinateVector 3 k) w =
      (1 / 2 : ℝ) *
        ((∑ a : Fin 3, ∑ b : Fin 3,fderiv ℝ (fun z => g z a b) y u * v a * w b) +
         (∑ a : Fin 3, ∑ b : Fin 3,fderiv ℝ (fun z => g z a b) y v * u a * w b) -
         (∑ a : Fin 3, ∑ b : Fin 3,fderiv ℝ (fun z => g z a b) y w * u a * v b)) := by
  classical
  have hLower (g : MetricTensor) (y : E3) (hg : IsUnit (g y).det)
      (hsym : ∀ a b, g y a b = g y b a) (u v w : E3) :
      coordinateInner g y
        (∑ k : Fin 3, (∑ a : Fin 3, ∑ b : Fin 3,
          christoffel g y a b k * u a * v b) • coordinateVector 3 k) w =
        (1 / 2 : ℝ) * (∑ a : Fin 3, ∑ b : Fin 3, ∑ l : Fin 3,
          (partial3 (fun z => g z l b) y a + partial3 (fun z => g z l a) y b -
            partial3 (fun z => g z a b) y l) * u a * v b * w l) := by
    classical
    have hlower (a b l : Fin 3) :
        (∑ k : Fin 3, g y l k * christoffel g y a b k) =
          (1 / 2 : ℝ) * (partial3 (fun z => g z l b) y a +
            partial3 (fun z => g z l a) y b - partial3 (fun z => g z a b) y l) := by
      let R : Fin 3 → ℝ := fun m => partial3 (fun z => g z m b) y a +
        partial3 (fun z => g z m a) y b - partial3 (fun z => g z a b) y m
      change (∑ k : Fin 3, g y l k * ((1 / 2 : ℝ) * ∑ m : Fin 3, (g y)⁻¹ k m * R m)) =
        (1 / 2 : ℝ) * R l
      calc
        _ = (1 / 2 : ℝ) * ∑ m : Fin 3, (g y * (g y)⁻¹) l m * R m := by
          simp only [Matrix.mul_apply,Fin.sum_univ_three]
          ring
        _ = _ := by
          rw [Matrix.mul_nonsing_inv _ hg]
          change (1 / 2 : ℝ) * (∑ m : Fin 3, (if l = m then 1 else 0) * R m) = _
          simp
    have hcoord (s : Fin 3 → ℝ) (k : Fin 3) :
        (∑ i : Fin 3,s i • coordinateVector 3 i) k = s k := by
      simp [coordinateVector,EuclideanSpace.single,Pi.single_apply]
    simp only [coordinateInner,hcoord]
    calc
      _ = ∑ a : Fin 3, ∑ b : Fin 3, ∑ l : Fin 3,
          (∑ k : Fin 3,g y l k * christoffel g y a b k) * u a * v b * w l := by
        simp only [Fin.sum_univ_three,hsym]
        ring
      _ = _ := by
        simp only [hlower,Fin.sum_univ_three]
        ring
  rw [hLower g y hg hsym]
  have hsum (v : E3) : (∑ i : Fin 3,v i • coordinateVector 3 i) = v := by
    ext j
    simp [coordinateVector,EuclideanSpace.single,Pi.single_apply]
  have hexpand (F : E3 → ℝ) (d : E3) : fderiv ℝ F y d =
      ∑ i : Fin 3,partial3 F y i * d i := by
    conv_lhs => rw [← hsum d]
    simp only [map_sum,map_smul,smul_eq_mul,partial3]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hdpartial (a i j : Fin 3) : partial3 (fun z => g z i j) y a =
      partial3 (fun z => g z j i) y a := by
    unfold partial3
    rw [hdsym i j]
  simp only [hexpand,Fin.sum_univ_three,hdpartial]
  ring
private theorem coordinate_inner_curve_derivative (g : MetricTensor)
    (Z V W : ℝ → E3) (x v w : E3)
    (hg : ∀ a b, DifferentiableAt ℝ (fun z => g z a b) (Z 0))
    (hZ : HasDerivAt Z x 0) (hV : HasDerivAt V v 0) (hW : HasDerivAt W w 0) :
    HasDerivAt (fun t => coordinateInner g (Z t) (V t) (W t))
      ((∑ a : Fin 3, ∑ b : Fin 3,
          fderiv ℝ (fun z => g z a b) (Z 0) x * V 0 a * W 0 b) +
        coordinateInner g (Z 0) v (W 0) + coordinateInner g (Z 0) (V 0) w) 0 := by
  have he (a b : Fin 3) : HasDerivAt (fun t => g (Z t) a b * V t a * W t b)
      ((fderiv ℝ (fun z => g z a b) (Z 0) x * V 0 a + g (Z 0) a b * v a) * W 0 b +
        (g (Z 0) a b * V 0 a) * w b) 0 := by
    have hga := (hg a b).hasFDerivAt.comp_hasDerivAt 0 hZ
    have hVa := (EuclideanSpace.proj a).hasFDerivAt.comp_hasDerivAt 0 hV
    have hWb := (EuclideanSpace.proj b).hasFDerivAt.comp_hasDerivAt 0 hW
    exact (hga.mul hVa).mul hWb
  convert! HasDerivAt.sum (u := Finset.univ) (fun a _ => HasDerivAt.sum (u := Finset.univ) (fun b _ => he a b)) using 1
  simp only [coordinateInner, Fin.sum_univ_three]
  ring

private theorem metric_connection_compatibility (g : MetricTensor) (y : E3)
    (hg : IsUnit (g y).det) (hsym : ∀ a b, g y a b = g y b a)
    (hdsym : ∀ a b, fderiv ℝ (fun z => g z a b) y = fderiv ℝ (fun z => g z b a) y)
    (u v w : E3) :
    coordinateInner g y (metricConnection g y u v) w +
      coordinateInner g y v (metricConnection g y u w) =
      ∑ a : Fin 3, ∑ b : Fin 3, fderiv ℝ (fun z => g z a b) y u * v a * w b := by
  rw [inner_symmetric g y hsym v (metricConnection g y u w)]
  unfold metricConnection
  rw [lowered_christoffel_formula g y hg hsym hdsym,
    lowered_christoffel_formula g y hg hsym hdsym]
  have hmdsym (d a b : E3) :
      (∑ i : Fin 3, ∑ j : Fin 3, fderiv ℝ (fun z => g z i j) y d * a i * b j) =
      ∑ i : Fin 3, ∑ j : Fin 3, fderiv ℝ (fun z => g z i j) y d * b i * a j := by
    simp only [Fin.sum_univ_three, hdsym]
    ring
  rw [hmdsym u w v, hmdsym v u w, hmdsym w u v]
  ring
private theorem covariant_inner_curve_hasDerivAt (g : MetricTensor)
    (Z V W : ℝ → E3) (x v w : E3)
    (hg : ∀ a b, DifferentiableAt ℝ (fun z => g z a b) (Z 0))
    (hu : IsUnit (g (Z 0)).det) (hs : ∀ a b, g (Z 0) a b = g (Z 0) b a)
    (hds : ∀ a b, fderiv ℝ (fun z => g z a b) (Z 0) = fderiv ℝ (fun z => g z b a) (Z 0))
    (hZ : HasDerivAt Z x 0) (hV : HasDerivAt V v 0) (hW : HasDerivAt W w 0) :
    HasDerivAt (fun t => coordinateInner g (Z t) (V t) (W t))
      (coordinateInner g (Z 0) (v + metricConnection g (Z 0) x (V 0)) (W 0) +
        coordinateInner g (Z 0) (V 0) (w + metricConnection g (Z 0) x (W 0))) 0 := by
  convert coordinate_inner_curve_derivative g Z V W x v w hg hZ hV hW using 1
  rw [coordinateInner_add_left]
  have hadd : coordinateInner g (Z 0) (V 0) (w + metricConnection g (Z 0) x (W 0)) =
      coordinateInner g (Z 0) (V 0) w +
      coordinateInner g (Z 0) (V 0) (metricConnection g (Z 0) x (W 0)) := by
    simp only [coordinateInner, PiLp.add_apply, mul_add, Finset.sum_add_distrib]
  rw [hadd]
  linarith [metric_connection_compatibility g (Z 0) hu hs hds x (V 0) (W 0)]
private theorem connection_symmetric (g : MetricTensor) (y : E3)
    (hds : ∀ a b, fderiv ℝ (fun z => g z a b) y = fderiv ℝ (fun z => g z b a) y)
    (u v : E3) : metricConnection g y u v = metricConnection g y v u := by
  have hΓ (a b k : Fin 3) : christoffel g y a b k = christoffel g y b a k := by
    unfold christoffel partial3
    rw [hds a b]
    apply congrArg ((1 / 2 : ℝ) * ·)
    apply Finset.sum_congr rfl
    intro l hl
    ring
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  calc
    _ = ∑ a : Fin 3, ∑ b : Fin 3, christoffel g y b a k * u a * v b := by
      simp only [hΓ]
    _ = _ := by simp only [Fin.sum_univ_three]; ring
/-- Whole fixed-chart density/divergence/normal-trace identity (L6.1).
No metric-compatibility identity, trace equation, stationarity or minimality
is assumed. Native moving-chart and canonical-row transport are owner work. -/
theorem fixed_chart_metric_divergence
    (U : Set E2) (V : Set E3) (hU : IsOpen U) (hV : IsOpen V)
    (g : CoordinateMetric V) (f : E2 → E3) (W : E3 → E3)
    (hf : ContDiffOn ℝ ∞ f U) (himage : MapsTo f U V)
    (hrank : ∀ x ∈ U, Function.Injective (fderiv ℝ f x))
    (hW : ContDiffOn ℝ 1 W V) :
    ∀ x ∈ U,
      (metricGram g.tensor (f x) (fderiv ℝ f x)).PosDef ∧
      0 < metricDensity g.tensor (f x) (fderiv ℝ f x) ∧
      (∀ v : E2, coordinateInner g.tensor (f x) (normalTrace g.tensor f x)
        (fderiv ℝ f x v) = 0) ∧
      metricDensity g.tensor (f x) (fderiv ℝ f x) *
          metricTangentialDivergence g.tensor W (f x) (fderiv ℝ f x) =
        planarDivergence (fun z => metricFlux g.tensor W (f z) (fderiv ℝ f z)) x -
          metricDensity g.tensor (f x) (fderiv ℝ f x) *
            coordinateInner g.tensor (f x) (normalTrace g.tensor f x) (W (f x)) := by
  intro x hx
  let y := f x
  let L := fderiv ℝ f x
  let e : Fin 2 → E3 := fun i => L (coordinateVector 2 i)
  let Q := metricGram g.tensor y L
  let A : Fin 2 → Fin 2 → E3 := fun i j => covariantAcceleration g.tensor f x i j
  let T : Fin 2 → Fin 2 → Fin 2 → ℝ := fun i j k => coordinateInner g.tensor y (A i j) (e k)
  let P : Fin 2 → ℝ := fun j => coordinateInner g.tensor y (W y) (e j)
  let R : Fin 2 → Fin 2 → ℝ := fun i j => coordinateInner g.tensor y
    (covariantFieldDerivative g.tensor W y (e i)) (e j)
  let S : Fin 2 → Fin 2 → ℝ := fun i j => coordinateInner g.tensor y (W y) (A i j)
  have hy : y ∈ V := himage hx
  have hsym := g.symmetric y hy
  have hpos := gram_positive g.tensor y L hsym (g.positive y hy) (hrank x hx)
  have hg (a b : Fin 3) : DifferentiableAt ℝ (fun z => g.tensor z a b) y :=
    ((g.smooth a b).contDiffAt (hV.mem_nhds hy)).differentiableAt (by simp)
  have hds (a b : Fin 3) : fderiv ℝ (fun z => g.tensor z a b) y =
      fderiv ℝ (fun z => g.tensor z b a) y := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [hV.mem_nhds hy] with z hz
    exact g.symmetric z hz a b
  have hgp : (g.tensor y).PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · apply Matrix.IsHermitian.ext
      intro i j
      simpa only [Matrix.conjTranspose_apply, star_trivial] using hsym j i
    · intro ξ hξ
      have hh := g.positive y hy (WithLp.toLp 2 ξ)
        (fun hz => hξ (WithLp.toLp_injective 2 hz))
      convert hh using 1
      simp only [dotProduct, Matrix.mulVec, star_trivial, coordinateInner, Fin.sum_univ_three]
      ring
  have hu : IsUnit (g.tensor y).det := isUnit_iff_ne_zero.mpr hgp.det_pos.ne'
  have hfd : DifferentiableAt ℝ f x :=
    (hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hLd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_of_isOpen hU (m := 1) (by simp)).contDiffAt (hU.mem_nhds hx)).differentiableAt one_ne_zero
  have hWd : DifferentiableAt ℝ W y :=
    (hW.contDiffAt (hV.mem_nhds hy)).differentiableAt one_ne_zero
  have hEd (j : Fin 2) : HasFDerivAt (fun z => graphTangent f z j)
      ((fderiv ℝ (fderiv ℝ f) x).flip (coordinateVector 2 j)) x := by
    convert hLd.hasFDerivAt.clm_apply (hasFDerivAt_const (coordinateVector 2 j) x) using 1 <;>
      simp [graphTangent]
  have hsecond (i j : Fin 2) : fderiv ℝ (fun z => graphTangent f z j) x (coordinateVector 2 i) =
      fderiv ℝ (fderiv ℝ f) x (coordinateVector 2 i) (coordinateVector 2 j) := by
    rw [(hEd j).fderiv]
    rfl
  have hA (i j : Fin 2) : A i j = A j i := by
    dsimp only [A, covariantAcceleration]
    rw [hsecond, hsecond,
      ((hf.contDiffAt (hU.mem_nhds hx)).isSymmSndFDerivAt (by simp)).eq]
    congr 1
    exact connection_symmetric g.tensor y hds (e i) (e j)
  have hT (i j k : Fin 2) : T i j k = T j i k := by dsimp only [T]; rw [hA]
  have hQ (i j : Fin 2) : Q⁻¹ i j = Q⁻¹ j i := by
    simpa only [star_trivial] using hpos.inv.isHermitian.apply j i
  have hfluxd : DifferentiableAt ℝ (fun z => metricFlux g.tensor W (f z) (fderiv ℝ f z)) x :=
    flux_differentiableAt g.tensor f (fderiv ℝ f) W x hLd (hWd.comp x hfd)
      (fun a b => (hg a b).comp x hfd) hpos
  have hdir (i : Fin 2) : fderiv ℝ
      (fun z => (metricFlux g.tensor W (f z) (fderiv ℝ f z)) i) x (coordinateVector 2 i) =
      metricDensity g.tensor y L *
        ((1 / 2 : ℝ) * (∑ a : Fin 2, ∑ b : Fin 2, Q⁻¹ a b * (T i b a + T i a b)) *
          (∑ j : Fin 2, Q⁻¹ i j * P j) +
          (∑ j : Fin 2, ((-(∑ a : Fin 2, ∑ b : Fin 2,
            Q⁻¹ i a * (T i a b + T i b a) * Q⁻¹ b j)) * P j + Q⁻¹ i j * (R i j + S i j)))) := by
    let c : ℝ → E2 := fun t => x + t • coordinateVector 2 i
    have hc : HasDerivAt c (coordinateVector 2 i) 0 := by
      simpa only [c, id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const (coordinateVector 2 i)).const_add x
    have hc0 : c 0 = x := by simp [c]
    have hF : HasDerivAt (fun t => f (c t)) (e i) 0 := by
      simpa only [hc0, e, L, Function.comp_def] using
        (show HasFDerivAt f (fderiv ℝ f x) (c 0) from by simpa only [hc0] using hfd.hasFDerivAt).comp_hasDerivAt 0 hc
    have hE (j : Fin 2) : HasDerivAt (fun t => graphTangent f (c t) j)
        (fderiv ℝ (fun z => graphTangent f z j) x (coordinateVector 2 i)) 0 := by
      simpa only [hc0, Function.comp_def] using
        (show HasFDerivAt (fun z => graphTangent f z j)
          (fderiv ℝ (fun z => graphTangent f z j) x) (c 0) from by
            simpa only [hc0] using (hEd j).differentiableAt.hasFDerivAt).comp_hasDerivAt 0 hc
    have hWc : HasDerivAt (fun t => W (f (c t))) (fderiv ℝ W y (e i)) 0 := by
      simpa only [hc0, y, Function.comp_def] using
        (show HasFDerivAt W (fderiv ℝ W y) (f (c 0)) from by
          simpa only [hc0, y] using hWd.hasFDerivAt).comp_hasDerivAt 0 hF
    have hG (a b : Fin 2) : HasDerivAt
        (fun t => metricGram g.tensor (f (c t)) (fderiv ℝ f (c t)) a b)
        (T i a b + T i b a) 0 := by
      have hd := covariant_inner_curve_hasDerivAt g.tensor
        (fun t => f (c t)) (fun t => graphTangent f (c t) a)
        (fun t => graphTangent f (c t) b) (e i) _ _
        (by simpa only [hc0, y] using hg) (by simpa only [hc0, y] using hu)
        (by simpa only [hc0, y] using hsym) (by simpa only [hc0, y] using hds) hF (hE a) (hE b)
      simpa only [metricGram, graphTangent, hc0, covariantAcceleration, A, T,
        e, L, y, metricConnection, inner_symmetric g.tensor y hsym] using hd
    have hP (j : Fin 2) : HasDerivAt
        (fun t => coordinateInner g.tensor (f (c t)) (W (f (c t))) (graphTangent f (c t) j))
        (R i j + S i j) 0 := by
      have hd := covariant_inner_curve_hasDerivAt g.tensor (fun t => f (c t))
        (fun t => W (f (c t))) (fun t => graphTangent f (c t) j) (e i) _ _
        (by simpa only [hc0, y] using hg) (by simpa only [hc0, y] using hu)
        (by simpa only [hc0, y] using hsym) (by simpa only [hc0, y] using hds) hF hWc (hE j)
      simpa only [hc0, covariantFieldDerivative, covariantAcceleration, A, R, S,
        graphTangent, e, L, y, metricConnection] using hd
    have hj := flux_curve_hasDerivAt
      (fun t => metricGram g.tensor (f (c t)) (fderiv ℝ f (c t)))
      (fun a b => T i a b + T i b a)
      (fun t j => coordinateInner g.tensor (f (c t)) (W (f (c t))) (graphTangent f (c t) j))
      (fun j => R i j + S i j) (by simpa only [hc0, y, L] using hpos) hG hP i
    have hd : HasDerivAt
        (fun t => (metricFlux g.tensor W (f (c t)) (fderiv ℝ f (c t))) i)
        (fderiv ℝ (fun z => (metricFlux g.tensor W (f z) (fderiv ℝ f z)) i) x (coordinateVector 2 i)) 0 := by
      have hd0 : HasFDerivAt
          (fun z => (metricFlux g.tensor W (f z) (fderiv ℝ f z)) i)
          (fderiv ℝ (fun z => (metricFlux g.tensor W (f z) (fderiv ℝ f z)) i) x) (c 0) := by
        have hdscalar : DifferentiableAt ℝ
            (fun z => (metricFlux g.tensor W (f z) (fderiv ℝ f z)) i) x := by
          exact (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) i).differentiableAt.comp x hfluxd
        simpa only [hc0] using hdscalar.hasFDerivAt
      simpa only [Function.comp_def] using hd0.comp_hasDerivAt 0 hc
    exact hd.unique (by simpa only [metricFlux, metricDensity, graphTangent, hc0, y, L, Q, P] using hj)
  refine ⟨hpos, Real.sqrt_pos.mpr hpos.det_pos,
    normalProjection_orthogonal g.tensor y L (tracedAcceleration g.tensor f x) hsym hpos, ?_⟩
  have hdiv : planarDivergence (fun z => metricFlux g.tensor W (f z) (fderiv ℝ f z)) x =
      metricDensity g.tensor y L *
        ((∑ i : Fin 2, ∑ j : Fin 2, Q⁻¹ i j * R i j) +
          (∑ i : Fin 2, ∑ j : Fin 2, Q⁻¹ i j * S i j) -
          (∑ a : Fin 2, ∑ b : Fin 2, Q⁻¹ a b *
            (∑ i : Fin 2, ∑ j : Fin 2, Q⁻¹ i j * T i j a) * P b)) := by
    unfold planarDivergence
    simp only [hdir]
    rw [← Finset.mul_sum]
    congr 1
    exact flux_trace_algebra Q⁻¹ T P R S hQ hT
  have hnormal : coordinateInner g.tensor y (normalTrace g.tensor f x) (W y) =
      (∑ i : Fin 2, ∑ j : Fin 2, Q⁻¹ i j * S i j) -
      (∑ a : Fin 2, ∑ b : Fin 2, Q⁻¹ a b *
        (∑ i : Fin 2, ∑ j : Fin 2, Q⁻¹ i j * T i j a) * P b) := by
    unfold normalTrace normalProjection tangentProjection tracedAcceleration
    change coordinateInner g.tensor y
      ((∑ i : Fin 2, ∑ j : Fin 2, Q⁻¹ i j • A i j) -
        ∑ a : Fin 2, (∑ b : Fin 2, Q⁻¹ a b * coordinateInner g.tensor y (e b)
          (∑ i : Fin 2, ∑ j : Fin 2, Q⁻¹ i j • A i j)) • e a) (W y) = _
    simp only [Fin.sum_univ_two, coordinateInner, PiLp.sub_apply, PiLp.add_apply,
      PiLp.smul_apply, smul_eq_mul, Fin.sum_univ_three, T, S, P,
      coordinateInner, Fin.sum_univ_three, hsym, hQ 1 0]
    ring
  rw [hdiv, hnormal]
  change metricDensity g.tensor y L * (∑ i : Fin 2, ∑ j : Fin 2, Q⁻¹ i j * R i j) = _
  ring

/-- Closed-halfbox derivatives are within the genuine closed set; they are
not ordinary derivatives of an arbitrarily chosen extension at the boundary. -/
def halfBoxDomain (positive : Bool) (a b h : ℝ) : Set E2 :=
  coordinates ⁻¹' halfBox positive a b h

def openHalfBoxDomain (positive : Bool) (a b h : ℝ) : Set E2 :=
  coordinates ⁻¹' openHalfBox positive a b h

def halfBoxDifferential (f : E2 → E3) (positive : Bool) (a b h : ℝ)
    (x : E2) : E2 →L[ℝ] E3 :=
  fderivWithin ℝ f (halfBoxDomain positive a b h) x

def boundaryPoint (u : ℝ) : E2 := coordinates.symm (u, 0)

/-- Euclidean outward covector at the common r=0 edge. -/
def outwardCovector (positive : Bool) : E2 :=
  if positive then -coordinateVector 2 1 else coordinateVector 2 1

/-- The q-inverse normalized outward conormal, pushed by the same differential.
Its normalization, metric unit length, edge orthogonality and sign are outputs. -/
def metricConormal (g : MetricTensor) (y : E3) (L : E2 →L[ℝ] E3)
    (n : E2) : E3 :=
  let q := metricGram g y L
  let c : E2 := WithLp.toLp 2 (fun a : Fin 2 => ∑ b : Fin 2, q⁻¹ a b * n b)
  (Real.sqrt (∑ a : Fin 2, ∑ b : Fin 2, n a * q⁻¹ a b * n b))⁻¹ • L c

def metricEdgeSpeed (g : MetricTensor) (y : E3) (L : E2 →L[ℝ] E3) : ℝ :=
  Real.sqrt (coordinateInner g y (L (coordinateVector 2 0)) (L (coordinateVector 2 0)))

/-- The continuous metric flux built from the actual closed-side differential. -/
def halfBoxFlux (g : MetricTensor) (f : E2 → E3) (W : E3 → E3)
    (positive : Bool) (a b h : ℝ) : ℝ × ℝ → ℝ × ℝ :=
  fun z => coordinates (metricFlux g W (f (coordinates.symm z))
    (halfBoxDifferential f positive a b h (coordinates.symm z)))

private theorem gram_pullback (g : MetricTensor) (y : E3) (L : E2 →L[ℝ] E3)
    (u v : E2) : coordinateInner g y (L u) (L v) =
      ∑ a : Fin 2, ∑ b : Fin 2, metricGram g y L a b * u a * v b := by
  conv_lhs => rw [← basis_sum u, ← basis_sum v, map_sum, map_sum]
  simp only [map_smul, metricGram, coordinateInner, Fin.sum_univ_two, Fin.sum_univ_three,
    PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring
private theorem conormal_data (g : MetricTensor) (y : E3) (L : E2 →L[ℝ] E3)
    (W : E3 → E3) (positive : Bool)
    (hs : ∀ a b, g y a b = g y b a) (hq : (metricGram g y L).PosDef) :
    let eta := metricConormal g y L (outwardCovector positive)
    0 < metricEdgeSpeed g y L ∧
    coordinateInner g y eta eta = 1 ∧
    coordinateInner g y eta (L (coordinateVector 2 0)) = 0 ∧
    (∃ v : E2, L v = eta ∧ 0 < inner ℝ (outwardCovector positive) v) ∧
    (if positive then -(metricFlux g W y L) 1 else (metricFlux g W y L) 1) =
      coordinateInner g y eta (W y) * metricEdgeSpeed g y L := by
  let q := metricGram g y L
  let n := outwardCovector positive
  let c : E2 := WithLp.toLp 2 (fun a : Fin 2 => ∑ b : Fin 2, q⁻¹ a b * n b)
  let d := Real.sqrt (∑ a : Fin 2, ∑ b : Fin 2, n a * q⁻¹ a b * n b)
  have hsym : q 1 0 = q 0 1 := by simpa only [star_trivial] using hq.isHermitian.apply 0 1
  have hisym : q⁻¹ 0 1 = q⁻¹ 1 0 := by simpa only [star_trivial] using hq.inv.isHermitian.apply 1 0
  have hA : 0 < q 0 0 := hq.diag_pos
  have hiA : 0 < q⁻¹ 1 1 := hq.inv.diag_pos
  have hD : 0 < q.det := hq.det_pos
  have hn0 : n 0 = 0 := by cases positive <;> simp [n, outwardCovector, coordinateVector, EuclideanSpace.single]
  have hn1 : n 1 = if positive then -1 else 1 := by cases positive <;> simp [n, outwardCovector, coordinateVector, EuclideanSpace.single]
  have hn1sq : (n 1)^2 = 1 := by rw [hn1]; cases positive <;> norm_num
  have hd2 : d^2 = q⁻¹ 1 1 := by
    dsimp [d]
    have heq : (∑ a : Fin 2, ∑ b : Fin 2, n a * q⁻¹ a b * n b) = q⁻¹ 1 1 := by
      simp only [Fin.sum_univ_two, hn0, zero_mul, mul_zero, zero_add, add_zero]
      nlinarith [hn1sq]
    rw [heq]
    exact Real.sq_sqrt hiA.le
  have hd : 0 < d := by
    apply Real.sqrt_pos.mpr
    simp only [Fin.sum_univ_two, hn0, zero_mul, mul_zero, zero_add, add_zero]
    nlinarith [hn1sq]
  have hqc (a : Fin 2) : (∑ b : Fin 2, q a b * c b) = n a := by
    change (Matrix.mulVec q (Matrix.mulVec q⁻¹ (fun b => n b))) a = n a
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hD.ne'), Matrix.one_mulVec]
  have hcc : coordinateInner g y (L c) (L c) = d^2 := by
    rw [gram_pullback]
    change (∑ a : Fin 2, ∑ b : Fin 2, q a b * c a * c b) = d^2
    calc
      _ = ∑ a : Fin 2, (∑ b : Fin 2, q a b * c b) * c a := by
        simp only [Fin.sum_univ_two]
        ring
      _ = ∑ a : Fin 2, n a * c a := by simp only [hqc]
      _ = d^2 := by
        dsimp [c]
        simp only [Fin.sum_univ_two, hn0, mul_zero, zero_mul, zero_add]
        rw [hd2]
        nlinarith [hn1sq]
  have hc0 : coordinateInner g y (L c) (L (coordinateVector 2 0)) = 0 := by
    rw [inner_symmetric g y hs, gram_pullback]
    simpa [coordinateVector, EuclideanSpace.single, Fin.sum_univ_two, hn0] using hqc 0
  have hnc : inner ℝ n c = d^2 := by
    rw [PiLp.inner_apply]
    simp only [Fin.sum_univ_two, RCLike.inner_apply, starRingEnd_apply, star_trivial]
    dsimp [c]
    simp only [Fin.sum_univ_two, hn0, mul_zero, zero_mul, zero_add, add_zero]
    rw [hd2]
    nlinarith [hn1sq]
  have hsqrt : metricDensity g y L * d = metricEdgeSpeed g y L := by
    have hii : q⁻¹ 1 1 = (q 0 0) / q.det := by
      rw [Matrix.inv_def, Matrix.adjugate_fin_two]
      simp [div_eq_mul_inv, mul_comm, Ring.inverse_eq_inv]
    change Real.sqrt q.det * d = Real.sqrt (q 0 0)
    have heq : d = Real.sqrt (q⁻¹ 1 1) := by
      dsimp [d]
      congr 1
      simp only [Fin.sum_univ_two, hn0, mul_zero, zero_mul, zero_add]
      nlinarith [hn1sq]
    rw [heq, hii, Real.sqrt_div hA.le]
    field_simp [ne_of_gt (Real.sqrt_pos.mpr hD)]
  change 0 < metricEdgeSpeed g y L ∧
    coordinateInner g y (d⁻¹ • L c) (d⁻¹ • L c) = 1 ∧
    coordinateInner g y (d⁻¹ • L c) (L (coordinateVector 2 0)) = 0 ∧
    (∃ v : E2, L v = d⁻¹ • L c ∧ 0 < inner ℝ n v) ∧ _
  refine ⟨Real.sqrt_pos.mpr hA, ?_, ?_, ?_, ?_⟩
  · rw [coordinateInner_smul_left, inner_symmetric g y hs, coordinateInner_smul_left,
      inner_symmetric g y hs, hcc]
    field_simp [hd.ne']
  · rw [coordinateInner_smul_left, hc0, mul_zero]
  · refine ⟨d⁻¹ • c, L.map_smul _ _, ?_⟩
    rw [inner_smul_right, hnc]
    positivity
  · have hpair : coordinateInner g y (d⁻¹ • L c) (W y) =
        d⁻¹ * (∑ a : Fin 2, c a * coordinateInner g y (L (coordinateVector 2 a)) (W y)) := by
      rw [coordinateInner_smul_left]
      conv_lhs => rw [← basis_sum c, map_sum]
      simp only [map_smul, coordinateInner, Fin.sum_univ_two, Fin.sum_univ_three,
        PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    change (if positive then -(metricFlux g W y L) 1 else (metricFlux g W y L) 1) =
      coordinateInner g y (d⁻¹ • L c) (W y) * metricEdgeSpeed g y L
    rw [hpair, ← hsqrt]
    simp only [metricFlux, c, Fin.sum_univ_two, hn0, hn1,
      mul_zero, add_zero, inner_symmetric g y hs, hisym]
    cases positive <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      field_simp [hd.ne'] <;> ring

private theorem uniqueDiff_halfBox (a b h : ℝ) (hab : a < b) (hh : 0 < h) (p : Bool) :
    UniqueDiffOn ℝ (halfBoxDomain p a b h) := by
  apply coordinates.uniqueDiffOn_preimage_iff.mpr
  cases p
  · simpa only [halfBox, Bool.false_eq_true, ↓reduceIte, Icc_prod_eq] using
      (uniqueDiffOn_Icc hab).prod (uniqueDiffOn_Icc (neg_lt_zero.mpr hh))
  · simpa only [halfBox, ↓reduceIte, Icc_prod_eq] using
      (uniqueDiffOn_Icc hab).prod (uniqueDiffOn_Icc hh)
private theorem boundary_mem_halfBox (a b h : ℝ) (hh : 0 < h) (p : Bool)
    {u : ℝ} (hu : u ∈ Icc a b) : boundaryPoint u ∈ halfBoxDomain p a b h := by
  cases p <;> simpa [halfBoxDomain, boundaryPoint, halfBox, hh.le, (neg_nonpos.mpr hh.le)] using hu
private theorem boundary_derivative (f : E2 → E3) (a b h : ℝ)
    (hab : a < b) (hh : 0 < h) (p : Bool)
    (hf : ContDiffOn ℝ 1 f (halfBoxDomain p a b h)) :
    ∀ u ∈ Ioo a b, HasDerivAt (fun t => f (boundaryPoint t))
      (halfBoxDifferential f p a b h (boundaryPoint u) (coordinateVector 2 0)) u := by
  intro u hu
  have huf : boundaryPoint u ∈ halfBoxDomain p a b h :=
    boundary_mem_halfBox a b h hh p ⟨hu.1.le, hu.2.le⟩
  have hdf := (hf.differentiableOn one_ne_zero _ huf).hasFDerivWithinAt
  have hb : HasDerivAt boundaryPoint (coordinateVector 2 0) u := by
    have hb := coordinates.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt u
      ((hasDerivAt_id u).prodMk (hasDerivAt_const u (0 : ℝ)))
    convert! hb using 1
    ext i
    fin_cases i <;> simp [coordinateVector, EuclideanSpace.single, coordinates]
  apply hdf.comp_hasDerivAt u hb
  filter_upwards [isOpen_Ioo.mem_nhds hu] with t ht
  exact boundary_mem_halfBox a b h hh p ⟨ht.1.le, ht.2.le⟩

private theorem open_halfBox_interior (p : Bool) (a b h : ℝ) :
    openHalfBoxDomain p a b h = interior (halfBoxDomain p a b h) := by
  unfold openHalfBoxDomain halfBoxDomain
  change (coordinates.toHomeomorph : E2 → ℝ × ℝ) ⁻¹' openHalfBox p a b h =
    interior ((coordinates.toHomeomorph : E2 → ℝ × ℝ) ⁻¹' halfBox p a b h)
  rw [← coordinates.toHomeomorph.preimage_interior]
  congr 1
  cases p <;> simp only [openHalfBox, halfBox, Bool.false_eq_true, ↓reduceIte,
    Icc_prod_eq, interior_prod_eq, interior_Icc]
private theorem open_halfBox_isOpen (p : Bool) (a b h : ℝ) :
    IsOpen (openHalfBoxDomain p a b h) := by
  rw [open_halfBox_interior]
  exact isOpen_interior
private theorem halfBox_ae_open (p : Bool) (a b h : ℝ) :
    halfBox p a b h =ᵐ[volume] openHalfBox p a b h := by
  cases p
  · simpa only [halfBox, openHalfBox, Bool.false_eq_true, ↓reduceIte, Icc_prod_eq,
      MeasureTheory.Measure.volume_eq_prod] using
      (Measure.set_prod_ae_eq (Ioo_ae_eq_Icc (a := a) (b := b))
        (Ioo_ae_eq_Icc (a := -h) (b := 0))).symm
  · simpa only [halfBox, openHalfBox, ↓reduceIte, Icc_prod_eq,
      MeasureTheory.Measure.volume_eq_prod] using
      (Measure.set_prod_ae_eq (Ioo_ae_eq_Icc (a := a) (b := b))
        (Ioo_ae_eq_Icc (a := 0) (b := h))).symm
/-- L8 in its general form, retaining the normal-curvature term for the
original A2 owner to eliminate after proving minimality. Only C1 regularity
on the closed halfbox is assumed; all higher sheet regularity is interior.
The actual combined divergence integrand is explicitly required integrable. -/
theorem c1_halfbox_metric_flux
    (V : Set E3) (hV : IsOpen V) (g : CoordinateMetric V)
    (f : E2 → E3) (W : E3 → E3)
    (a b h : ℝ) (hab : a < b) (hh : 0 < h) (positive : Bool)
    (hf : ContDiffOn ℝ 1 f (halfBoxDomain positive a b h))
    (hsmooth : ContDiffOn ℝ ∞ f (openHalfBoxDomain positive a b h))
    (himage : MapsTo f (halfBoxDomain positive a b h) V)
    (hrank : ∀ x ∈ halfBoxDomain positive a b h,
      Function.Injective (halfBoxDifferential f positive a b h x))
    (hW : ContDiffOn ℝ 1 W V)
    (hfaces : ∀ v ∈ (if positive then Icc 0 h else Icc (-h) 0),
      (metricFlux g.tensor W (f (coordinates.symm (a, v)))
        (halfBoxDifferential f positive a b h (coordinates.symm (a, v)))) 0 = 0 ∧
      (metricFlux g.tensor W (f (coordinates.symm (b, v)))
        (halfBoxDifferential f positive a b h (coordinates.symm (b, v)))) 0 = 0)
    (houter : ∀ u ∈ Icc a b,
      (metricFlux g.tensor W (f (coordinates.symm (u, if positive then h else -h)))
        (halfBoxDifferential f positive a b h
          (coordinates.symm (u, if positive then h else -h)))) 1 = 0)
    (hi : IntegrableOn (fun z : ℝ × ℝ =>
      let x := coordinates.symm z
      let L := halfBoxDifferential f positive a b h x
      metricDensity g.tensor (f x) L *
        (metricTangentialDivergence g.tensor W (f x) L +
          coordinateInner g.tensor (f x) (normalTrace g.tensor f x) (W (f x))))
      (halfBox positive a b h)) :
    ContinuousOn (halfBoxFlux g.tensor f W positive a b h) (halfBox positive a b h) ∧
    DifferentiableOn ℝ (halfBoxFlux g.tensor f W positive a b h)
      (openHalfBox positive a b h) ∧
    (∀ u ∈ Ioo a b,
      HasDerivAt (fun t => f (boundaryPoint t))
        (halfBoxDifferential f positive a b h (boundaryPoint u) (coordinateVector 2 0)) u) ∧
    (∀ u ∈ Icc a b,
      let x := boundaryPoint u
      let L := halfBoxDifferential f positive a b h x
      let eta := metricConormal g.tensor (f x) L (outwardCovector positive)
      0 < metricEdgeSpeed g.tensor (f x) L ∧
      coordinateInner g.tensor (f x) eta eta = 1 ∧
      coordinateInner g.tensor (f x) eta (L (coordinateVector 2 0)) = 0 ∧
      (∃ v : E2, L v = eta ∧ 0 < inner ℝ (outwardCovector positive) v) ∧
      (if positive then -(metricFlux g.tensor W (f x) L) 1
        else (metricFlux g.tensor W (f x) L) 1) =
        coordinateInner g.tensor (f x) eta (W (f x)) * metricEdgeSpeed g.tensor (f x) L) ∧
    (∫ z in halfBox positive a b h,
      let x := coordinates.symm z
      let L := halfBoxDifferential f positive a b h x
      metricDensity g.tensor (f x) L *
        (metricTangentialDivergence g.tensor W (f x) L +
          coordinateInner g.tensor (f x) (normalTrace g.tensor f x) (W (f x)))) =
      ∫ u in Icc a b,
        let x := boundaryPoint u
        let L := halfBoxDifferential f positive a b h x
        coordinateInner g.tensor (f x)
          (metricConormal g.tensor (f x) L (outwardCovector positive)) (W (f x)) *
          metricEdgeSpeed g.tensor (f x) L := by
  let D := halfBoxDomain positive a b h
  let U := openHalfBoxDomain positive a b h
  let F : E2 → E2 := fun x => metricFlux g.tensor W (f x) (fderiv ℝ f x)
  let B := halfBoxFlux g.tensor f W positive a b h
  have hU : IsOpen U := open_halfBox_isOpen positive a b h
  have hUD : U ⊆ D := by
    dsimp only [U, D]
    rw [open_halfBox_interior]
    exact interior_subset
  have hclosed (z : ℝ × ℝ) (hz : z ∈ halfBox positive a b h) : coordinates.symm z ∈ D := by
    change coordinates (coordinates.symm z) ∈ halfBox positive a b h
    simpa only [coordinates.apply_symm_apply] using hz
  have hopen (z : ℝ × ℝ) (hz : z ∈ openHalfBox positive a b h) : coordinates.symm z ∈ U := by
    change coordinates (coordinates.symm z) ∈ openHalfBox positive a b h
    simpa only [coordinates.apply_symm_apply] using hz
  have hd (x : E2) (hx : x ∈ U) : halfBoxDifferential f positive a b h x = fderiv ℝ f x := by
    apply fderivWithin_of_mem_nhds
    exact Filter.mem_of_superset (hU.mem_nhds hx) hUD
  have hgram (x : E2) (hx : x ∈ D) :
      (metricGram g.tensor (f x) (halfBoxDifferential f positive a b h x)).PosDef :=
    gram_positive g.tensor _ _ (g.symmetric _ (himage hx)) (g.positive _ (himage hx)) (hrank x hx)
  have hfc : ContinuousOn (fun x => metricFlux g.tensor W (f x)
      (halfBoxDifferential f positive a b h x)) D := by
    apply flux_continuousOn D g.tensor f _ W hf.continuousOn
      (hf.continuousOn_fderivWithin (uniqueDiff_halfBox a b h hab hh positive) (by simp))
      (hW.continuousOn.comp hf.continuousOn himage)
      (fun a b => (g.smooth a b).continuousOn.comp hf.continuousOn himage) hgram
  have hBc : ContinuousOn B (halfBox positive a b h) := by
    exact coordinates.continuous.comp_continuousOn
      (hfc.comp coordinates.symm.continuous.continuousOn hclosed)
  have hFd (x : E2) (hx : x ∈ U) : DifferentiableAt ℝ F x := by
    have hdf := (hsmooth.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
    have hdl := ((hsmooth.fderiv_of_isOpen hU (m := 1) (by simp)).contDiffAt
      (hU.mem_nhds hx)).differentiableAt one_ne_zero
    apply flux_differentiableAt g.tensor f (fderiv ℝ f) W x hdl
      (((hW.contDiffAt (hV.mem_nhds (himage (hUD hx)))).differentiableAt one_ne_zero).comp x hdf)
      (fun a b => (((g.smooth a b).contDiffAt (hV.mem_nhds (himage (hUD hx)))).differentiableAt (by simp)).comp x hdf)
    simpa only [hd x hx] using hgram x (hUD hx)
  have heq : Set.EqOn B (fun z => coordinates (F (coordinates.symm z)))
      (openHalfBox positive a b h) := by
    intro z hz
    unfold B halfBoxFlux
    rw [hd _ (hopen z hz)]
  have hzEq (z : ℝ × ℝ) (hz : z ∈ openHalfBox positive a b h) :
      B =ᶠ[𝓝 z] (fun w => coordinates (F (coordinates.symm w))) := by
    have ho : IsOpen (openHalfBox positive a b h) := by
      cases positive <;> exact isOpen_Ioo.prod isOpen_Ioo
    filter_upwards [ho.mem_nhds hz] with w hw
    exact heq hw
  have hBd (z : ℝ × ℝ) (hz : z ∈ openHalfBox positive a b h) : DifferentiableAt ℝ B z := by
    apply (hzEq z hz).differentiableAt_iff.mpr
    exact coordinates.differentiableAt.comp z
      ((hFd _ (hopen z hz)).comp z coordinates.symm.differentiableAt)
  have hgeom (u : ℝ) (hu : u ∈ Icc a b) :=
    conormal_data g.tensor (f (boundaryPoint u))
      (halfBoxDifferential f positive a b h (boundaryPoint u)) W positive
      (g.symmetric _ (himage (boundary_mem_halfBox a b h hh positive hu)))
      (hgram _ (boundary_mem_halfBox a b h hh positive hu))
  refine ⟨hBc, (fun z hz => (hBd z hz).differentiableWithinAt),
    boundary_derivative f a b h hab hh positive hf, hgeom, ?_⟩
  let I : ℝ × ℝ → ℝ := fun z =>
    let x := coordinates.symm z
    let L := halfBoxDifferential f positive a b h x
    metricDensity g.tensor (f x) L *
      (metricTangentialDivergence g.tensor W (f x) L +
        coordinateInner g.tensor (f x) (normalTrace g.tensor f x) (W (f x)))
  let P : ℝ × ℝ → ℝ := fun z => (B z).1
  let R : ℝ × ℝ → ℝ := fun z => (B z).2
  let P' := fderiv ℝ P
  let R' := fderiv ℝ R
  have hPi (z : ℝ × ℝ) (hz : z ∈ openHalfBox positive a b h) :
      P' z (1,0) + R' z (0,1) = I z := by
    have hFd0 : DifferentiableAt ℝ (fun x => F x 0) (coordinates.symm z) :=
      (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0).differentiableAt.comp _ (hFd _ (hopen z hz))
    have hFd1 : DifferentiableAt ℝ (fun x => F x 1) (coordinates.symm z) :=
      (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 1).differentiableAt.comp _ (hFd _ (hopen z hz))
    have he0 : P =ᶠ[𝓝 z] (fun w => F (coordinates.symm w) 0) :=
      (hzEq z hz).fun_comp (fun w : ℝ × ℝ => w.1)
    have he1 : R =ᶠ[𝓝 z] (fun w => F (coordinates.symm w) 1) :=
      (hzEq z hz).fun_comp (fun w : ℝ × ℝ => w.2)
    have hv0 : coordinates.symm (1,0) = coordinateVector 2 0 := by
      ext i
      fin_cases i <;> simp [coordinates, coordinateVector, EuclideanSpace.single]
    have hv1 : coordinates.symm (0,1) = coordinateVector 2 1 := by
      ext i
      fin_cases i <;> simp [coordinates, coordinateVector, EuclideanSpace.single]
    have hq0 := (hFd0.hasFDerivAt.comp z coordinates.symm.hasFDerivAt).fderiv
    have hq1 := (hFd1.hasFDerivAt.comp z coordinates.symm.hasFDerivAt).fderiv
    change fderiv ℝ (fun w => F (coordinates.symm w) 0) z =
      (fderiv ℝ (fun x => F x 0) (coordinates.symm z)).comp
        coordinates.symm.toContinuousLinearMap at hq0
    change fderiv ℝ (fun w => F (coordinates.symm w) 1) z =
      (fderiv ℝ (fun x => F x 1) (coordinates.symm z)).comp
        coordinates.symm.toContinuousLinearMap at hq1
    change fderiv ℝ P z (1,0) + fderiv ℝ R z (0,1) = _
    rw [he0.fderiv_eq, he1.fderiv_eq, hq0, hq1]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, hv0, hv1]
    have hfixed := fixed_chart_metric_divergence U V hU hV g f W hsmooth
      (fun x hx => himage (hUD hx))
      (fun x hx => by simpa only [hd x hx] using hrank x (hUD hx)) hW
      (coordinates.symm z) (hopen z hz)
    dsimp only [I]
    rw [hd _ (hopen z hz)]
    have hfixed0 := hfixed.2.2.2
    change metricDensity g.tensor (f (coordinates.symm z)) (fderiv ℝ f (coordinates.symm z)) *
      metricTangentialDivergence g.tensor W (f (coordinates.symm z)) (fderiv ℝ f (coordinates.symm z)) =
      planarDivergence F (coordinates.symm z) - _ at hfixed0
    simp only [planarDivergence, Fin.sum_univ_two] at hfixed0
    linarith [hfixed0]
  have hBmeas : MeasurableSet (halfBox positive a b h) := by cases positive <;> exact measurableSet_Icc
  have hae : ∀ᵐ z ∂volume.restrict (halfBox positive a b h), z ∈ openHalfBox positive a b h := by
    rw [Measure.restrict_congr_set (halfBox_ae_open positive a b h)]
    apply ae_restrict_mem
    cases positive <;> exact measurableSet_Ioo.prod measurableSet_Ioo
  have haeI : (fun z => P' z (1,0) + R' z (0,1)) =ᵐ[volume.restrict (halfBox positive a b h)] I := by
    filter_upwards [hae] with z hz
    exact hPi z hz
  have hp : ∀ z ∈ openHalfBox positive a b h, HasFDerivAt P (P' z) z := fun z hz =>
    ((hBd z hz).fst).hasFDerivAt
  have hr : ∀ z ∈ openHalfBox positive a b h, HasFDerivAt R (R' z) z := fun z hz =>
    ((hBd z hz).snd).hasFDerivAt
  have hgg := lower_upper_half_box_adapter P R P' R' a b h hab hh positive
    hBc.fst hBc.snd hp hr (hi.congr_fun_ae haeI.symm) hfaces houter
  change (∫ z in halfBox positive a b h, I z) = _
  rw [← integral_congr_ae haeI, hgg]
  have hedge : (fun u => if positive then -R (u,0) else R (u,0)) =ᵐ[volume.restrict (Icc a b)]
      (fun u => coordinateInner g.tensor (f (boundaryPoint u))
        (metricConormal g.tensor (f (boundaryPoint u))
          (halfBoxDifferential f positive a b h (boundaryPoint u)) (outwardCovector positive))
        (W (f (boundaryPoint u))) *
        metricEdgeSpeed g.tensor (f (boundaryPoint u))
          (halfBoxDifferential f positive a b h (boundaryPoint u))) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    exact (hgeom u hu).2.2.2.2
  cases positive <;> simpa only [Bool.false_eq_true, ↓reduceIte, integral_neg] using integral_congr_ae hedge


def clockEdge (f : E2 → E3) (clock : ℝ → ℝ) (t : ℝ) : E3 :=
  f (boundaryPoint (clock t))

/-- Actual metric speed of the same boundary image under the common clock. -/
def clockMetricSpeed (g : MetricTensor) (f : E2 → E3)
    (clock : ℝ → ℝ) (t : ℝ) : ℝ :=
  let gamma := clockEdge f clock
  Real.sqrt (coordinateInner g (gamma t) (fderiv ℝ gamma t 1) (fderiv ℝ gamma t 1))

/-- L8 clock transport: a C1 change along the boundary alone, with absolute
Jacobian and positive actual metric edge speed. No bulk reparametrization
or smoothness across a possible sector apex is asserted or required. -/
theorem c1_boundary_clock_metric_flux
    (V : Set E3) (hV : IsOpen V) (g : CoordinateMetric V)
    (f : E2 → E3) (W : E3 → E3)
    (a b h : ℝ) (hab : a < b) (hh : 0 < h) (positive : Bool)
    (hf : ContDiffOn ℝ 1 f (halfBoxDomain positive a b h))
    (himage : MapsTo f (halfBoxDomain positive a b h) V)
    (hrank : ∀ x ∈ halfBoxDomain positive a b h,
      Function.Injective (halfBoxDifferential f positive a b h x))
    (hW : ContinuousOn W V)
    (clock : ℝ → ℝ) (l r l0 r0 : ℝ) (hlr : l < r)
    (hwindow : Icc l r ⊆ Ioo l0 r0)
    (hclock : ContDiffOn ℝ 1 clock (Ioo l0 r0))
    (hclockRegular : ∀ t ∈ Icc l r, deriv clock t ≠ 0)
    (hclockInjective : InjOn clock (Icc l r))
    (hclockImage : clock '' Icc l r = Icc a b) :
    (∀ t ∈ Ioo l r,
      let x := boundaryPoint (clock t)
      let L := halfBoxDifferential f positive a b h x
      let eta := metricConormal g.tensor (f x) L (outwardCovector positive)
      0 < clockMetricSpeed g.tensor f clock t ∧
      clockMetricSpeed g.tensor f clock t =
        |deriv clock t| * metricEdgeSpeed g.tensor (f x) L ∧
      |deriv clock t| *
          (if positive then -(metricFlux g.tensor W (f x) L) 1
            else (metricFlux g.tensor W (f x) L) 1) =
        coordinateInner g.tensor (f x) eta (W (f x)) * clockMetricSpeed g.tensor f clock t) ∧
    (∫ u in Icc a b,
      let x := boundaryPoint u
      let L := halfBoxDifferential f positive a b h x
      coordinateInner g.tensor (f x)
        (metricConormal g.tensor (f x) L (outwardCovector positive)) (W (f x)) *
        metricEdgeSpeed g.tensor (f x) L) =
      ∫ t in Icc l r,
        let x := boundaryPoint (clock t)
        let L := halfBoxDifferential f positive a b h x
        coordinateInner g.tensor (f x)
          (metricConormal g.tensor (f x) L (outwardCovector positive)) (W (f x)) *
          clockMetricSpeed g.tensor f clock t := by
  have hc (t : ℝ) (ht : t ∈ Icc l r) : HasDerivAt clock (deriv clock t) t :=
    (hclock.contDiffAt (isOpen_Ioo.mem_nhds (hwindow ht))).differentiableAt one_ne_zero |>.hasDerivAt
  have hclosed (t : ℝ) (ht : t ∈ Icc l r) : clock t ∈ Icc a b := by
    rw [← hclockImage]
    exact mem_image_of_mem clock ht
  have hopen (t : ℝ) (ht : t ∈ Ioo l r) : clock t ∈ Ioo a b := by
    have htcl : t ∈ Icc l r := ⟨ht.1.le, ht.2.le⟩
    have hb := hclosed t htcl
    constructor
    · apply lt_of_le_of_ne hb.1
      intro heq
      have hmin : IsLocalMin clock t := by
        filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
        rw [← heq]
        exact (hclosed u ⟨hu.1.le,hu.2.le⟩).1
      exact hclockRegular t htcl hmin.deriv_eq_zero
    · apply lt_of_le_of_ne hb.2
      intro heq
      have hmax : IsLocalMax clock t := by
        filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
        rw [heq]
        exact (hclosed u ⟨hu.1.le,hu.2.le⟩).2
      exact hclockRegular t htcl hmax.deriv_eq_zero
  have hs (t : ℝ) (ht : t ∈ Ioo l r) :
      clockMetricSpeed g.tensor f clock t = |deriv clock t| *
        metricEdgeSpeed g.tensor (f (boundaryPoint (clock t)))
          (halfBoxDifferential f positive a b h (boundaryPoint (clock t))) := by
    have hbd := boundary_derivative f a b h hab hh positive hf (clock t) (hopen t ht)
    have hd := hbd.hasFDerivAt.comp_hasDerivAt t (hc t ⟨ht.1.le,ht.2.le⟩)
    have he : fderiv ℝ (clockEdge f clock) t 1 = deriv clock t •
        halfBoxDifferential f positive a b h (boundaryPoint (clock t)) (coordinateVector 2 0) := by
      change fderiv ℝ (fun s => f (boundaryPoint (clock s))) t 1 = _
      simpa only [Function.comp_def, ContinuousLinearMap.toSpanSingleton_apply,
        one_smul] using congrArg (fun L : ℝ →L[ℝ] E3 => L 1) hd.hasFDerivAt.fderiv
    unfold clockMetricSpeed metricEdgeSpeed
    dsimp only [clockEdge]
    rw [he, coordinateInner_smul_left]
    have hright (s : ℝ) (v : E3) : coordinateInner g.tensor (f (boundaryPoint (clock t))) v (s • v) =
        s * coordinateInner g.tensor (f (boundaryPoint (clock t))) v v := by
      simp only [coordinateInner, PiLp.smul_apply, smul_eq_mul, Fin.sum_univ_three]
      ring
    rw [hright]
    rw [show deriv clock t * (deriv clock t * coordinateInner g.tensor
      (f (boundaryPoint (clock t)))
      (halfBoxDifferential f positive a b h (boundaryPoint (clock t)) (coordinateVector 2 0))
      (halfBoxDifferential f positive a b h (boundaryPoint (clock t)) (coordinateVector 2 0))) =
      (deriv clock t)^2 * coordinateInner g.tensor (f (boundaryPoint (clock t)))
      (halfBoxDifferential f positive a b h (boundaryPoint (clock t)) (coordinateVector 2 0))
      (halfBoxDifferential f positive a b h (boundaryPoint (clock t)) (coordinateVector 2 0)) by ring]
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
  have hg (t : ℝ) (ht : t ∈ Ioo l r) :=
    conormal_data g.tensor (f (boundaryPoint (clock t)))
      (halfBoxDifferential f positive a b h (boundaryPoint (clock t))) W positive
      (g.symmetric _ (himage (boundary_mem_halfBox a b h hh positive
        (hclosed t ⟨ht.1.le,ht.2.le⟩))))
      (gram_positive g.tensor _ _
        (g.symmetric _ (himage (boundary_mem_halfBox a b h hh positive (hclosed t ⟨ht.1.le,ht.2.le⟩))))
        (g.positive _ (himage (boundary_mem_halfBox a b h hh positive (hclosed t ⟨ht.1.le,ht.2.le⟩))))
        (hrank _ (boundary_mem_halfBox a b h hh positive (hclosed t ⟨ht.1.le,ht.2.le⟩))))
  constructor
  · intro t ht
    dsimp only
    refine ⟨?_, hs t ht, ?_⟩
    · rw [hs t ht]
      exact mul_pos (abs_pos.mpr (hclockRegular t ⟨ht.1.le,ht.2.le⟩)) (hg t ht).1
    · rw [(hg t ht).2.2.2.2, hs t ht]
      ring
  · let B : ℝ → ℝ := fun u =>
      let x := boundaryPoint u
      let L := halfBoxDifferential f positive a b h x
      coordinateInner g.tensor (f x) (metricConormal g.tensor (f x) L (outwardCovector positive))
        (W (f x)) * metricEdgeSpeed g.tensor (f x) L
    change (∫ u in Icc a b, B u) = _
    rw [← hclockImage]
    rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Icc
      (fun t ht => (hc t ht).hasDerivWithinAt) hclockInjective B]
    calc
      _ = ∫ t in Ioo l r, |deriv clock t| • B (clock t) :=
        setIntegral_congr_set Ioo_ae_eq_Icc.symm
      _ = ∫ t in Ioo l r,
        coordinateInner g.tensor (f (boundaryPoint (clock t)))
          (metricConormal g.tensor (f (boundaryPoint (clock t)))
            (halfBoxDifferential f positive a b h (boundaryPoint (clock t)))
            (outwardCovector positive)) (W (f (boundaryPoint (clock t)))) *
          clockMetricSpeed g.tensor f clock t := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro t ht
        dsimp only [B]
        rw [hs t ht]
        simp only [smul_eq_mul]
        ring
      _ = _ := setIntegral_congr_set Ioo_ae_eq_Icc

/-- Compact coordinate-line tests after the native owner rectifies its smooth
ambient seam or graph. The affine line, support set and trace are actual data;
the entire smooth compact extension is an output. -/
theorem smooth_compact_affine_line_test_extension
    (O : Set E3) (hO : IsOpen O) (p e v : E3) (he : e ≠ 0)
    (phi : ℝ → ℝ) (hphi : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
    (hs : (fun t : ℝ => p + t • e) '' tsupport phi ⊆ O) :
    ∃ W : E3 → E3, ContDiff ℝ ∞ W ∧ HasCompactSupport W ∧ tsupport W ⊆ O ∧
      ∀ t : ℝ, W (p + t • e) = phi t • v := by
  let A : ℝ → E3 := fun t => p + t • e
  let K : Set E3 := A '' tsupport phi
  have hK : IsCompact K := hc.image (by fun_prop)
  obtain ⟨B, hBopen, hKB, hBcompact⟩ := exists_isOpen_superset_and_isCompact_closure hK
  obtain ⟨U, hUopen, hKU, hUcl⟩ :=
    hK.exists_isOpen_closure_subset ((hO.inter hBopen).mem_nhdsSet.2 (subset_inter hs hKB))
  obtain ⟨ψ, hψcd, hψrange, hψsupp, hψone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hUopen hK.isClosed hKU
  have hψcl : tsupport ψ = closure U := congrArg closure hψsupp
  have hψcompact : HasCompactSupport ψ := by
    rw [HasCompactSupport, hψcl]
    exact hBcompact.of_isClosed_subset isClosed_closure
      (fun x hx => subset_closure (hUcl hx).2)
  let ell : E3 → ℝ := fun y => inner ℝ (y - p) e / inner ℝ e e
  have hell : ContDiff ℝ ∞ ell :=
    ((contDiff_id.sub contDiff_const).inner ℝ contDiff_const).div_const _
  let W : E3 → E3 := fun y => ψ y • (phi (ell y) • v)
  refine ⟨W, hψcd.smul ((hphi.comp hell).smul contDiff_const),
    hψcompact.smul_right, ?_, ?_⟩
  · exact (tsupport_smul_subset_left _ _).trans
      (hψcl ▸ (fun x hx => (hUcl hx).1))
  · intro t
    have hEll : ell (A t) = t := by
      dsimp [ell, A]
      rw [add_sub_cancel_left, inner_smul_left]
      exact mul_div_cancel_right₀ t (inner_self_ne_zero.mpr he)
    change ψ (A t) • (phi (ell (A t)) • v) = phi t • v
    rw [hEll]
    by_cases ht : t ∈ tsupport phi
    · rw [(hψone (A t)).mp ⟨t, ht, rfl⟩, one_smul]
    · rw [image_eq_zero_of_notMem_tsupport ht, zero_smul, smul_zero]

end SeifertSurfaces.OriginalEndpoints.A2MetricFlux
