import A2NativeNormalProjection

set_option autoImplicit false
open Set Matrix
open scoped ContDiff BigOperators
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.A2NativeTests
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.A2NativeNormalProjection

private theorem matrix_det_smooth {n : Type*} [Fintype n] [DecidableEq n]
    (A : E2 → Matrix n n ℝ) (U : Set E2)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) U) :
    ContDiffOn ℝ ∞ (fun x => (A x).det) U := by
  simp only [Matrix.det_apply']
  apply ContDiffOn.sum
  intro σ _
  apply contDiffOn_const.mul
  apply contDiffOn_prod
  intro i _
  exact hA (σ i) i

private theorem matrix_inverse_smooth {n : Type*} [Fintype n] [DecidableEq n]
    (A : E2 → Matrix n n ℝ) (U : Set E2)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) U)
    (hdet : ∀ x ∈ U, (A x).det ≠ 0) :
    ∀ i j, ContDiffOn ℝ ∞ (fun x => (A x)⁻¹ i j) U := by
  have hd := (matrix_det_smooth A U hA).inv hdet
  intro i j
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul,
    Matrix.adjugate_apply]
  apply hd.mul
  apply matrix_det_smooth
  intro a b
  by_cases ha : a = j
  · subst a
    simpa only [Matrix.updateRow_self] using (contDiffOn_const :
      ContDiffOn ℝ ∞ (fun _ : E2 => (Pi.single i (1 : ℝ) : n → ℝ) b) U)
  · simpa only [Matrix.updateRow_ne ha] using hA a b

private theorem coordinate_inner_smooth (g : MetricTensor) (f v w : E2 → E3)
    (U : Set E2) (hg : ∀ a b, ContDiffOn ℝ ∞ (fun x => g (f x) a b) U)
    (hv : ContDiffOn ℝ ∞ v U) (hw : ContDiffOn ℝ ∞ w U) :
    ContDiffOn ℝ ∞ (fun x => coordinateInner g (f x) (v x) (w x)) U := by
  unfold coordinateInner
  apply ContDiffOn.sum
  intro a _
  apply ContDiffOn.sum
  intro b _
  exact ((hg a b).mul ((contDiffOn_piLp 2).mp hv a)).mul ((contDiffOn_piLp 2).mp hw b)

private theorem coordinate_christoffel_composite_smooth
    (g : MetricTensor) (V : Set E3) (hV : IsOpen V)
    (hg : ∀ a b, ContDiffOn ℝ ∞ (fun z => g z a b) V)
    (hdet : ∀ z ∈ V, (g z).det ≠ 0)
    (f : E2 → E3) (U : Set E2) (hf : ContDiffOn ℝ ∞ f U)
    (hmap : MapsTo f U V) :
    ∀ a b k, ContDiffOn ℝ ∞ (fun x => christoffel g (f x) a b k) U := by
  have hG (a b : Fin 3) : ContDiffOn ℝ ∞ (fun x => g (f x) a b) U :=
    (hg a b).comp hf hmap
  have hInv := matrix_inverse_smooth (fun x => g (f x)) U hG
    (fun x hx => hdet (f x) (hmap hx))
  have hpartial (a b c : Fin 3) :
      ContDiffOn ℝ ∞ (fun x => partial3 (fun z => g z a b) (f x) c) U :=
    (((hg a b).fderiv_of_isOpen hV (by simp)).clm_apply contDiffOn_const).comp hf hmap
  intro a b k
  unfold christoffel
  apply contDiffOn_const.mul
  apply ContDiffOn.sum
  intro l _
  exact (hInv k l).mul (((hpartial l b a).add (hpartial l a b)).sub (hpartial a b l))

/-- Smoothness of the actual normal trace, from the smooth immersion and metric.
No stationarity or vanishing conclusion is an input. -/
theorem normal_trace_smooth (g : MetricTensor) (V : Set E3) (hV : IsOpen V)
    (hg : ∀ a b, ContDiffOn ℝ ∞ (fun z => g z a b) V)
    (hdet : ∀ z ∈ V, (g z).det ≠ 0)
    (f : E2 → E3) (U : Set E2) (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (hmap : MapsTo f U V)
    (hgram : ∀ x ∈ U, (inducedMetric g f x).det ≠ 0) :
    ContDiffOn ℝ ∞ (fun x => normalProjection g (f x) (fderiv ℝ f x)
      (tracedAcceleration g f x)) U := by
  have hG (a b : Fin 3) : ContDiffOn ℝ ∞ (fun x => g (f x) a b) U :=
    (hg a b).comp hf hmap
  have htan (i : Fin 2) : ContDiffOn ℝ ∞ (fun x => graphTangent f x i) U :=
    (hf.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
  have hgramSmooth (i j : Fin 2) :
      ContDiffOn ℝ ∞ (fun x => inducedMetric g f x i j) U :=
    coordinate_inner_smooth g f _ _ U hG (htan i) (htan j)
  have hInv := matrix_inverse_smooth (inducedMetric g f) U hgramSmooth hgram
  have hΓ := coordinate_christoffel_composite_smooth g V hV hg hdet f U hf hmap
  have hacc (i j : Fin 2) : ContDiffOn ℝ ∞ (fun x => covariantAcceleration g f x i j) U := by
    unfold covariantAcceleration
    apply ContDiffOn.add
    · exact ((htan j).fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
    · apply ContDiffOn.sum
      intro k _
      apply ContDiffOn.smul_const
      apply ContDiffOn.sum
      intro a _
      apply ContDiffOn.sum
      intro b _
      exact ((hΓ a b k).mul ((contDiffOn_piLp 2).mp (htan i) a)).mul
        ((contDiffOn_piLp 2).mp (htan j) b)
  have htrace : ContDiffOn ℝ ∞ (tracedAcceleration g f) U := by
    unfold tracedAcceleration
    apply ContDiffOn.sum
    intro i _
    apply ContDiffOn.sum
    intro j _
    exact (hInv i j).smul (hacc i j)
  change ContDiffOn ℝ ∞ (fun x => tracedAcceleration g f x -
    ∑ i : Fin 2, (∑ j : Fin 2, (inducedMetric g f x)⁻¹ i j *
      coordinateInner g (f x) (graphTangent f x j) (tracedAcceleration g f x)) •
      graphTangent f x i) U
  apply htrace.sub
  apply ContDiffOn.sum
  intro i _
  have hcoeff : ContDiffOn ℝ ∞ (fun x => ∑ j : Fin 2, (inducedMetric g f x)⁻¹ i j *
      coordinateInner g (f x) (graphTangent f x j) (tracedAcceleration g f x)) U := by
    apply ContDiffOn.sum
    intro j _
    exact (hInv i j).mul (coordinate_inner_smooth g f _ _ U hG (htan j) htrace)
  exact hcoeff.smul (htan i)

#print axioms normal_trace_smooth
end SeifertSurfaces.OriginalEndpoints.A2NativeTests
