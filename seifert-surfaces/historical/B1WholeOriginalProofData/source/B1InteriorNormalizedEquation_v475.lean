import B1InteriorNormalization_v475
import B1LocalFluxClassical_v475
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Division by the paid positive solution removes the zeroth-order term in
the complete classical equation. -/
theorem native_interior_divide_positive_classical_v475
    (N : InteriorNormalizationData_v475) :
    ∀ x ∈ N.O, classicalL N.leading N.drift (fun _ => 0) N.v x = 0 := by
  let U := N.O
  let f := N.u
  let Xf : E2 → E2 := fun x => matrixAction (N.a x) (planarGradient f x)
  let Xh : E2 → E2 := fun x => matrixAction (N.a x) (planarGradient N.h x)
  let X : E2 → E2 := fun x => matrixAction (N.leading x) (planarGradient N.v x)
  have hU : IsOpen U := N.isOpen_O
  have hfAt (x : E2) (hx : x ∈ U) : ContDiffAt ℝ ∞ f x :=
    (N.smooth_u x hx).contDiffAt (hU.mem_nhds hx)
  have hhAt (x : E2) (hx : x ∈ U) : ContDiffAt ℝ ∞ N.h x :=
    (N.smooth_h x hx).contDiffAt (hU.mem_nhds hx)
  have hhne (x : E2) (hx : x ∈ U) : N.h x ≠ 0 := (N.h_positive x hx).ne'
  have hvAt (x : E2) (hx : x ∈ U) : ContDiffAt ℝ ∞ N.v x :=
    (hfAt x hx).div (hhAt x hx) (hhne x hx)
  have haAt (x : E2) (hx : x ∈ U) (i j : Fin 2) :
      ContDiffAt ℝ ∞ (fun y => N.a y i j) x :=
    (N.elliptic.1 i j x hx).contDiffAt (hU.mem_nhds hx)
  have hgradAt (v : E2 → ℝ) (x : E2) (hv : ContDiffAt ℝ ∞ v x) :
      ContDiffAt ℝ ∞ (planarGradient v) x := by
    delta planarGradient
    apply ContDiffAt.sum
    intro i hi
    exact ((hv.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).smul contDiffAt_const
  have hactionAt (v : E2 → E2) (x : E2) (hx : x ∈ U)
      (hv : ContDiffAt ℝ ∞ v x) : ContDiffAt ℝ ∞ (fun y => matrixAction (N.a y) (v y)) x := by
    apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.contDiff.contDiffAt.comp
    apply contDiffAt_pi.mpr
    intro i
    apply ContDiffAt.sum
    intro j hj
    exact (haAt x hx i j).mul
      ((EuclideanSpace.proj (𝕜 := ℝ) (j : Fin 2)).contDiff.contDiffAt.comp x hv)
  have hXfAt (x : E2) (hx : x ∈ U) : ContDiffAt ℝ ∞ Xf x :=
    hactionAt _ x hx (hgradAt f x (hfAt x hx))
  have hXhAt (x : E2) (hx : x ∈ U) : ContDiffAt ℝ ∞ Xh x :=
    hactionAt _ x hx (hgradAt N.h x (hhAt x hx))
  have hqgrad (x : E2) (hx : x ∈ U) :
      N.h x • planarGradient N.v x = planarGradient f x - N.v x • planarGradient N.h x := by
    have hf := (hfAt x hx).differentiableAt (by simp)
    have hh := (hhAt x hx).differentiableAt (by simp)
    have hinv := (hasDerivAt_inv (hhne x hx)).comp_hasFDerivAt x hh.hasFDerivAt
    have hfd := hf.hasFDerivAt.mul hinv
    delta InteriorNormalizationData_v475.v planarGradient
    simp only [div_eq_mul_inv]
    dsimp only [Pi.mul_def,Function.comp_def] at hfd
    rw [hfd.fderiv]
    simp only [add_apply,smul_apply,smul_eq_mul]
    rw [Finset.smul_sum,Finset.smul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [smul_smul]
    rw [← sub_smul]
    congr 1
    dsimp only [f]
    field_simp [hhne x hx]
    ring
  have hXeq (x : E2) (hx : x ∈ U) : X x = Xf x - N.v x • Xh x := by
    have hg := hqgrad x hx
    have hma : matrixAction (N.leading x) (planarGradient N.v x) =
        matrixAction (N.a x) (N.h x • planarGradient N.v x) := by
      ext i
      change (∑ j, (N.h x * N.a x i j) * planarGradient N.v x j) =
        ∑ j, N.a x i j * (N.h x * planarGradient N.v x j)
      apply Finset.sum_congr rfl
      intro j hj
      ring
    dsimp only [X,Xf,Xh]
    rw [hma,hg]
    ext i
    change (∑ j, N.a x i j * (planarGradient f x j - N.v x * planarGradient N.h x j)) =
      (∑ j, N.a x i j * planarGradient f x j) - N.v x * ∑ j, N.a x i j * planarGradient N.h x j
    simp only [Fin.sum_univ_two]
    ring
  have hXAt (x : E2) (hx : x ∈ U) : ContDiffAt ℝ ∞ X x := by
    apply ((hXfAt x hx).sub ((hvAt x hx).smul (hXhAt x hx))).congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hXeq y hy
  have hgcoord (v : E2 → ℝ) (x : E2) (i : Fin 2) :
      planarGradient v x i = fderiv ℝ v x (coordinateVector 2 i) := by
    fin_cases i <;> simp [planarGradient,coordinateVector,Fin.sum_univ_two]
  have hclassical (x : E2) (hx : x ∈ U) :
      (∑ i : Fin 2, fderiv ℝ (fun y => X y i) x (coordinateVector 2 i)) +
        inner ℝ (N.drift x) (planarGradient N.v x) = 0 := by
    have hdx (i : Fin 2) : fderiv ℝ (fun y => X y i) x =
        fderiv ℝ (fun y => Xf y i) x -
          (N.v x • fderiv ℝ (fun y => Xh y i) x + Xh x i • fderiv ℝ N.v x) := by
      have hevent : (fun y => X y i) =ᶠ[nhds x]
          (fun y => Xf y i - N.v y * Xh y i) := by
        filter_upwards [hU.mem_nhds hx] with y hy
        exact congrArg (fun v : E2 => v i) (hXeq y hy)
      rw [hevent.fderiv_eq]
      exact (((EuclideanSpace.proj (𝕜 := ℝ) (i : Fin 2)).differentiableAt.comp x
        ((hXfAt x hx).differentiableAt (by simp))).hasFDerivAt.sub
        (((hvAt x hx).differentiableAt (by simp)).hasFDerivAt.mul
          (((EuclideanSpace.proj (𝕜 := ℝ) (i : Fin 2)).differentiableAt.comp x
            ((hXhAt x hx).differentiableAt (by simp))).hasFDerivAt))).fderiv
    have hf := N.u_classical x hx
    have hh := N.h_classical x hx
    have hvh : f x = N.v x * N.h x := by
      change f x = (f x / N.h x) * N.h x
      rw [div_mul_cancel₀ _ (hhne x hx)]
    have hg0 := congrArg (fun v : E2 => v 0) (hqgrad x hx)
    have hg1 := congrArg (fun v : E2 => v 1) (hqgrad x hx)
    simp only [PiLp.smul_apply,PiLp.sub_apply,smul_eq_mul] at hg0 hg1
    simp only [Fin.sum_univ_two,hdx,sub_apply,add_apply,smul_apply,smul_eq_mul]
    simp only [classicalL,Fin.sum_univ_two] at hf hh
    change fderiv ℝ (fun y => Xf y 0) x (coordinateVector 2 0) +
      fderiv ℝ (fun y => Xf y 1) x (coordinateVector 2 1) +
      inner ℝ (N.b x) (planarGradient f x) + N.c x * f x = 0 at hf
    change fderiv ℝ (fun y => Xh y 0) x (coordinateVector 2 0) +
      fderiv ℝ (fun y => Xh y 1) x (coordinateVector 2 1) +
      inner ℝ (N.b x) (planarGradient N.h x) + N.c x * N.h x = 0 at hh
    simp only [InteriorNormalizationData_v475.drift]
    change _ + inner ℝ (Xh x + N.h x • N.b x) (planarGradient N.v x) = 0
    simp only [EuclideanSpace.inner_eq_star_dotProduct,Fin.sum_univ_two,
      dotProduct,star_trivial,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul] at hf hh ⊢
    simp only [← hgcoord] at hf hh ⊢
    rw [hvh] at hf
    linear_combination hf - N.v x * hh + N.b x 0 * hg0 + N.b x 1 * hg1
  intro x hx
  simpa only [classicalL,zero_mul,add_zero] using hclassical x hx

#print axioms native_interior_divide_positive_classical_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
