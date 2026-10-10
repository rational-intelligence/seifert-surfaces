import ProductCoordinates

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology BigOperators ContDiff ENNReal
namespace SeifertSurfaces.QuasilinearProviderBridge.Helpers
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.QuasilinearLocalization

lemma gradient3_coordinate (f : E3 → ℝ) (y : E3) (i : Fin 3) :
    gradient3 f y i = fderiv ℝ f y (coordinateVector 3 i) := by
  fin_cases i <;> simp [gradient3, Fin.sum_univ_succ, coordinateVector, EuclideanSpace.single]

lemma horizontal_smooth (t : ℝ) : ContDiff ℝ ∞ (fun x : E2 => liftedPoint x t) := by
  exact productCLE.contDiff.comp (contDiff_id.prodMk contDiff_const)

lemma vertical_smooth (x : E2) : ContDiff ℝ ∞ (fun t : ℝ => liftedPoint x t) := by
  exact productCLE.contDiff.comp (contDiff_const.prodMk contDiff_id)

lemma horizontal_closed (t : ℝ) : Topology.IsClosedEmbedding (fun x : E2 => liftedPoint x t) := by
  exact productCLE.toHomeomorph.isClosedEmbedding.comp
    (show Topology.IsClosedEmbedding (fun x : E2 => (x, t)) from
      Topology.IsClosedEmbedding.of_isEmbedding_isClosedMap (isEmbedding_prodMkLeft t) (isClosedMap_prodMk_right t))

lemma vertical_closed (x : E2) : Topology.IsClosedEmbedding (fun t : ℝ => liftedPoint x t) := by
  exact productCLE.toHomeomorph.isClosedEmbedding.comp
    (show Topology.IsClosedEmbedding (fun t : ℝ => (x, t)) from
      Topology.IsClosedEmbedding.of_isEmbedding_isClosedMap (isEmbedding_prodMkRight x) (isClosedMap_prodMk_left x))

lemma vertical_hasDeriv (x : E2) (t : ℝ) :
    HasDerivAt (fun s : ℝ => liftedPoint x s) (coordinateVector 3 2) t := by
  convert ((hasDerivAt_id t).smul_const (coordinateVector 3 2)).const_add (liftedPoint x 0) using 1
  · funext s
    ext i
    fin_cases i <;> simp [liftedPoint, coordinateVector, EuclideanSpace.single]
  · simp

lemma vertical_deriv {ψ : E3 → ℝ} (hψ : ContDiff ℝ ∞ ψ) (x : E2) (t : ℝ) :
    deriv (fun s => ψ (liftedPoint x s)) t = gradient3 ψ (liftedPoint x t) 2 := by
  rw [gradient3_coordinate]
  exact ((hψ.differentiable (by simp) (liftedPoint x t)).hasFDerivAt.comp_hasDerivAt t (vertical_hasDeriv x t)).deriv

lemma horizontal_gradient {ψ : E3 → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (x : E2) (t : ℝ) :
    planarGradient (fun z => ψ (liftedPoint z t)) x = planarPart (gradient3 ψ (liftedPoint x t)) := by
  let S : E2 →L[ℝ] E3 := productCLE.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ E2 ℝ)
  have hs (z : E2) : S z = liftedPoint z 0 := rfl
  have heq : (fun z => liftedPoint z t) = fun z => S z + liftedPoint 0 t := by
    funext z; ext i; fin_cases i <;> simp [hs, liftedPoint]
  have hd : HasFDerivAt (fun z => liftedPoint z t) S x := by
    rw [heq]
    exact S.hasFDerivAt.add_const _
  have hcomp := (hψ.differentiable (by simp) (liftedPoint x t)).hasFDerivAt.comp x hd
  simp only [Function.comp_def] at hcomp
  have hb (i : Fin 2) : S (coordinateVector 2 i) = coordinateVector 3 (Fin.castSucc i) := by
    rw [hs]
    ext j; fin_cases i <;> fin_cases j <;> simp [liftedPoint, coordinateVector, EuclideanSpace.single]
  have hp (f : E2 → ℝ) (z : E2) (i : Fin 2) :
      planarGradient f z i = fderiv ℝ f z (coordinateVector 2 i) := by
    fin_cases i <;> simp [planarGradient, Fin.sum_univ_succ, coordinateVector, EuclideanSpace.single]
  ext i
  rw [hp, hcomp.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  rw [hb]
  fin_cases i <;> simp [planarPart, gradient3_coordinate]

lemma gradient3_zero {ψ : E3 → ℝ} {y : E3} (hy : y ∉ tsupport ψ) :
    gradient3 ψ y = 0 := by
  simp [gradient3, fderiv_of_notMem_tsupport ℝ hy]

lemma vertical_integral {ψ : E3 → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (x : E2) (D g : ℝ) :
    (∫ t : ℝ, g * ψ (liftedPoint x t) +
      (D + t * g) * gradient3 ψ (liftedPoint x t) 2) = 0 := by
  let f : ℝ → ℝ := fun t => ψ (liftedPoint x t)
  have hf : ContDiff ℝ ∞ f := hψ.comp (vertical_smooth x)
  have hfc : HasCompactSupport f := hc.comp_isClosedEmbedding (vertical_closed x)
  have hdi : Integrable (fun t => (D + t * g) * deriv f t) :=
    (((continuous_const.add (continuous_id.mul continuous_const)).mul
      (hf.continuous_deriv (by simp))).integrable_of_hasCompactSupport hfc.deriv.mul_left)
  have hfi : Integrable (fun t => g * f t) :=
    (continuous_const.mul hf.continuous).integrable_of_hasCompactSupport hfc.mul_left
  have hpi : Integrable (fun t => (D + t * g) * f t) :=
    ((continuous_const.add (continuous_id.mul continuous_const)).mul hf.continuous).integrable_of_hasCompactSupport
      hfc.mul_left
  have hd (t : ℝ) : HasDerivAt (fun s => (D + s * g) * f s)
      (g * f t + (D + t * g) * deriv f t) t := by
    convert (((hasDerivAt_id t).mul_const g).const_add D).mul
      ((hf.differentiable (by simp) t).hasDerivAt) using 1
    · rfl
    · simp
  have he := integral_eq_zero_of_hasDerivAt_of_integrable hd (hfi.add hdi) hpi
  simpa only [f, vertical_deriv hψ] using he

end SeifertSurfaces.QuasilinearProviderBridge.Helpers
