import A2MetricFluxV468

set_option autoImplicit false
open Set Matrix
open scoped ContDiff BigOperators
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.A2NativeTests
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.A2NativeNormalProjection
open SeifertSurfaces.OriginalEndpoints.A2MetricFlux
run_cmd do
  let pref := Lean.Name.num (`_private.A2MetricFluxV468) 0
  let n := (["SeifertSurfaces", "OriginalEndpoints", "A2MetricFlux"].foldl Lean.Name.str pref)
  Lean.Elab.Command.modifyScope fun s => { s with openDecls := .simple n [] :: s.openDecls }

/-- In the same actual rank-two metric tangent plane the outward metric
unit conormal is unique. Both signs are oriented towards the negative
second halfbox coordinate, as for the paid positive-halfbox formula. -/
theorem actual_outward_unit_conormal_unique (g : MetricTensor) (y : E3)
    (L : E2 →L[ℝ] E3) (hq : (metricGram g y L).PosDef) (v w : E2)
    (hvunit : coordinateInner g y (L v) (L v) = 1)
    (hwunit : coordinateInner g y (L w) (L w) = 1)
    (hvorth : coordinateInner g y (L v) (L (coordinateVector 2 0)) = 0)
    (hworth : coordinateInner g y (L w) (L (coordinateVector 2 0)) = 0)
    (hvout : v 1 < 0) (hwout : w 1 < 0) : L v = L w := by
  let q := metricGram g y L
  have hq00 : 0 < q 0 0 := hq.diag_pos
  have hqsym : q 1 0 = q 0 1 := by
    simpa only [star_trivial] using hq.isHermitian.apply 0 1
  have hvn : q 0 0 * v 0 * v 0 + 2 * q 0 1 * v 0 * v 1 + q 1 1 * v 1 * v 1 = 1 := by
    rw [gram_pullback] at hvunit
    change (∑ a : Fin 2, ∑ b : Fin 2, q a b * v a * v b) = 1 at hvunit
    simp only [Fin.sum_univ_two,hqsym] at hvunit
    nlinarith [hvunit]
  have hwn : q 0 0 * w 0 * w 0 + 2 * q 0 1 * w 0 * w 1 + q 1 1 * w 1 * w 1 = 1 := by
    rw [gram_pullback] at hwunit
    change (∑ a : Fin 2, ∑ b : Fin 2, q a b * w a * w b) = 1 at hwunit
    simp only [Fin.sum_univ_two,hqsym] at hwunit
    nlinarith [hwunit]
  have hvo : q 0 0 * v 0 + q 0 1 * v 1 = 0 := by
    rw [gram_pullback] at hvorth
    change (∑ a : Fin 2, ∑ b : Fin 2, q a b * v a * (coordinateVector 2 0) b) = 0 at hvorth
    simpa only [Fin.sum_univ_two, coordinateVector, EuclideanSpace.single_apply,
      if_true, if_false, Fin.isValue, zero_ne_one, one_ne_zero, hqsym,
      mul_one, mul_zero, add_zero, zero_add] using hvorth
  have hwo : q 0 0 * w 0 + q 0 1 * w 1 = 0 := by
    rw [gram_pullback] at hworth
    change (∑ a : Fin 2, ∑ b : Fin 2, q a b * w a * (coordinateVector 2 0) b) = 0 at hworth
    simpa only [Fin.sum_univ_two, coordinateVector, EuclideanSpace.single_apply,
      if_true, if_false, Fin.isValue, zero_ne_one, one_ne_zero, hqsym,
      mul_one, mul_zero, add_zero, zero_add] using hworth
  have hvdet : q.det * (v 1)^2 = q 0 0 := by
    have hn := congrArg (fun a : ℝ => q 0 0 * a) hvn
    have ho := congrArg (fun a : ℝ => a^2) hvo
    rw [Matrix.det_fin_two,hqsym]
    nlinarith only [hn,ho]
  have hwdet : q.det * (w 1)^2 = q 0 0 := by
    have hn := congrArg (fun a : ℝ => q 0 0 * a) hwn
    have ho := congrArg (fun a : ℝ => a^2) hwo
    rw [Matrix.det_fin_two,hqsym]
    nlinarith only [hn,ho]
  have hsq : (v 1)^2 = (w 1)^2 :=
    mul_left_cancel₀ hq.det_pos.ne' (hvdet.trans hwdet.symm)
  have he1 : v 1 = w 1 := by nlinarith only [hsq,hvout,hwout]
  have he0 : v 0 = w 0 := by
    apply mul_left_cancel₀ hq00.ne'
    rw [he1] at hvo
    linarith only [hvo,hwo]
  congr 1
  ext a
  fin_cases a
  · exact he0
  · exact he1

#print axioms actual_outward_unit_conormal_unique

/-- The conormal from the paid positive-halfbox formula is precisely any
native outward unit conormal in the same metric plane and halfbox frame. -/
theorem native_outward_conormal_eq_paid_halfbox_conormal (g : MetricTensor) (y : E3)
    (L : E2 →L[ℝ] E3) (hs : ∀ a b, g y a b = g y b a)
    (hq : (metricGram g y L).PosDef) (v : E2)
    (hvunit : coordinateInner g y (L v) (L v) = 1)
    (hvorth : coordinateInner g y (L v) (L (coordinateVector 2 0)) = 0)
    (hvout : v 1 < 0) :
    L v = metricConormal g y L (outwardCovector true) := by
  obtain ⟨hspd,hu,ho,⟨w,hw,hsign⟩,hflux⟩ := conormal_data g y L (fun _ => 0) true hs hq
  have hwout : w 1 < 0 := by
    have hsign' : 0 < -w 1 := by
      simpa [outwardCovector,coordinateVector,EuclideanSpace.inner_eq_star_dotProduct,
        dotProduct,Fin.sum_univ_two,EuclideanSpace.single_apply] using hsign
    linarith only [hsign']
  rw [← hw] at hu ho ⊢
  exact actual_outward_unit_conormal_unique g y L hq v w hvunit hu hvorth ho hvout hwout

#print axioms native_outward_conormal_eq_paid_halfbox_conormal
end SeifertSurfaces.OriginalEndpoints.A2NativeTests
