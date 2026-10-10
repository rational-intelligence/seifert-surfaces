import A2MetricFluxV468

set_option autoImplicit false
open Set Matrix
open scoped BigOperators
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.A2NativeTests
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.A2MetricFlux
run_cmd do
  let pref := Lean.Name.num (`_private.A2MetricFluxV468) 0
  let n := (["SeifertSurfaces", "OriginalEndpoints", "A2MetricFlux"].foldl Lean.Name.str pref)
  Lean.Elab.Command.modifyScope fun s => { s with openDecls := .simple n [] :: s.openDecls }

/-- Positive definiteness of the actual pulled-back Gram matrix proves
injectivity of that same closed differential. -/
theorem actual_positive_gram_differential_injective (g : MetricTensor) (y : E3)
    (L : E2 →L[ℝ] E3) (hq : (metricGram g y L).PosDef) : Function.Injective L := by
  intro v w hvw
  by_contra hne
  let z := v-w
  have hz : z ≠ 0 := sub_ne_zero.mpr hne
  have hz' : z.ofLp ≠ 0 := by
    intro h
    apply hz
    exact WithLp.ofLp_injective 2 h
  have hp := hq.dotProduct_mulVec_pos hz'
  have he : L z = 0 := by simpa only [z,map_sub,hvw,sub_self]
  have hi : coordinateInner g y (L z) (L z) = 0 := by simp [he,coordinateInner]
  rw [gram_pullback] at hi
  have hp' : 0 < ∑ a : Fin 2, ∑ b : Fin 2, metricGram g y L a b * z a * z b := by
    convert hp using 1
    simp only [dotProduct,Matrix.mulVec,Pi.star_apply,star_trivial,Fin.sum_univ_two]
    ring
  exact hp'.ne' hi

#print axioms actual_positive_gram_differential_injective
end SeifertSurfaces.OriginalEndpoints.A2NativeTests
