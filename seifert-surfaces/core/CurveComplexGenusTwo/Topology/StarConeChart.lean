import CurveComplexGenusTwo.Topology.StarRadialCoordinates
import CurveComplexGenusTwo.Foundations.ConePairSDR

namespace CurveComplexGenusTwo.Topology

open CurveComplex Set
open unitInterval

variable {V : Type*} [DecidableEq V]

/-- The canonical barycentric map from the quotient cone on the realized link
to the realized closed star. Quotient well-definedness uses the proved
independence of the apex from the link coordinate. -/
noncomputable def closedStarConeMap
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (separating : V → Prop) (v : {u : V // separating u})
    (hfull : HasRealizedStarFaces K intersect v) :
    TopologicalCone (RealizedSeparatingLink K intersect separating v) →
      ClosedStarLocus K intersect v :=
  Quotient.lift
    (fun p : I × RealizedSeparatingLink K intersect separating v =>
      closedStarInterpolate K intersect v hfull p.1
        ⟨p.2.1, p.2.property.1⟩)
    (by
      intro p q hpq
      rcases hpq with hpq | ⟨hp, hq⟩
      · cases hpq
        rfl
      · rw [hp, hq]
        calc
          _ = closedStarApex K intersect v := by
            simpa using closedStarInterpolate_one K intersect v hfull
              (⟨p.2.1, p.2.property.1⟩ : ClosedStarLocus K intersect v)
          _ = _ := by
            symm
            simpa using closedStarInterpolate_one K intersect v hfull
              (⟨q.2.1, q.2.property.1⟩ : ClosedStarLocus K intersect v))

theorem closedStarConeMap_mk
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (separating : V → Prop) (v : {u : V // separating u})
    (hfull : HasRealizedStarFaces K intersect v)
    (t : I) (x : RealizedSeparatingLink K intersect separating v) :
    closedStarConeMap K intersect separating v hfull (topologicalConeMk t x) =
      closedStarInterpolate K intersect v hfull t ⟨x.1, x.property.1⟩ := rfl

theorem closedStarConeMap_base
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (separating : V → Prop) (v : {u : V // separating u})
    (hfull : HasRealizedStarFaces K intersect v)
    (x : RealizedSeparatingLink K intersect separating v) :
    closedStarConeMap K intersect separating v hfull (topologicalConeBase x) =
      ⟨x.1, x.property.1⟩ := by
  rw [topologicalConeBase, closedStarConeMap_mk]
  exact closedStarInterpolate_zero K intersect v hfull _

/-- Algebraic surjectivity of the cone chart. This theorem deliberately says
nothing about the quotient topology; continuity of the chart and inverse are
separate properties. -/
theorem closedStarConeMap_surjective
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (separating : V → Prop)
    (hsep : ∀ a b, separating a → separating b → a ≠ b →
      1 < intersect a b)
    (v : {u : V // separating u})
    (hfull : HasRealizedStarFaces K intersect v)
    (hne : Nonempty (RealizedSeparatingLink K intersect separating v)) :
    Function.Surjective (closedStarConeMap K intersect separating v hfull) := by
  intro x
  by_cases hx : x.1.weight v < 1
  · refine ⟨topologicalConeMk
      ⟨x.1.weight v, x.1.nonneg v, realization_weight_le_one K x.1 v⟩
      (radialLinkPoint K intersect separating hsep v x hx), ?_⟩
    rw [closedStarConeMap_mk]
    exact closedStar_radial_reconstruct K intersect separating hsep v hfull x hx
  · have hv : x.1.weight v = 1 :=
      le_antisymm (realization_weight_le_one K x.1 v) (le_of_not_gt hx)
    let l := Classical.choice hne
    refine ⟨topologicalConeApex l, ?_⟩
    rw [topologicalConeApex, closedStarConeMap_mk]
    calc
      _ = closedStarApex K intersect v := by
        simpa using closedStarInterpolate_one K intersect v hfull
          (⟨l.1, l.property.1⟩ : ClosedStarLocus K intersect v)
      _ = x := by
        apply Subtype.ext
        exact (realization_eq_vertex_of_weight_one K x.1 v hv).symm

omit [DecidableEq V] in
private theorem conePoint_ext_weight
    (K : AbstractSimplicialComplex V) {x y : RealizationPoint K}
    (h : x.weight = y.weight) : x = y := by
  cases x with
  | mk wx hx px =>
    cases y with
    | mk wy hy py =>
      cases h
      rfl

theorem closedStarConeMap_injective
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (separating : V → Prop) (v : {u : V // separating u})
    (hfull : HasRealizedStarFaces K intersect v) :
    Function.Injective (closedStarConeMap K intersect separating v hfull) := by
  intro c d hcd
  induction c using Quotient.inductionOn with
  | _ p =>
    induction d using Quotient.inductionOn with
    | _ q =>
      rcases p with ⟨t, x⟩
      rcases q with ⟨u, y⟩
      change topologicalConeMk t x = topologicalConeMk u y
      change closedStarInterpolate K intersect v hfull t
          ⟨x.1, x.property.1⟩ =
        closedStarInterpolate K intersect v hfull u
          ⟨y.1, y.property.1⟩ at hcd
      have ht : (t : ℝ) = (u : ℝ) := by
        have he := congrArg (fun z : ClosedStarLocus K intersect v =>
          z.1.weight v) hcd
        simp only [closedStarInterpolate_weight, coneWeight] at he
        have hxzero : x.1.weight v = 0 := x.property.2 v v.property
        have hyzero : y.1.weight v = 0 := y.property.2 v v.property
        simpa [hxzero, hyzero] using he
      have htu : t = u := Subtype.ext ht
      subst u
      by_cases htop : t = 1
      · apply Quotient.sound
        exact Or.inr ⟨htop, htop⟩
      · have hxyeq : x = y := by
          apply Subtype.ext
          apply conePoint_ext_weight K
          funext w
          by_cases hw : w = (v : V)
          · subst w
            exact (x.property.2 v v.property).trans
              (y.property.2 v v.property).symm
          · have he := congrArg (fun z : ClosedStarLocus K intersect v =>
                z.1.weight w) hcd
            simp only [closedStarInterpolate_weight, coneWeight,
              ite_eq_right hw, add_zero] at he
            have hfactor : (1 - (t : ℝ)) ≠ 0 := by
              intro hz
              have htone : (t : ℝ) = 1 := by linarith
              exact htop (Subtype.ext htone)
            exact mul_left_cancel₀ hfactor he
        subst y
        rfl

end CurveComplexGenusTwo.Topology
