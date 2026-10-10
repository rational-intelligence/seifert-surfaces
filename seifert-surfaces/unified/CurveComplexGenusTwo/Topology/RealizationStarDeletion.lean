import CurveComplexGenusTwo.Topology.StarFaceAssembly

namespace CurveComplexGenusTwo.Topology

open CurveComplex Set

/-- The realized link is the part of a closed separating star lying in the
nonseparating core. This is the target of each local star deformation. -/
def RealizedSeparatingLink {V : Type*} [DecidableEq V]
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (separating : V → Prop) (v : V) : Set (RealizationPoint K) :=
  ClosedStarLocus K intersect v ∩ NonseparatingWeightLocus K separating

theorem realizedSeparatingLink_eq_inter {V : Type*} [DecidableEq V]
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (separating : V → Prop) (v : V) :
    ClosedStarLocus K intersect v ∩ NonseparatingWeightLocus K separating =
      RealizedSeparatingLink K intersect separating v := rfl

/-- Assemble the geometric realization version of simultaneous separating
star deletion. The only remaining input is the local deformation of each
actual realized star onto its realized link. The cover and cylinder topology
follow from the finite-face construction, even for infinitely many stars. -/
theorem realization_simultaneous_separating_star_deletion
    {V : Type*} [DecidableEq V] (K : AbstractSimplicialComplex V)
    (intersect : V → V → ℕ) (separating : V → Prop)
    (hcurve : ∀ σ : Finset V, σ ∈ K.faces → CurveFace intersect 1 σ)
    (hsep : ∀ a b, separating a → separating b → a ≠ b →
      1 < intersect a b)
    (hlocal : ∀ v : {u : V // separating u},
      IsStrongDeformationRetract
        {x : ClosedStarLocus K intersect v |
          (x : RealizationPoint K) ∈
            RealizedSeparatingLink K intersect separating v}) :
    IsStrongDeformationRetract (NonseparatingWeightLocus K separating) := by
  apply simultaneousStarDeletion
    (NonseparatingWeightLocus K separating)
    (fun v : {u : V // separating u} => ClosedStarLocus K intersect v)
    (fun v : {u : V // separating u} =>
      RealizedSeparatingLink K intersect separating v)
  · convert realization_core_stars_weak_cover K intersect separating hcurve using 1
    funext j
    cases j <;> rfl
  · intro v
    rfl
  · intro v w hvw
    exact closedStarLoci_overlap_in_core K intersect separating hsep v w hvw
  · exact hlocal
  · convert realization_core_stars_product_weak_cover K intersect separating hcurve using 1
    funext j
    cases j <;> rfl

end CurveComplexGenusTwo.Topology
