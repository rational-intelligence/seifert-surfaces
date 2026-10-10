import Schoenflies.Inversion
import Schoenflies.JordanClosed
import Mathlib.Topology.Compactification.OnePoint.Sphere

namespace CurveComplex.SphereGapFinish

noncomputable section

open Filter Metric

/-- Inversion has a finite limit at infinity, namely its centre. The value at
the centre itself is irrelevant for the exterior restriction. -/
def invertAtInfinity (a : Schoenflies.Plane) :
    OnePoint Schoenflies.Plane → Schoenflies.Plane
  | .infty => a
  | .some x => Schoenflies.invert a x

theorem invertAtInfinity_continuousAt_infty (a : Schoenflies.Plane) :
    ContinuousAt (invertAtInfinity a) OnePoint.infty := by
  rw [OnePoint.continuousAt_infty']
  rw [coclosedCompact_eq_cocompact]
  apply tendsto_iff_dist_tendsto_zero.mpr
  convert tendsto_inv_atTop_zero.comp (tendsto_dist_right_cocompact_atTop a) using 1
  funext x
  exact Schoenflies.dist_invert_center a x

/-- The closed exterior together with the compactification point. -/
def compactifiedExterior (C : Set Schoenflies.Plane) :
    Set (OnePoint Schoenflies.Plane) :=
  {OnePoint.infty} ∪ OnePoint.some '' closure (Schoenflies.outside C)

theorem compactifiedExterior_isClosed (C : Set Schoenflies.Plane) :
    IsClosed (compactifiedExterior C) := by
  apply isOpen_compl_iff.mp
  have hcomp : (compactifiedExterior C)ᶜ =
      OnePoint.some '' (closure (Schoenflies.outside C))ᶜ := by
    ext x
    cases x with
    | infty => simp [compactifiedExterior]
    | coe y => simp [compactifiedExterior]
  rw [hcomp]
  exact OnePoint.isOpen_image_coe.mpr isClosed_closure.isOpen_compl

theorem compactifiedExterior_isCompact (C : Set Schoenflies.Plane) :
    IsCompact (compactifiedExterior C) :=
  (compactifiedExterior_isClosed C).isCompact

theorem invertAtInfinity_continuousOn_exterior
    (C : Set Schoenflies.Plane) (hC : Schoenflies.IsJordanCurve C)
    (a : Schoenflies.Plane) (ha : a ∈ Schoenflies.inside C) :
    ContinuousOn (invertAtInfinity a) (compactifiedExterior C) := by
  have hsep := Schoenflies.jordan_curve_theorem hC
  have hclosure : closure (Schoenflies.outside C) =
      Schoenflies.outside C ∪ C :=
    (Schoenflies.IsRegionOf.outside C).closure_eq hsep
  intro x hx
  cases x with
  | infty =>
    exact (invertAtInfinity_continuousAt_infty a).continuousWithinAt
  | coe x =>
    have hxext : x ∈ closure (Schoenflies.outside C) := by
      simpa [compactifiedExterior] using hx
    have hxa : x ≠ a := by
      rw [hclosure] at hxext
      rcases hxext with hout | hcurve
      · intro h; subst x
        exact (Set.disjoint_left.mp Schoenflies.disjoint_inside_outside ha) hout
      · intro h; subst x
        exact ha.1 hcurve
    exact (OnePoint.continuousAt_coe.mpr (by
      change ContinuousAt (Schoenflies.invert a) x
      exact Schoenflies.continuousAt_invert hxa)).continuousWithinAt

theorem invertAtInfinity_image_exterior
    (C : Set Schoenflies.Plane) (hC : Schoenflies.IsJordanCurve C)
    (a : Schoenflies.Plane) (ha : a ∈ Schoenflies.inside C) :
    invertAtInfinity a '' compactifiedExterior C =
      closure (Schoenflies.inside (Schoenflies.invert a '' C)) := by
  have hsep := Schoenflies.jordan_curve_theorem hC
  have hclosure : closure (Schoenflies.outside C) =
      C ∪ Schoenflies.outside C := by
    rw [(Schoenflies.IsRegionOf.outside C).closure_eq hsep, Set.union_comm]
  have hC' : Schoenflies.IsJordanCurve (Schoenflies.invert a '' C) :=
    hC.invert_image ha.1
  have htarget : closure (Schoenflies.inside (Schoenflies.invert a '' C)) =
      Schoenflies.invert a '' C ∪
        Schoenflies.inside (Schoenflies.invert a '' C) := by
    rw [(Schoenflies.IsRegionOf.inside _).closure_eq
      (Schoenflies.jordan_curve_theorem hC'), Set.union_comm]
  have himage : invertAtInfinity a '' compactifiedExterior C =
      {a} ∪ Schoenflies.invert a '' closure (Schoenflies.outside C) := by
    simp [compactifiedExterior, Set.image_image, invertAtInfinity]
  rw [himage, hclosure,
    Schoenflies.invert_image_union_outside
      (fun _ h => Schoenflies.arc_complement h) hC ha, htarget]
  have ha' := Schoenflies.mem_inside_invert_image
    (fun _ h => Schoenflies.arc_complement h) hC ha
  ext x
  by_cases hx : x = a
  · subst x
    simp [ha']
  · simp [hx]

private theorem exterior_ne_center
    (C : Set Schoenflies.Plane) (hC : Schoenflies.IsJordanCurve C)
    (a : Schoenflies.Plane) (ha : a ∈ Schoenflies.inside C)
    {x : Schoenflies.Plane}
    (hx : (x : OnePoint Schoenflies.Plane) ∈ compactifiedExterior C) :
    x ≠ a := by
  have hsep := Schoenflies.jordan_curve_theorem hC
  have hclosure : closure (Schoenflies.outside C) =
      Schoenflies.outside C ∪ C :=
    (Schoenflies.IsRegionOf.outside C).closure_eq hsep
  have hx' : x ∈ closure (Schoenflies.outside C) := by
    simpa [compactifiedExterior] using hx
  rw [hclosure] at hx'
  rcases hx' with hout | hcurve
  · intro h; subst x
    exact (Set.disjoint_left.mp Schoenflies.disjoint_inside_outside ha) hout
  · intro h; subst x
    exact ha.1 hcurve

theorem invertAtInfinity_injOn_exterior
    (C : Set Schoenflies.Plane) (hC : Schoenflies.IsJordanCurve C)
    (a : Schoenflies.Plane) (ha : a ∈ Schoenflies.inside C) :
    Set.InjOn (invertAtInfinity a) (compactifiedExterior C) := by
  intro x hx y hy hxy
  cases x with
  | infty =>
    cases y with
    | infty => rfl
    | coe y =>
      have hya := exterior_ne_center C hC a ha hy
      exact False.elim (hya (Schoenflies.invert_eq_center_iff.mp hxy.symm))
  | coe x =>
    cases y with
    | infty =>
      have hxa := exterior_ne_center C hC a ha hx
      exact False.elim (hxa (Schoenflies.invert_eq_center_iff.mp hxy))
    | coe y =>
      exact congrArg OnePoint.some (Schoenflies.invert_injective a hxy)

/-- The compactified closed exterior is homeomorphic to the closed interior
of the inverted Jordan curve. The continuous inverse follows from compactness
and injectivity of the explicit inversion map. -/
noncomputable def exteriorToInvertedInterior
    (C : Set Schoenflies.Plane) (hC : Schoenflies.IsJordanCurve C)
    (a : Schoenflies.Plane) (ha : a ∈ Schoenflies.inside C) :
    compactifiedExterior C ≃ₜ
      closure (Schoenflies.inside (Schoenflies.invert a '' C)) := by
  let f : compactifiedExterior C → Schoenflies.Plane :=
    fun z => invertAtInfinity a z
  letI : CompactSpace (compactifiedExterior C) :=
    isCompact_iff_compactSpace.mp (compactifiedExterior_isCompact C)
  have hcont : Continuous f :=
    (continuousOn_iff_continuous_domRestrict.mp
      (invertAtInfinity_continuousOn_exterior C hC a ha))
  have hinj : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext (invertAtInfinity_injOn_exterior C hC a ha x.property y.property hxy)
  have hemb : Topology.IsEmbedding f := (hcont.isClosedEmbedding hinj).isEmbedding
  have himage : Set.range f =
      closure (Schoenflies.inside (Schoenflies.invert a '' C)) := by
    rw [← invertAtInfinity_image_exterior C hC a ha]
    ext z
    simp [f, Set.mem_range, Set.mem_image]
  exact hemb.toHomeomorph.trans (Homeomorph.setCongr himage)

end

end CurveComplex.SphereGapFinish
