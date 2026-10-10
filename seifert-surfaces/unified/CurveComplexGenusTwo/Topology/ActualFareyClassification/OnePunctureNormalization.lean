import CurveComplexGenusTwo.Topology.TorusStrip.PeriodicChartCrosscutIsotopy
import Mathlib

open Set Topology Schoenflies CurveComplex

/-- Any actual lattice-equivariant ambient isotopy can be normalized by the
actual motion of ONE puncture. This constructs an ambient isotopy fixing every
lift of that puncture throughout; no puncture-free operation disk is assumed.
The exact target translation is retained rather than silently discarded. -/
theorem equivariant_ambient_isotopy_pin_one_puncture
    (H : AmbientIsotopy Plane) (T : ℝ) (p : Plane)
    (heq : ∀ t (i : ℤ×ℤ) z,
      H.map (t,z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))=
        H.map (t,z)+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) :
    ∃ P : AmbientIsotopy Plane,
      (∀ t z, P.map (t,z)=H.map (t,z)-H.map (t,p)+p) ∧
      (∀ t (i : ℤ×ℤ) z,
        P.map (t,z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))=
          P.map (t,z)+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ∧
      (∀ t (i : ℤ×ℤ), P.map (t,p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))=
        p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ∧
      (∀ A : Set Plane, P.finalMap '' A=
        (fun z : Plane => z-H.finalMap p+p) '' (H.finalMap '' A)) := by
  let P : AmbientIsotopy Plane := {
    map := ⟨fun q => H.map (q.1,q.2)-H.map (q.1,p)+p,by fun_prop⟩
    homeomorphism_at := by
      intro t
      obtain ⟨e,he⟩ := H.homeomorphism_at t
      refine ⟨e.trans (Homeomorph.addRight (-H.map (t,p)+p)),?_⟩
      intro z
      change e z+(-H.map (t,p)+p)=H.map (t,z)-H.map (t,p)+p
      rw [he]
      abel
    at_zero := by
      intro z
      change H.map (⟨0,by norm_num⟩,z)-H.map (⟨0,by norm_num⟩,p)+p=z
      rw [H.at_zero,H.at_zero]
      abel }
  refine ⟨P,by intro t z; rfl,?_,?_,?_⟩
  · intro t i z
    change H.map (t,z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))-H.map (t,p)+p=
      H.map (t,z)-H.map (t,p)+p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)
    rw [heq]
    abel
  · intro t i
    change H.map (t,p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))-H.map (t,p)+p=
      p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)
    rw [heq]
    abel
  · intro A
    rw [←image_comp]
    rfl

/-- The normalized actual one-puncture move sends every old translated arc to
its explicit translated new arc. This exact identity can be used with the
correspondingly translated reference family in an intersection count. -/
theorem one_puncture_normalized_move_actual_full_orbit_targets
    (H : AmbientIsotopy Plane) (T : ℝ) (p : Plane) (A B : Set Plane)
    (heq : ∀ t (i : ℤ×ℤ) z,
      H.map (t,z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))=
        H.map (t,z)+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))
    (hmove : ∀ i : ℤ×ℤ, H.finalMap ''
      ((fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) '' A)=
      (fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) '' B) :
    ∃ P : AmbientIsotopy Plane,
      (∀ t (i : ℤ×ℤ), P.map (t,p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))=
        p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ∧
      (∀ t (i : ℤ×ℤ) z,
        P.map (t,z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))=
          P.map (t,z)+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ∧
      (∀ i : ℤ×ℤ, P.finalMap ''
        ((fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) '' A)=
        (fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ''
          ((fun z : Plane => z-H.finalMap p+p) '' B)) := by
  obtain ⟨P,hP,hPeq,hPfix,hPimage⟩ := equivariant_ambient_isotopy_pin_one_puncture H T p heq
  refine ⟨P,hPfix,hPeq,?_⟩
  intro i
  rw [hPimage,hmove,←image_comp,←image_comp]
  congr 1
  funext z
  dsimp only [Function.comp_apply]
  abel

#print axioms equivariant_ambient_isotopy_pin_one_puncture
#print axioms one_puncture_normalized_move_actual_full_orbit_targets
