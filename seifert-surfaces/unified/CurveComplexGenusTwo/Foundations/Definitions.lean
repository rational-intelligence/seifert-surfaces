import Mathlib

/-!
Source: curve-complex-genus-two.pdf, Sections 1.1 and 2.1--2.4.
Candidate definitions; quotient well-definedness proofs are open obligations.
-/

namespace CurveComplex

open scoped Manifold ContDiff
open Topology

abbrev Interval := Set.Icc (0 : ℝ) 1

/-- A closed surface is a compact connected smooth two-manifold without boundary. -/
class ClosedSurface (S : Type*) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] : Prop extends
    T2Space S, CompactSpace S, ConnectedSpace S,
    IsManifold (𝓡 2) ∞ S

/-- A parametrized simple closed curve, considered by its image below. -/
structure Curve (S : Type*) [TopologicalSpace S] where
  map : Circle → S
  embedded : IsEmbedding map

def Curve.image {S : Type*} [TopologicalSpace S] (c : Curve S) : Set S :=
  Set.range c.map

/-- A topological ambient isotopy starts at the identity and is a homeomorphism
at every time. The endpoint operation is applied to subsets, so departure
directions and parametrizations are not fixed. -/
structure AmbientIsotopy (S : Type*) [TopologicalSpace S] where
  map : C(Interval × S, S)
  homeomorphism_at : ∀ t : Interval, ∃ h : S ≃ₜ S, ∀ x, h x = map (t, x)
  at_zero : ∀ x, map (⟨0, by norm_num⟩, x) = x

def AmbientIsotopy.finalMap {S : Type*} [TopologicalSpace S]
    (H : AmbientIsotopy S) (x : S) : S :=
  H.map (⟨1, by norm_num⟩, x)

def AmbientIsotopy.Rel {S : Type*} [TopologicalSpace S]
    (a b : Set S) : Prop :=
  ∃ H : AmbientIsotopy S, H.finalMap '' a = b

theorem ambientIsotopy_equivalence {S : Type*} [TopologicalSpace S] :
    Equivalence (AmbientIsotopy.Rel (S := S)) := by
  let zero : Interval := ⟨0, by norm_num⟩
  let one : Interval := ⟨1, by norm_num⟩
  let reverse : Interval → Interval := fun t =>
    ⟨1 - (t : ℝ), by
      rcases t.property with ⟨h0, h1⟩
      constructor <;> linarith⟩
  have reverse_cont : Continuous reverse :=
    (continuous_const.sub continuous_subtype_val).subtype_mk (fun t => (reverse t).property)
  let first : Interval → Interval := fun t =>
    ⟨min (2 * (t : ℝ)) 1, by
      rcases t.property with ⟨h0, h1⟩
      exact ⟨le_min (by linarith) (by norm_num), min_le_right _ _⟩⟩
  let second : Interval → Interval := fun t =>
    ⟨max (2 * (t : ℝ) - 1) 0, by
      rcases t.property with ⟨h0, h1⟩
      exact ⟨le_max_right _ _, max_le (by linarith) (by norm_num)⟩⟩
  have first_cont : Continuous first :=
    ((continuous_const.mul continuous_subtype_val).min continuous_const).subtype_mk
      (fun t => (first t).property)
  have second_cont : Continuous second :=
    (((continuous_const.mul continuous_subtype_val).sub continuous_const).max
      continuous_const).subtype_mk (fun t => (second t).property)
  have reverse_zero : reverse zero = one := Subtype.ext (by norm_num [reverse, zero, one])
  have reverse_one : reverse one = zero := Subtype.ext (by norm_num [reverse, zero, one])
  have first_zero : first zero = zero := Subtype.ext (by norm_num [first, zero])
  have first_one : first one = one := Subtype.ext (by norm_num [first, one])
  have second_zero : second zero = zero := Subtype.ext (by norm_num [second, zero])
  have second_one : second one = one := Subtype.ext (by norm_num [second, one])
  constructor
  · intro a
    refine ⟨{ map := ⟨fun p => p.2, continuous_snd⟩
              homeomorphism_at := ?_
              at_zero := by intro x; rfl }, ?_⟩
    · intro t
      exact ⟨Homeomorph.refl S, fun x => rfl⟩
    · change (id : S → S) '' a = a
      exact Set.image_id a
  · intro a b hab
    obtain ⟨H, hH⟩ := hab
    obtain ⟨h, hh⟩ := H.homeomorphism_at one
    have hfinal : ∀ x, h x = H.finalMap x := hh
    let K : AmbientIsotopy S := {
      map := ⟨fun p => H.map (reverse p.1, h.symm p.2), by
        exact H.map.continuous.comp
          ((reverse_cont.comp continuous_fst).prodMk
            (h.symm.continuous.comp continuous_snd))⟩
      homeomorphism_at := by
        intro t
        obtain ⟨g, hg⟩ := H.homeomorphism_at (reverse t)
        exact ⟨h.symm.trans g, fun x => by
          simpa [Homeomorph.trans_apply] using (hg (h.symm x))⟩
      at_zero := by
        intro x
        change H.map (reverse zero, h.symm x) = x
        rw [reverse_zero]
        rw [← hh]
        exact h.apply_symm_apply x }
    refine ⟨K, ?_⟩
    have hKfinal : ∀ x, K.finalMap x = h.symm x := by
      intro x
      change H.map (reverse one, h.symm x) = h.symm x
      rw [reverse_one]
      exact H.at_zero _
    simp_rw [hKfinal]
    have himage : h '' a = b := by
      simpa only [← hfinal] using hH
    rw [← himage]
    simp [Set.image_image]
  · intro a b c hab hbc
    obtain ⟨H, hH⟩ := hab
    obtain ⟨K, hK⟩ := hbc
    let L : AmbientIsotopy S := {
      map := ⟨fun p => K.map (second p.1, H.map (first p.1, p.2)), by
        exact K.map.continuous.comp
          ((second_cont.comp continuous_fst).prodMk
            (H.map.continuous.comp
              ((first_cont.comp continuous_fst).prodMk continuous_snd)))⟩
      homeomorphism_at := by
        intro t
        obtain ⟨h, hh⟩ := H.homeomorphism_at (first t)
        obtain ⟨k, hk⟩ := K.homeomorphism_at (second t)
        exact ⟨h.trans k, fun x => by simp [Homeomorph.trans_apply, hh, hk]⟩
      at_zero := by
        intro x
        change K.map (second zero, H.map (first zero, x)) = x
        rw [first_zero, second_zero]
        rw [H.at_zero, K.at_zero] }
    refine ⟨L, ?_⟩
    have hLfinal : ∀ x, L.finalMap x = K.finalMap (H.finalMap x) := by
      intro x
      change K.map (second one, H.map (first one, x)) =
        K.map (one, H.map (one, x))
      rw [first_one, second_one]
    simp_rw [hLfinal]
    change (K.finalMap ∘ H.finalMap) '' a = c
    rw [Set.image_comp, hH, hK]

def curveSetoid (S : Type*) [TopologicalSpace S] : Setoid (Curve S) where
  r a b := AmbientIsotopy.Rel a.image b.image
  iseqv := by
    exact ambientIsotopy_equivalence.comap Curve.image

abbrev CurveClass (S : Type*) [TopologicalSpace S] :=
  Quotient (curveSetoid S)

/-- An embedded closed disc witnessing inessentiality. -/
def BoundsDisc {S : Type*} [TopologicalSpace S] (c : Curve S) : Prop :=
  ∃ f : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, S),
    IsEmbedding f ∧
    f '' {x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 |
      (x : EuclideanSpace ℝ (Fin 2)) ∈ Metric.sphere 0 1} = c.image

def Essential {S : Type*} [TopologicalSpace S] (c : Curve S) : Prop :=
  ¬ BoundsDisc c

theorem essential_isotopy_invariant {S : Type*} [TopologicalSpace S]
    {a b : Curve S} (h : (curveSetoid S).r a b) :
    Essential a ↔ Essential b := by
  obtain ⟨H, hH⟩ := h
  let one : Interval := ⟨1, by norm_num⟩
  obtain ⟨e, he⟩ := H.homeomorphism_at one
  have hforward : e '' a.image = b.image := by
    have hefinal : (e : S → S) = H.finalMap := funext he
    rw [hefinal]
    exact hH
  have hback : e.symm '' b.image = a.image := by
    rw [← hforward]
    simp [Set.image_image]
  have transport (c d : Curve S) (g : S ≃ₜ S)
      (hg : g '' c.image = d.image) : BoundsDisc c → BoundsDisc d := by
    intro hc
    obtain ⟨f, hf, hboundary⟩ := hc
    refine ⟨⟨fun x => g (f x), g.continuous.comp f.continuous⟩,
      g.isEmbedding.comp hf, ?_⟩
    change (g ∘ (f : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 → S)) ''
      {x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 |
        (x : EuclideanSpace ℝ (Fin 2)) ∈ Metric.sphere 0 1} = d.image
    rw [Set.image_comp, hboundary, hg]
  constructor
  · intro ha hb
    exact ha (transport b a e.symm hback hb)
  · intro hb ha
    exact hb (transport a b e hforward ha)

abbrev EssentialCurve (S : Type*) [TopologicalSpace S] :=
  {c : Curve S // Essential c}

def essentialCurveSetoid (S : Type*) [TopologicalSpace S] :
    Setoid (EssentialCurve S) where
  r a b := (curveSetoid S).r a.val b.val
  iseqv := by
    exact (curveSetoid S).iseqv.comap Subtype.val

abbrev Vertex (S : Type*) [TopologicalSpace S] :=
  Quotient (essentialCurveSetoid S)

end CurveComplex
