import CurveComplexGenusTwo.Dictionary.Genus
import CurveComplexGenusTwo.Dictionary.BranchedCover

/-!
Geometric objects in the six-marked sphere of §§2.2-2.3 and §4.
This module uses the foundation package's ambient isotopy and curve images.
-/

namespace CurveComplex

open Topology

/-- The actual source model: a genus-two total surface over a two-sphere. -/
structure HyperellipticModel (E : Type) (S : Type)
    [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] where
  cover : BranchedDoubleCover E S
  sphere : S ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
  genusTwo : IsGenus E 2

namespace HyperellipticModel

variable {E : Type} {S : Type}
  [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- A marked arc has no marked point in its interior. -/
structure MarkedArc (M : HyperellipticModel E S) where
  map : Interval → S
  continuous : Continuous map
  injective_except_loop_closure : ∀ t u, map t = map u →
    t = u ∨
      (t = ⟨0, by norm_num⟩ ∧ u = ⟨1, by norm_num⟩) ∨
      (t = ⟨1, by norm_num⟩ ∧ u = ⟨0, by norm_num⟩)
  start_marked : map ⟨0, by norm_num⟩ ∈ M.cover.branch
  end_marked : map ⟨1, by norm_num⟩ ∈ M.cover.branch
  marked_only_at_ends : ∀ t, map t ∈ M.cover.branch →
    t = ⟨0, by norm_num⟩ ∨ t = ⟨1, by norm_num⟩

def MarkedArc.image {M : HyperellipticModel E S} (a : MarkedArc M) : Set S :=
  Set.range a.map

/-- The non-loop arcs of Theorem 1.4. -/
abbrev NonLoopArc (M : HyperellipticModel E S) :=
  {a : MarkedArc M // a.map ⟨0, by norm_num⟩ ≠ a.map ⟨1, by norm_num⟩}

/-- Loop arcs are retained for Lemma 4.2(iii), but are outside the dictionary. -/
abbrev LoopArc (M : HyperellipticModel E S) :=
  {a : MarkedArc M // a.map ⟨0, by norm_num⟩ = a.map ⟨1, by norm_num⟩}

theorem NonLoopArc.injective {M : HyperellipticModel E S}
    (a : NonLoopArc M) : Function.Injective a.val.map := by
  intro t u h
  rcases a.val.injective_except_loop_closure t u h with h | h | h
  · exact h
  · rcases h with ⟨rfl, rfl⟩
    exact False.elim (a.property h)
  · rcases h with ⟨rfl, rfl⟩
    exact False.elim (a.property h.symm)

theorem NonLoopArc.image_inter_branch {M : HyperellipticModel E S}
    (a : NonLoopArc M) :
    a.val.image ∩ (M.cover.branch : Set S) =
      {a.val.map ⟨0, by norm_num⟩, a.val.map ⟨1, by norm_num⟩} := by
  ext x
  constructor
  · rintro ⟨⟨t, rfl⟩, ht⟩
    rcases a.val.marked_only_at_ends t ht with h | h
    · subst t
      simp
    · subst t
      simp
  · intro hx
    rcases Set.mem_insert_iff.mp hx with h | h
    · subst x
      exact ⟨⟨⟨0, by norm_num⟩, rfl⟩, a.val.start_marked⟩
    · have h' : x = a.val.map ⟨1, by norm_num⟩ := by simpa using h
      subst x
      exact ⟨⟨⟨1, by norm_num⟩, rfl⟩, a.val.end_marked⟩

theorem NonLoopArc.image_isCompact {M : HyperellipticModel E S}
    (a : NonLoopArc M) : IsCompact a.val.image := by
  change IsCompact (Set.range a.val.map)
  exact isCompact_range a.val.continuous

theorem NonLoopArc.isEmbedding {M : HyperellipticModel E S}
    (a : NonLoopArc M) : IsEmbedding a.val.map := by
  letI : T2Space S := M.sphere.symm.t2Space
  exact (a.val.continuous.isClosedEmbedding a.injective).isEmbedding

def NonLoopArc.image {M : HyperellipticModel E S} (a : NonLoopArc M) : Set S :=
  a.val.image

/-- A downstairs circle avoids all six branch points. -/
structure PuncturedCircle (M : HyperellipticModel E S) where
  curve : Curve S
  avoids_branch : Disjoint curve.image (M.cover.branch : Set S)

def PuncturedCircle.image {M : HyperellipticModel E S}
    (c : PuncturedCircle M) : Set S := c.curve.image

/-- The two connected complementary sides contain `m` and `n` marked points.
The Jordan curve theorem makes these sides unique up to exchange. -/
noncomputable def SplitsMarked (M : HyperellipticModel E S)
    (c : PuncturedCircle M) (m n : ℕ) : Prop := by
  classical
  exact ∃ U V : Set S,
    IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
    U.Nonempty ∧ V.Nonempty ∧ Disjoint U V ∧
    U ∪ V = c.imageᶜ ∧
    (M.cover.branch.filter (· ∈ U)).card = m ∧
    (M.cover.branch.filter (· ∈ V)).card = n

abbrev Circle33 (M : HyperellipticModel E S) :=
  {c : PuncturedCircle M // SplitsMarked M c 3 3}

abbrev Circle24 (M : HyperellipticModel E S) :=
  {c : PuncturedCircle M // SplitsMarked M c 2 4 ∨ SplitsMarked M c 4 2}

/-- Source Convention 2.1: an ambient isotopy fixes each branch point throughout. -/
def MarkedIsotopyRel (M : HyperellipticModel E S) (A B : Set S) : Prop :=
  ∃ H : AmbientIsotopy S,
    (∀ t b, b ∈ M.cover.branch → H.map (t, b) = b) ∧
    H.finalMap '' A = B

theorem markedIsotopy_equivalence (M : HyperellipticModel E S) :
    Equivalence (MarkedIsotopyRel M) := by
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
  · intro A
    refine ⟨{ map := ⟨fun p => p.2, continuous_snd⟩
              homeomorphism_at := ?_
              at_zero := by intro x; rfl }, ?_, ?_⟩
    · intro t
      exact ⟨Homeomorph.refl S, fun x => rfl⟩
    · intro t b hb
      rfl
    · change (id : S → S) '' A = A
      exact Set.image_id A
  · intro A B hAB
    obtain ⟨H, hfix, hH⟩ := hAB
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
    refine ⟨K, ?_, ?_⟩
    · intro t b hb
      have hhb : h b = b := by
        rw [hh]
        exact hfix one b hb
      have hs : h.symm b = b := by
        apply h.injective
        rw [h.apply_symm_apply, hhb]
      change H.map (reverse t, h.symm b) = b
      rw [hs]
      exact hfix (reverse t) b hb
    · have hKfinal : ∀ x, K.finalMap x = h.symm x := by
        intro x
        change H.map (reverse one, h.symm x) = h.symm x
        rw [reverse_one]
        exact H.at_zero _
      simp_rw [hKfinal]
      have himage : h '' A = B := by
        simpa only [← hfinal] using hH
      rw [← himage]
      simp [Set.image_image]
  · intro A B C hAB hBC
    obtain ⟨H, hHfix, hH⟩ := hAB
    obtain ⟨K, hKfix, hK⟩ := hBC
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
    refine ⟨L, ?_, ?_⟩
    · intro t b hb
      change K.map (second t, H.map (first t, b)) = b
      rw [hHfix (first t) b hb, hKfix (second t) b hb]
    · have hLfinal : ∀ x, L.finalMap x = K.finalMap (H.finalMap x) := by
        intro x
        change K.map (second one, H.map (first one, x)) =
          K.map (one, H.map (one, x))
        rw [first_one, second_one]
      simp_rw [hLfinal]
      change (K.finalMap ∘ H.finalMap) '' A = C
      rw [Set.image_comp, hH, hK]

def nonLoopArcSetoid (M : HyperellipticModel E S) : Setoid (NonLoopArc M) where
  r a b := MarkedIsotopyRel M a.image b.image
  iseqv := by
    exact (markedIsotopy_equivalence M).comap NonLoopArc.image

abbrev NonLoopArcClass (M : HyperellipticModel E S) :=
  Quotient (nonLoopArcSetoid M)

def circle33Setoid (M : HyperellipticModel E S) : Setoid (Circle33 M) where
  r a b := MarkedIsotopyRel M a.val.image b.val.image
  iseqv := by
    exact (markedIsotopy_equivalence M).comap (fun c : Circle33 M => c.val.image)

abbrev Circle33Class (M : HyperellipticModel E S) :=
  Quotient (circle33Setoid M)

/-- The auxiliary 2|4 circle class used to descend arc isotopies. -/
def circle24Setoid (M : HyperellipticModel E S) : Setoid (Circle24 M) where
  r a b := MarkedIsotopyRel M a.val.image b.val.image
  iseqv := by
    exact (markedIsotopy_equivalence M).comap (fun c : Circle24 M => c.val.image)

abbrev Circle24Class (M : HyperellipticModel E S) :=
  Quotient (circle24Setoid M)

/-- A disk neighborhood of an arc with exactly its endpoints marked. -/
structure ArcNeighborhood {M : HyperellipticModel E S} (a : NonLoopArc M) where
  closedSet : Set S
  disk : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ closedSet
  arc_inside : a.image ⊆ interior closedSet
  marked_inside : (M.cover.branch : Set S) ∩ closedSet =
    {a.val.map ⟨0, by norm_num⟩, a.val.map ⟨1, by norm_num⟩}
  boundary : PuncturedCircle M
  boundary_eq_frontier : boundary.image = frontier closedSet


end HyperellipticModel
end CurveComplex
