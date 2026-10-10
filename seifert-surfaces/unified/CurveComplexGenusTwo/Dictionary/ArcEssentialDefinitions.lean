import CurveComplexGenusTwo.Dictionary.MarkedSphere
import CurveComplexGenusTwo.Intersection.SmoothArc
import CurveComplexGenusTwo.Filtration.FinalAbutment
import CurveComplexGenusTwo.Filtration.FirstPageSplit
import CurveComplexGenusTwo.Filtration.E1BridgeAssembly
import CurveComplexGenusTwo.Filtration.PageComplex
import CurveComplexGenusTwo.Filtration.FiltrationSpectralObjectFull

/-! Candidate statement scaffold for Definitions 2.3, 2.5, 8.2, 8.4,
Lemma 8.5, Theorem 8.9, and Theorem 11.1 of curve-complex-genus-two.pdf. -/

namespace CurveComplex.HyperellipticModel

open CurveGenusTwo.Filtration
open CategoryTheory

set_option maxHeartbeats 400000

variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

private def startPoint {M : HyperellipticModel E S} (a : MarkedArc M) : S :=
  a.map ⟨0, by norm_num⟩

private def endPoint {M : HyperellipticModel E S} (a : MarkedArc M) : S :=
  a.map ⟨1, by norm_num⟩

/-- A complementary component, expressed without choosing its name. -/
def IsComplementComponent (a : Set S) (U : Set S) : Prop :=
  U.Nonempty ∧ IsConnected U ∧ U ⊆ aᶜ ∧
    ∀ V : Set S, IsConnected V → U ⊆ V → V ⊆ aᶜ → V = U

/-- Definition 2.3: for a loop, neither side may have only its endpoint marked.
For a non-loop arc, Observation 2.4 makes essentiality automatic. -/
def IsEssentialMarkedArc (M : HyperellipticModel E S) (a : MarkedArc M) : Prop :=
  startPoint a ≠ endPoint a ∨
    ∀ U : Set S, IsComplementComponent a.image U →
      ∃ b, b ∈ M.cover.branch ∧ b ∈ U

abbrev EssentialMarkedArc (M : HyperellipticModel E S) :=
  {a : MarkedArc M // IsEssentialMarkedArc M a}

def essentialArcSetoid (M : HyperellipticModel E S) : Setoid (EssentialMarkedArc M) where
  r a b := MarkedIsotopyRel M a.val.image b.val.image
  iseqv := (markedIsotopy_equivalence M).comap
    (fun a : EssentialMarkedArc M => a.val.image)

abbrev EssentialArcClass (M : HyperellipticModel E S) :=
  Quotient (essentialArcSetoid M)

noncomputable local instance (M : HyperellipticModel E S) :
    DecidableEq (EssentialArcClass M) := Classical.decEq _

noncomputable def arcEndpoints (M : HyperellipticModel E S)
    (a : EssentialMarkedArc M) : Finset S := by
  classical
  exact {startPoint a.val, endPoint a.val}

/-- Convention 2.1 fixes marked points throughout, hence fixes endpoint sets. -/
theorem arcEndpoints_isotopy_invariant (M : HyperellipticModel E S)
    (a b : EssentialMarkedArc M)
    (h : MarkedIsotopyRel M a.val.image b.val.image) :
    arcEndpoints M a = arcEndpoints M b := by
  classical
  have ends (c : EssentialMarkedArc M) (x : S) :
      x ∈ arcEndpoints M c ↔ x ∈ c.val.image ∧ x ∈ M.cover.branch := by
    constructor
    · intro hx
      simp only [arcEndpoints, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ⟨⟨⟨0, by norm_num⟩, rfl⟩, c.val.start_marked⟩
      · exact ⟨⟨⟨1, by norm_num⟩, rfl⟩, c.val.end_marked⟩
    · rintro ⟨⟨t, rfl⟩, ht⟩
      rcases c.val.marked_only_at_ends t ht with rfl | rfl <;>
        simp [arcEndpoints, startPoint, endPoint]
  obtain ⟨H, hfix, himage⟩ := h
  obtain ⟨e, he⟩ := H.homeomorphism_at ⟨1, by norm_num⟩
  have hinj : Function.Injective H.finalMap := by
    intro x y hxy
    apply e.injective
    simpa only [he, AmbientIsotopy.finalMap] using hxy
  ext x
  rw [ends a x, ends b x]
  constructor
  · rintro ⟨hx, hm⟩
    refine ⟨?_, hm⟩
    rw [← himage]
    exact ⟨x, hx, hfix ⟨1, by norm_num⟩ x hm⟩
  · rintro ⟨hx, hm⟩
    rw [← himage] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    have hyx : y = x := hinj (hxy.trans (hfix ⟨1, by norm_num⟩ x hm).symm)
    exact ⟨hyx ▸ hy, hm⟩

noncomputable def classEndpoints (M : HyperellipticModel E S) :
    EssentialArcClass M → Finset S :=
  Quotient.lift (arcEndpoints M) (arcEndpoints_isotopy_invariant M)

theorem classEndpoints_card (M : HyperellipticModel E S)
    (v : EssentialArcClass M) :
    (classEndpoints M v).card = 1 ∨ (classEndpoints M v).card = 2 := by
  classical
  induction v using Quotient.inductionOn with
  | h a =>
    change (arcEndpoints M a).card = 1 ∨ (arcEndpoints M a).card = 2
    by_cases h : startPoint a.val = endPoint a.val
    · left
      simp [arcEndpoints, h]
    · right
      simp [arcEndpoints, h]

noncomputable def actualArcLabels (M : HyperellipticModel E S) :
    ArcLabels (EssentialArcClass M) S where
  isLoop v := (classEndpoints M v).card = 1
  endpointPair := classEndpoints M
  nonloop_endpoint_card := by
    intro v hv
    rcases classEndpoints_card M v with h | h
    · exact False.elim (hv h)
    · exact h

/-- Interior excludes both marked endpoints, also for a loop. -/
def arcInterior (M : HyperellipticModel E S) (a : EssentialMarkedArc M) : Set S :=
  a.val.image \ (M.cover.branch : Set S)

/-- Definition 2.5: one simultaneous choice of pairwise interior-disjoint
representatives for the entire finite simplex. -/
def IsArcSimplex (M : HyperellipticModel E S)
    (σ : Finset (EssentialArcClass M)) : Prop :=
  ∃ representatives : (v : {v // v ∈ σ}) → EssentialMarkedArc M,
    (∀ v, Quotient.mk (essentialArcSetoid M) (representatives v) = v.val) ∧
    ∀ v w, v ≠ w →
      Disjoint (arcInterior M (representatives v))
        (arcInterior M (representatives w))

theorem arcSimplex_down (M : HyperellipticModel E S)
    {σ τ : Finset (EssentialArcClass M)}
    (h : τ ⊆ σ) (hσ : IsArcSimplex M σ) : IsArcSimplex M τ := by
  obtain ⟨r, hr, hd⟩ := hσ
  let lift : {v // v ∈ τ} → {v // v ∈ σ} := fun v => ⟨v.val, h v.property⟩
  refine ⟨fun v => r (lift v), fun v => hr (lift v), ?_⟩
  intro v w hvw
  apply hd
  intro heq
  apply hvw
  apply Subtype.ext
  exact congrArg (fun u : {v // v ∈ σ} => u.val) heq

noncomputable def actualA (M : HyperellipticModel E S) :
    FiniteComplex (EssentialArcClass M) where
  simplices := {σ | IsArcSimplex M σ}
  down_closed := by
    intro σ τ hsub hσ
    exact arcSimplex_down M hsub hσ


end CurveComplex.HyperellipticModel
