import Section5GeometricDefinitions

set_option autoImplicit false
noncomputable section
open Set Topology Function
open scoped Manifold ContDiff

namespace SeifertSurfaces.OriginalEndpoints.Section5.WholeAssemblyV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.GenusLinking SeifertSurfaces.Complexity
open SeifertSurfaces.OriginalEndpoints.Section4

variable {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)

/-- The real-area lexicographic relation is exactly the native positive-area relation. -/
theorem native_complexity_lt_iff (H : SourceGeometry E) (v w : Vertices E) :
    Section4.complexity E H v < Section4.complexity E H w ↔
      SeifertSurfaces.Section5.Combinatorics.complexity (vertexGenus E) (areaInfimum E H) v <
      SeifertSurfaces.Section5.Combinatorics.complexity (vertexGenus E) (areaInfimum E H) w := by
  simp only [Prod.Lex.lt_iff]
  rfl

/-- Every part of Proposition 5.2 is assembled using the fixed native exchange
outputs, with one descended vertex valid for every integer genus cutoff. -/
theorem whole_proposition52 (H : SourceGeometry E)
    (hconnected : (oneSkeleton.{0} E).Connected)
    (hflag : Flag E (complexFaces E))
    (hwell : IsWellOrder (attainedValues E H) (· < ·))
    (hexchange : SeifertSurfaces.Section5.Combinatorics.HasExchangePairs
      (oneSkeleton E) (vertexGenus E) (areaInfimum E H)) :
    (∀ u w : Vertices E, graphDistance E u w = 2 →
    (∃ x : Vertices E, Apex E u w x) ∧
    (∀ x : Vertices E, x ∈ commonNeighbors E u w →
      ∀ up down : Vertices E, ExchangePair E H x u w up down →
        Apex E u w up ∧ Apex E u w down) ∧
    (∃ x : Vertices E, Apex E u w x ∧
      Section4.complexity E H x < max (Section4.complexity E H u) (Section4.complexity E H w) ∧
      ∀ ell : ℤ, (vertexGenus E u : ℤ) ≤ ell → (vertexGenus E w : ℤ) ≤ ell →
        (vertexGenus E x : ℤ) ≤ ell)) ∧
    ExchangeComplex E H := by
  letI := hwell
  have hwNative : WellFounded (fun v w : Vertices E =>
      Section4.complexity E H v < Section4.complexity E H w) :=
    InvImage.wf (fun v => (⟨Section4.complexity E H v, ⟨v, rfl⟩⟩ : attainedValues E H))
      (IsWellOrder.wf (r := (· < ·)))
  have hwReal : WellFounded (fun v w : Vertices E =>
      SeifertSurfaces.Section5.Combinatorics.complexity (vertexGenus E) (areaInfimum E H) v <
      SeifertSurfaces.Section5.Combinatorics.complexity (vertexGenus E) (areaInfimum E H) w) :=
    hwNative.mono (fun v w h => (native_complexity_lt_iff E H v w).mpr h)
  have hdesc : ∀ u w : Vertices E, graphDistance E u w = 2 →
      ∃ x : Vertices E, Apex E u w x ∧
        Section4.complexity E H x < max (Section4.complexity E H u) (Section4.complexity E H w) ∧
        ∀ ell : ℤ, (vertexGenus E u : ℤ) ≤ ell → (vertexGenus E w : ℤ) ≤ ell →
          (vertexGenus E x : ℤ) ≤ ell := by
    intro u w hd
    obtain ⟨x, hx, hlt, hgen⟩ :=
      SeifertSurfaces.Section5.Combinatorics.descending_apex_of_exchange
        (oneSkeleton E) (vertexGenus E) (areaInfimum E H) hexchange hwReal u w hd
    refine ⟨x, hx, ?_, ?_⟩
    · rcases lt_max_iff.mp hlt with hu | hw
      · exact lt_max_iff.mpr (Or.inl ((native_complexity_lt_iff E H x u).mpr hu))
      · exact lt_max_iff.mpr (Or.inr ((native_complexity_lt_iff E H x w).mpr hw))
    · intro ell hu hw
      have hm : vertexGenus E x ≤ max (vertexGenus E u) (vertexGenus E w) :=
        hgen _ (le_max_left _ _) (le_max_right _ _)
      omega
  constructor
  · intro u w hd
    obtain ⟨x, hx, hlt, hgen⟩ := hdesc u w hd
    refine ⟨⟨x, hx⟩, ?_, ⟨x, hx, hlt, hgen⟩⟩
    intro center _ up down hp
    exact SeifertSurfaces.Section5.Combinatorics.exchange_pair_outputs_are_apices
      (oneSkeleton E) (vertexGenus E) (areaInfimum E H) center u w up down hd hp
  · refine ⟨hconnected.nonempty, hconnected, hflag, hwell, ?_, ?_⟩
    · intro u w hd
      obtain ⟨x, hx, _⟩ := hdesc u w hd
      exact ⟨x, hx⟩
    · intro u w hd
      obtain ⟨x, hx, hlt, _⟩ := hdesc u w hd
      exact ⟨x, hx, hlt⟩

end SeifertSurfaces.OriginalEndpoints.Section5.WholeAssemblyV480
