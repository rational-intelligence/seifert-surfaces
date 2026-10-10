import Section2.WeakRealization
import CurveComplexGenusTwo.Foundations.RealizationCW
import CurveComplexGenusTwo.Foundations.JoinFiniteSupport

/-!
Coordinate-preserving transport between the Section 2 weak realization and
the compiled generic realization in the neighboring curve-complex project.
The maps have explicit data; new proof fields and assertions remain obligations.
No statement asserts definitional equality of the two namespace copies.
-/

namespace SeifertSurfaces.TopologyAdapters

universe u w

variable {V : Type u}

/-- The same barycentric coordinates in the existing generic realization. -/
def toCurveRealization (K : AbstractSimplicialComplex V)
    (x : SeifertSurfaces.RealizationPoint K) : CurveComplex.RealizationPoint K where
  weight := x.weight
  nonneg := x.nonneg
  liesInFace := x.liesInFace

/-- The inverse coordinate reinterpretation. -/
def fromCurveRealization (K : AbstractSimplicialComplex V)
    (x : CurveComplex.RealizationPoint K) : SeifertSurfaces.RealizationPoint K where
  weight := x.weight
  nonneg := x.nonneg
  liesInFace := x.liesInFace

theorem toCurveRealization_weight (K : AbstractSimplicialComplex V)
    (x : SeifertSurfaces.RealizationPoint K) (v : V) :
    (toCurveRealization K x).weight v = x.weight v := by
  rfl

theorem fromCurveRealization_weight (K : AbstractSimplicialComplex V)
    (x : CurveComplex.RealizationPoint K) (v : V) :
    (fromCurveRealization K x).weight v = x.weight v := by
  rfl

theorem fromCurveRealization_toCurveRealization (K : AbstractSimplicialComplex V)
    (x : SeifertSurfaces.RealizationPoint K) :
    fromCurveRealization K (toCurveRealization K x) = x := by
  cases x
  rfl

theorem toCurveRealization_fromCurveRealization (K : AbstractSimplicialComplex V)
    (x : CurveComplex.RealizationPoint K) :
    toCurveRealization K (fromCurveRealization K x) = x := by
  cases x
  rfl

/-- This is compatibility of the actual finite-simplex charts. -/
theorem toCurveRealization_faceInclusion (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces) (p : SeifertSurfaces.FiniteSimplex σ) :
    toCurveRealization K (SeifertSurfaces.faceInclusion K σ hσ p) =
      CurveComplex.faceInclusion K σ hσ p := by
  rfl

theorem fromCurveRealization_faceInclusion (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces) (p : CurveComplex.FiniteSimplex σ) :
    fromCurveRealization K (CurveComplex.faceInclusion K σ hσ p) =
      SeifertSurfaces.faceInclusion K σ hσ p := by
  rfl

theorem continuous_toCurveRealization (K : AbstractSimplicialComplex V) :
    Continuous (toCurveRealization K) := by
  rw [continuous_def]
  intro U hU σ hσ
  change IsOpen ((toCurveRealization K ∘ SeifertSurfaces.faceInclusion K σ hσ) ⁻¹' U)
  have heq : toCurveRealization K ∘ SeifertSurfaces.faceInclusion K σ hσ =
      CurveComplex.faceInclusion K σ hσ := by
    funext p
    exact toCurveRealization_faceInclusion K σ hσ p
  rw [heq]
  exact hU σ hσ

theorem continuous_fromCurveRealization (K : AbstractSimplicialComplex V) :
    Continuous (fromCurveRealization K) := by
  rw [continuous_def]
  intro U hU σ hσ
  change IsOpen ((fromCurveRealization K ∘ CurveComplex.faceInclusion K σ hσ) ⁻¹' U)
  have heq : fromCurveRealization K ∘ CurveComplex.faceInclusion K σ hσ =
      SeifertSurfaces.faceInclusion K σ hσ := by
    funext p
    exact fromCurveRealization_faceInclusion K σ hσ p
  rw [heq]
  exact hU σ hσ

/-- The canonical coordinate-preserving homeomorphism for the weak topologies. -/
def weakRealizationHomeomorph (K : AbstractSimplicialComplex V) :
    SeifertSurfaces.RealizationPoint K ≃ₜ CurveComplex.RealizationPoint K where
  toFun := toCurveRealization K
  invFun := fromCurveRealization K
  left_inv := fromCurveRealization_toCurveRealization K
  right_inv := toCurveRealization_fromCurveRealization K
  continuous_toFun := continuous_toCurveRealization K
  continuous_invFun := continuous_fromCurveRealization K

theorem weakRealizationHomeomorph_weight (K : AbstractSimplicialComplex V)
    (x : SeifertSurfaces.RealizationPoint K) (v : V) :
    (weakRealizationHomeomorph K x).weight v = x.weight v := by
  rfl

theorem weakRealization_contractible_iff (K : AbstractSimplicialComplex V) :
    ContractibleSpace (SeifertSurfaces.RealizationPoint K) ↔
      ContractibleSpace (CurveComplex.RealizationPoint K) := by
  exact (weakRealizationHomeomorph K).contractibleSpace_iff

/-- The final topology can be used directly on the Section 2 type. -/
theorem weakRealization_continuous_iff_on_faces
    {Y : Type w} [TopologicalSpace Y] (K : AbstractSimplicialComplex V)
    (f : SeifertSurfaces.RealizationPoint K → Y) :
    Continuous f ↔ ∀ (σ : Finset V) (hσ : σ ∈ K.faces),
      Continuous (f ∘ SeifertSurfaces.faceInclusion K σ hσ) := by
  constructor
  · intro hf σ hσ
    have hc : Continuous (SeifertSurfaces.faceInclusion K σ hσ) := by
      rw [continuous_def]
      intro U hU
      exact hU σ hσ
    exact hf.comp hc
  · intro hf
    rw [continuous_def]
    intro U hU σ hσ
    exact (hf σ hσ).isOpen_preimage U hU

/-- Source Proposition A.1's compact finite support, in coordinate form.
The bound is a finite set of vertices, not a claim of local finiteness. -/
theorem compact_has_finite_vertex_support (K : AbstractSimplicialComplex V)
    (C : Set (SeifertSurfaces.RealizationPoint K)) (hC : IsCompact C) :
    ∃ F : Finset V, ∀ x ∈ C, ∀ v ∉ F, x.weight v = 0 := by
  classical
  obtain ⟨F, hF⟩ := CurveComplex.compact_realization_has_finite_support K
    (toCurveRealization K '' C) (hC.image (continuous_toCurveRealization K))
  refine ⟨F, ?_⟩
  intro x hx v hv
  by_contra hn
  exact hv (hF (toCurveRealization K x) ⟨x, hx, rfl⟩
    ((CurveComplex.mem_supportFinset_iff K (toCurveRealization K x) v).mpr hn))

end SeifertSurfaces.TopologyAdapters
