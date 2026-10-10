import CurveComplexGenusTwo.Topology.Basic
import Mathlib.Topology.CompactOpen
import CurveComplexGenusTwo.Foundations.GenericRealization

namespace CurveComplexGenusTwo.Topology

open Set

/-- Continuity out of a product can be checked on a weak cover of its first
factor when the second factor is locally compact. -/
theorem continuous_of_weakTopology_product
    {X Y Z I : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] [LocallyCompactSpace Y]
    (pieces : I → Set X) (hweak : HasWeakTopologyFromCover pieces)
    {f : X × Y → Z}
    (hf : ∀ i, Continuous (fun p : (pieces i) × Y => f (p.1.1, p.2))) :
    Continuous f := by
  have hvertical (x : X) : Continuous (fun y : Y => f (x, y)) := by
    have hx : x ∈ ⋃ i, pieces i := by rw [hweak.1]; trivial
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    convert (hf i).comp
      ((continuous_const : Continuous fun _ : Y => (⟨x, hi⟩ : pieces i)).prodMk continuous_id) using 1
    funext y
    rfl
  let F : X → C(Y, Z) := fun x => ⟨fun y => f (x, y), hvertical x⟩
  have hF : Continuous F := by
    rw [hweak.2, continuous_iSup_dom]
    intro i
    rw [continuous_coinduced_dom]
    have hi : Continuous (fun p : (pieces i) × Y => f (p.1.1, p.2)) := hf i
    have hc := (ContinuousMap.curry ⟨_, hi⟩).continuous
    convert hc using 1
    funext x
    rfl
  convert (ContinuousMap.continuous_uncurry_of_continuous ⟨F, hF⟩) using 1
  funext p
  rfl


end CurveComplexGenusTwo.Topology

namespace CurveComplex

open Set

theorem faceInclusion_surjective
    {V : Type*} {K : AbstractSimplicialComplex V}
    (x : RealizationPoint K) :
    ∃ (σ : Finset V) (hσ : σ ∈ K.faces) (p : FiniteSimplex σ),
      faceInclusion K σ hσ p = x := by
  rcases x.liesInFace with ⟨σ, hσ, hzero, hsum⟩
  let q : σ → ℝ := fun v => x.weight v
  have hq : (∀ v, 0 ≤ q v) ∧ ∑ v, q v = 1 := by
    constructor
    · intro v
      exact x.nonneg v
    · change (∑ v : σ, x.weight v) = 1
      simpa only [Finset.sum_attach, Finset.univ_eq_attach] using hsum
  let p : FiniteSimplex σ := ⟨q, hq⟩
  refine ⟨σ, hσ, p, ?_⟩
  have hw : (faceInclusion K σ hσ p).weight = x.weight := by
    funext v
    by_cases hv : v ∈ σ
    · simp [faceInclusion, p, q, hv]
    · simp [faceInclusion, p, q, hv, hzero v hv]
  cases x with
  | mk wx wn wl =>
    cases hface : faceInclusion K σ hσ p with
    | mk wy yn yl =>
      have hw' : wy = wx := by simpa [hface] using hw
      exact (RealizationPoint.mk.injEq wy yn yl wx wn wl).mpr hw'

end CurveComplex

namespace CurveComplexGenusTwo.Topology

open CurveComplex Set

theorem continuous_realization_product_of_faces
    {V : Type*} {K : AbstractSimplicialComplex V}
    {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    [LocallyCompactSpace Y]
    {f : RealizationPoint K × Y → Z}
    (hf : ∀ (σ : Finset V) (hσ : σ ∈ K.faces),
      Continuous (fun p : FiniteSimplex σ × Y =>
        f (faceInclusion K σ hσ p.1, p.2))) :
    Continuous f := by
  have hvertical (x : RealizationPoint K) : Continuous (fun y : Y => f (x, y)) := by
    rcases faceInclusion_surjective x with ⟨σ, hσ, p, hp⟩
    convert (hf σ hσ).comp
      ((continuous_const : Continuous fun _ : Y => p).prodMk continuous_id) using 1
    funext y
    simp only [Function.comp_apply, id_eq]
    rw [hp]
  let F : RealizationPoint K → C(Y, Z) := fun x =>
    ⟨fun y => f (x, y), hvertical x⟩
  have hF : Continuous F := by
    rw [continuous_def]
    intro U hU
    change ∀ (σ : Finset V) (hσ : σ ∈ K.faces),
      IsOpen ((faceInclusion K σ hσ) ⁻¹' F ⁻¹' U)
    intro σ hσ
    have hc := (ContinuousMap.curry
      ⟨fun p : FiniteSimplex σ × Y => f (faceInclusion K σ hσ p.1, p.2), hf σ hσ⟩).continuous
    have hp : Continuous (fun p : FiniteSimplex σ => F (faceInclusion K σ hσ p)) := by
      convert hc using 1
      funext p
      rfl
    exact hp.isOpen_preimage U hU
  convert (ContinuousMap.continuous_uncurry_of_continuous ⟨F, hF⟩) using 1
  funext p
  rfl

end CurveComplexGenusTwo.Topology

namespace CurveComplexGenusTwo.Topology

open CurveComplex

/-- Taking the product with a locally compact space preserves the final
topology of the weak realization over its finite faces. -/
theorem realization_product_topology_eq_final
    {V : Type*} (K : AbstractSimplicialComplex V)
    {Y : Type*} [TopologicalSpace Y] [LocallyCompactSpace Y] :
    (inferInstance : TopologicalSpace (RealizationPoint K × Y)) =
      ⨆ (σ : Finset V) (hσ : σ ∈ K.faces),
        TopologicalSpace.coinduced
          (fun p : FiniteSimplex σ × Y =>
            (faceInclusion K σ hσ p.1, p.2)) inferInstance := by
  let t : TopologicalSpace (RealizationPoint K × Y) :=
    ⨆ (σ : Finset V) (hσ : σ ∈ K.faces),
      TopologicalSpace.coinduced
        (fun p : FiniteSimplex σ × Y =>
          (faceInclusion K σ hσ p.1, p.2)) inferInstance
  change instTopologicalSpaceProd = t
  apply le_antisymm
  · rw [← continuous_id_iff_le]
    apply @continuous_realization_product_of_faces V K Y
      (RealizationPoint K × Y) _ t _
    intro σ hσ
    change Continuous (fun p : FiniteSimplex σ × Y =>
      (faceInclusion K σ hσ p.1, p.2))
    rw [show t = ⨆ (τ : Finset V) (hτ : τ ∈ K.faces),
      TopologicalSpace.coinduced
        (fun p : FiniteSimplex τ × Y =>
          (faceInclusion K τ hτ p.1, p.2)) inferInstance from rfl]
    exact continuous_iff_coinduced_le.mpr
      (le_iSup_of_le σ (le_iSup_of_le hσ le_rfl))
  · apply iSup_le
    intro σ
    apply iSup_le
    intro hσ
    have hface : Continuous (faceInclusion K σ hσ) := by
      rw [continuous_def]
      intro U hU
      exact hU σ hσ
    exact continuous_iff_coinduced_le.mp (hface.prodMap continuous_id)

end CurveComplexGenusTwo.Topology
