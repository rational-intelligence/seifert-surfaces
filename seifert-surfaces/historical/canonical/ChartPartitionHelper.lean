import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Order.Disjointed
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Topology.Compactness.Compact

open Set Topology MeasureTheory

noncomputable section
namespace SeifertSurfaces.MetricFoundations

lemma finite_measurable_partition_subordinate
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (U : X → Set X) (hopen : ∀ x, IsOpen (U x)) (hmem : ∀ x, x ∈ U x) :
    ∃ (n : ℕ) (center : Fin n → X) (piece : Fin n → Set X),
      (∀ i, MeasurableSet (piece i)) ∧ (∀ i, piece i ⊆ U (center i)) ∧
      Pairwise (fun i j => Disjoint (piece i) (piece j)) ∧
      (⋃ i, piece i) = univ := by
  classical
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hopen (by
    intro x _
    exact mem_iUnion.mpr ⟨x, hmem x⟩)
  let center : Fin t.card → X := fun i => (t.equivFin.symm i : X)
  let V : Fin t.card → Set X := fun i => U (center i)
  have hmeas : ∀ i, MeasurableSet (V i) := fun i => (hopen (center i)).measurableSet
  have hcover : (⋃ i, V i) = univ := by
    apply Subset.antisymm (subset_univ _)
    intro x hx
    rcases mem_iUnion.mp (ht hx) with ⟨y, hy⟩
    rcases mem_iUnion.mp hy with ⟨hyt, hxy⟩
    refine mem_iUnion.mpr ⟨t.equivFin ⟨y, hyt⟩, ?_⟩
    simpa only [V, center, Equiv.symm_apply_apply] using hxy
  refine ⟨t.card, center, disjointed V, ?_, disjointed_subset V,
    disjoint_disjointed V, ?_⟩
  · intro i
    rw [disjointed_eq_inter_compl]
    exact (hmeas i).inter (MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun _ => (hmeas j).compl)
  · rw [iUnion_disjointed]
    exact hcover

end SeifertSurfaces.MetricFoundations
