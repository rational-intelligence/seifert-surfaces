import CurveComplexGenusTwo.Foundations.FiniteSupportTopology

set_option maxHeartbeats 1000000

namespace CurveComplex

open Set unitInterval

variable {V : Type*} [DecidableEq V]

set_option linter.unusedSectionVars false

/-- A weak-realization homotopy is continuous once a finite output support is
known and all coordinates on that support are continuous. This is the
chartwise finite-support interface used by join contractions. -/
theorem continuous_joinFactorHomotopy_of_coordinates
    (K : AbstractSimplicialComplex V)
    (H : I × RealizationPoint K → RealizationPoint K)
    (F : Finset V)
    (hF : ∀ p : I × RealizationPoint K,
      H p ∈ finiteSupportLocus K F)
    (hcoord : ∀ w : F, Continuous (fun p => (H p).weight w.1)) :
    Continuous H := by
  apply continuous_of_finite_support_and_coordinates K F H hF
  intro w
  exact hcoord w

/-- Any set that meets every finite simplex in finitely many points is closed
in the weak realization. -/
theorem isClosed_of_facewiseFinite
    (K : AbstractSimplicialComplex V)
    (S : Set (RealizationPoint K))
    (hS : ∀ tau : Finset V, ∀ htau : tau ∈ K.faces,
      ((faceInclusion K tau htau) ⁻¹' S).Finite) :
    IsClosed S := by
  rw [← isOpen_compl_iff]
  change ∀ tau : Finset V, ∀ htau : tau ∈ K.faces,
    IsOpen ((faceInclusion K tau htau) ⁻¹' Sᶜ)
  intro tau htau
  rw [Set.preimage_compl]
  exact (hS tau htau).isClosed.isOpen_compl

/-- A compact subset with finite intersection with every finite face is
finite. The intermediate selected set is closed and discrete in the weak
topology, which is the obstruction to unbounded compact support. -/
theorem finite_of_compact_facewiseFinite
    (K : AbstractSimplicialComplex V)
    (S : Set (RealizationPoint K))
    (hcompact : IsCompact S)
    (hS : ∀ tau : Finset V, ∀ htau : tau ∈ K.faces,
      ((faceInclusion K tau htau) ⁻¹' S).Finite) :
    S.Finite := by
  have hdiscrete : IsDiscrete S := by
    apply isDiscrete_iff_forall_subset_exists_isOpen.mpr
    intro T hTS
    have hclosed : IsClosed (S \ T) := by
      apply isClosed_of_facewiseFinite K
      intro tau htau
      exact (hS tau htau).subset (by intro x hx; exact hx.1)
    refine ⟨(S \ T)ᶜ, hclosed.isOpen_compl, ?_⟩
    ext x
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_sdiff]
    constructor
    · rintro ⟨h, hx⟩
      by_contra hnot
      exact h ⟨hx, hnot⟩
    · intro hx
      exact ⟨fun hbad => hbad.2 hx, hTS hx⟩
  exact hcompact.finite hdiscrete

/-- Every compact set in the weak realization is contained in a finite
subcomplex. This is the support bound needed for homotopies whose domains are
finite simplex times a compact interval. -/
theorem compact_realization_has_finite_support
    (K : AbstractSimplicialComplex V)
    (C : Set (RealizationPoint K)) (hC : IsCompact C) :
    ∃ F : Finset V, ∀ x ∈ C, supportFinset K x ⊆ F := by
  classical
  let U : Set V := {v | ∃ x ∈ C, v ∈ supportFinset K x}
  have hU : U.Finite := by
    by_contra hfin
    have hinf : U.Infinite := hfin
    let e : ℕ ↪ U := hinf.natEmbedding U
    let v : ℕ → V := fun n => (e n).1
    have hv_inj : Function.Injective v := by
      intro n m h
      exact e.injective (Subtype.ext h)
    have hv_mem (n : ℕ) : v n ∈ U := (e n).2
    let x : ℕ → RealizationPoint K := fun n =>
      Classical.choose (hv_mem n)
    have hxC (n : ℕ) : x n ∈ C :=
      (Classical.choose_spec (hv_mem n)).1
    have hxv (n : ℕ) : v n ∈ supportFinset K (x n) :=
      (Classical.choose_spec (hv_mem n)).2
    let S : Set (RealizationPoint K) := Set.range x
    have hSsub : S ⊆ C := by
      rintro y ⟨n, rfl⟩
      exact hxC n
    have hSface : ∀ tau : Finset V, ∀ htau : tau ∈ K.faces,
        ((faceInclusion K tau htau) ⁻¹' S).Finite := by
      intro tau htau
      let N : Set ℕ := {n | x n ∈ faceCarrier K tau}
      have hN : N.Finite := by
        have hsub : N ⊆ v ⁻¹' (tau : Set V) := by
          intro n hn
          exact (mem_faceCarrier_iff_support_subset K tau (x n)).mp hn (hxv n)
        exact ((tau.finite_toSet).preimage hv_inj.injOn).subset hsub
      have hSf : (S ∩ faceCarrier K tau).Finite := by
        apply (hN.image x).subset
        rintro y ⟨⟨n, rfl⟩, hy⟩
        exact ⟨n, hy, rfl⟩
      apply (hSf.preimage (faceInclusion_injective K tau htau).injOn).subset
      intro p hp
      exact ⟨hp, by
        rw [faceCarrier_eq_range_faceInclusion K tau htau]
        exact ⟨p, rfl⟩⟩
    have hSclosed : IsClosed S := isClosed_of_facewiseFinite K S hSface
    have hScompact : IsCompact S := hC.of_isClosed_subset hSclosed hSsub
    have hSfinite : S.Finite :=
      finite_of_compact_facewiseFinite K S hScompact hSface
    have hused : (⋃ y ∈ S, (supportFinset K y : Set V)).Finite :=
      hSfinite.biUnion (fun y _ => (supportFinset K y).finite_toSet)
    have hrange : Set.range v ⊆ ⋃ y ∈ S, (supportFinset K y : Set V) := by
      rintro z ⟨n, rfl⟩
      exact Set.mem_iUnion.mpr ⟨x n,
        Set.mem_iUnion.mpr ⟨⟨n, rfl⟩, hxv n⟩⟩
    exact (Set.infinite_range_of_injective hv_inj)
      (hused.subset hrange)
  refine ⟨hU.toFinset, ?_⟩
  intro x hx w hw
  have : w ∈ U := ⟨x, hx, hw⟩
  simpa using this

end CurveComplex
