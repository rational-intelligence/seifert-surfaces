import Mathlib

/-!
# Topological and differential supports for Appendix C.11–C.12

Source: `references/seifert-surfaces.txt`, lines 2218–2281.
The maximum principle and geometric rank hypotheses are explicit inputs.
-/

noncomputable section
namespace SeifertSurfaces.AppendixC

variable {S L : Type*} [TopologicalSpace S] [TopologicalSpace L]

/-- The compactness/maximum-principle argument of C.11. The local-minimum
input is supplied by C.6 and the strong maximum principle, and is not assumed
to hold for arbitrary continuous functions. -/
theorem c11_barrier_from_local_minimum_principle
    [CompactSpace S] [ConnectedSpace S]
    (u : S → ℝ) (hu : Continuous u)
    (B : Set S) (hB : B.Nonempty) (hboundary : ∀ p ∈ B, u p = 0)
    (hminimum : ∀ p, u p < 0 → IsLocalMin u p →
      ∃ U : Set S, IsOpen U ∧ p ∈ U ∧ ∀ q ∈ U, u q = u p) :
    ∀ p, 0 ≤ u p := by
  intro p
  by_contra hp
  obtain ⟨a, _, hmin⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hu.continuousOn
  have ha : u a < 0 := lt_of_le_of_lt (hmin (Set.mem_univ p)) (lt_of_not_ge hp)
  have hopen : IsOpen {q | u q = u a} := by
    apply isOpen_iff_forall_mem_open.mpr
    intro q hq
    have hqmin : IsLocalMin u q := by
      apply IsMinOn.isLocalMin (s := Set.univ) _ Filter.univ_mem
      intro z _
      rw [hq]
      exact hmin (Set.mem_univ z)
    obtain ⟨U, hU, hqU, hconst⟩ := hminimum q (hq ▸ ha) hqmin
    exact ⟨U, fun z hz => (hconst z hz).trans hq, hU, hqU⟩
  have hall : {q | u q = u a} = Set.univ :=
    IsClopen.eq_univ ⟨isClosed_eq hu continuous_const, hopen⟩ ⟨a, rfl⟩
  obtain ⟨b, hb⟩ := hB
  have hbval : u b = u a := by
    have h : b ∈ {q | u q = u a} := hall ▸ Set.mem_univ b
    exact h
  exact (ne_of_lt ha) (hbval.symm.trans (hboundary b hb))

/-- C.12(i)'s connected-interior argument. `hnonzero` must still be obtained
from C.6's equality case and the nonconstant, onto boundary map in L1. -/
theorem c12i_positive_interior_from_zero_propagation
    (u : S → ℝ) (hu : Continuous u) (B : Set S)
    (hintconnected : IsConnected Bᶜ) (hintdense : Dense Bᶜ)
    (hnonneg : ∀ p, 0 ≤ u p) (hnonzero : ¬ ∀ p, u p = 0)
    (hpropagate : ∀ p ∈ Bᶜ, u p = 0 →
      ∃ U : Set S, IsOpen U ∧ p ∈ U ∧ ∀ q ∈ U ∩ Bᶜ, u q = 0) :
    ∀ p ∈ Bᶜ, 0 < u p := by
  let hconn : ConnectedSpace ↥(Bᶜ) := isConnected_iff_connectedSpace.mp hintconnected
  let Z : Set ↥(Bᶜ) := {p | u p = 0}
  have hclosed : IsClosed Z := isClosed_eq (hu.comp continuous_subtype_val) continuous_const
  have hopen : IsOpen Z := by
    apply isOpen_iff_forall_mem_open.mpr
    rintro ⟨p, hp⟩ hz
    obtain ⟨U, hU, hpU, hconst⟩ := hpropagate p hp hz
    exact ⟨Subtype.val ⁻¹' U, fun q hq => hconst q ⟨hq, q.2⟩,
      hU.preimage continuous_subtype_val, hpU⟩
  intro p hp
  refine lt_of_le_of_ne (hnonneg p) ?_
  intro hzero
  have hall : Z = Set.univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨⟨p, hp⟩, hzero.symm⟩
  have hinterior : Bᶜ ⊆ {q | u q = 0} := by
    intro q hq
    have h : (⟨q, hq⟩ : ↥(Bᶜ)) ∈ Z := hall ▸ Set.mem_univ _
    exact h
  have hfull := closure_minimal hinterior (isClosed_eq hu continuous_const)
  rw [hintdense.closure_eq] at hfull
  exact hnonzero fun q => hfull (Set.mem_univ q)

/-- The circle-map step of C.12(iv). A local homeomorphism with connected
fibers and surjective boundary image is a homeomorphism. -/
theorem c12iv_boundary_homeomorphism
    (f : S → L) (hlocal : IsLocalHomeomorph f)
    (honto : Function.Surjective f)
    (hfibers : ∀ y, IsConnected (f ⁻¹' {y})) :
    IsHomeomorph f := by
  refine ⟨hlocal.continuous, hlocal.isOpenMap, ?_, honto⟩
  intro a b hab
  let T := f ⁻¹' {f a}
  let hdiscimage : DiscreteTopology (f '' T) := by
    have hsub : (f '' T).Subsingleton := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact hx.trans hy.symm
    let : Subsingleton (f '' T) := ⟨fun a b => Subtype.ext (hsub a.2 b.2)⟩
    infer_instance
  let hdisc : DiscreteTopology T :=
    (hlocal.isLocalHomeomorphOn.mono (Set.subset_univ T)).discreteTopology_of_image
  let hconn : ConnectedSpace T := isConnected_iff_connectedSpace.mp (hfibers (f a))
  let : Subsingleton T := ⟨fun x y => isPreconnected_univ.subsingleton
    (Set.mem_univ x) (Set.mem_univ y)⟩
  exact congrArg Subtype.val (Subsingleton.elim (⟨a, rfl⟩ : T) ⟨b, hab.symm⟩)

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]

/-- The coordinate inverse-function-theorem bridge used in C.14.
`F` is the actual full-disc C¹ extension of the boundary chart map.
An injective differential has a linear left inverse in finite dimensions. -/
theorem c14_injective_differential_locally_injective
    (F : V → W) (U : Set V) (hU : IsOpen U) (p : V) (hp : p ∈ U)
    (hF : ContDiffOn ℝ 1 F U)
    (hrank : Function.Injective (fderiv ℝ F p)) :
    ∃ N : Set V, IsOpen N ∧ p ∈ N ∧ N ⊆ U ∧ Set.InjOn F N := by
  obtain ⟨g, hg⟩ := (fderiv ℝ F p).toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hrank)
  let G : W →L[ℝ] V := g.toContinuousLinearMap
  have hcomp : G.comp (fderiv ℝ F p) = ContinuousLinearMap.id ℝ V := by
    ext x
    exact LinearMap.congr_fun hg x
  have hstrict := G.hasStrictFDerivAt.comp p
    ((hF.contDiffAt (hU.mem_nhds hp)).hasStrictFDerivAt (by norm_num))
  rw [hcomp] at hstrict
  have hstrict' : HasStrictFDerivAt (fun x => G (F x))
      (ContinuousLinearEquiv.refl ℝ V : V →L[ℝ] V) p := hstrict
  let e := hstrict'.toOpenPartialHomeomorph (fun x => G (F x))
  refine ⟨e.source ∩ U, e.open_source.inter hU,
    ⟨hstrict'.mem_toOpenPartialHomeomorph_source, hp⟩, Set.inter_subset_right, ?_⟩
  intro x hx y hy hxy
  apply e.injOn hx.1 hy.1
  change G (F x) = G (F y)
  rw [hxy]

/-- Rank persistence in C.12(iv), expressed on the derivative rather than a
dummy immersion predicate. The manifold/chart bridge remains to be supplied. -/
theorem c12iv_injective_differential_open
    (F : V → W) (U : Set V) (hU : IsOpen U) (hF : ContDiffOn ℝ 1 F U) :
    IsOpen {p : V | p ∈ U ∧ Function.Injective (fderiv ℝ F p)} := by
  exact (hF.continuousOn_fderiv_of_isOpen hU (by norm_num)).isOpen_inter_preimage
    hU ContinuousLinearMap.isOpen_injective

end SeifertSurfaces.AppendixC
