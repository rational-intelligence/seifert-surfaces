import Section5RadialCompatibilityV489
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
noncomputable section
universe u v

theorem finite_germ_gluing {X : Type u} [TopologicalSpace X] {ι : Type v} [Finite ι]
    (S : Set X) (U W : ι → Set X) (f : ι → X → ℝ)
    (hW : ∀ i, IsOpen (W i)) (hWU : ∀ i, closure (W i) ⊆ U i)
    (hcover : S ⊆ ⋃ i, W i)
    (hagree : ∀ p ∈ S, ∀ i j, p ∈ U i → p ∈ U j → f i =ᶠ[𝓝 p] f j) :
    ∃ V : Set X, IsOpen V ∧ S ⊆ V ∧ ∃ F : X → ℝ,
      ∀ p ∈ V, ∃ i, p ∈ U i ∧ F =ᶠ[𝓝 p] f i := by
  classical
  let bad (i j : ι) := closure {x | x ∈ closure (W i) ∧ x ∈ closure (W j) ∧ f i x ≠ f j x}
  have hbad (p : X) (hp : p ∈ S) (i j : ι) : p ∉ bad i j := by
    intro hb
    have hi : p ∈ closure (W i) :=
      closure_minimal (fun x hx => hx.1) isClosed_closure hb
    have hj : p ∈ closure (W j) :=
      closure_minimal (fun x hx => hx.2.1) isClosed_closure hb
    have heq := hagree p hp i j (hWU i hi) (hWU j hj)
    obtain ⟨O,hO,hOo,hpO⟩ := mem_nhds_iff.mp heq
    obtain ⟨x,hxO,hx⟩ := mem_closure_iff.mp hb O hOo hpO
    exact hx.2.2 (hO hxO)
  let V := (⋃ i, W i) \ (⋃ i, ⋃ j, bad i j)
  have hV : IsOpen V :=
    (isOpen_iUnion hW).sdiff (isClosed_iUnion_of_finite (fun i =>
      isClosed_iUnion_of_finite (fun j => isClosed_closure)))
  have hSV : S ⊆ V := by
    intro p hp
    refine ⟨hcover hp,?_⟩
    simpa only [mem_iUnion,not_exists] using hbad p hp
  let F : X → ℝ := fun x => if h : ∃ i, x ∈ W i then f h.choose x else 0
  refine ⟨V,hV,hSV,F,?_⟩
  intro p hp
  obtain ⟨i,hi⟩ := mem_iUnion.mp hp.1
  refine ⟨i,hWU i (subset_closure hi),?_⟩
  filter_upwards [hV.mem_nhds hp,(hW i).mem_nhds hi] with x hxV hxi
  have hex : ∃ j, x ∈ W j := ⟨i,hxi⟩
  dsimp only [F]
  rw [dite_eq_left hex]
  by_contra hne
  apply hxV.2
  exact mem_iUnion.mpr ⟨hex.choose,mem_iUnion.mpr ⟨i,
    subset_closure ⟨subset_closure hex.choose_spec,subset_closure hxi,hne⟩⟩⟩

theorem compact_germ_gluing {X : Type u} [TopologicalSpace X] [RegularSpace X]
    {ι : Type v} (S : Set X) (hS : IsCompact S)
    (U : ι → Set X) (f : ι → X → ℝ)
    (hU : ∀ i, IsOpen (U i)) (hcover : S ⊆ ⋃ i, U i)
    (hagree : ∀ p ∈ S, ∀ i j, p ∈ U i → p ∈ U j → f i =ᶠ[𝓝 p] f j) :
    ∃ V : Set X, IsOpen V ∧ S ⊆ V ∧ ∃ F : X → ℝ,
      ∀ p ∈ V, ∃ i, p ∈ U i ∧ F =ᶠ[𝓝 p] f i := by
  classical
  have hx (p : S) : ∃ i, p.val ∈ U i := mem_iUnion.mp (hcover p.property)
  choose idx hidx using hx
  have hsmall (p : S) : ∃ W : Set X, p.val ∈ W ∧ IsOpen W ∧ closure W ⊆ U (idx p) := by
    obtain ⟨W,⟨hp,hWo⟩,hsub⟩ := (hasBasis_opens_closure p.val).mem_iff.mp
      ((hU (idx p)).mem_nhds (hidx p))
    exact ⟨W,hp,hWo,hsub⟩
  choose W hWp hWo hWU using hsmall
  have hcov : S ⊆ ⋃ p : S, W p := fun p hp => mem_iUnion.mpr ⟨⟨p,hp⟩,hWp ⟨p,hp⟩⟩
  obtain ⟨t,ht⟩ := hS.elim_finite_subcover W hWo hcov
  let U' : t → Set X := fun i => U (idx i.val)
  let W' : t → Set X := fun i => W i.val
  let f' : t → X → ℝ := fun i => f (idx i.val)
  have hcov' : S ⊆ ⋃ i : t, W' i := by
    intro p hp
    obtain ⟨i,hi,hip⟩ := mem_iUnion₂.mp (ht hp)
    exact mem_iUnion.mpr ⟨⟨i,hi⟩,hip⟩
  obtain ⟨V,hV,hSV,F,hF⟩ := finite_germ_gluing S U' W' f'
    (fun i => hWo i.val) (fun i => hWU i.val) hcov'
    (fun p hp i j hi hj => hagree p hp (idx i.val) (idx j.val) hi hj)
  refine ⟨V,hV,hSV,F,?_⟩
  intro p hp
  obtain ⟨i,hi,hFi⟩ := hF p hp
  exact ⟨idx i.val,hi,hFi⟩

#print axioms compact_germ_gluing
end
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
