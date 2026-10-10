import TopologyAdapters.StarDeletionAdapter
import CurveComplexGenusTwo.Foundations.ConeRealization

/-!
Generic topology for the successor step of Theorem B (source PDF pp. 5--6).
These statements use the literal flag complex and genuine weak realization.
They apply to arbitrary vertex types and arbitrary infinite neighbor links.
-/

namespace SeifertSurfaces.TopologyAdapters

universe u w

variable {V : Type u}

private theorem fullToAmbient_supportedToFull_eq
    (K : AbstractSimplicialComplex V) (D : Set V) (x : fullSupportLocus K D) :
    fullToAmbient K D (supportedToFull K D x) = x.1 := by
  exact congrArg Subtype.val (fullToSupported_supportedToFull K D x)

private noncomputable def fullSupportInLargerHomeomorph
    (K : AbstractSimplicialComplex V) (D E : Set V) (hED : E ⊆ D) :
    SeifertSurfaces.RealizationPoint (SeifertSurfaces.fullSubcomplex K E) ≃ₜ
      fullSupportLocus (SeifertSurfaces.fullSubcomplex K D) {w : D | w.1 ∈ E} := by
  let forward (x : SeifertSurfaces.RealizationPoint (SeifertSurfaces.fullSubcomplex K E)) :
      fullSupportLocus (SeifertSurfaces.fullSubcomplex K D) {w : D | w.1 ∈ E} :=
    ⟨supportedToFull K D ⟨fullToAmbient K E x, by
      intro w hw
      exact fullToAmbient_weight_of_not_mem K E x w (fun he => hw (hED he))⟩, by
      intro w hw
      exact fullToAmbient_weight_of_not_mem K E x w.1 hw⟩
  let backward (x : fullSupportLocus (SeifertSurfaces.fullSubcomplex K D) {w : D | w.1 ∈ E}) :
      SeifertSurfaces.RealizationPoint (SeifertSurfaces.fullSubcomplex K E) :=
    supportedToFull K E ⟨fullToAmbient K D x.1, by
      intro w hw
      by_cases hwD : w ∈ D
      · rw [fullToAmbient_weight_of_mem K D x.1 w hwD]
        exact x.2 ⟨w, hwD⟩ hw
      · exact fullToAmbient_weight_of_not_mem K D x.1 w hwD⟩
  refine {
    toFun := forward
    invFun := backward
    left_inv := ?_
    right_inv := ?_
    continuous_toFun := ?_
    continuous_invFun := ?_ }
  · intro x
    apply fullToAmbient_injective K E
    change fullToAmbient K E (supportedToFull K E _) = fullToAmbient K E x
    exact (fullToAmbient_supportedToFull_eq K E _).trans
      (fullToAmbient_supportedToFull_eq K D _)
  · intro x
    apply Subtype.ext
    apply fullToAmbient_injective K D
    change fullToAmbient K D (supportedToFull K D _) = fullToAmbient K D x.1
    exact (fullToAmbient_supportedToFull_eq K D _).trans
      (fullToAmbient_supportedToFull_eq K E _)
  · exact ((continuous_supportedToFull K D).comp
      ((continuous_fullToAmbient K E).subtype_mk _)).subtype_mk _
  · exact (continuous_supportedToFull K E).comp
      (((continuous_fullToAmbient K D).comp continuous_subtype_val).subtype_mk _)

/-- The vertices of the closed star in a flag complex. -/
def closedNeighborhood (G : SimpleGraph V) (v : V) : Set V :=
  {w | w = v ∨ G.Adj v w}

/-- The actual closed-star locus, expressed as its full closed-neighborhood
subcomplex in the flag case. -/
def closedStarSupportLocus (K : AbstractSimplicialComplex V)
    (G : SimpleGraph V) (v : V) : Set (SeifertSurfaces.RealizationPoint K) :=
  fullSupportLocus K (closedNeighborhood G v)

theorem flag_realization_deletion_union_star
    (K : AbstractSimplicialComplex V) (G : SimpleGraph V)
    (hflag : SeifertSurfaces.IsFlagComplex G K) (v : V) :
    vertexDeletionLocus K v ∪ closedStarSupportLocus K G v = Set.univ := by
  classical
  apply Set.eq_univ_of_forall
  intro x
  by_cases hv : x.weight v = 0
  · exact Or.inl hv
  · right
    intro w hw
    obtain ⟨σ, hσ, hsupp, _⟩ := x.liesInFace
    have hvσ : v ∈ σ := by
      by_contra hn
      exact hv (hsupp v hn)
    by_cases hwσ : w ∈ σ
    · have hwv : w ≠ v := fun heq => hw (Or.inl heq)
      exact (hw (Or.inr (((hflag σ).mp hσ).2 hvσ hwσ hwv.symm))).elim
    · exact hsupp w hwσ

theorem flag_realization_deletion_inter_star
    (K : AbstractSimplicialComplex V) (G : SimpleGraph V)
    (hflag : SeifertSurfaces.IsFlagComplex G K) (v : V) :
    vertexDeletionLocus K v ∩ closedStarSupportLocus K G v =
      fullSupportLocus K (G.neighborSet v) := by
  ext x
  constructor
  · rintro ⟨hzero, hstar⟩ w hw
    change x.weight v = 0 at hzero
    by_cases heq : w = v
    · simpa only [heq] using hzero
    · exact hstar w (by simpa only [closedNeighborhood, Set.mem_setOf_eq, not_or] using ⟨heq, hw⟩)
  · intro hx
    refine ⟨hx v G.irrefl, ?_⟩
    intro w hw
    exact hx w (fun hadj => hw (Or.inr hadj))

/-- The full closed star is contractible by the literal cone-apex construction. -/
theorem flag_closed_star_contractible
    (K : AbstractSimplicialComplex V) (G : SimpleGraph V)
    (hflag : SeifertSurfaces.IsFlagComplex G K) (v : V) :
    ContractibleSpace (SeifertSurfaces.RealizationPoint
      (SeifertSurfaces.fullSubcomplex K (closedNeighborhood G v))) := by
  classical
  apply (weakRealization_contractible_iff _).mpr
  apply CurveComplex.coneApex_contractible _ ⟨v, Or.inl rfl⟩
  intro σ hσ
  apply (SeifertSurfaces.full_subcomplex_is_flag K G hflag (closedNeighborhood G v)
    (insert ⟨v, Or.inl rfl⟩ σ)).mpr
  refine ⟨Finset.insert_nonempty _ _, ?_⟩
  rw [Finset.coe_insert]
  apply ((SeifertSurfaces.full_subcomplex_is_flag K G hflag (closedNeighborhood G v)
    σ).mp hσ).2.insert
  intro w hw hne
  change G.Adj v w.1
  rcases w.2 with heq | hadj
  · exact (hne (Subtype.ext heq.symm)).elim
  · exact hadj

/-- Generic one-vertex successor: contractible deletion and neighbor link imply
contractibility of the whole flag complex. No nonempty premise is hidden:
each ContractibleSpace hypothesis itself entails nonemptiness. -/
theorem flag_complex_contractible_of_vertex_deletion
    (K : AbstractSimplicialComplex V) (G : SimpleGraph V)
    (hflag : SeifertSurfaces.IsFlagComplex G K) (v : V)
    (hdelete : ContractibleSpace (SeifertSurfaces.RealizationPoint
      (SeifertSurfaces.fullSubcomplex K {w | w ≠ v})))
    (hlink : ContractibleSpace
      (SeifertSurfaces.RealizationPoint (neighborLinkComplex K G v))) :
    ContractibleSpace (SeifertSurfaces.RealizationPoint K) := by
  apply contractible_of_sdr_and_contractible_subspace (vertexDeletionLocus K v)
    (weak_vertex_deletion_sdr K G hflag v hlink)
  rw [vertexDeletionLocus_eq_fullSupportLocus]
  exact (fullSubcomplex_contractible_iff_supported K {w | w ≠ v}).mp hdelete

/-- The source successor written literally as adjoining a vertex to a full
subcomplex. The link in the new complex has vertices `D ∩ N(v)`. -/
theorem adjoin_vertex_contractible
    (K : AbstractSimplicialComplex V) (G : SimpleGraph V)
    (hflag : SeifertSurfaces.IsFlagComplex G K) (D : Set V) (v : V)
    (hv : v ∉ D)
    (hdelete : ContractibleSpace
      (SeifertSurfaces.RealizationPoint (SeifertSurfaces.fullSubcomplex K D)))
    (hlink : ContractibleSpace (SeifertSurfaces.RealizationPoint
      (SeifertSurfaces.fullSubcomplex K (D ∩ G.neighborSet v)))) :
    ContractibleSpace (SeifertSurfaces.RealizationPoint
      (SeifertSurfaces.fullSubcomplex K (insert v D))) := by
  classical
  let A := insert v D
  let a : A := ⟨v, Set.mem_insert v D⟩
  let KA := SeifertSurfaces.fullSubcomplex K A
  let GA := G.induce A
  have hD : D ⊆ A := Set.subset_insert v D
  have hP : ({w : A | w ≠ a} : Set A) = {w | w.1 ∈ D} := by
    ext w
    change w ≠ a ↔ w.1 ∈ D
    constructor
    · intro hw
      rcases w.2 with heq | hm
      · exact (hw (Subtype.ext heq)).elim
      · exact hm
    · intro hw heq
      exact hv (by simpa only [congrArg Subtype.val heq] using hw)
  have hN : GA.neighborSet a = {w : A | w.1 ∈ D ∩ G.neighborSet v} := by
    ext w
    change G.Adj v w.1 ↔ w.1 ∈ D ∧ G.Adj v w.1
    refine ⟨fun hw => ⟨?_, hw⟩, And.right⟩
    rcases w.2 with heq | hm
    · exact (hw.ne heq.symm).elim
    · exact hm
  have hdelete' : ContractibleSpace (SeifertSurfaces.RealizationPoint
      (SeifertSurfaces.fullSubcomplex KA {w | w ≠ a})) := by
    apply (fullSubcomplex_contractible_iff_supported KA {w | w ≠ a}).mpr
    rw [hP]
    letI := hdelete
    exact (fullSupportInLargerHomeomorph K A D hD).symm.contractibleSpace
  have hlink' : ContractibleSpace (SeifertSurfaces.RealizationPoint
      (neighborLinkComplex KA GA a)) := by
    apply (fullSubcomplex_contractible_iff_supported KA (GA.neighborSet a)).mpr
    rw [hN]
    letI := hlink
    exact (fullSupportInLargerHomeomorph K A (D ∩ G.neighborSet v)
      (fun _ hw => hD hw.1)).symm.contractibleSpace
  exact flag_complex_contractible_of_vertex_deletion KA GA
    (SeifertSurfaces.full_subcomplex_is_flag K G hflag A) a hdelete' hlink'

/-- With an injective complexity and a largest vertex, deleting that vertex is
exactly taking the strict sublevel. This equality includes all other vertices. -/
theorem deletion_vertices_eq_strict_sublevel
    {W : Type w} [LinearOrder W] (c : V → W) (hc : Function.Injective c)
    (v : V) (hmax : ∀ w, c w ≤ c v) :
    {w : V | w ≠ v} = {w | c w < c v} := by
  ext w
  change w ≠ v ↔ c w < c v
  exact ⟨fun hw => lt_of_le_of_ne (hmax w) (fun h => hw (hc h)),
    fun hw heq => (ne_of_lt hw) (congrArg c heq)⟩

/-- In the same situation the full neighbor link is precisely the descending
link from Lemma 2.4, without changing vertex types or topologies. -/
theorem neighbor_vertices_eq_descending_link
    {W : Type w} [LinearOrder W] (G : SimpleGraph V) (c : V → W)
    (hc : Function.Injective c) (v : V) (hmax : ∀ w, c w ≤ c v) :
    G.neighborSet v = SeifertSurfaces.descendingLinkVertices G c v := by
  ext w
  change G.Adj v w ↔ G.Adj v w ∧ c w < c v
  refine ⟨fun hw => ⟨hw, ?_⟩, And.left⟩
  exact lt_of_le_of_ne (hmax w) (fun h => hw.ne (hc h).symm)

/-- The topological successor step in the exact complexity-sublevel form used
by Theorem B. Exchange axioms and ordinal induction supply the two hypotheses;
the gluing conclusion itself needs only flagness and an injective maximum. -/
theorem maximum_vertex_successor_contractible
    {W : Type w} [LinearOrder W]
    (K : AbstractSimplicialComplex V) (G : SimpleGraph V)
    (hflag : SeifertSurfaces.IsFlagComplex G K) (c : V → W)
    (hc : Function.Injective c) (v : V) (hmax : ∀ w, c w ≤ c v)
    (hdelete : ContractibleSpace (SeifertSurfaces.RealizationPoint
      (SeifertSurfaces.fullSubcomplex K {w | c w < c v})))
    (hlink : ContractibleSpace (SeifertSurfaces.RealizationPoint
      (SeifertSurfaces.fullSubcomplex K
        (SeifertSurfaces.descendingLinkVertices G c v)))) :
    ContractibleSpace (SeifertSurfaces.RealizationPoint K) := by
  apply flag_complex_contractible_of_vertex_deletion K G hflag v
  · rw [deletion_vertices_eq_strict_sublevel c hc v hmax]
    exact hdelete
  · change ContractibleSpace (SeifertSurfaces.RealizationPoint
      (SeifertSurfaces.fullSubcomplex K (G.neighborSet v)))
    rw [neighbor_vertices_eq_descending_link G c hc v hmax]
    exact hlink

end SeifertSurfaces.TopologyAdapters
