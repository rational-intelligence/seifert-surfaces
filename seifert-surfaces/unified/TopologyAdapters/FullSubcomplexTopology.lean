import TopologyAdapters.WeakBridge
import Section2.FlagComplex
import CurveComplexGenusTwo.Foundations.FullSubcomplex

/-!
The literal full subcomplex from Section 2 is identified with its supported
barycentric locus using the weak subspace topology. All vertex sets can be
infinite. The explicit coordinate maps are zero extension and restriction.
-/

namespace SeifertSurfaces.TopologyAdapters

universe u w

variable {V : Type u}

private theorem fullComplex_eq [DecidableEq V]
    (K : AbstractSimplicialComplex V) (D : Set V) :
    SeifertSurfaces.fullSubcomplex K D = CurveComplex.fullSubcomplex K (fun v => v ∈ D) := by
  ext σ
  change σ.map (Function.Embedding.subtype D) ∈ K.faces ↔
    σ.image Subtype.val ∈ K.faces
  rw [Finset.map_eq_image]
  rfl

private theorem weakPoint_ext {K : AbstractSimplicialComplex V}
    {x y : SeifertSurfaces.RealizationPoint K} (h : x.weight = y.weight) : x = y := by
  cases x
  cases y
  cases h
  rfl

private def complexRealizationHomeomorph (K L : AbstractSimplicialComplex V)
    (h : K = L) : CurveComplex.RealizationPoint K ≃ₜ CurveComplex.RealizationPoint L := by
  subst L
  exact Homeomorph.refl _

private theorem complexRealizationHomeomorph_weight (K L : AbstractSimplicialComplex V)
    (h : K = L) (x : CurveComplex.RealizationPoint K) (v : V) :
    (complexRealizationHomeomorph K L h x).weight v = x.weight v := by
  subst L
  rfl

/-- The ambient points whose coordinates outside `D` vanish. -/
def fullSupportLocus (K : AbstractSimplicialComplex V) (D : Set V) :
    Set (SeifertSurfaces.RealizationPoint K) :=
  {x | ∀ v, v ∉ D → x.weight v = 0}

/-- Zero extension of coordinates from a full subcomplex. -/
noncomputable def fullToAmbient (K : AbstractSimplicialComplex V) (D : Set V)
    (x : SeifertSurfaces.RealizationPoint (SeifertSurfaces.fullSubcomplex K D)) :
    SeifertSurfaces.RealizationPoint K := by
  classical
  exact {
    weight := fun v => if hv : v ∈ D then x.weight ⟨v, hv⟩ else 0
    nonneg := by
      intro v
      split_ifs with hv
      · exact x.nonneg _
      · exact le_refl _
    liesInFace := by
      obtain ⟨σ, hσ, hz, hs⟩ := x.liesInFace
      refine ⟨σ.map (Function.Embedding.subtype D), hσ, ?_, ?_⟩
      · intro v hv
        by_cases hp : v ∈ D
        · simp only [dite_eq_left hp]
          apply hz
          intro hm
          exact hv (Finset.mem_map.mpr ⟨⟨v, hp⟩, hm, rfl⟩)
        · simp [hp]
      · rw [Finset.sum_map]
        calc
          (∑ v ∈ σ, if hv : v.1 ∈ D then x.weight ⟨v.1, hv⟩ else 0) =
              ∑ v ∈ σ, x.weight v := by
                apply Finset.sum_congr rfl
                intro v hv
                simp [v.property]
          _ = 1 := hs }

theorem fullToAmbient_weight_of_mem (K : AbstractSimplicialComplex V)
    (D : Set V)
    (x : SeifertSurfaces.RealizationPoint (SeifertSurfaces.fullSubcomplex K D))
    (v : V) (hv : v ∈ D) :
    (fullToAmbient K D x).weight v = x.weight ⟨v, hv⟩ := by
  classical
  simp [fullToAmbient, hv]

theorem fullToAmbient_weight_of_not_mem (K : AbstractSimplicialComplex V)
    (D : Set V)
    (x : SeifertSurfaces.RealizationPoint (SeifertSurfaces.fullSubcomplex K D))
    (v : V) (hv : v ∉ D) :
    (fullToAmbient K D x).weight v = 0 := by
  classical
  simp [fullToAmbient, hv]

/-- The same zero extension, with its support condition bundled. -/
noncomputable def fullToSupported (K : AbstractSimplicialComplex V) (D : Set V)
    (x : SeifertSurfaces.RealizationPoint (SeifertSurfaces.fullSubcomplex K D)) :
    fullSupportLocus K D :=
  ⟨fullToAmbient K D x, by
    intro v hv
    exact fullToAmbient_weight_of_not_mem K D x v hv⟩

/-- Restriction of the ambient coordinates to the selected vertices. -/
def supportedToFull (K : AbstractSimplicialComplex V) (D : Set V)
    (x : fullSupportLocus K D) :
    SeifertSurfaces.RealizationPoint (SeifertSurfaces.fullSubcomplex K D) where
  weight := fun v => x.1.weight v.1
  nonneg := fun v => x.1.nonneg v.1
  liesInFace := by
    classical
    rw [fullComplex_eq K D]
    exact (CurveComplex.supportedToFull K (fun v => v ∈ D)
      ⟨toCurveRealization K x.1, x.2⟩).liesInFace

theorem fullToAmbient_injective (K : AbstractSimplicialComplex V) (D : Set V) :
    Function.Injective (fullToAmbient K D) := by
  intro x y hxy
  apply weakPoint_ext
  funext v
  have he := congrArg (fun z : SeifertSurfaces.RealizationPoint K => z.weight v.1) hxy
  simpa only [fullToAmbient_weight_of_mem K D x v.1 v.2,
    fullToAmbient_weight_of_mem K D y v.1 v.2] using he

theorem fullToSupported_supportedToFull (K : AbstractSimplicialComplex V)
    (D : Set V) (x : fullSupportLocus K D) :
    fullToSupported K D (supportedToFull K D x) = x := by
  apply Subtype.ext
  apply weakPoint_ext
  funext v
  change (fullToAmbient K D (supportedToFull K D x)).weight v = x.1.weight v
  by_cases hv : v ∈ D
  · exact fullToAmbient_weight_of_mem K D (supportedToFull K D x) v hv
  · rw [fullToAmbient_weight_of_not_mem K D _ v hv]
    exact (x.2 v hv).symm

theorem supportedToFull_fullToSupported (K : AbstractSimplicialComplex V)
    (D : Set V)
    (x : SeifertSurfaces.RealizationPoint (SeifertSurfaces.fullSubcomplex K D)) :
    supportedToFull K D (fullToSupported K D x) = x := by
  apply weakPoint_ext
  funext v
  exact fullToAmbient_weight_of_mem K D x v.1 v.2

theorem continuous_fullToAmbient (K : AbstractSimplicialComplex V) (D : Set V) :
    Continuous (fullToAmbient K D) := by
  classical
  let e := complexRealizationHomeomorph (SeifertSurfaces.fullSubcomplex K D)
    (CurveComplex.fullSubcomplex K (fun v => v ∈ D)) (fullComplex_eq K D)
  have heq : fullToAmbient K D = fromCurveRealization K ∘
      CurveComplex.fullToAmbient K (fun v => v ∈ D) ∘ e ∘
        toCurveRealization (SeifertSurfaces.fullSubcomplex K D) := by
    funext x
    apply weakPoint_ext
    funext v
    by_cases hv : v ∈ D
    · simp only [Function.comp_apply, fromCurveRealization_weight,
        fullToAmbient_weight_of_mem K D x v hv,
        CurveComplex.fullToAmbient_weight_of_property K (fun v => v ∈ D) _ v hv,
        e, complexRealizationHomeomorph_weight, toCurveRealization_weight]
    · simp only [Function.comp_apply, fromCurveRealization_weight,
        fullToAmbient_weight_of_not_mem K D x v hv,
        CurveComplex.fullToAmbient_weight_of_not_property K (fun v => v ∈ D) _ v hv]
  rw [heq]
  exact (continuous_fromCurveRealization K).comp
    ((CurveComplex.fullToAmbient_continuous K (fun v => v ∈ D)).comp
      (e.continuous.comp (continuous_toCurveRealization _)))

theorem continuous_supportedToFull (K : AbstractSimplicialComplex V) (D : Set V) :
    Continuous (supportedToFull K D) := by
  classical
  let e := complexRealizationHomeomorph (CurveComplex.fullSubcomplex K (fun v => v ∈ D))
    (SeifertSurfaces.fullSubcomplex K D) (fullComplex_eq K D).symm
  let t : fullSupportLocus K D → CurveComplex.fullSupportLocus K (fun v => v ∈ D) :=
    fun x => ⟨toCurveRealization K x.1, x.2⟩
  have ht : Continuous t :=
    ((continuous_toCurveRealization K).comp continuous_subtype_val).subtype_mk _
  have heq : supportedToFull K D = fromCurveRealization _ ∘ e ∘
      CurveComplex.supportedToFull K (fun v => v ∈ D) ∘ t := by
    funext x
    apply weakPoint_ext
    funext v
    simp only [Function.comp_apply, fromCurveRealization_weight,
      e, complexRealizationHomeomorph_weight]
    rfl
  rw [heq]
  exact (continuous_fromCurveRealization _).comp
    (e.continuous.comp ((CurveComplex.supportedToFull_continuous K (fun v => v ∈ D)).comp ht))

/-- The topology of a full subcomplex is the actual ambient subspace topology. -/
noncomputable def fullSubcomplexHomeomorphSupported
    (K : AbstractSimplicialComplex V) (D : Set V) :
    SeifertSurfaces.RealizationPoint (SeifertSurfaces.fullSubcomplex K D) ≃ₜ
      fullSupportLocus K D where
  toFun := fullToSupported K D
  invFun := supportedToFull K D
  left_inv := supportedToFull_fullToSupported K D
  right_inv := fullToSupported_supportedToFull K D
  continuous_toFun := (continuous_fullToAmbient K D).subtype_mk _
  continuous_invFun := continuous_supportedToFull K D

theorem isClosed_fullSupportLocus (K : AbstractSimplicialComplex V) (D : Set V) :
    IsClosed (fullSupportLocus K D) := by
  classical
  exact (CurveComplex.isClosed_fullSupportLocus K (fun v => v ∈ D)).preimage
    (continuous_toCurveRealization K)

theorem fullToAmbient_isClosedEmbedding (K : AbstractSimplicialComplex V)
    (D : Set V) : Topology.IsClosedEmbedding (fullToAmbient K D) := by
  exact (isClosed_fullSupportLocus K D).isClosedEmbedding_subtypeVal.comp
    (fullSubcomplexHomeomorphSupported K D).isClosedEmbedding

theorem fullToAmbient_range (K : AbstractSimplicialComplex V) (D : Set V) :
    Set.range (fullToAmbient K D) = fullSupportLocus K D := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (fullToSupported K D y).2
  · intro hx
    refine ⟨supportedToFull K D ⟨x, hx⟩, ?_⟩
    exact congrArg Subtype.val (fullToSupported_supportedToFull K D ⟨x, hx⟩)

/-- The two full-subcomplex definitions have the same faces (`map` vs `image`). -/
theorem fullSubcomplex_eq_curve_fullSubcomplex [DecidableEq V]
    (K : AbstractSimplicialComplex V) (D : Set V) :
    SeifertSurfaces.fullSubcomplex K D =
      CurveComplex.fullSubcomplex K (fun v => v ∈ D) := by
  exact fullComplex_eq K D

theorem fullSupportLocus_curve_preimage (K : AbstractSimplicialComplex V)
    (D : Set V) :
    fullSupportLocus K D = toCurveRealization K ⁻¹'
      CurveComplex.fullSupportLocus K (fun v => v ∈ D) := by
  rfl

theorem fullSubcomplex_contractible_iff_supported
    (K : AbstractSimplicialComplex V) (D : Set V) :
    ContractibleSpace
        (SeifertSurfaces.RealizationPoint (SeifertSurfaces.fullSubcomplex K D)) ↔
      ContractibleSpace (fullSupportLocus K D) := by
  exact (fullSubcomplexHomeomorphSupported K D).contractibleSpace_iff

/-- The canonical continuous factor is restriction of the supported coordinates.
Compactness is not needed for this topology bridge. -/
def fullSubcomplexFactor
    {Y : Type w} [TopologicalSpace Y] (K : AbstractSimplicialComplex V)
    (D : Set V) (f : C(Y, SeifertSurfaces.RealizationPoint K))
    (hf : ∀ y, f y ∈ fullSupportLocus K D) :
    C(Y, SeifertSurfaces.RealizationPoint (SeifertSurfaces.fullSubcomplex K D)) where
  toFun := fun y => supportedToFull K D ⟨f y, hf y⟩
  continuous_toFun := (continuous_supportedToFull K D).comp (f.continuous.subtype_mk hf)

theorem fullSubcomplexFactor_commutes
    {Y : Type w} [TopologicalSpace Y] (K : AbstractSimplicialComplex V)
    (D : Set V) (f : C(Y, SeifertSurfaces.RealizationPoint K))
    (hf : ∀ y, f y ∈ fullSupportLocus K D) (y : Y) :
    fullToAmbient K D (fullSubcomplexFactor K D f hf y) = f y := by
  exact congrArg Subtype.val (fullToSupported_supportedToFull K D ⟨f y, hf y⟩)

/-- The source limit step uses this existence statement after selecting a
smaller supported vertex set. The canonical factor is defined above. -/
theorem continuous_factor_through_fullSubcomplex
    {Y : Type w} [TopologicalSpace Y] (K : AbstractSimplicialComplex V)
    (D : Set V) (f : C(Y, SeifertSurfaces.RealizationPoint K))
    (hf : ∀ y, f y ∈ fullSupportLocus K D) :
    ∃ g : C(Y,
        SeifertSurfaces.RealizationPoint (SeifertSurfaces.fullSubcomplex K D)),
      ∀ y, fullToAmbient K D (g y) = f y := by
  exact ⟨fullSubcomplexFactor K D f hf, fullSubcomplexFactor_commutes K D f hf⟩

/-- On full subcomplexes, induced graph cliques match the original face set. -/
theorem graphFlagComplex_induce_eq_fullSubcomplex
    (G : SimpleGraph V) (D : Set V) :
    SeifertSurfaces.graphFlagComplex (G.induce D) =
      SeifertSurfaces.fullSubcomplex (SeifertSurfaces.graphFlagComplex G) D := by
  ext σ
  exact (SeifertSurfaces.full_subcomplex_is_flag (SeifertSurfaces.graphFlagComplex G) G
    (SeifertSurfaces.graph_flag_complex_is_flag G) D σ).symm

end SeifertSurfaces.TopologyAdapters
