import TopologyAdapters.FullSubcomplexTopology
import WhiteheadSupport.CompactFactorization
import WhiteheadSupport.RealizationConsumer

/-!
# Theorem B: compact containment and the limit mechanism

Source: `references/seifert-surfaces.txt`, lines 244--252, PDF p. 6.
All realizations below carry the existing finite-simplex weak topology.
Contractible carriers are genuine full subcomplexes; the carrier condition is
an intermediate hypothesis to be established from the ordinal induction.
-/

namespace SeifertSurfaces.OrdinalAssembly

universe u w

open TopologyAdapters

variable {V : Type u}

private noncomputable def vertex_point (X : AbstractSimplicialComplex V) (v : V) :
    RealizationPoint X := by
  classical
  exact {
    weight := fun w => if w = v then 1 else 0
    nonneg := by intro w; split_ifs <;> norm_num
    liesInFace := ⟨{v}, X.singleton_mem v, by simp, by simp⟩ }

private theorem vertex_point_weight_self (X : AbstractSimplicialComplex V) (v : V) :
    (vertex_point X v).weight v = 1 := by
  classical
  simp [vertex_point]

/-- A nonempty vertex type gives a nonempty weak realization. -/
theorem weak_realization_nonempty [Nonempty V]
    (X : AbstractSimplicialComplex V) :
    Nonempty (RealizationPoint X) := by
  exact ⟨vertex_point X (Classical.choice inferInstance)⟩

/-- Source base case: the realization of a complex with exactly one vertex
is contractible, with its actual weak topology. -/
theorem singleton_weak_realization_contractible [Nonempty V] [Subsingleton V]
    (X : AbstractSimplicialComplex V) :
    ContractibleSpace (RealizationPoint X) := by
  classical
  have hweight (p : RealizationPoint X) (v : V) : p.weight v = 1 := by
    obtain ⟨σ, hσ, hz, hs⟩ := p.liesInFace
    obtain ⟨w, hw⟩ := (X.isRelLowerSet_faces hσ).1
    have hsing : σ = {v} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨by simpa only [Subsingleton.elim w v] using hw,
        fun q _ => Subsingleton.elim q v⟩
    simpa only [hsing, Finset.sum_singleton] using hs
  let : Nonempty (RealizationPoint X) := weak_realization_nonempty X
  let : Subsingleton (RealizationPoint X) := ⟨fun p q => by
    have hw : p.weight = q.weight := funext fun v => (hweight p v).trans (hweight q v).symm
    cases p
    cases q
    cases hw
    rfl⟩
  infer_instance

/-- Finite-vertex carriers control all compact subsets of the weak realization.
The selected full subcomplex can have an arbitrary infinite vertex set. -/
theorem compact_contractible_containment_of_finite_carriers
    (X : AbstractSimplicialComplex V)
    (hcarriers : ∀ F : Finset V, ∃ D : Set V,
      (∀ v ∈ F, v ∈ D) ∧ ContractibleSpace (RealizationPoint (fullSubcomplex X D)))
    (C : Set (RealizationPoint X)) (hC : IsCompact C) :
    ∃ D : Set V, C ⊆ fullSupportLocus X D ∧
      ContractibleSpace (RealizationPoint (fullSubcomplex X D)) := by
  obtain ⟨F, hF⟩ := compact_has_finite_vertex_support X C hC
  obtain ⟨D, hD, hc⟩ := hcarriers F
  refine ⟨D, ?_, hc⟩
  intro x hx v hv
  exact hF x hx v (fun hmem => hv (hD v hmem))

/-- A compact map has an actual continuous factor in a contractible carrier,
with the exact zero-extension equation. -/
theorem compact_map_factors_contractible_carrier
    {A : Type w} [TopologicalSpace A] [CompactSpace A]
    (X : AbstractSimplicialComplex V)
    (hcarriers : ∀ F : Finset V, ∃ D : Set V,
      (∀ v ∈ F, v ∈ D) ∧ ContractibleSpace (RealizationPoint (fullSubcomplex X D)))
    (f : C(A, RealizationPoint X)) :
    ∃ D : Set V, ContractibleSpace (RealizationPoint (fullSubcomplex X D)) ∧
      ∃ g : C(A, RealizationPoint (fullSubcomplex X D)),
        ∀ a, fullToAmbient X D (g a) = f a := by
  obtain ⟨D, hD, hc⟩ := compact_contractible_containment_of_finite_carriers X hcarriers
    (Set.range f) (isCompact_range f.continuous)
  obtain ⟨g, hg⟩ := continuous_factor_through_fullSubcomplex X D f
    (fun a => hD ⟨a, rfl⟩)
  exact ⟨D, hc, g, hg⟩

/-- Based factorization includes both the cube image and the basepoint's finite
support, even for the zero-dimensional cube. Every map is bundled continuous. -/
theorem gen_loop_factors_contractible_carrier
    (X : AbstractSimplicialComplex V)
    (hcarriers : ∀ F : Finset V, ∃ D : Set V,
      (∀ v ∈ F, v ∈ D) ∧ ContractibleSpace (RealizationPoint (fullSubcomplex X D)))
    (n : ℕ) (x : RealizationPoint X)
    (f : GenLoop (Fin n) (RealizationPoint X) x) :
    ∃ D : Set V, ContractibleSpace (RealizationPoint (fullSubcomplex X D)) ∧
      ∃ xD : RealizationPoint (fullSubcomplex X D),
      ∃ g : GenLoop (Fin n) (RealizationPoint (fullSubcomplex X D)) xD,
        fullToAmbient X D xD = x ∧
        ∀ a, fullToAmbient X D (g a) = f a := by
  classical
  obtain ⟨F, hF⟩ := WhiteheadSupport.compact_map_has_finite_support X f.val
  obtain ⟨σ, hσ, hx, hsum⟩ := x.liesInFace
  obtain ⟨D, hD, hc⟩ := hcarriers (F ∪ σ)
  have hxD : x ∈ fullSupportLocus X D := fun v hv =>
    hx v (fun hmem => hv (hD v (Finset.mem_union.mpr (Or.inr hmem))))
  let xD := supportedToFull X D ⟨x, hxD⟩
  have hbase : fullToAmbient X D xD = x :=
    congrArg Subtype.val (fullToSupported_supportedToFull X D ⟨x, hxD⟩)
  have hfD : ∀ a, f a ∈ fullSupportLocus X D := fun a v hv =>
    hF a v (fun hmem => hv (hD v (Finset.mem_union.mpr (Or.inl hmem))))
  let fg := fullSubcomplexFactor X D f.val hfD
  have hfg (a) : fullToAmbient X D (fg a) = f a :=
    fullSubcomplexFactor_commutes X D f.val hfD a
  let g : GenLoop (Fin n) (RealizationPoint (fullSubcomplex X D)) xD :=
    ⟨fg, fun a ha => fullToAmbient_injective X D
      ((hfg a).trans ((GenLoop.boundary f a ha).trans hbase.symm))⟩
  exact ⟨D, hc, xD, g, hbase, hfg⟩

/-- The finite-carrier condition yields a genuine path-connected realization,
which is the dimension-zero part of the source limit argument. -/
theorem path_connected_of_finite_contractible_carriers [Nonempty V]
    (X : AbstractSimplicialComplex V)
    (hcarriers : ∀ F : Finset V, ∃ D : Set V,
      (∀ v ∈ F, v ∈ D) ∧ ContractibleSpace (RealizationPoint (fullSubcomplex X D))) :
    PathConnectedSpace (RealizationPoint X) := by
  classical
  let : Nonempty (RealizationPoint X) := weak_realization_nonempty X
  refine ⟨inferInstance, ?_⟩
  intro x y
  obtain ⟨σ, hσ, hx, hxs⟩ := x.liesInFace
  obtain ⟨τ, hτ, hy, hys⟩ := y.liesInFace
  obtain ⟨D, hD, hc⟩ := hcarriers (σ ∪ τ)
  let : ContractibleSpace (RealizationPoint (fullSubcomplex X D)) := hc
  have hxD : x ∈ fullSupportLocus X D := fun v hv =>
    hx v (fun hmem => hv (hD v (Finset.mem_union.mpr (Or.inl hmem))))
  have hyD : y ∈ fullSupportLocus X D := fun v hv =>
    hy v (fun hmem => hv (hD v (Finset.mem_union.mpr (Or.inr hmem))))
  have h := (PathConnectedSpace.joined (supportedToFull X D ⟨x, hxD⟩)
    (supportedToFull X D ⟨y, hyD⟩)).map (continuous_fullToAmbient X D)
  have hx' : fullToAmbient X D (supportedToFull X D ⟨x, hxD⟩) = x :=
    congrArg Subtype.val (fullToSupported_supportedToFull X D ⟨x, hxD⟩)
  have hy' : fullToAmbient X D (supportedToFull X D ⟨y, hyD⟩) = y :=
    congrArg Subtype.val (fullToSupported_supportedToFull X D ⟨y, hyD⟩)
  simpa only [hx', hy'] using h

/-- Every positive-dimensional based cube loop is relatively nullhomotopic.
The imported based-loop repair handles contractions moving the basepoint. -/
theorem gen_loop_nullhomotopic_of_finite_contractible_carriers
    (X : AbstractSimplicialComplex V)
    (hcarriers : ∀ F : Finset V, ∃ D : Set V,
      (∀ v ∈ F, v ∈ D) ∧ ContractibleSpace (RealizationPoint (fullSubcomplex X D)))
    (n : ℕ) (hn : 1 ≤ n) (x : RealizationPoint X)
    (f : GenLoop (Fin n) (RealizationPoint X) x) :
    GenLoop.Homotopic f
      (GenLoop.const (N := Fin n) (X := RealizationPoint X) (x := x)) := by
  obtain ⟨D, hc, xD, g, hxD, hg⟩ := gen_loop_factors_contractible_carrier X hcarriers n x f
  let : ContractibleSpace (RealizationPoint (fullSubcomplex X D)) := hc
  exact WhiteheadSupport.cube_loop_nullhomotopic_of_contractible_factor n hn x xD
    ⟨fullToAmbient X D, continuous_fullToAmbient X D⟩ hxD f g hg

/-- All positive homotopy groups vanish at every actual basepoint. -/
theorem pi_subsingleton_of_finite_contractible_carriers
    (X : AbstractSimplicialComplex V)
    (hcarriers : ∀ F : Finset V, ∃ D : Set V,
      (∀ v ∈ F, v ∈ D) ∧ ContractibleSpace (RealizationPoint (fullSubcomplex X D)))
    (n : ℕ) (hn : 1 ≤ n) (x : RealizationPoint X) :
    Subsingleton (HomotopyGroup.Pi n (RealizationPoint X) x) := by
  constructor
  intro a b
  induction a using Quotient.inductionOn with
  | h f =>
    induction b using Quotient.inductionOn with
    | h g =>
      exact Quotient.sound
        ((gen_loop_nullhomotopic_of_finite_contractible_carriers X hcarriers n hn x f).trans
          (gen_loop_nullhomotopic_of_finite_contractible_carriers X hcarriers n hn x g).symm)

/-- Generic B7 endpoint: compact containment in contractible full subcomplexes
implies actual contractibility. CW/Hausdorff structure is obtained from the
existing realization adapters; neither is a caller-supplied oracle. -/
theorem weak_realization_contractible_of_compact_containment [Nonempty V]
    (X : AbstractSimplicialComplex V)
    (hcompact : ∀ C : Set (RealizationPoint X), IsCompact C →
      ∃ D : Set V, C ⊆ fullSupportLocus X D ∧
        ContractibleSpace (RealizationPoint (fullSubcomplex X D))) :
    ContractibleSpace (RealizationPoint X) := by
  classical
  have hcarriers : ∀ F : Finset V, ∃ D : Set V,
      (∀ v ∈ F, v ∈ D) ∧ ContractibleSpace (RealizationPoint (fullSubcomplex X D)) := by
    intro F
    let C : Set (RealizationPoint X) := vertex_point X '' (F : Set V)
    have hC : IsCompact C := (F.finite_toSet.image (vertex_point X)).isCompact
    obtain ⟨D, hD, hc⟩ := hcompact C hC
    refine ⟨D, ?_, hc⟩
    intro v hv
    by_contra hn
    have he := hD ⟨v, hv, rfl⟩ v hn
    rw [vertex_point_weight_self] at he
    norm_num at he
  let : PathConnectedSpace (RealizationPoint X) :=
    path_connected_of_finite_contractible_carriers X hcarriers
  exact WhiteheadSupport.contractible_weak_realization_of_all_pi_subsingleton X
    (pi_subsingleton_of_finite_contractible_carriers X hcarriers)

/-- Generator-facing B7 endpoint for the finite supports supplied by the source
CW compactness theorem. No finite/countable/local-finite restriction is imposed
on `V`, `X`, or any carrier `D`. -/
theorem weak_realization_contractible_of_finite_carriers [Nonempty V]
    (X : AbstractSimplicialComplex V)
    (hcarriers : ∀ F : Finset V, ∃ D : Set V,
      (∀ v ∈ F, v ∈ D) ∧ ContractibleSpace (RealizationPoint (fullSubcomplex X D))) :
    ContractibleSpace (RealizationPoint X) := by
  exact weak_realization_contractible_of_compact_containment X
    (compact_contractible_containment_of_finite_carriers X hcarriers)

end SeifertSurfaces.OrdinalAssembly
