import TopologyAdapters.FullSubcomplexTopology
import CurveComplexGenusTwo.Topology.StarConeTopology
import CurveComplexGenusTwo.Topology.StarSDRConditional

/-!
Specialization of the existing actual star-deletion API to a single vertex of
a flag complex. The natural-number relation is just a graph encoding. No
surface geometry, finite-link premise, or contractibility surrogate is used.
-/

namespace SeifertSurfaces.TopologyAdapters

universe u

variable {V : Type u}

/-- The intersection-one API recognizes exactly graph edges between distinct
vertices. The value on the diagonal is irrelevant to pairwise face predicates. -/
noncomputable def graphIntersection (G : SimpleGraph V) (a b : V) : ℕ := by
  classical
  exact if a = b ∨ G.Adj a b then 0 else 2

/-- The deletion is the coordinate-zero locus, with the ambient subspace topology. -/
def vertexDeletionLocus (K : AbstractSimplicialComplex V) (v : V) :
    Set (SeifertSurfaces.RealizationPoint K) :=
  {x | x.weight v = 0}

/-- The actual neighbor link in a flag complex is its full neighbor subcomplex. -/
noncomputable abbrev neighborLinkComplex (K : AbstractSimplicialComplex V)
    (G : SimpleGraph V) (v : V) :=
  SeifertSurfaces.fullSubcomplex K (G.neighborSet v)

theorem vertexDeletionLocus_eq_fullSupportLocus
    (K : AbstractSimplicialComplex V) (v : V) :
    vertexDeletionLocus K v = fullSupportLocus K {w | w ≠ v} := by
  ext x
  change x.weight v = 0 ↔ ∀ w, ¬ w ≠ v → x.weight w = 0
  simp

section EncodedStar

variable [DecidableEq V]

/-- Existing realized separating-link locus, with the marked set exactly `{v}`. -/
abbrev curveNeighborLink (K : AbstractSimplicialComplex V) (G : SimpleGraph V)
    (v : V) :=
  CurveComplexGenusTwo.Topology.RealizedSeparatingLink K (graphIntersection G)
    (fun w => w = v) v

theorem graph_curve_face_iff (G : SimpleGraph V) (σ : Finset V) :
    CurveComplexGenusTwo.Topology.CurveFace (graphIntersection G) 1 σ ↔
      G.IsClique (σ : Set V) := by
  unfold CurveComplexGenusTwo.Topology.CurveFace SimpleGraph.IsClique
  constructor
  · intro h a ha b hb hab
    have hab' := h ha hb hab
    by_contra hn
    simp [graphIntersection, hab, hn] at hab'
  · intro h a ha b hb hab
    simp [graphIntersection, hab, h ha hb hab]

theorem flag_faces_are_curve_faces (K : AbstractSimplicialComplex V)
    (G : SimpleGraph V) (hflag : SeifertSurfaces.IsFlagComplex G K) :
    ∀ σ : Finset V, σ ∈ K.faces →
      CurveComplexGenusTwo.Topology.CurveFace (graphIntersection G) 1 σ := by
  intro σ hσ
  exact (graph_curve_face_iff G σ).mpr ((hflag σ).mp hσ).2

theorem nonempty_curve_faces_are_flag_faces (K : AbstractSimplicialComplex V)
    (G : SimpleGraph V) (hflag : SeifertSurfaces.IsFlagComplex G K) :
    ∀ σ : Finset V, σ.Nonempty →
      CurveComplexGenusTwo.Topology.CurveFace (graphIntersection G) 1 σ →
        σ ∈ K.faces := by
  intro σ hne hσ
  exact (hflag σ).mpr ⟨hne, (graph_curve_face_iff G σ).mp hσ⟩

/-- The separation hypothesis of the existing API is automatic for a singleton. -/
theorem singleton_vertex_separation (G : SimpleGraph V) (v : V) :
    ∀ a b : V, a = v → b = v → a ≠ b → 1 < graphIntersection G a b := by
  intro a b ha hb hab
  exact (hab (ha.trans hb.symm)).elim

theorem graph_has_realized_star_faces (K : AbstractSimplicialComplex V)
    (G : SimpleGraph V) (hflag : SeifertSurfaces.IsFlagComplex G K) (v : V) :
    CurveComplexGenusTwo.Topology.HasRealizedStarFaces K (graphIntersection G) v := by
  exact CurveComplexGenusTwo.Topology.hasRealizedStarFaces_of_fullCurveFaces
    K (graphIntersection G) v (nonempty_curve_faces_are_flag_faces K G hflag)

/-- The imported link locus is exactly the barycentric neighbor-support locus. -/
theorem curveNeighborLink_eq_fullSupportLocus (K : AbstractSimplicialComplex V)
    (G : SimpleGraph V) (hflag : SeifertSurfaces.IsFlagComplex G K) (v : V) :
    curveNeighborLink K G v =
      CurveComplex.fullSupportLocus K (fun w => G.Adj v w) := by
  ext x
  constructor
  · rintro ⟨⟨σ, hσ, hstar, hsupp⟩, hzero⟩ w hw
    by_cases hmem : w ∈ σ
    · by_cases heq : w = v
      · exact hzero w heq
      · have hclique := (graph_curve_face_iff G (insert v σ)).mp hstar
        exact (hw (hclique (by simp) (by simp [hmem]) (Ne.symm heq))).elim
    · exact hsupp w hmem
  · intro hx
    let σ := CurveComplex.supportFinset K x
    have hσ := CurveComplex.supportFinset_mem_faces K x
    have hadj (w : V) (hw : w ∈ σ) : G.Adj v w := by
      by_contra hn
      exact ((CurveComplex.mem_supportFinset_iff K x w).mp hw) (hx w hn)
    refine ⟨⟨σ, hσ, ?_, ?_⟩, ?_⟩
    · apply (graph_curve_face_iff G (insert v σ)).mpr
      rw [Finset.coe_insert]
      exact ((hflag σ).mp hσ).2.insert (fun w hw _ => hadj w hw)
    · intro w hw
      exact not_ne_iff.mp (fun hn => hw ((CurveComplex.mem_supportFinset_iff K x w).mpr hn))
    · intro w hw
      subst w
      exact hx v G.irrefl

theorem curve_vertex_core_eq_fullSupportLocus (K : AbstractSimplicialComplex V)
    (v : V) :
    CurveComplexGenusTwo.Topology.NonseparatingWeightLocus K (fun w => w = v) =
      CurveComplex.fullSupportLocus K (fun w => w ≠ v) := by
  ext x
  change (∀ w, w = v → x.weight w = 0) ↔ ∀ w, ¬ w ≠ v → x.weight w = 0
  simp

/-- Zero extension identifies a literal neighbor-link point with the imported
actual link locus. Its weight function is fully specified. -/
noncomputable def neighborLinkToCurve (K : AbstractSimplicialComplex V)
    (G : SimpleGraph V) (hflag : SeifertSurfaces.IsFlagComplex G K) (v : V)
    (x : SeifertSurfaces.RealizationPoint (neighborLinkComplex K G v)) :
    curveNeighborLink K G v :=
  ⟨toCurveRealization K (fullToAmbient K (G.neighborSet v) x), by
    rw [curveNeighborLink_eq_fullSupportLocus K G hflag v]
    intro w hw
    exact fullToAmbient_weight_of_not_mem K (G.neighborSet v) x w hw⟩

/-- Restrict an imported link point to its actual neighbor coordinates. -/
def curveLinkToNeighbor (K : AbstractSimplicialComplex V)
    (G : SimpleGraph V) (hflag : SeifertSurfaces.IsFlagComplex G K) (v : V)
    (x : curveNeighborLink K G v) :
    SeifertSurfaces.RealizationPoint (neighborLinkComplex K G v) :=
  supportedToFull K (G.neighborSet v) ⟨fromCurveRealization K x.1, by
    have hx := x.property
    have hx' := (curveNeighborLink_eq_fullSupportLocus K G hflag v).le hx
    exact hx'⟩

/-- The precise topology bridge required before transferring link contractibility. -/
noncomputable def neighborLinkHomeomorphCurveLink
    (K : AbstractSimplicialComplex V) (G : SimpleGraph V)
    (hflag : SeifertSurfaces.IsFlagComplex G K) (v : V) :
    SeifertSurfaces.RealizationPoint (neighborLinkComplex K G v) ≃ₜ
      curveNeighborLink K G v where
  toFun := neighborLinkToCurve K G hflag v
  invFun := curveLinkToNeighbor K G hflag v
  left_inv := by
    intro x
    change supportedToFull K (G.neighborSet v) (fullToSupported K (G.neighborSet v) x) = x
    exact supportedToFull_fullToSupported K (G.neighborSet v) x
  right_inv := by
    intro x
    apply Subtype.ext
    apply CurveComplex.RealizationPoint.ext
    funext w
    change (fullToAmbient K (G.neighborSet v)
      (curveLinkToNeighbor K G hflag v x)).weight w = x.1.weight w
    by_cases hw : w ∈ G.neighborSet v
    · rw [fullToAmbient_weight_of_mem K (G.neighborSet v) _ w hw]
      rfl
    · rw [fullToAmbient_weight_of_not_mem K (G.neighborSet v) _ w hw]
      have hx := x.property
      have hx' := (curveNeighborLink_eq_fullSupportLocus K G hflag v).le hx
      exact (hx' w hw).symm
  continuous_toFun := by
    exact (continuous_toCurveRealization K |>.comp
      (continuous_fullToAmbient K (G.neighborSet v))).subtype_mk _
  continuous_invFun := by
    exact (continuous_supportedToFull K (G.neighborSet v)).comp
      (((continuous_fromCurveRealization K).comp continuous_subtype_val).subtype_mk _)

theorem neighborLinkHomeomorphCurveLink_weight
    (K : AbstractSimplicialComplex V) (G : SimpleGraph V)
    (hflag : SeifertSurfaces.IsFlagComplex G K) (v : V)
    (x : SeifertSurfaces.RealizationPoint (neighborLinkComplex K G v))
    (w : G.neighborSet v) :
    (neighborLinkHomeomorphCurveLink K G hflag v x).1.weight w.1 = x.weight w := by
  exact fullToAmbient_weight_of_mem K (G.neighborSet v) x w.1 w.2

/-- All hypotheses of the existing quotient-chart theorem are discharged by
flagness and the singleton marking, apart from the genuine nonempty link. -/
theorem graph_closedStarConeMap_isQuotientMap
    (K : AbstractSimplicialComplex V) (G : SimpleGraph V)
    (hflag : SeifertSurfaces.IsFlagComplex G K) (v : V)
    (hne : Nonempty (curveNeighborLink K G v)) :
    Topology.IsQuotientMap
      (CurveComplexGenusTwo.Topology.closedStarConeMap K (graphIntersection G)
        (fun w => w = v) ⟨v, rfl⟩
        (graph_has_realized_star_faces K G hflag v)) := by
  exact CurveComplexGenusTwo.Topology.closedStarConeMap_isQuotientMap
    K (graphIntersection G) (fun w => w = v)
    (flag_faces_are_curve_faces K G hflag)
    (nonempty_curve_faces_are_flag_faces K G hflag)
    (singleton_vertex_separation G v) ⟨v, rfl⟩
    (graph_has_realized_star_faces K G hflag v) hne

/-- The compiled star-deletion theorem specialized to one arbitrary vertex. -/
theorem curve_vertex_deletion_sdr
    (K : AbstractSimplicialComplex V) (G : SimpleGraph V)
    (hflag : SeifertSurfaces.IsFlagComplex G K) (v : V)
    (hlink : ContractibleSpace
      (SeifertSurfaces.RealizationPoint (neighborLinkComplex K G v))) :
    CurveComplexGenusTwo.Topology.IsStrongDeformationRetract
      (CurveComplexGenusTwo.Topology.NonseparatingWeightLocus K (fun w => w = v)) := by
  letI := hlink
  have hlink' : ContractibleSpace (curveNeighborLink K G v) :=
    (neighborLinkHomeomorphCurveLink K G hflag v).symm.contractibleSpace
  apply CurveComplexGenusTwo.Topology.realization_star_deletion_of_contractible_links_and_quotient_charts
    K (graphIntersection G) (fun w => w = v)
    (flag_faces_are_curve_faces K G hflag) (singleton_vertex_separation G v)
    (fun w => graph_has_realized_star_faces K G hflag w)
  · intro w
    rcases w with ⟨w, hw⟩
    subst w
    exact hlink'
  · intro w
    rcases w with ⟨w, hw⟩
    subst w
    letI := hlink'
    exact graph_closedStarConeMap_isQuotientMap K G hflag v inferInstance

end EncodedStar

/-- The actual source-facing strong deformation retract, transported along the
coordinate homeomorphism. Classical decidability is internal to its proof. -/
theorem weak_vertex_deletion_sdr
    (K : AbstractSimplicialComplex V) (G : SimpleGraph V)
    (hflag : SeifertSurfaces.IsFlagComplex G K) (v : V)
    (hlink : ContractibleSpace
      (SeifertSurfaces.RealizationPoint (neighborLinkComplex K G v))) :
    CurveComplexGenusTwo.Topology.IsStrongDeformationRetract
      (vertexDeletionLocus K v) := by
  classical
  let e := weakRealizationHomeomorph K
  obtain ⟨H, hzero, hone, hfix⟩ := curve_vertex_deletion_sdr K G hflag v hlink
  let H' : C(SeifertSurfaces.RealizationPoint K × CurveComplexGenusTwo.Topology.Interval,
      SeifertSurfaces.RealizationPoint K) :=
    ⟨fun p => e.symm (H (e p.1, p.2)), e.symm.continuous.comp
      (H.continuous.comp ((e.continuous.comp continuous_fst).prodMk continuous_snd))⟩
  refine ⟨H', ?_, ?_, ?_⟩
  · intro x
    change e.symm (H (e x, CurveComplexGenusTwo.Topology.timeZero)) = x
    rw [hzero, e.symm_apply_apply]
  · intro x
    exact hone (e x) v rfl
  · intro x hx t
    have hx' : e x ∈ CurveComplexGenusTwo.Topology.NonseparatingWeightLocus K (fun w => w = v) := by
      intro w hw
      subst w
      exact hx
    change e.symm (H (e x, t)) = x
    rw [hfix (e x) hx' t, e.symm_apply_apply]

/-- A genuine strong deformation retract onto a contractible subspace makes
the ambient space contractible. This is an adapter to Mathlib's homotopy class. -/
theorem contractible_of_sdr_and_contractible_subspace
    {Y : Type u} [TopologicalSpace Y] (A : Set Y)
    (hA : CurveComplexGenusTwo.Topology.IsStrongDeformationRetract A)
    (hc : ContractibleSpace A) : ContractibleSpace Y := by
  letI := hc
  obtain ⟨H, hzero, hone, hfix⟩ := hA
  let r : C(Y, A) := ⟨fun x => ⟨H (x, CurveComplexGenusTwo.Topology.timeOne), hone x⟩,
    (H.continuous.comp (continuous_id.prodMk continuous_const)).subtype_mk _⟩
  let i : C(A, Y) := ⟨Subtype.val, continuous_subtype_val⟩
  have hhom : (ContinuousMap.id Y).Homotopic (i.comp r) := by
    refine ⟨{ toFun := fun p => H (p.2, p.1)
              continuous_toFun := H.continuous.comp (continuous_snd.prodMk continuous_fst)
              map_zero_left := hzero
              map_one_left := fun _ => rfl }⟩
  let e : ContinuousMap.HomotopyEquiv Y A := {
    toFun := r
    invFun := i
    left_inv := hhom.symm
    right_inv := by
      have heq : r.comp i = ContinuousMap.id A := by
        ext x
        exact hfix x.1 x.2 CurveComplexGenusTwo.Topology.timeOne
      rw [heq]
      }
  exact e.contractibleSpace

end SeifertSurfaces.TopologyAdapters
