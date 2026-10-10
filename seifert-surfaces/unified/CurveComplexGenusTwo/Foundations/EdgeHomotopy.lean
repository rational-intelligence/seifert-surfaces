import CurveComplexGenusTwo.Foundations.GenericRealization
import CurveComplexGenusTwo.Topology.WeakProduct
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Subpath

set_option maxHeartbeats 1000000

namespace CurveComplex

variable {V : Type*}

private theorem point_ext {K : AbstractSimplicialComplex V}
    {x y : RealizationPoint K} (h : x.weight = y.weight) : x = y := by
  cases x with
  | mk wx nx fx =>
    cases y with
    | mk wy ny fy =>
      cases h
      rfl

/-- The map on weak realizations induced by an inclusion of face sets. -/
noncomputable def realizationMap (K L : AbstractSimplicialComplex V)
    (h : ∀ σ, σ ∈ K.faces → σ ∈ L.faces) :
    RealizationPoint K → RealizationPoint L :=
  fun x => ⟨x.weight, x.nonneg, by
    obtain ⟨σ, hσ, hz, hs⟩ := x.liesInFace
    exact ⟨σ, h σ hσ, hz, hs⟩⟩

theorem realizationMap_weight (K L : AbstractSimplicialComplex V)
    (h : ∀ σ, σ ∈ K.faces → σ ∈ L.faces)
    (x : RealizationPoint K) (v : V) :
    (realizationMap K L h x).weight v = x.weight v := rfl

theorem continuous_faceInclusion_local (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces) :
    Continuous (faceInclusion K σ hσ) := by
  rw [continuous_def]
  intro U hU
  exact hU σ hσ

theorem realizationMap_faceInclusion (K L : AbstractSimplicialComplex V)
    (h : ∀ σ, σ ∈ K.faces → σ ∈ L.faces)
    (σ : Finset V) (hσ : σ ∈ K.faces) (x : FiniteSimplex σ) :
    realizationMap K L h (faceInclusion K σ hσ x) =
      faceInclusion L σ (h σ hσ) x := by
  apply point_ext
  rfl

theorem realizationMap_continuous (K L : AbstractSimplicialComplex V)
    (h : ∀ σ, σ ∈ K.faces → σ ∈ L.faces) :
    Continuous (realizationMap K L h) := by
  rw [continuous_def]
  intro U hU σ hσ
  have heq : realizationMap K L h ∘ faceInclusion K σ hσ =
      faceInclusion L σ (h σ hσ) := by
    funext x
    exact realizationMap_faceInclusion K L h σ hσ x
  change IsOpen ((realizationMap K L h ∘ faceInclusion K σ hσ) ⁻¹' U)
  rw [heq]
  exact hU σ (h σ hσ)

theorem realizationMap_id (K : AbstractSimplicialComplex V)
    (h : ∀ σ, σ ∈ K.faces → σ ∈ K.faces)
    (x : RealizationPoint K) : realizationMap K K h x = x := by
  apply point_ext
  rfl

abbrev EdgeTime := Set.Icc (0 : ℝ) 1

/-- Affine interpolation in a finite closed simplex. -/
noncomputable def finiteSimplexSegment (σ : Finset V)
    (x y : FiniteSimplex σ) (t : EdgeTime) : FiniteSimplex σ :=
  ⟨fun v => (1 - (t : ℝ)) * x.val v + (t : ℝ) * y.val v,
    by
      intro v
      exact add_nonneg
        (mul_nonneg (sub_nonneg.mpr t.property.2) (x.property.1 v))
        (mul_nonneg t.property.1 (y.property.1 v)),
    by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [x.property.2, y.property.2]
      ring⟩

theorem finiteSimplexSegment_continuous (σ : Finset V)
    (x y : FiniteSimplex σ) :
    Continuous (finiteSimplexSegment σ x y) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro v
  change Continuous (fun t : EdgeTime =>
    (1 - (t : ℝ)) * x.val v + (t : ℝ) * y.val v)
  fun_prop

theorem finiteSimplexSegment_zero (σ : Finset V)
    (x y : FiniteSimplex σ) :
    finiteSimplexSegment σ x y ⟨0, by norm_num⟩ = x := by
  apply Subtype.ext
  funext v
  simp [finiteSimplexSegment]

theorem finiteSimplexSegment_one (σ : Finset V)
    (x y : FiniteSimplex σ) :
    finiteSimplexSegment σ x y ⟨1, by norm_num⟩ = y := by
  apply Subtype.ext
  funext v
  simp [finiteSimplexSegment]

theorem finiteSimplexSegment_self (σ : Finset V)
    (x : FiniteSimplex σ) (t : EdgeTime) :
    finiteSimplexSegment σ x x t = x := by
  apply Subtype.ext
  funext v
  change (1 - (t : ℝ)) * x.val v + (t : ℝ) * x.val v = x.val v
  ring

/-- Every finite face contains an actual continuous straight edge path. -/
noncomputable def faceSegment (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces)
    (x y : FiniteSimplex σ) : EdgeTime → RealizationPoint K :=
  faceInclusion K σ hσ ∘ finiteSimplexSegment σ x y

theorem faceSegment_continuous (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces)
    (x y : FiniteSimplex σ) :
    Continuous (faceSegment K σ hσ x y) :=
  (continuous_faceInclusion_local K σ hσ).comp
    (finiteSimplexSegment_continuous σ x y)

theorem faceSegment_zero (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces)
    (x y : FiniteSimplex σ) :
    faceSegment K σ hσ x y ⟨0, by norm_num⟩ = faceInclusion K σ hσ x := by
  exact congrArg (faceInclusion K σ hσ) (finiteSimplexSegment_zero σ x y)

theorem faceSegment_one (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces)
    (x y : FiniteSimplex σ) :
    faceSegment K σ hσ x y ⟨1, by norm_num⟩ = faceInclusion K σ hσ y := by
  exact congrArg (faceInclusion K σ hσ) (finiteSimplexSegment_one σ x y)

/-- An edge path in a subcomplex maps to the identical barycentric edge path
in the larger complex. -/
theorem faceSegment_realizationMap (K L : AbstractSimplicialComplex V)
    (h : ∀ σ, σ ∈ K.faces → σ ∈ L.faces)
    (σ : Finset V) (hσ : σ ∈ K.faces)
    (x y : FiniteSimplex σ) (t : EdgeTime) :
    realizationMap K L h (faceSegment K σ hσ x y t) =
      faceSegment L σ (h σ hσ) x y t := by
  exact realizationMap_faceInclusion K L h σ hσ _

/-- A line segment as a path in the closed simplex. -/
noncomputable def finiteSegmentPath (σ : Finset V)
    (x y : FiniteSimplex σ) : Path x y where
  toFun := finiteSimplexSegment σ x y
  continuous_toFun := finiteSimplexSegment_continuous σ x y
  source' := finiteSimplexSegment_zero σ x y
  target' := finiteSimplexSegment_one σ x y

/-- Straight interpolation between any two paths with the same endpoints
inside one finite simplex is a homotopy relative to those endpoints. -/
noncomputable def finiteSimplexPathHomotopy (σ : Finset V)
    {x y : FiniteSimplex σ} (p q : Path x y) : p.Homotopy q where
  toFun z := finiteSimplexSegment σ (p z.2) (q z.2) z.1
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro v
    change Continuous (fun z : EdgeTime × EdgeTime =>
      (1 - (z.1 : ℝ)) * (p z.2).val v +
      (z.1 : ℝ) * (q z.2).val v)
    have hp : Continuous (fun z : EdgeTime × EdgeTime =>
        (p z.2).val v) :=
      (continuous_apply v).comp
        (continuous_subtype_val.comp (p.continuous.comp continuous_snd))
    have hq : Continuous (fun z : EdgeTime × EdgeTime =>
        (q z.2).val v) :=
      (continuous_apply v).comp
        (continuous_subtype_val.comp (q.continuous.comp continuous_snd))
    have ht : Continuous (fun z : EdgeTime × EdgeTime => (z.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    exact ((continuous_const.sub ht).mul hp).add (ht.mul hq)
  map_zero_left t := finiteSimplexSegment_zero σ (p t) (q t)
  map_one_left t := finiteSimplexSegment_one σ (p t) (q t)
  prop' t u hu := by
    rcases hu with hu | hu
    · subst u
      change finiteSimplexSegment σ (p 0) (q 0) t = p 0
      rw [p.source, q.source]
      exact finiteSimplexSegment_self σ x t
    · rw [Set.mem_singleton_iff] at hu
      subst u
      change finiteSimplexSegment σ (p 1) (q 1) t = p 1
      rw [p.target, q.target]
      exact finiteSimplexSegment_self σ y t

/-- The direct edge and the two-edge detour across a triangle are homotopic
relative to endpoints in its closed simplex. -/
noncomputable def finiteTriangleEdgeHomotopy (σ : Finset V)
    (x y z : FiniteSimplex σ) :
    (finiteSegmentPath σ x y).Homotopy
      ((finiteSegmentPath σ x z).trans (finiteSegmentPath σ z y)) :=
  finiteSimplexPathHomotopy σ _ _

/-- The three-vertex homotopy in the actual weak realization. -/
noncomputable def faceTriangleEdgeHomotopy
    (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces)
    (x y z : FiniteSimplex σ) :
    ((finiteSegmentPath σ x y).map
      (continuous_faceInclusion_local K σ hσ)).Homotopy
      (((finiteSegmentPath σ x z).trans
        (finiteSegmentPath σ z y)).map
          (continuous_faceInclusion_local K σ hσ)) :=
  (finiteTriangleEdgeHomotopy σ x y z).map
    ⟨faceInclusion K σ hσ, continuous_faceInclusion_local K σ hσ⟩

/-- The barycentric vertex of a finite simplex. -/
noncomputable def finiteSimplexVertex [DecidableEq V]
    (σ : Finset V) (v : V) (hv : v ∈ σ) : FiniteSimplex σ := by
  classical
  refine ⟨fun w => if (w : V) = v then 1 else 0, ?_, ?_⟩
  · intro w
    by_cases h : (w : V) = v <;> simp [h]
  · change (∑ w : σ, if (w : V) = v then (1 : ℝ) else 0) = 1
    have heq (w : σ) : ((w : V) = v) ↔ w = ⟨v, hv⟩ :=
      ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    simp only [(heq _)]
    simp

theorem finiteSimplexVertex_weight [DecidableEq V]
    (σ : Finset V) (v : V) (hv : v ∈ σ) (w : σ) :
    (finiteSimplexVertex σ v hv).val w = if (w : V) = v then 1 else 0 := rfl

theorem finiteSimplexVertex_faceInclusion_weight [DecidableEq V]
    (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces)
    (v : V) (hv : v ∈ σ) (w : V) :
    (faceInclusion K σ hσ (finiteSimplexVertex σ v hv)).weight w =
      if w = v then 1 else 0 := by
  classical
  by_cases hw : w ∈ σ
  · simp [faceInclusion, finiteSimplexVertex, hw]
  · have hne : w ≠ v := by
      intro h
      exact hw (h ▸ hv)
    simp [faceInclusion, hw, hne]

/-- Extend barycentric coordinates by zero from a subface to a larger face. -/
noncomputable def finiteSimplexInclude [DecidableEq V]
    (σ τ : Finset V) (hστ : σ ⊆ τ) :
    FiniteSimplex σ → FiniteSimplex τ := by
  classical
  intro x
  refine ⟨fun v => if hv : (v : V) ∈ σ then x.val ⟨v, hv⟩ else 0, ?_, ?_⟩
  · intro v
    by_cases hv : (v : V) ∈ σ
    · simpa [hv] using x.property.1 ⟨v, hv⟩
    · simp [hv]
  · have hs :
        (∑ v ∈ τ, if hv : v ∈ σ then x.val ⟨v, hv⟩ else 0) =
        ∑ v ∈ σ, if hv : v ∈ σ then x.val ⟨v, hv⟩ else 0 := by
      symm
      apply Finset.sum_subset hστ
      intro v hvτ hvσ
      simp [hvσ]
    have hsumσ :
        (∑ v ∈ σ, if hv : v ∈ σ then x.val ⟨v, hv⟩ else 0) = 1 := by
      calc
        _ = ∑ v ∈ σ.attach,
              (if hv : (v : V) ∈ σ then x.val ⟨(v : V), hv⟩ else 0) := by
                rw [← Finset.sum_attach]
        _ = ∑ v : σ, x.val v := by simp [Finset.univ_eq_attach]
        _ = 1 := x.property.2
    have hsumτ := hs.trans hsumσ
    change (∑ v : τ, if hv : (v : V) ∈ σ then x.val ⟨(v : V), hv⟩ else 0) = 1
    calc
      _ = ∑ v ∈ τ.attach,
            (if hv : (v : V) ∈ σ then x.val ⟨(v : V), hv⟩ else 0) := by
              simp [Finset.univ_eq_attach]
      _ = ∑ v ∈ τ, if hv : v ∈ σ then x.val ⟨v, hv⟩ else 0 := by
            exact Finset.sum_attach τ
              (fun v : V => if hv : v ∈ σ then x.val ⟨v, hv⟩ else 0)
      _ = 1 := hsumτ

theorem finiteSimplexInclude_continuous [DecidableEq V]
    (σ τ : Finset V) (hστ : σ ⊆ τ) :
    Continuous (finiteSimplexInclude σ τ hστ) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro v
  by_cases hv : (v : V) ∈ σ
  · convert ((continuous_apply (⟨v, hv⟩ : σ)).comp continuous_subtype_val) using 1
    funext a
    simp only [dite_eq_left hv, Function.comp_apply]
  · simpa [finiteSimplexInclude, hv] using
      (continuous_const : Continuous (fun _ : FiniteSimplex σ => (0 : ℝ)))

theorem finiteSimplexInclude_faceInclusion [DecidableEq V]
    (K : AbstractSimplicialComplex V)
    (σ τ : Finset V) (hσ : σ ∈ K.faces) (hτ : τ ∈ K.faces)
    (hστ : σ ⊆ τ) (x : FiniteSimplex σ) :
    faceInclusion K τ hτ (finiteSimplexInclude σ τ hστ x) =
      faceInclusion K σ hσ x := by
  apply point_ext
  funext v
  by_cases hvσ : v ∈ σ
  · have hvτ : v ∈ τ := hστ hvσ
    simp [faceInclusion, finiteSimplexInclude, hvσ, hvτ]
  · simp [faceInclusion, finiteSimplexInclude, hvσ]

theorem finiteSimplexInclude_segment [DecidableEq V]
    (σ τ : Finset V) (hστ : σ ⊆ τ)
    (x y : FiniteSimplex σ) (t : EdgeTime) :
    finiteSimplexInclude σ τ hστ (finiteSimplexSegment σ x y t) =
      finiteSimplexSegment τ
        (finiteSimplexInclude σ τ hστ x)
        (finiteSimplexInclude σ τ hστ y) t := by
  apply Subtype.ext
  funext v
  by_cases hv : (v : V) ∈ σ
  · simp [finiteSimplexInclude, finiteSimplexSegment, hv]
  · simp [finiteSimplexInclude, finiteSimplexSegment, hv]

theorem finiteSimplexInclude_vertex [DecidableEq V]
    (σ τ : Finset V) (hστ : σ ⊆ τ)
    (v : V) (hv : v ∈ σ) :
    finiteSimplexInclude σ τ hστ (finiteSimplexVertex σ v hv) =
      finiteSimplexVertex τ v (hστ hv) := by
  apply Subtype.ext
  funext w
  by_cases hw : (w : V) ∈ σ
  · simp [finiteSimplexInclude, finiteSimplexVertex, hw]
  · have hne : (w : V) ≠ v := by
      intro h
      exact hw (h ▸ hv)
    simp [finiteSimplexInclude, finiteSimplexVertex, hw, hne]

/-- A segment drawn in a subface agrees pointwise with the same segment
drawn in the containing face of the weak realization. -/
theorem faceSegment_subface [DecidableEq V]
    (K : AbstractSimplicialComplex V)
    (σ τ : Finset V) (hσ : σ ∈ K.faces) (hτ : τ ∈ K.faces)
    (hστ : σ ⊆ τ) (x y : FiniteSimplex σ) (t : EdgeTime) :
    faceSegment K σ hσ x y t =
      faceSegment K τ hτ
        (finiteSimplexInclude σ τ hστ x)
        (finiteSimplexInclude σ τ hστ y) t := by
  change faceInclusion K σ hσ (finiteSimplexSegment σ x y t) =
    faceInclusion K τ hτ
      (finiteSimplexSegment τ
        (finiteSimplexInclude σ τ hστ x)
        (finiteSimplexInclude σ τ hστ y) t)
  rw [← finiteSimplexInclude_segment]
  exact (finiteSimplexInclude_faceInclusion K σ τ hσ hτ hστ _).symm

/-- Any finite triangle face gives a genuine homotopy of its direct edge
against the two edges through the third vertex in the weak realization. -/
noncomputable def triangleVertexEdgeHomotopy [DecidableEq V]
    (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces)
    (a b c : V) (ha : a ∈ σ) (hb : b ∈ σ) (hc : c ∈ σ) :
    ((finiteSegmentPath σ
        (finiteSimplexVertex σ a ha)
        (finiteSimplexVertex σ b hb)).map
      (continuous_faceInclusion_local K σ hσ)).Homotopy
      (((finiteSegmentPath σ
        (finiteSimplexVertex σ a ha)
        (finiteSimplexVertex σ c hc)).trans
        (finiteSegmentPath σ
          (finiteSimplexVertex σ c hc)
          (finiteSimplexVertex σ b hb))).map
      (continuous_faceInclusion_local K σ hσ)) :=
  faceTriangleEdgeHomotopy K σ hσ
    (finiteSimplexVertex σ a ha)
    (finiteSimplexVertex σ b hb)
    (finiteSimplexVertex σ c hc)

end CurveComplex

#print axioms CurveComplex.realizationMap_continuous
#print axioms CurveComplex.faceSegment_continuous
#print axioms CurveComplex.finiteTriangleEdgeHomotopy
#print axioms CurveComplex.triangleVertexEdgeHomotopy

namespace CurveComplex

/-- Each barycentric coordinate is continuous for the actual weak topology. -/
theorem realization_weight_continuous (K : AbstractSimplicialComplex V)
    (v : V) : Continuous (fun x : RealizationPoint K => x.weight v) := by
  rw [continuous_def]
  intro U hU σ hσ
  by_cases hv : v ∈ σ
  · have heq : (fun x : RealizationPoint K => x.weight v) ∘
        faceInclusion K σ hσ =
        fun x : FiniteSimplex σ => x.val ⟨v, hv⟩ := by
      funext x
      simp [faceInclusion, hv]
    change IsOpen (((fun x : RealizationPoint K => x.weight v) ∘
      faceInclusion K σ hσ) ⁻¹' U)
    rw [heq]
    exact hU.preimage
      ((continuous_apply (⟨v, hv⟩ : σ)).comp continuous_subtype_val)
  · have heq : (fun x : RealizationPoint K => x.weight v) ∘
        faceInclusion K σ hσ = fun _ : FiniteSimplex σ => (0 : ℝ) := by
      funext x
      simp [faceInclusion, hv]
    change IsOpen (((fun x : RealizationPoint K => x.weight v) ∘
      faceInclusion K σ hσ) ⁻¹' U)
    rw [heq]
    exact hU.preimage continuous_const

def openVertexStar (K : AbstractSimplicialComplex V) (v : V) :
    Set (RealizationPoint K) := {x | 0 < x.weight v}

theorem openVertexStar_isOpen (K : AbstractSimplicialComplex V) (v : V) :
    IsOpen (openVertexStar K v) := by
  exact isOpen_lt continuous_const (realization_weight_continuous K v)

theorem exists_mem_openVertexStar (K : AbstractSimplicialComplex V)
    (x : RealizationPoint K) : ∃ v, x ∈ openVertexStar K v := by
  obtain ⟨σ, hσ, hz, hs⟩ := x.liesInFace
  by_contra hn
  push Not at hn
  have hzero : ∀ v, x.weight v = 0 := by
    intro v
    exact le_antisymm (le_of_not_gt (hn v)) (x.nonneg v)
  simp [hzero] at hs

/-- Finite-interval star subdivision for every continuous path in the weak
realization. Each entire closed subinterval lies in the star of one vertex. -/
theorem exists_openVertexStar_subdivision
    (K : AbstractSimplicialComplex V)
    (γ : EdgeTime → RealizationPoint K) (hγ : Continuous γ) :
    ∃ t : ℕ → EdgeTime, t 0 = 0 ∧ Monotone t ∧
      (∃ N, ∀ n ≥ N, t n = 1) ∧
      ∀ n, ∃ v : V,
        ∀ s ∈ Set.Icc (t n) (t (n + 1)), γ s ∈ openVertexStar K v := by
  let c : V → Set EdgeTime := fun v => γ ⁻¹' openVertexStar K v
  have hcopen : ∀ v, IsOpen (c v) := by
    intro v
    exact (openVertexStar_isOpen K v).preimage hγ
  have hcover : Set.univ ⊆ ⋃ v, c v := by
    intro s hs
    obtain ⟨v, hv⟩ := exists_mem_openVertexStar K (γ s)
    exact Set.mem_iUnion.mpr ⟨v, hv⟩
  obtain ⟨t, ht0, htmono, ⟨N, hN⟩, htstar⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hcopen hcover
  refine ⟨t, ht0, htmono, ⟨N, hN⟩, ?_⟩
  intro n
  obtain ⟨v, hv⟩ := htstar n
  exact ⟨v, fun s hs => hv hs⟩

theorem edge_face_of_positive_weights [DecidableEq V]
    (K : AbstractSimplicialComplex V)
    (x : RealizationPoint K) (a b : V)
    (ha : 0 < x.weight a) (hb : 0 < x.weight b) :
    ({a, b} : Finset V) ∈ K.faces := by
  obtain ⟨σ, hσ, hz, hs⟩ := x.liesInFace
  have haσ : a ∈ σ := by
    by_contra h
    exact (ne_of_gt ha) (hz a h)
  have hbσ : b ∈ σ := by
    by_contra h
    exact (ne_of_gt hb) (hz b h)
  exact (K.isRelLowerSet_faces hσ).2
    (by intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv;
        rcases hv with rfl | rfl <;> assumption)
    (by simp)

/-- A continuous path admits a finite star subdivision with a selected
vertex for each interval. Adjacent selected vertices form actual edges. -/
theorem exists_openVertexStar_edge_subdivision [DecidableEq V]
    (K : AbstractSimplicialComplex V)
    (γ : EdgeTime → RealizationPoint K) (hγ : Continuous γ) :
    ∃ (t : ℕ → EdgeTime) (v : ℕ → V),
      t 0 = 0 ∧ Monotone t ∧
      (∃ N, ∀ n ≥ N, t n = 1) ∧
      (∀ n, ∀ s ∈ Set.Icc (t n) (t (n + 1)),
        γ s ∈ openVertexStar K (v n)) ∧
      ∀ n, ({v n, v (n + 1)} : Finset V) ∈ K.faces := by
  obtain ⟨t, ht0, htmono, htend, htstar⟩ :=
    exists_openVertexStar_subdivision K γ hγ
  classical
  choose v hv using htstar
  refine ⟨t, v, ht0, htmono, htend, hv, ?_⟩
  intro n
  have hleft : t n ≤ t (n + 1) := htmono (Nat.le_succ n)
  have hright : t (n + 1) ≤ t (n + 1 + 1) := htmono (Nat.le_succ (n + 1))
  have ha : 0 < (γ (t (n + 1))).weight (v n) :=
    hv n (t (n + 1)) ⟨hleft, le_refl _⟩
  have hb : 0 < (γ (t (n + 1))).weight (v (n + 1)) :=
    hv (n + 1) (t (n + 1)) ⟨le_refl _, hright⟩
  exact edge_face_of_positive_weights K (γ (t (n + 1))) _ _ ha hb

end CurveComplex

#print axioms CurveComplex.exists_openVertexStar_subdivision
#print axioms CurveComplex.exists_openVertexStar_edge_subdivision

namespace CurveComplex

/-- A cutoff that turns on vertex interpolation only where its barycentric
weight is positive. If the weight is at least `δ`, time one reaches the vertex. -/
noncomputable def localizedConeFactor (K : AbstractSimplicialComplex V)
    (v : V) (δ : ℝ) (hδ : 0 < δ)
    (x : RealizationPoint K) (t : EdgeTime) : EdgeTime :=
  ⟨min 1 ((t : ℝ) * x.weight v / δ), by
    constructor
    · exact le_min (by norm_num)
        (div_nonneg (mul_nonneg t.property.1 (x.nonneg v)) hδ.le)
    · exact min_le_left _ _⟩

theorem localizedConeFactor_zero_weight (K : AbstractSimplicialComplex V)
    (v : V) (δ : ℝ) (hδ : 0 < δ)
    (x : RealizationPoint K) (t : EdgeTime)
    (hv : x.weight v = 0) : localizedConeFactor K v δ hδ x t = 0 := by
  apply Subtype.ext
  simp [localizedConeFactor, hv]

theorem localizedConeFactor_zero_time (K : AbstractSimplicialComplex V)
    (v : V) (δ : ℝ) (hδ : 0 < δ)
    (x : RealizationPoint K) :
    localizedConeFactor K v δ hδ x 0 = 0 := by
  apply Subtype.ext
  simp [localizedConeFactor]

theorem localizedConeFactor_one_of_le_weight
    (K : AbstractSimplicialComplex V)
    (v : V) (δ : ℝ) (hδ : 0 < δ)
    (x : RealizationPoint K) (hx : δ ≤ x.weight v) :
    localizedConeFactor K v δ hδ x 1 = 1 := by
  apply Subtype.ext
  have h : 1 ≤ x.weight v / δ :=
    (le_div_iff₀ hδ).mpr (by nlinarith)
  simp [localizedConeFactor, min_eq_left h]

noncomputable def localizedConeWeight [DecidableEq V] (K : AbstractSimplicialComplex V)
    (v : V) (δ : ℝ) (hδ : 0 < δ)
    (x : RealizationPoint K) (t : EdgeTime) (w : V) : ℝ :=
  (1 - (localizedConeFactor K v δ hδ x t : ℝ)) * x.weight w +
    if w = v then (localizedConeFactor K v δ hδ x t : ℝ) else 0

/-- A globally defined cutoff interpolation. It stays inside each original
face: outside the star the cutoff is zero. -/
noncomputable def localizedCone [DecidableEq V] (K : AbstractSimplicialComplex V)
    (v : V) (δ : ℝ) (hδ : 0 < δ)
    (x : RealizationPoint K) (t : EdgeTime) : RealizationPoint K := by
  classical
  let s := localizedConeFactor K v δ hδ x t
  refine ⟨localizedConeWeight K v δ hδ x t, ?_, ?_⟩
  · intro w
    unfold localizedConeWeight
    apply add_nonneg
    · exact mul_nonneg (sub_nonneg.mpr s.property.2) (x.nonneg w)
    · split_ifs
      · exact s.property.1
      · exact le_refl 0
  · obtain ⟨σ, hσ, hz, hsum⟩ := x.liesInFace
    refine ⟨σ, hσ, ?_, ?_⟩
    · intro w hw
      by_cases hv : v ∈ σ
      · have hne : w ≠ v := by
          intro h
          exact hw (h ▸ hv)
        simp [localizedConeWeight, hz w hw, hne]
      · have hsv : x.weight v = 0 := hz v hv
        have hs0 := localizedConeFactor_zero_weight K v δ hδ x t hsv
        simp [localizedConeWeight, hz w hw, hs0]
    · by_cases hv : v ∈ σ
      · have hdelta :
            (∑ w ∈ σ, if w = v then (s : ℝ) else 0) = s := by
          simp [hv]
        simp only [localizedConeWeight, Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [hsum, hdelta]
        ring
      · have hsv : x.weight v = 0 := hz v hv
        have hs0 := localizedConeFactor_zero_weight K v δ hδ x t hsv
        simpa [localizedConeWeight, hs0] using hsum

theorem localizedCone_zero [DecidableEq V]
    (K : AbstractSimplicialComplex V) (v : V)
    (δ : ℝ) (hδ : 0 < δ) (x : RealizationPoint K) :
    localizedCone K v δ hδ x 0 = x := by
  apply point_ext
  funext w
  simp [localizedCone, localizedConeWeight,
    localizedConeFactor_zero_time]

theorem localizedCone_one_of_le_weight [DecidableEq V]
    (K : AbstractSimplicialComplex V) (v : V)
    (δ : ℝ) (hδ : 0 < δ) (x : RealizationPoint K)
    (hx : δ ≤ x.weight v) (w : V) :
    (localizedCone K v δ hδ x 1).weight w =
      if w = v then 1 else 0 := by
  simp [localizedCone, localizedConeWeight,
    localizedConeFactor_one_of_le_weight K v δ hδ x hx]

/-- The cutoff interpolation restricted to a finite face, viewed in that
same face. -/
noncomputable def finiteLocalizedConeMap [DecidableEq V]
    (K : AbstractSimplicialComplex V) (v : V)
    (δ : ℝ) (hδ : 0 < δ)
    (σ : Finset V) (hσ : σ ∈ K.faces) :
    FiniteSimplex σ × EdgeTime → FiniteSimplex σ := by
  classical
  intro p
  let y := faceInclusion K σ hσ p.1
  let s := localizedConeFactor K v δ hδ y p.2
  refine ⟨fun w => localizedConeWeight K v δ hδ y p.2 w, ?_, ?_⟩
  · intro w
    exact (localizedCone K v δ hδ y p.2).nonneg w
  · have hsum : ∑ w ∈ σ, y.weight w = 1 := by
      calc
        _ = ∑ w ∈ σ.attach, y.weight (w : V) := by rw [← Finset.sum_attach]
        _ = ∑ w : σ, p.1.val w := by
          simp [y, faceInclusion, Finset.univ_eq_attach]
        _ = 1 := p.1.property.2
    by_cases hv : v ∈ σ
    · have hdelta :
          (∑ w ∈ σ, if w = v then (s : ℝ) else 0) = s := by simp [hv]
      have htotal :
          (∑ w ∈ σ, localizedConeWeight K v δ hδ y p.2 w) = 1 := by
        simp only [localizedConeWeight, Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [hsum, hdelta]
        ring
      simpa only [Finset.sum_attach, Finset.univ_eq_attach] using htotal
    · have hy0 : y.weight v = 0 := by simp [y, faceInclusion, hv]
      have hs0 := localizedConeFactor_zero_weight K v δ hδ y p.2 hy0
      have htotal :
          (∑ w ∈ σ, localizedConeWeight K v δ hδ y p.2 w) = 1 := by
        simpa [localizedConeWeight, hs0] using hsum
      simpa only [Finset.sum_attach, Finset.univ_eq_attach] using htotal

theorem finiteLocalizedConeMap_continuous [DecidableEq V]
    (K : AbstractSimplicialComplex V) (v : V)
    (δ : ℝ) (hδ : 0 < δ)
    (σ : Finset V) (hσ : σ ∈ K.faces) :
    Continuous (finiteLocalizedConeMap K v δ hδ σ hσ) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro w
  let y : FiniteSimplex σ × EdgeTime → RealizationPoint K :=
    fun p => faceInclusion K σ hσ p.1
  have hy (z : V) : Continuous (fun p : FiniteSimplex σ × EdgeTime => (y p).weight z) := by
    by_cases hz : z ∈ σ
    · have heq : (fun p : FiniteSimplex σ × EdgeTime => (y p).weight z) =
          fun p => p.1.val ⟨z, hz⟩ := by
        funext p
        simp [y, faceInclusion, hz]
      rw [heq]
      exact (continuous_apply (⟨z, hz⟩ : σ)).comp
        (continuous_subtype_val.comp continuous_fst)
    · have heq : (fun p : FiniteSimplex σ × EdgeTime => (y p).weight z) =
          fun _ => (0 : ℝ) := by
        funext p
        simp [y, faceInclusion, hz]
      rw [heq]
      exact continuous_const
  have ht : Continuous (fun p : FiniteSimplex σ × EdgeTime => (p.2 : ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  have hs : Continuous (fun p : FiniteSimplex σ × EdgeTime =>
      (localizedConeFactor K v δ hδ (y p) p.2 : ℝ)) := by
    change Continuous (fun p : FiniteSimplex σ × EdgeTime =>
      min (1 : ℝ) (((p.2 : ℝ) * (y p).weight v) / δ))
    exact continuous_const.min ((ht.mul (hy v)).div_const δ)
  change Continuous (fun p : FiniteSimplex σ × EdgeTime =>
    localizedConeWeight K v δ hδ (y p) p.2 w)
  have hone : Continuous (fun _ : FiniteSimplex σ × EdgeTime => (1 : ℝ)) :=
    continuous_const
  by_cases hw : (w : V) = v
  · convert ((hone.sub hs).mul (hy w)).add hs using 1
    funext p
    simp only [localizedConeWeight, ite_eq_left hw]
    rfl
  · convert (hone.sub hs).mul (hy w) using 1
    funext p
    simp only [localizedConeWeight, ite_eq_right hw, add_zero]
    rfl

theorem finiteLocalizedConeMap_faceInclusion [DecidableEq V]
    (K : AbstractSimplicialComplex V) (v : V)
    (δ : ℝ) (hδ : 0 < δ)
    (σ : Finset V) (hσ : σ ∈ K.faces)
    (p : FiniteSimplex σ × EdgeTime) :
    faceInclusion K σ hσ (finiteLocalizedConeMap K v δ hδ σ hσ p) =
      localizedCone K v δ hδ (faceInclusion K σ hσ p.1) p.2 := by
  apply point_ext
  funext w
  by_cases hw : w ∈ σ
  · simp [faceInclusion, finiteLocalizedConeMap, localizedCone, hw]
  · have hy0 : (faceInclusion K σ hσ p.1).weight w = 0 :=
      by simp [faceInclusion, hw]
    by_cases hv : v ∈ σ
    · have hne : w ≠ v := by
        intro h
        exact hw (h ▸ hv)
      simp [faceInclusion, localizedCone, localizedConeWeight, hw, hne]
    · have hv0 : (faceInclusion K σ hσ p.1).weight v = 0 := by
        simp [faceInclusion, hv]
      have hs0 := localizedConeFactor_zero_weight K v δ hδ
        (faceInclusion K σ hσ p.1) p.2 hv0
      rw [show (faceInclusion K σ hσ
          (finiteLocalizedConeMap K v δ hδ σ hσ p)).weight w = 0 by
            simp [faceInclusion, hw]]
      change (0 : ℝ) = localizedConeWeight K v δ hδ
        (faceInclusion K σ hσ p.1) p.2 w
      simp [localizedConeWeight, hy0, hs0]

theorem localizedCone_continuous [DecidableEq V]
    (K : AbstractSimplicialComplex V) (v : V)
    (δ : ℝ) (hδ : 0 < δ) :
    Continuous (fun p : RealizationPoint K × EdgeTime =>
      localizedCone K v δ hδ p.1 p.2) := by
  apply CurveComplexGenusTwo.Topology.continuous_realization_product_of_faces
  intro σ hσ
  have heq : (fun p : FiniteSimplex σ × EdgeTime =>
      localizedCone K v δ hδ (faceInclusion K σ hσ p.1) p.2) =
      faceInclusion K σ hσ ∘ finiteLocalizedConeMap K v δ hδ σ hσ := by
    funext p
    exact (finiteLocalizedConeMap_faceInclusion K v δ hδ σ hσ p).symm
  rw [heq]
  exact (continuous_faceInclusion_local K σ hσ).comp
    (finiteLocalizedConeMap_continuous K v δ hδ σ hσ)

theorem exists_positive_star_lower_bound
    (K : AbstractSimplicialComplex V)
    (γ : EdgeTime → RealizationPoint K) (hγ : Continuous γ)
    (a b : EdgeTime) (hab : a ≤ b) (v : V)
    (hstar : ∀ s ∈ Set.Icc a b, γ s ∈ openVertexStar K v) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ s ∈ Set.Icc a b, δ ≤ (γ s).weight v := by
  let f : EdgeTime → ℝ := fun s => (γ s).weight v
  have hf : Continuous f := (realization_weight_continuous K v).comp hγ
  obtain ⟨s, hs, hmin⟩ :=
    isCompact_Icc.exists_isMinOn
      (Set.nonempty_Icc.mpr hab) hf.continuousOn
  refine ⟨f s, hstar s hs, ?_⟩
  intro u hu
  exact hmin hu

/-- A path segment contained in an open vertex star contracts continuously to
that vertex as an unbased map on the segment. -/
theorem exists_star_interval_contraction [DecidableEq V]
    (K : AbstractSimplicialComplex V)
    (γ : EdgeTime → RealizationPoint K) (hγ : Continuous γ)
    (a b : EdgeTime) (hab : a ≤ b) (v : V)
    (hstar : ∀ s ∈ Set.Icc a b, γ s ∈ openVertexStar K v) :
    ∃ (z : RealizationPoint K),
      Nonempty (ContinuousMap.Homotopy
        ⟨fun s : Set.Icc a b => γ s.1,
          hγ.comp continuous_subtype_val⟩
        (ContinuousMap.const (Set.Icc a b) z)) := by
  obtain ⟨δ, hδ, hbound⟩ :=
    exists_positive_star_lower_bound K γ hγ a b hab v hstar
  let z := localizedCone K v δ hδ (γ a) 1
  have hza : δ ≤ (γ a).weight v := hbound a ⟨le_refl _, hab⟩
  refine ⟨z, ⟨{
    toFun := fun p => localizedCone K v δ hδ (γ p.2.1) p.1
    continuous_toFun := (localizedCone_continuous K v δ hδ).comp
      ((hγ.comp (continuous_subtype_val.comp continuous_snd)).prodMk continuous_fst)
    map_zero_left := by
      intro s
      exact localizedCone_zero K v δ hδ (γ s.1)
    map_one_left := by
      intro s
      change localizedCone K v δ hδ (γ s.1) 1 = z
      apply point_ext
      funext w
      rw [localizedCone_one_of_le_weight K v δ hδ (γ s.1)
        (hbound s.1 s.2) w]
      exact (localizedCone_one_of_le_weight K v δ hδ (γ a) hza w).symm
  }⟩⟩

/-- Straight contraction inside the open star of a vertex. -/
noncomputable def starCone [DecidableEq V] (K : AbstractSimplicialComplex V)
    (v : V) (x : openVertexStar K v) (t : EdgeTime) : openVertexStar K v := by
  classical
  let y : RealizationPoint K := by
    refine ⟨fun w => (1 - (t : ℝ)) * x.1.weight w +
        if w = v then (t : ℝ) else 0, ?_, ?_⟩
    · intro w
      apply add_nonneg
      · exact mul_nonneg (sub_nonneg.mpr t.property.2) (x.1.nonneg w)
      · split_ifs with h
        · exact t.property.1
        · exact le_refl _
    · obtain ⟨σ, hσ, hz, hs⟩ := x.1.liesInFace
      have hv : v ∈ σ := by
        by_contra hn
        exact (ne_of_gt x.2) (hz v hn)
      refine ⟨σ, hσ, ?_, ?_⟩
      · intro w hw
        have hne : w ≠ v := by intro h; exact hw (h ▸ hv)
        simp [hz w hw, hne]
      · simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [hs]
        simp [hv]
  refine ⟨y, ?_⟩
  change 0 < y.weight v
  dsimp only [y]
  simp only [ite_true]
  rcases eq_or_lt_of_le t.property.1 with ht | ht
  · have ht0 : (t : ℝ) = 0 := ht.symm
    have hx : 0 < x.1.weight v := x.2
    simpa [ht0] using hx
  · exact lt_of_lt_of_le ht (le_add_of_nonneg_left
      (mul_nonneg (sub_nonneg.mpr t.property.2) (x.1.nonneg v)))

theorem starCone_zero [DecidableEq V] (K : AbstractSimplicialComplex V)
    (v : V) (x : openVertexStar K v) : starCone K v x 0 = x := by
  apply Subtype.ext
  apply point_ext
  funext w
  simp [starCone]

theorem starCone_one [DecidableEq V] (K : AbstractSimplicialComplex V)
    (v : V) (x y : openVertexStar K v) :
    starCone K v x 1 = starCone K v y 1 := by
  apply Subtype.ext
  apply point_ext
  funext w
  simp [starCone]

noncomputable def starConeTime (K : AbstractSimplicialComplex V)
    (v : V) (δ : ℝ) (hδ : 0 < δ)
    (p : openVertexStar K v × EdgeTime) : EdgeTime :=
  ⟨min 1 ((p.2 : ℝ) * δ / p.1.1.weight v), by
    constructor
    · exact le_min (by norm_num)
        (div_nonneg (mul_nonneg p.2.property.1 hδ.le) (p.1.1.nonneg v))
    · exact min_le_left _ _⟩

theorem starConeTime_continuous (K : AbstractSimplicialComplex V)
    (v : V) (δ : ℝ) (hδ : 0 < δ) :
    Continuous (starConeTime K v δ hδ) := by
  apply Continuous.subtype_mk
  change Continuous (fun p : openVertexStar K v × EdgeTime =>
    min (1 : ℝ) ((p.2 : ℝ) * δ / p.1.1.weight v))
  have hw : Continuous (fun p : openVertexStar K v × EdgeTime => p.1.1.weight v) :=
    (realization_weight_continuous K v).comp
      (continuous_subtype_val.comp continuous_fst)
  have ht : Continuous (fun p : openVertexStar K v × EdgeTime => (p.2 : ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  exact continuous_const.min ((ht.mul_const δ).div hw
    (fun p => ne_of_gt p.1.2))

theorem starConeTime_factor (K : AbstractSimplicialComplex V)
    (v : V) (δ : ℝ) (hδ : 0 < δ)
    (p : openVertexStar K v × EdgeTime)
    (hp : δ ≤ p.1.1.weight v) :
    localizedConeFactor K v δ hδ p.1.1 (starConeTime K v δ hδ p) = p.2 := by
  apply Subtype.ext
  have hw : 0 < p.1.1.weight v := p.1.2
  have htime : (p.2 : ℝ) * δ / p.1.1.weight v ≤ 1 := by
    apply (div_le_iff₀ hw).mpr
    nlinarith [p.2.property.2]
  change min 1 ((min 1 ((p.2 : ℝ) * δ / p.1.1.weight v)) *
    p.1.1.weight v / δ) = (p.2 : ℝ)
  rw [min_eq_right htime]
  have hcalc : ((p.2 : ℝ) * δ / p.1.1.weight v) *
      p.1.1.weight v / δ = (p.2 : ℝ) := by
    field_simp
  rw [hcalc, min_eq_right p.2.property.2]

theorem starCone_eq_localizedCone [DecidableEq V]
    (K : AbstractSimplicialComplex V) (v : V)
    (δ : ℝ) (hδ : 0 < δ)
    (p : openVertexStar K v × EdgeTime)
    (hp : δ ≤ p.1.1.weight v) :
    (starCone K v p.1 p.2).1 =
      localizedCone K v δ hδ p.1.1 (starConeTime K v δ hδ p) := by
  apply point_ext
  funext w
  change (1 - (p.2 : ℝ)) * p.1.1.weight w +
      (if w = v then (p.2 : ℝ) else 0) =
    localizedConeWeight K v δ hδ p.1.1
      (starConeTime K v δ hδ p) w
  simp [localizedConeWeight, starConeTime_factor K v δ hδ p hp]

theorem starCone_continuous [DecidableEq V]
    (K : AbstractSimplicialComplex V) (v : V) :
    Continuous (fun p : openVertexStar K v × EdgeTime =>
      starCone K v p.1 p.2) := by
  let U : {δ : ℝ // 0 < δ} → Set (openVertexStar K v × EdgeTime) :=
    fun δ => {p | δ.1 < p.1.1.weight v}
  have hUopen : ∀ δ, IsOpen (U δ) := by
    intro δ
    exact isOpen_lt continuous_const
      ((realization_weight_continuous K v).comp
        (continuous_subtype_val.comp continuous_fst))
  have hUcover : ⋃ δ, U δ = Set.univ := by
    apply Set.eq_univ_of_forall
    intro p
    let δ : {δ : ℝ // 0 < δ} :=
      ⟨p.1.1.weight v / 2, half_pos p.1.2⟩
    exact Set.mem_iUnion.mpr ⟨δ, by
      change p.1.1.weight v / 2 < p.1.1.weight v
      have hp : 0 < p.1.1.weight v := p.1.2
      linarith⟩
  apply continuous_of_continuousOn_iUnion_of_isOpen ?_ hUopen hUcover
  intro δ
  rw [continuousOn_iff_continuous_domRestrict]
  apply Continuous.subtype_mk
  have heq : (fun q : U δ => (starCone K v q.1.1 q.1.2).1) =
      fun q : U δ => localizedCone K v δ.1 δ.2 q.1.1.1
        (starConeTime K v δ.1 δ.2 q.1) := by
    funext q
    exact starCone_eq_localizedCone K v δ.1 δ.2 q.1 (le_of_lt q.2)
  change Continuous (fun q : U δ => (starCone K v q.1.1 q.1.2).1)
  rw [heq]
  have hleft : Continuous (fun q : U δ => q.1.1.1) :=
    (continuous_subtype_val.comp continuous_fst).comp continuous_subtype_val
  have hright : Continuous (fun q : U δ => starConeTime K v δ.1 δ.2 q.1) :=
    (starConeTime_continuous K v δ.1 δ.2).comp continuous_subtype_val
  exact (localizedCone_continuous K v δ.1 δ.2).comp
    (hleft.prodMk hright)

theorem openVertexStar_contractible [DecidableEq V]
    (K : AbstractSimplicialComplex V) (v : V)
    (hne : Nonempty (openVertexStar K v)) :
    ContractibleSpace (openVertexStar K v) := by
  let x₀ := Classical.choice hne
  let z := starCone K v x₀ 1
  apply (contractible_iff_id_nullhomotopic (openVertexStar K v)).mpr
  refine ⟨z, ⟨{
    toFun := fun p => starCone K v p.2 p.1
    continuous_toFun := (starCone_continuous K v).comp continuous_swap
    map_zero_left := by
      intro x
      exact starCone_zero K v x
    map_one_left := by
      intro x
      exact starCone_one K v x x₀
  }⟩⟩

/-- Any two paths with the same endpoints and image inside one open vertex
star are homotopic relative to their endpoints. -/
theorem openVertexStar_paths_homotopic [DecidableEq V]
    (K : AbstractSimplicialComplex V) (v : V)
    {x y : RealizationPoint K} (p q : Path x y)
    (hp : ∀ t, p t ∈ openVertexStar K v)
    (hq : ∀ t, q t ∈ openVertexStar K v) :
    Path.Homotopic p q := by
  let xs : openVertexStar K v := ⟨x, by simpa only [p.source] using hp 0⟩
  let ys : openVertexStar K v := ⟨y, by simpa only [p.target] using hp 1⟩
  let ps : Path xs ys := {
    toFun := fun t => ⟨p t, hp t⟩
    continuous_toFun := p.continuous.subtype_mk _
    source' := by apply Subtype.ext; exact p.source
    target' := by apply Subtype.ext; exact p.target
  }
  let qs : Path xs ys := {
    toFun := fun t => ⟨q t, hq t⟩
    continuous_toFun := q.continuous.subtype_mk _
    source' := by apply Subtype.ext; exact q.source
    target' := by apply Subtype.ext; exact q.target
  }
  haveI : ContractibleSpace (openVertexStar K v) :=
    openVertexStar_contractible K v ⟨xs⟩
  haveI : SimplyConnectedSpace (openVertexStar K v) :=
    SimplyConnectedSpace.ofContractible _
  obtain ⟨H⟩ := SimplyConnectedSpace.paths_homotopic ps qs
  let F := H.map ⟨Subtype.val, continuous_subtype_val⟩
  have hpeq : ps.map continuous_subtype_val = p := by
    ext t
    rfl
  have hqeq : qs.map continuous_subtype_val = q := by
    ext t
    rfl
  exact ⟨F.cast hpeq hqeq⟩

/-- The radial path from a point in an open star to its vertex, with a fixed
anchor making all endpoints definitionally identical. -/
noncomputable def starConePath [DecidableEq V]
    (K : AbstractSimplicialComplex V) (v : V)
    (anchor x : openVertexStar K v) :
    Path x (starCone K v anchor 1) where
  toFun := starCone K v x
  continuous_toFun := (starCone_continuous K v).comp
    (continuous_const.prodMk continuous_id)
  source' := starCone_zero K v x
  target' := starCone_one K v x anchor

/-- The explicit two-radial-path replacement of a path in one open star. -/
noncomputable def starConeDetour [DecidableEq V]
    (K : AbstractSimplicialComplex V) (v : V)
    (anchor x y : openVertexStar K v) : Path x y :=
  (starConePath K v anchor x).trans (starConePath K v anchor y).symm

theorem starPath_homotopic_coneDetour [DecidableEq V]
    (K : AbstractSimplicialComplex V) (v : V)
    (anchor x y : openVertexStar K v) (p : Path x y) :
    Path.Homotopic p (starConeDetour K v anchor x y) := by
  haveI : ContractibleSpace (openVertexStar K v) :=
    openVertexStar_contractible K v ⟨anchor⟩
  haveI : SimplyConnectedSpace (openVertexStar K v) :=
    SimplyConnectedSpace.ofContractible _
  exact SimplyConnectedSpace.paths_homotopic p _

/-- A two-radial detour in the ambient realization, with its endpoints fixed. -/
noncomputable def starDetourPath [DecidableEq V]
    (K : AbstractSimplicialComplex V) (v : V)
    {x y : RealizationPoint K}
    (hx : x ∈ openVertexStar K v) (hy : y ∈ openVertexStar K v) :
    Path x y :=
  (starConeDetour K v ⟨x, hx⟩ ⟨x, hx⟩ ⟨y, hy⟩).map
    continuous_subtype_val

theorem path_homotopic_starDetour [DecidableEq V]
    (K : AbstractSimplicialComplex V) (v : V)
    {x y : RealizationPoint K} (p : Path x y)
    (hp : ∀ t, p t ∈ openVertexStar K v) :
    Path.Homotopic p
      (starDetourPath K v (by simpa only [p.source] using hp 0)
        (by simpa only [p.target] using hp 1)) := by
  let hx : x ∈ openVertexStar K v := by simpa only [p.source] using hp 0
  let hy : y ∈ openVertexStar K v := by simpa only [p.target] using hp 1
  let ps : Path (⟨x, hx⟩ : openVertexStar K v) ⟨y, hy⟩ := {
    toFun := fun t => ⟨p t, hp t⟩
    continuous_toFun := p.continuous.subtype_mk _
    source' := by apply Subtype.ext; exact p.source
    target' := by apply Subtype.ext; exact p.target
  }
  obtain ⟨H⟩ := starPath_homotopic_coneDetour K v
    ⟨x, hx⟩ ⟨x, hx⟩ ⟨y, hy⟩ ps
  let F := H.map ⟨Subtype.val, continuous_subtype_val⟩
  have hpeq : ps.map continuous_subtype_val = p := by
    ext t
    rfl
  exact ⟨F.cast hpeq rfl⟩

theorem subpath_mem_openVertexStar
    (K : AbstractSimplicialComplex V) (v : V)
    {x y : RealizationPoint K} (p : Path x y)
    (a b : EdgeTime) (hab : a ≤ b)
    (hstar : ∀ s ∈ Set.Icc a b, p s ∈ openVertexStar K v) :
    ∀ u, p.subpath a b u ∈ openVertexStar K v := by
  intro u
  have hu : p.subpath a b u ∈ Set.range (p.subpath a b) := ⟨u, rfl⟩
  rw [Path.range_subpath_of_le p a b hab] at hu
  obtain ⟨s, hs, hsu⟩ := hu
  exact hsu ▸ hstar s hs

/-- Replace every segment of a finite star subdivision by the explicit
two-radial detour through its selected vertex. -/
noncomputable def finiteStarDetours [DecidableEq V]
    (K : AbstractSimplicialComplex V)
    {x y : RealizationPoint K} (p : Path x y)
    {n : ℕ} (t : Fin (n + 1) → EdgeTime) (v : Fin n → V)
    (htmono : ∀ k : Fin n, t k.castSucc ≤ t k.succ)
    (hstar : ∀ k : Fin n, ∀ s ∈ Set.Icc (t k.castSucc) (t k.succ),
      p s ∈ openVertexStar K (v k))
    (k : Fin n) : Path (p (t k.castSucc)) (p (t k.succ)) :=
  starDetourPath K (v k)
    (hstar k (t k.castSucc) ⟨le_refl _, htmono k⟩)
    (hstar k (t k.succ) ⟨htmono k, le_refl _⟩)

theorem finiteStarDetours_homotopic [DecidableEq V]
    (K : AbstractSimplicialComplex V)
    {x y : RealizationPoint K} (p : Path x y)
    {n : ℕ} (t : Fin (n + 1) → EdgeTime) (v : Fin n → V)
    (htmono : ∀ k : Fin n, t k.castSucc ≤ t k.succ)
    (hstar : ∀ k : Fin n, ∀ s ∈ Set.Icc (t k.castSucc) (t k.succ),
      p s ∈ openVertexStar K (v k)) :
    Path.Homotopic
      (Path.concat (p ∘ t)
        (fun k => p.subpath (t k.castSucc) (t k.succ)))
      (Path.concat (p ∘ t)
        (finiteStarDetours K p t v htmono hstar)) := by
  apply Path.Homotopic.concat_hcomp
  intro k
  exact path_homotopic_starDetour K (v k)
    (p.subpath (t k.castSucc) (t k.succ))
    (subpath_mem_openVertexStar K (v k) p _ _ (htmono k) (hstar k))

/-- Every path has a finite, endpoint-fixed replacement by radial detours
through vertices selected from open stars. Consecutive selected vertices
span genuine edges of the complex. -/
theorem exists_finiteStarDetour_approximation [DecidableEq V]
    (K : AbstractSimplicialComplex V)
    {x y : RealizationPoint K} (p : Path x y) :
    ∃ (N : ℕ) (t : ℕ → EdgeTime) (v : ℕ → V)
      (htmono : Monotone t)
      (hstar : ∀ n, ∀ s ∈ Set.Icc (t n) (t (n + 1)),
        p s ∈ openVertexStar K (v n)),
      t 0 = 0 ∧ t N = 1 ∧
      (∀ n, ({v n, v (n + 1)} : Finset V) ∈ K.faces) ∧
      let τ : Fin (N + 1) → EdgeTime := fun k => t k
      let hmono : ∀ k : Fin N, τ k.castSucc ≤ τ k.succ :=
        fun k => htmono (Nat.le_succ k)
      let hstar : ∀ k : Fin N,
          ∀ s ∈ Set.Icc (τ k.castSucc) (τ k.succ),
          p s ∈ openVertexStar K (v k) := by
        intro k s hs
        exact hstar k s hs
      Path.Homotopic (p.subpath (τ 0) (τ (Fin.last N)))
        (Path.concat (p ∘ τ)
          (finiteStarDetours K p τ (fun k => v k) hmono hstar)) := by
  obtain ⟨t, v, ht0, htmono, ⟨N, hN⟩, hstar, hedge⟩ :=
    exists_openVertexStar_edge_subdivision K p p.continuous
  refine ⟨N, t, v, htmono, hstar, ht0, hN N le_rfl, hedge, ?_⟩
  let τ : Fin (N + 1) → EdgeTime := fun k => t k
  let hmono : ∀ k : Fin N, τ k.castSucc ≤ τ k.succ := by
    intro k
    exact htmono (Nat.le_succ k)
  let hstar' : ∀ k : Fin N,
      ∀ s ∈ Set.Icc (τ k.castSucc) (τ k.succ),
      p s ∈ openVertexStar K (v k) := by
    intro k s hs
    exact hstar k s hs
  exact (Path.Homotopic.concat_subpath p τ).symm.trans
    (finiteStarDetours_homotopic K p τ (fun k => v k) hmono hstar')

/-- Coordinates of a realization point represented in a chosen finite face. -/
noncomputable def finiteSimplexOfFace
    (K : AbstractSimplicialComplex V)
    (x : RealizationPoint K) (σ : Finset V)
    (_hzero : ∀ w ∉ σ, x.weight w = 0)
    (hsum : ∑ w ∈ σ, x.weight w = 1) : FiniteSimplex σ := by
  refine ⟨fun w => x.weight w, ?_, ?_⟩
  · intro w
    exact x.nonneg w
  · simpa only [Finset.sum_attach, Finset.univ_eq_attach] using hsum

theorem finiteSimplexOfFace_inclusion
    (K : AbstractSimplicialComplex V)
    (x : RealizationPoint K) (σ : Finset V) (hσ : σ ∈ K.faces)
    (hzero : ∀ w ∉ σ, x.weight w = 0)
    (hsum : ∑ w ∈ σ, x.weight w = 1) :
    faceInclusion K σ hσ (finiteSimplexOfFace K x σ hzero hsum) = x := by
  apply point_ext
  funext w
  by_cases hw : w ∈ σ
  · simp [faceInclusion, finiteSimplexOfFace, hw]
  · simp [faceInclusion, hw, hzero w hw]

/-- A radial leg in an open star is literally an affine segment in any finite
face carrying the point and the selected vertex. -/
theorem starCone_eq_faceSegment [DecidableEq V]
    (K : AbstractSimplicialComplex V) (v : V)
    (x : RealizationPoint K) (hx : x ∈ openVertexStar K v)
    (σ : Finset V) (hσ : σ ∈ K.faces)
    (hzero : ∀ w ∉ σ, x.weight w = 0)
    (hsum : ∑ w ∈ σ, x.weight w = 1)
    (hv : v ∈ σ) (t : EdgeTime) :
    (starCone K v ⟨x, hx⟩ t).1 =
      faceSegment K σ hσ
        (finiteSimplexOfFace K x σ hzero hsum)
        (finiteSimplexVertex σ v hv) t := by
  apply point_ext
  funext w
  by_cases hw : w ∈ σ
  · simp [starCone, faceSegment, faceInclusion, finiteSimplexSegment,
      finiteSimplexOfFace, finiteSimplexVertex, hw]
  · have hne : w ≠ v := by intro h; exact hw (h ▸ hv)
    simp [starCone, faceSegment, faceInclusion, finiteSimplexSegment,
      finiteSimplexOfFace, finiteSimplexVertex, hw, hzero w hw, hne]

/-- At a subdivision junction, the two radial legs through the original
point can be replaced by the direct edge between the selected star vertices. -/
noncomputable def faceJunctionEdgeHomotopy [DecidableEq V]
    (K : AbstractSimplicialComplex V)
    (x : RealizationPoint K) (σ : Finset V) (hσ : σ ∈ K.faces)
    (hzero : ∀ w ∉ σ, x.weight w = 0)
    (hsum : ∑ w ∈ σ, x.weight w = 1)
    (a b : V) (ha : a ∈ σ) (hb : b ∈ σ) :
    (((finiteSegmentPath σ
        (finiteSimplexVertex σ a ha)
        (finiteSimplexOfFace K x σ hzero hsum)).trans
      (finiteSegmentPath σ
        (finiteSimplexOfFace K x σ hzero hsum)
        (finiteSimplexVertex σ b hb))).map
      (continuous_faceInclusion_local K σ hσ)).Homotopy
    ((finiteSegmentPath σ
        (finiteSimplexVertex σ a ha)
        (finiteSimplexVertex σ b hb)).map
      (continuous_faceInclusion_local K σ hσ)) :=
  (faceTriangleEdgeHomotopy K σ hσ
    (finiteSimplexVertex σ a ha)
    (finiteSimplexVertex σ b hb)
    (finiteSimplexOfFace K x σ hzero hsum)).symm

noncomputable def starVertexPoint [DecidableEq V]
    (K : AbstractSimplicialComplex V) (v : V)
    (x : RealizationPoint K) (hx : x ∈ openVertexStar K v) :
    RealizationPoint K :=
  (starCone K v ⟨x, hx⟩ 1).1

noncomputable def radialPath [DecidableEq V]
    (K : AbstractSimplicialComplex V) (v : V)
    (x : RealizationPoint K) (hx : x ∈ openVertexStar K v) :
    Path x (starVertexPoint K v x hx) :=
  (starConePath K v ⟨x, hx⟩ ⟨x, hx⟩).map continuous_subtype_val

theorem radialPath_apply [DecidableEq V]
    (K : AbstractSimplicialComplex V) (v : V)
    (x : RealizationPoint K) (hx : x ∈ openVertexStar K v)
    (t : EdgeTime) :
    radialPath K v x hx t = (starCone K v ⟨x, hx⟩ t).1 := rfl

theorem radialPath_eq_faceSegment [DecidableEq V]
    (K : AbstractSimplicialComplex V) (v : V)
    (x : RealizationPoint K) (hx : x ∈ openVertexStar K v)
    (σ : Finset V) (hσ : σ ∈ K.faces)
    (hzero : ∀ w ∉ σ, x.weight w = 0)
    (hsum : ∑ w ∈ σ, x.weight w = 1)
    (hv : v ∈ σ) (t : EdgeTime) :
    radialPath K v x hx t =
      faceSegment K σ hσ
        (finiteSimplexOfFace K x σ hzero hsum)
        (finiteSimplexVertex σ v hv) t :=
  starCone_eq_faceSegment K v x hx σ hσ hzero hsum hv t

theorem finiteSimplexSegment_symm
    (σ : Finset V) (x y : FiniteSimplex σ) (t : EdgeTime) :
    finiteSimplexSegment σ x y (unitInterval.symm t) =
      finiteSimplexSegment σ y x t := by
  apply Subtype.ext
  funext w
  change (1 - (1 - (t : ℝ))) * x.val w + (1 - (t : ℝ)) * y.val w =
    (1 - (t : ℝ)) * y.val w + (t : ℝ) * x.val w
  ring

theorem finiteSegmentPath_symm
    (σ : Finset V) (x y : FiniteSimplex σ) :
    (finiteSegmentPath σ x y).symm = finiteSegmentPath σ y x := by
  apply DFunLike.ext
  intro t
  exact finiteSimplexSegment_symm σ x y t

theorem starVertexPoint_eq [DecidableEq V]
    (K : AbstractSimplicialComplex V) (v : V)
    (x y : RealizationPoint K)
    (hx : x ∈ openVertexStar K v)
    (hy : y ∈ openVertexStar K v) :
    starVertexPoint K v x hx = starVertexPoint K v y hy :=
  congrArg Subtype.val (starCone_one K v ⟨x, hx⟩ ⟨y, hy⟩)

theorem starVertexPoint_eq_faceVertex [DecidableEq V]
    (K : AbstractSimplicialComplex V) (v : V)
    (x : RealizationPoint K) (hx : x ∈ openVertexStar K v)
    (σ : Finset V) (hσ : σ ∈ K.faces)
    (_hzero : ∀ w ∉ σ, x.weight w = 0)
    (_hsum : ∑ w ∈ σ, x.weight w = 1)
    (hv : v ∈ σ) :
    starVertexPoint K v x hx =
      faceInclusion K σ hσ (finiteSimplexVertex σ v hv) := by
  apply point_ext
  funext w
  rw [finiteSimplexVertex_faceInclusion_weight]
  simp [starVertexPoint, starCone]

theorem exists_common_carrier_of_star_intersection
    (K : AbstractSimplicialComplex V)
    (x : RealizationPoint K) (a b : V)
    (ha : x ∈ openVertexStar K a)
    (hb : x ∈ openVertexStar K b) :
    ∃ σ : Finset V, σ ∈ K.faces ∧
      (∀ w ∉ σ, x.weight w = 0) ∧
      (∑ w ∈ σ, x.weight w = 1) ∧ a ∈ σ ∧ b ∈ σ := by
  obtain ⟨σ, hσ, hzero, hsum⟩ := x.liesInFace
  refine ⟨σ, hσ, hzero, hsum, ?_, ?_⟩
  · by_contra h
    exact (ne_of_gt ha) (hzero a h)
  · by_contra h
    exact (ne_of_gt hb) (hzero b h)

theorem radialPath_eq_facePath_cast [DecidableEq V]
    (K : AbstractSimplicialComplex V) (v : V)
    (x : RealizationPoint K) (hx : x ∈ openVertexStar K v)
    (σ : Finset V) (hσ : σ ∈ K.faces)
    (hzero : ∀ w ∉ σ, x.weight w = 0)
    (hsum : ∑ w ∈ σ, x.weight w = 1)
    (hv : v ∈ σ) :
    radialPath K v x hx =
      ((finiteSegmentPath σ
        (finiteSimplexOfFace K x σ hzero hsum)
        (finiteSimplexVertex σ v hv)).map
        (continuous_faceInclusion_local K σ hσ)).cast
        (finiteSimplexOfFace_inclusion K x σ hσ hzero hsum).symm
        (starVertexPoint_eq_faceVertex K v x hx σ hσ hzero hsum hv) := by
  apply DFunLike.ext
  intro t
  exact radialPath_eq_faceSegment K v x hx σ hσ hzero hsum hv t

/-- Two adjacent detours can be cancelled at their common endpoint whenever
the junction triangle homotopy is supplied. -/
theorem two_detours_cancel
    {X : Type*} [TopologicalSpace X]
    {x₀ x₁ x₂ a₀ a₁ : X}
    (r₀ : Path x₀ a₀) (r₁ : Path x₁ a₀)
    (s₁ : Path x₁ a₁) (r₂ : Path x₂ a₁)
    (e : Path a₀ a₁)
    (h : Path.Homotopic (r₁.symm.trans s₁) e) :
    Path.Homotopic
      ((r₀.trans r₁.symm).trans (s₁.trans r₂.symm))
      ((r₀.trans e).trans r₂.symm) := by
  have hA := Path.Homotopic.trans_assoc r₀ r₁.symm (s₁.trans r₂.symm)
  have hB := Path.Homotopic.hcomp (Path.Homotopic.refl r₀)
    ((Path.Homotopic.trans_assoc r₁.symm s₁ r₂.symm).symm)
  have hC := Path.Homotopic.hcomp (Path.Homotopic.refl r₀)
    (Path.Homotopic.hcomp h (Path.Homotopic.refl r₂.symm))
  exact hA.trans (hB.trans (hC.trans (Path.Homotopic.trans_assoc r₀ e r₂.symm).symm))

theorem append_detour_cancel
    {X : Type*} [TopologicalSpace X]
    {x₀ x₁ x₂ a₀ a₁ a₂ : X}
    (r₀ : Path x₀ a₀) (edges : Path a₀ a₁)
    (r₁ : Path x₁ a₁) (s₁ : Path x₁ a₂)
    (r₂ : Path x₂ a₂) (e : Path a₁ a₂)
    (h : Path.Homotopic (r₁.symm.trans s₁) e) :
    Path.Homotopic
      ((r₀.trans (edges.trans r₁.symm)).trans
        (s₁.trans r₂.symm))
      (r₀.trans ((edges.trans e).trans r₂.symm)) := by
  have h0 := Path.Homotopic.trans_assoc r₀ (edges.trans r₁.symm)
    (s₁.trans r₂.symm)
  have h1 := Path.Homotopic.hcomp (Path.Homotopic.refl r₀)
    (Path.Homotopic.trans_assoc edges r₁.symm (s₁.trans r₂.symm))
  have h2 := Path.Homotopic.hcomp (Path.Homotopic.refl r₀)
    (Path.Homotopic.hcomp (Path.Homotopic.refl edges)
      (Path.Homotopic.trans_assoc r₁.symm s₁ r₂.symm).symm)
  have h3 := Path.Homotopic.hcomp (Path.Homotopic.refl r₀)
    (Path.Homotopic.hcomp (Path.Homotopic.refl edges)
      (Path.Homotopic.hcomp h (Path.Homotopic.refl r₂.symm)))
  have h4 := Path.Homotopic.hcomp (Path.Homotopic.refl r₀)
    (Path.Homotopic.trans_assoc edges e r₂.symm).symm
  exact h0.trans (h1.trans (h2.trans (h3.trans h4)))

/-- The finite cancellation induction for arbitrary endpoint-compatible
radial paths and junction edge homotopies. -/
theorem finite_detours_cancel
    {X : Type*} [TopologicalSpace X]
    (n : ℕ)
    (x : Fin (n + 2) → X) (z : Fin (n + 1) → X)
    (A : (k : Fin (n + 1)) → Path (x k.castSucc) (z k))
    (B : (k : Fin (n + 1)) → Path (x k.succ) (z k))
    (E : (k : Fin n) → Path (z k.castSucc) (z k.succ))
    (H : ∀ k : Fin n, Path.Homotopic
      ((B k.castSucc).symm.trans (A k.succ)) (E k)) :
    Path.Homotopic
      (Path.concat x (fun k => (A k).trans (B k).symm))
      ((A 0).trans ((Path.concat z E).trans (B (Fin.last n)).symm)) := by
  induction n with
  | zero =>
      simp only [Path.concat_succ, Path.concat_zero]
      exact (Path.Homotopic.refl_trans _).trans
        (Path.Homotopic.hcomp (Path.Homotopic.refl _)
          (Path.Homotopic.refl_trans _).symm)
  | succ n ih =>
      let x' : Fin (n + 2) → X := fun k => x k.castSucc
      let z' : Fin (n + 1) → X := fun k => z k.castSucc
      let A' : (k : Fin (n + 1)) → Path (x' k.castSucc) (z' k) :=
        fun k => A k.castSucc
      let B' : (k : Fin (n + 1)) → Path (x' k.succ) (z' k) :=
        fun k => B k.castSucc
      let E' : (k : Fin n) → Path (z' k.castSucc) (z' k.succ) :=
        fun k => E k.castSucc
      have H' : ∀ k : Fin n, Path.Homotopic
          ((B' k.castSucc).symm.trans (A' k.succ)) (E' k) := by
        intro k
        exact H k.castSucc
      have hi := ih x' z' A' B' E' H'
      conv_lhs => rw [Path.concat_succ]
      conv_rhs => rw [Path.concat_succ]
      have hchain := (Path.Homotopic.hcomp hi
        (Path.Homotopic.refl _)).trans
        (append_detour_cancel (A 0) (Path.concat z' E')
          (B (Fin.last n).castSucc)
          (A (Fin.last (n + 1))) (B (Fin.last (n + 1)))
          (E (Fin.last n)) (H (Fin.last n)))
      exact hchain

def IsAffineVertexEdge [DecidableEq V] (K : AbstractSimplicialComplex V)
    {u w : RealizationPoint K} (e : Path u w) : Prop :=
  ∃ (σ : Finset V) (hσ : σ ∈ K.faces)
    (a b : V) (ha : a ∈ σ) (hb : b ∈ σ)
    (hu : u = faceInclusion K σ hσ (finiteSimplexVertex σ a ha))
    (hw : w = faceInclusion K σ hσ (finiteSimplexVertex σ b hb)),
    e = ((finiteSegmentPath σ
      (finiteSimplexVertex σ a ha)
      (finiteSimplexVertex σ b hb)).map
        (continuous_faceInclusion_local K σ hσ)).cast hu hw

theorem IsAffineVertexEdge.cast [DecidableEq V]
    (K : AbstractSimplicialComplex V)
    {u w u' w' : RealizationPoint K} (e : Path u w)
    (he : IsAffineVertexEdge K e)
    (hu : u' = u) (hw : w' = w) :
    IsAffineVertexEdge K (e.cast hu hw) := by
  obtain ⟨σ, hσ, a, b, ha, hb, hsource, htarget, heq⟩ := he
  refine ⟨σ, hσ, a, b, ha, hb,
    hu.trans hsource, hw.trans htarget, ?_⟩
  rw [heq]
  apply DFunLike.ext
  intro t
  rfl

theorem IsAffineVertexEdge.exists_edge_face [DecidableEq V]
    (K : AbstractSimplicialComplex V)
    {u w : RealizationPoint K} (e : Path u w)
    (he : IsAffineVertexEdge K e) :
    ∃ a b : V, ({a, b} : Finset V) ∈ K.faces := by
  obtain ⟨σ, hσ, a, b, ha, hb, _, _, _⟩ := he
  refine ⟨a, b, ?_⟩
  exact (K.isRelLowerSet_faces hσ).2
    (by intro v hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl <;> assumption)
    (by simp)

/-- The two radial legs at an overlap point are genuinely homotopic to the
direct affine vertex edge between their star vertices. -/
theorem exists_radial_junction_edge [DecidableEq V]
    (K : AbstractSimplicialComplex V)
    (x : RealizationPoint K) (a b : V)
    (ha : x ∈ openVertexStar K a)
    (hb : x ∈ openVertexStar K b) :
    ∃ e : Path (starVertexPoint K a x ha) (starVertexPoint K b x hb),
      Path.Homotopic
        ((radialPath K a x ha).symm.trans (radialPath K b x hb)) e ∧
      IsAffineVertexEdge K e := by
  obtain ⟨σ, hσ, hzero, hsum, haσ, hbσ⟩ :=
    exists_common_carrier_of_star_intersection K x a b ha hb
  classical
  let X := finiteSimplexOfFace K x σ hzero hsum
  let A := finiteSimplexVertex σ a haσ
  let B := finiteSimplexVertex σ b hbσ
  let f := continuous_faceInclusion_local K σ hσ
  have hX : x = faceInclusion K σ hσ X :=
    (finiteSimplexOfFace_inclusion K x σ hσ hzero hsum).symm
  have hA : starVertexPoint K a x ha = faceInclusion K σ hσ A :=
    starVertexPoint_eq_faceVertex K a x ha σ hσ hzero hsum haσ
  have hB : starVertexPoint K b x hb = faceInclusion K σ hσ B :=
    starVertexPoint_eq_faceVertex K b x hb σ hσ hzero hsum hbσ
  let e : Path (starVertexPoint K a x ha) (starVertexPoint K b x hb) :=
    ((finiteSegmentPath σ A B).map f).cast hA hB
  refine ⟨e, ?_, ?_⟩
  have hra : radialPath K a x ha =
      ((finiteSegmentPath σ X A).map f).cast hX hA :=
    radialPath_eq_facePath_cast K a x ha σ hσ hzero hsum haσ
  have hrb : radialPath K b x hb =
      ((finiteSegmentPath σ X B).map f).cast hX hB :=
    radialPath_eq_facePath_cast K b x hb σ hσ hzero hsum hbσ
  have hstart : (radialPath K a x ha).symm.trans
      (radialPath K b x hb) =
      (((finiteSegmentPath σ A X).trans
        (finiteSegmentPath σ X B)).map f).cast hA hB := by
    rw [hra, hrb]
    rw [← Path.cast_symm]
    rw [← Path.cast_trans]
    simp only [Path.map_symm, finiteSegmentPath_symm, Path.map_trans]
  let F := faceJunctionEdgeHomotopy K x σ hσ hzero hsum a b haσ hbσ
  · exact ⟨F.pathCast hA hB |>.cast hstart.symm rfl⟩
  · exact ⟨σ, hσ, a, b, haσ, hbσ, hA, hB, rfl⟩

theorem anchoredRadial_eq_radial_cast [DecidableEq V]
    (K : AbstractSimplicialComplex V) (v : V)
    (anchor : openVertexStar K v)
    (x : RealizationPoint K) (hx : x ∈ openVertexStar K v) :
    (starConePath K v anchor ⟨x, hx⟩).map continuous_subtype_val =
      (radialPath K v x hx).cast rfl
        (starVertexPoint_eq K v anchor.1 x anchor.2 hx) := by
  apply DFunLike.ext
  intro t
  rfl

theorem exists_anchored_radial_junction_edge [DecidableEq V]
    (K : AbstractSimplicialComplex V)
    (x : RealizationPoint K) (a b : V)
    (ha : x ∈ openVertexStar K a)
    (hb : x ∈ openVertexStar K b)
    (anchorA : openVertexStar K a)
    (anchorB : openVertexStar K b) :
    ∃ e : Path (starCone K a anchorA 1).1
      (starCone K b anchorB 1).1,
      Path.Homotopic
        (((starConePath K a anchorA ⟨x, ha⟩).map
          continuous_subtype_val).symm.trans
          ((starConePath K b anchorB ⟨x, hb⟩).map
            continuous_subtype_val)) e ∧
      IsAffineVertexEdge K e := by
  obtain ⟨e, he, hedge⟩ := exists_radial_junction_edge K x a b ha hb
  let hA : (starCone K a anchorA 1).1 = starVertexPoint K a x ha :=
    starVertexPoint_eq K a anchorA.1 x anchorA.2 ha
  let hB : (starCone K b anchorB 1).1 = starVertexPoint K b x hb :=
    starVertexPoint_eq K b anchorB.1 x anchorB.2 hb
  refine ⟨e.cast hA hB, ?_, IsAffineVertexEdge.cast K e hedge hA hB⟩
  have hleft := anchoredRadial_eq_radial_cast K a anchorA x ha
  have hright := anchoredRadial_eq_radial_cast K b anchorB x hb
  have hstart :
      ((starConePath K a anchorA ⟨x, ha⟩).map
        continuous_subtype_val).symm.trans
        ((starConePath K b anchorB ⟨x, hb⟩).map
          continuous_subtype_val) =
      ((radialPath K a x ha).symm.trans
        (radialPath K b x hb)).cast hA hB := by
    rw [hleft, hright]
    rfl
  exact hstart.symm ▸ (he.pathCast hA hB)

noncomputable def finiteStarAnchor
    (K : AbstractSimplicialComplex V)
    {x y : RealizationPoint K} (p : Path x y)
    {n : ℕ} (t : Fin (n + 1) → EdgeTime) (v : Fin n → V)
    (htmono : ∀ k : Fin n, t k.castSucc ≤ t k.succ)
    (hstar : ∀ k : Fin n,
      ∀ s ∈ Set.Icc (t k.castSucc) (t k.succ),
      p s ∈ openVertexStar K (v k))
    (k : Fin n) : openVertexStar K (v k) :=
  ⟨p (t k.castSucc), hstar k (t k.castSucc) ⟨le_refl _, htmono k⟩⟩

noncomputable def finiteStarEnd
    (K : AbstractSimplicialComplex V)
    {x y : RealizationPoint K} (p : Path x y)
    {n : ℕ} (t : Fin (n + 1) → EdgeTime) (v : Fin n → V)
    (htmono : ∀ k : Fin n, t k.castSucc ≤ t k.succ)
    (hstar : ∀ k : Fin n,
      ∀ s ∈ Set.Icc (t k.castSucc) (t k.succ),
      p s ∈ openVertexStar K (v k))
    (k : Fin n) : openVertexStar K (v k) :=
  ⟨p (t k.succ), hstar k (t k.succ) ⟨htmono k, le_refl _⟩⟩

noncomputable def finiteStarVertices [DecidableEq V]
    (K : AbstractSimplicialComplex V)
    {x y : RealizationPoint K} (p : Path x y)
    {n : ℕ} (t : Fin (n + 1) → EdgeTime) (v : Fin n → V)
    (htmono : ∀ k : Fin n, t k.castSucc ≤ t k.succ)
    (hstar : ∀ k : Fin n,
      ∀ s ∈ Set.Icc (t k.castSucc) (t k.succ),
      p s ∈ openVertexStar K (v k))
    (k : Fin n) : RealizationPoint K :=
  (starCone K (v k) (finiteStarAnchor K p t v htmono hstar k) 1).1

noncomputable def finiteStarRadialStart [DecidableEq V]
    (K : AbstractSimplicialComplex V)
    {x y : RealizationPoint K} (p : Path x y)
    {n : ℕ} (t : Fin (n + 1) → EdgeTime) (v : Fin n → V)
    (htmono : ∀ k : Fin n, t k.castSucc ≤ t k.succ)
    (hstar : ∀ k : Fin n,
      ∀ s ∈ Set.Icc (t k.castSucc) (t k.succ),
      p s ∈ openVertexStar K (v k))
    (k : Fin n) :
    Path (p (t k.castSucc))
      (finiteStarVertices K p t v htmono hstar k) :=
  (starConePath K (v k)
    (finiteStarAnchor K p t v htmono hstar k)
    (finiteStarAnchor K p t v htmono hstar k)).map continuous_subtype_val

noncomputable def finiteStarRadialEnd [DecidableEq V]
    (K : AbstractSimplicialComplex V)
    {x y : RealizationPoint K} (p : Path x y)
    {n : ℕ} (t : Fin (n + 1) → EdgeTime) (v : Fin n → V)
    (htmono : ∀ k : Fin n, t k.castSucc ≤ t k.succ)
    (hstar : ∀ k : Fin n,
      ∀ s ∈ Set.Icc (t k.castSucc) (t k.succ),
      p s ∈ openVertexStar K (v k))
    (k : Fin n) :
    Path (p (t k.succ))
      (finiteStarVertices K p t v htmono hstar k) :=
  (starConePath K (v k)
    (finiteStarAnchor K p t v htmono hstar k)
    (finiteStarEnd K p t v htmono hstar k)).map continuous_subtype_val

theorem finiteStarDetours_eq_radial [DecidableEq V]
    (K : AbstractSimplicialComplex V)
    {x y : RealizationPoint K} (p : Path x y)
    {n : ℕ} (t : Fin (n + 1) → EdgeTime) (v : Fin n → V)
    (htmono : ∀ k : Fin n, t k.castSucc ≤ t k.succ)
    (hstar : ∀ k : Fin n,
      ∀ s ∈ Set.Icc (t k.castSucc) (t k.succ),
      p s ∈ openVertexStar K (v k))
    (k : Fin n) :
    finiteStarDetours K p t v htmono hstar k =
      (finiteStarRadialStart K p t v htmono hstar k).trans
        (finiteStarRadialEnd K p t v htmono hstar k).symm := by
  unfold finiteStarDetours starDetourPath starConeDetour
    finiteStarRadialStart finiteStarRadialEnd
  rw [Path.map_trans, ← Path.map_symm]
  rfl

theorem exists_finiteStarJunctionEdges [DecidableEq V]
    (K : AbstractSimplicialComplex V)
    {x y : RealizationPoint K} (p : Path x y)
    (n : ℕ) (t : Fin (n + 2) → EdgeTime) (v : Fin (n + 1) → V)
    (htmono : ∀ k : Fin (n + 1), t k.castSucc ≤ t k.succ)
    (hstar : ∀ k : Fin (n + 1),
      ∀ s ∈ Set.Icc (t k.castSucc) (t k.succ),
      p s ∈ openVertexStar K (v k)) :
    ∃ E : (k : Fin n) → Path
        (finiteStarVertices K p t v htmono hstar k.castSucc)
        (finiteStarVertices K p t v htmono hstar k.succ),
      (∀ k : Fin n, Path.Homotopic
        ((finiteStarRadialEnd K p t v htmono hstar k.castSucc).symm.trans
          (finiteStarRadialStart K p t v htmono hstar k.succ))
        (E k)) ∧
      ∀ k : Fin n, IsAffineVertexEdge K (E k) := by
  classical
  have hex : ∀ k : Fin n, ∃ e : Path
        (finiteStarVertices K p t v htmono hstar k.castSucc)
        (finiteStarVertices K p t v htmono hstar k.succ),
      Path.Homotopic
        ((finiteStarRadialEnd K p t v htmono hstar k.castSucc).symm.trans
          (finiteStarRadialStart K p t v htmono hstar k.succ)) e ∧
      IsAffineVertexEdge K e := by
    intro k
    obtain ⟨e, he, hedge⟩ := exists_anchored_radial_junction_edge K
      (p (t k.succ.castSucc)) (v k.castSucc) (v k.succ)
      (finiteStarEnd K p t v htmono hstar k.castSucc).2
      (finiteStarAnchor K p t v htmono hstar k.succ).2
      (finiteStarAnchor K p t v htmono hstar k.castSucc)
      (finiteStarAnchor K p t v htmono hstar k.succ)
    exact ⟨e, he, hedge⟩
  choose E hE using hex
  exact ⟨E, fun k => (hE k).1, fun k => (hE k).2⟩

/-- Geometric realization of the finite cancellation: every supplied star
subdivision is homotopic to its selected edge chain, with radial legs only
at the two outer endpoints. -/
theorem exists_finiteStarEdgeChain [DecidableEq V]
    (K : AbstractSimplicialComplex V)
    {x y : RealizationPoint K} (p : Path x y)
    (n : ℕ) (t : Fin (n + 2) → EdgeTime) (v : Fin (n + 1) → V)
    (htmono : ∀ k : Fin (n + 1), t k.castSucc ≤ t k.succ)
    (hstar : ∀ k : Fin (n + 1),
      ∀ s ∈ Set.Icc (t k.castSucc) (t k.succ),
      p s ∈ openVertexStar K (v k)) :
    ∃ E : (k : Fin n) → Path
        (finiteStarVertices K p t v htmono hstar k.castSucc)
        (finiteStarVertices K p t v htmono hstar k.succ),
      (∀ k : Fin n, IsAffineVertexEdge K (E k)) ∧
      Path.Homotopic
        (p.subpath (t 0) (t (Fin.last (n + 1))))
        ((finiteStarRadialStart K p t v htmono hstar 0).trans
          ((Path.concat (finiteStarVertices K p t v htmono hstar) E).trans
            (finiteStarRadialEnd K p t v htmono hstar (Fin.last n)).symm)) := by
  obtain ⟨E, hE, hAffine⟩ := exists_finiteStarJunctionEdges K p n t v htmono hstar
  refine ⟨E, hAffine, ?_⟩
  let A := finiteStarRadialStart K p t v htmono hstar
  let B := finiteStarRadialEnd K p t v htmono hstar
  let z := finiteStarVertices K p t v htmono hstar
  have hsub := (Path.Homotopic.concat_subpath p t).symm
  have hdetour := finiteStarDetours_homotopic K p t v htmono hstar
  have hpathEq : Path.concat (p ∘ t)
        (finiteStarDetours K p t v htmono hstar) =
      Path.concat (p ∘ t) (fun k => (A k).trans (B k).symm) := by
    congr 1
    funext k
    exact finiteStarDetours_eq_radial K p t v htmono hstar k
  rw [hpathEq] at hdetour
  exact hsub.trans (hdetour.trans (finite_detours_cancel n
    (p ∘ t) z A B E hE))

/-- Arbitrary continuous paths in the weak realization admit an affine edge
chain approximation, with only radial paths at their two original endpoints. -/
theorem exists_path_affine_edge_chain [DecidableEq V]
    (K : AbstractSimplicialComplex V)
    {x y : RealizationPoint K} (p : Path x y) :
    ∃ (n : ℕ) (t : Fin (n + 2) → EdgeTime)
      (v : Fin (n + 1) → V)
      (htmono : ∀ k : Fin (n + 1), t k.castSucc ≤ t k.succ)
      (hstar : ∀ k : Fin (n + 1),
        ∀ s ∈ Set.Icc (t k.castSucc) (t k.succ),
        p s ∈ openVertexStar K (v k))
      (E : (k : Fin n) → Path
        (finiteStarVertices K p t v htmono hstar k.castSucc)
        (finiteStarVertices K p t v htmono hstar k.succ)),
      t 0 = 0 ∧ t (Fin.last (n + 1)) = 1 ∧
      (∀ k : Fin n, IsAffineVertexEdge K (E k)) ∧
      Path.Homotopic
        (p.subpath (t 0) (t (Fin.last (n + 1))))
        ((finiteStarRadialStart K p t v htmono hstar 0).trans
          ((Path.concat (finiteStarVertices K p t v htmono hstar) E).trans
            (finiteStarRadialEnd K p t v htmono hstar (Fin.last n)).symm)) := by
  obtain ⟨t₀, v₀, ht0, htmono₀, ⟨N, hN⟩, hstar₀, _⟩ :=
    exists_openVertexStar_edge_subdivision K p p.continuous
  have hNne : N ≠ 0 := by
    intro h
    subst N
    have h01 : (0 : EdgeTime) = 1 := ht0.symm.trans (hN 0 le_rfl)
    have hval := congrArg Subtype.val h01
    norm_num at hval
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hNne
  let t : Fin (n + 2) → EdgeTime := fun k => t₀ k
  let v : Fin (n + 1) → V := fun k => v₀ k
  have htmono : ∀ k : Fin (n + 1), t k.castSucc ≤ t k.succ := by
    intro k
    exact htmono₀ (Nat.le_succ k)
  have hstar : ∀ k : Fin (n + 1),
      ∀ s ∈ Set.Icc (t k.castSucc) (t k.succ),
      p s ∈ openVertexStar K (v k) := by
    intro k s hs
    exact hstar₀ k s hs
  obtain ⟨E, hAffine, hApprox⟩ :=
    exists_finiteStarEdgeChain K p n t v htmono hstar
  exact ⟨n, t, v, htmono, hstar, E, ht0,
    hN (n + 1) le_rfl, hAffine, hApprox⟩

noncomputable def realizationVertex [DecidableEq V]
    (K : AbstractSimplicialComplex V) (v : V)
    (hv : ({v} : Finset V) ∈ K.faces) : RealizationPoint K :=
  faceInclusion K {v} hv
    (finiteSimplexVertex {v} v (by simp))

theorem realizationVertex_weight [DecidableEq V]
    (K : AbstractSimplicialComplex V) (v : V)
    (hv : ({v} : Finset V) ∈ K.faces) (w : V) :
    (realizationVertex K v hv).weight w = if w = v then 1 else 0 :=
  finiteSimplexVertex_faceInclusion_weight K {v} hv v (by simp) w

theorem realizationVertex_star_eq [DecidableEq V]
    (K : AbstractSimplicialComplex V) (v w : V)
    (hv : ({v} : Finset V) ∈ K.faces)
    (h : realizationVertex K v hv ∈ openVertexStar K w) : w = v := by
  have hpos : 0 < (realizationVertex K v hv).weight w := h
  rw [realizationVertex_weight] at hpos
  by_contra hne
  simp [hne] at hpos

theorem starCone_vertex_self [DecidableEq V]
    (K : AbstractSimplicialComplex V) (v : V)
    (hv : ({v} : Finset V) ∈ K.faces)
    (hstar : realizationVertex K v hv ∈ openVertexStar K v)
    (t : EdgeTime) :
    (starCone K v ⟨realizationVertex K v hv, hstar⟩ t).1 =
      realizationVertex K v hv := by
  apply point_ext
  funext w
  rw [realizationVertex_weight]
  change (1 - (t : ℝ)) *
      (realizationVertex K v hv).weight w +
    (if w = v then (t : ℝ) else 0) = if w = v then 1 else 0
  rw [realizationVertex_weight]
  by_cases hw : w = v <;> simp [hw]

theorem starCone_of_vertex_in_star [DecidableEq V]
    (K : AbstractSimplicialComplex V) (v w : V)
    (hv : ({v} : Finset V) ∈ K.faces)
    (hstar : realizationVertex K v hv ∈ openVertexStar K w)
    (t : EdgeTime) :
    (starCone K w ⟨realizationVertex K v hv, hstar⟩ t).1 =
      realizationVertex K v hv := by
  have hw := realizationVertex_star_eq K v w hv hstar
  subst w
  exact starCone_vertex_self K v hv hstar t

theorem drop_constant_radials
    {X : Type*} [TopologicalSpace X]
    {x y a b : X}
    (p : Path x y) (A : Path x a) (E : Path a b) (B : Path y b)
    (h : Path.Homotopic p (A.trans (E.trans B.symm)))
    (hA : ∀ t, A t = x) (hB : ∀ t, B t = y) :
    ∃ e : Path x y, Path.Homotopic p e ∧
      e = E.cast (by simpa only [A.target] using (hA 1).symm)
        (by simpa only [B.target] using (hB 1).symm) := by
  have ha : x = a := by simpa only [A.target] using (hA 1).symm
  have hb : y = b := by simpa only [B.target] using (hB 1).symm
  refine ⟨E.cast ha hb, ?_, rfl⟩
  cases ha
  cases hb
  have hAeq : A = Path.refl x := by
    apply DFunLike.ext
    intro t
    exact hA t
  have hBeq : B = Path.refl y := by
    apply DFunLike.ext
    intro t
    exact hB t
  rw [hAeq, hBeq] at h
  exact h.trans ((Path.Homotopic.refl_trans _).trans
    (Path.Homotopic.trans_refl E))

def IsFiniteAffineEdgePath [DecidableEq V]
    (K : AbstractSimplicialComplex V)
    {x y : RealizationPoint K} (q : Path x y) : Prop :=
  ∃ (n : ℕ) (z : Fin (n + 1) → RealizationPoint K)
    (E : (k : Fin n) → Path (z k.castSucc) (z k.succ))
    (hx : x = z 0) (hy : y = z (Fin.last n)),
    (∀ k, IsAffineVertexEdge K (E k)) ∧
      q = (Path.concat z E).cast hx hy

theorem exists_based_loop_affine_edge_path [DecidableEq V]
    (K : AbstractSimplicialComplex V)
    (base : V) (hbase : ({base} : Finset V) ∈ K.faces)
    (p : Path (realizationVertex K base hbase)
      (realizationVertex K base hbase)) :
    ∃ q : Path (realizationVertex K base hbase)
        (realizationVertex K base hbase),
      Path.Homotopic p q ∧ IsFiniteAffineEdgePath K q := by
  obtain ⟨n, t, v, htmono, hstar, E, ht0, htlast, hAffine, hApprox⟩ :=
    exists_path_affine_edge_chain K p
  let b := realizationVertex K base hbase
  let z := finiteStarVertices K p t v htmono hstar
  let A := finiteStarRadialStart K p t v htmono hstar 0
  let B := finiteStarRadialEnd K p t v htmono hstar (Fin.last n)
  let edge := Path.concat z E
  have hfirstStar : b ∈ openVertexStar K (v 0) := by
    have h := hstar 0 (t 0) ⟨le_refl _, htmono 0⟩
    simpa only [ht0, p.source] using h
  have hlastStar : b ∈ openVertexStar K (v (Fin.last n)) := by
    have h := hstar (Fin.last n) (t (Fin.last (n + 1)))
      ⟨htmono (Fin.last n), le_refl _⟩
    simpa only [htlast, p.target] using h
  have hA : ∀ u, A u = b := by
    intro u
    change (starCone K (v 0)
      (finiteStarAnchor K p t v htmono hstar 0) u).1 = b
    have hanchor : finiteStarAnchor K p t v htmono hstar 0 =
        (⟨b, hfirstStar⟩ : openVertexStar K (v 0)) := by
      apply Subtype.ext
      change p (t 0) = b
      rw [ht0, p.source]
    rw [hanchor]
    exact starCone_of_vertex_in_star K base (v 0) hbase hfirstStar u
  have hB : ∀ u, B u = b := by
    intro u
    change (starCone K (v (Fin.last n))
      (finiteStarEnd K p t v htmono hstar (Fin.last n)) u).1 = b
    have hend : finiteStarEnd K p t v htmono hstar (Fin.last n) =
        (⟨b, hlastStar⟩ : openVertexStar K (v (Fin.last n))) := by
      apply Subtype.ext
      change p (t (Fin.last (n + 1))) = b
      rw [htlast, p.target]
    rw [hend]
    exact starCone_of_vertex_in_star K base (v (Fin.last n)) hbase hlastStar u
  have hx : b = p (t 0) := by rw [ht0, p.source]
  have hy : b = p (t (Fin.last (n + 1))) := by rw [htlast, p.target]
  let A' : Path b (z 0) := A.cast hx rfl
  let B' : Path b (z (Fin.last n)) := B.cast hy rfl
  have hApprox' : p.Homotopic (A'.trans (edge.trans B'.symm)) := by
    have hcast := hApprox.pathCast hx hy
    have hleft : (p.subpath (t 0) (t (Fin.last (n + 1)))).cast hx hy = p := by
      apply DFunLike.ext
      intro u
      simp [Path.subpath, ht0, htlast]
    have hright :
        ((A.trans (edge.trans B.symm)).cast hx hy) =
          A'.trans (edge.trans B'.symm) := rfl
    rcases hcast with ⟨F⟩
    exact ⟨F.cast hleft hright⟩
  obtain ⟨q, hq, hqcast⟩ :=
    drop_constant_radials p A' edge B' hApprox' hA hB
  refine ⟨q, hq, n, z, E, ?_, ?_, hAffine, ?_⟩
  · simpa [A] using (hA 1).symm.trans A.target
  · simpa [B] using (hB 1).symm.trans B.target
  · exact hqcast



end CurveComplex

#print axioms CurveComplex.localizedCone
#print axioms CurveComplex.localizedCone_continuous
#print axioms CurveComplex.exists_positive_star_lower_bound
#print axioms CurveComplex.exists_star_interval_contraction
