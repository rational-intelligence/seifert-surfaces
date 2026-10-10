import Mathlib

/-!
An eight-sided disk with the boundary word a b a⁻¹ b⁻¹ c d c⁻¹ d⁻¹.
This file constructs the actual side-pairing quotient and checks its finite
incidence certificate. Smooth manifold and homology claims are separate.
-/

namespace CurveComplex.Octagon

abbrev Side := Fin 8
abbrev Edge := Fin 4
abbrev Disk := Metric.closedBall (0 : ℂ) 1

def pair (i : Side) : Side :=
  match i.val with
  | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1
  | 4 => 6 | 5 => 7 | 6 => 4 | _ => 5

def edge (i : Side) : Edge :=
  match i.val with
  | 0 | 2 => 0
  | 1 | 3 => 1
  | 4 | 6 => 2
  | _ => 3

def next (i : Side) : Side := ⟨(i.val + 1) % 8, Nat.mod_lt _ (by decide)⟩

theorem pair_involutive (i : Side) : pair (pair i) = i := by
  fin_cases i <;> decide

theorem pair_fixed_point_free (i : Side) : pair i ≠ i := by
  fin_cases i <;> decide

theorem edge_pair (i : Side) : edge (pair i) = edge i := by
  fin_cases i <;> decide

theorem pair_opposite_orientation (i : Side) :
    (i.val < 2 ∨ 4 ≤ i.val ∧ i.val < 6) ↔
      ¬(pair i).val < 2 ∧ ¬(4 ≤ (pair i).val ∧ (pair i).val < 6) := by
  fin_cases i <;> decide

/-- Each of the four edge labels occurs at exactly two side positions. -/
theorem edge_fiber_card (e : Edge) :
    (Finset.univ.filter (fun i : Side => edge i = e)).card = 2 := by
  fin_cases e <;> decide

/-- The full side pairing reverses the boundary parameter. -/
def boundaryPair (p : Side × unitInterval) : Side × unitInterval :=
  (pair p.1, unitInterval.symm p.2)

theorem boundaryPair_involutive : Function.Involutive boundaryPair := by
  rintro ⟨i, t⟩
  simp [boundaryPair, pair_involutive, unitInterval.symm_symm]

noncomputable def boundaryPairEquiv : Side × unitInterval ≃ Side × unitInterval :=
  Equiv.ofBijective boundaryPair boundaryPair_involutive.bijective

/-- The geometric side is the corresponding eighth of the unit circle. -/
noncomputable def side (i : Side) (t : unitInterval) : Disk :=
  ⟨Circle.exp (2 * Real.pi * ((i.val : ℝ) + t) / 8), by
    rw [Metric.mem_closedBall]
    exact (Circle.exp (2 * Real.pi * ((i.val : ℝ) + t) / 8)).property.le⟩

theorem continuous_side (i : Side) : Continuous (side i) := by
  have hc : Continuous (fun t : unitInterval =>
      2 * Real.pi * ((i.val : ℝ) + (t : ℝ)) / 8) := by
    fun_prop
  apply Continuous.subtype_mk
  exact continuous_subtype_val.comp (Circle.exp.continuous.comp hc)

theorem continuous_side_pair (i : Side) :
    Continuous (fun t : unitInterval =>
      (side i t, side (pair i) (unitInterval.symm t))) := by
  exact (continuous_side i).prodMk
    ((continuous_side (pair i)).comp unitInterval.symmHomeomorph.continuous)

theorem side_pair_graph_isClosed (i : Side) :
    IsClosed (Set.range (fun t : unitInterval =>
      (side i t, side (pair i) (unitInterval.symm t)))) := by
  exact (isCompact_range (continuous_side_pair i)).isClosed

theorem side_norm (i : Side) (t : unitInterval) : ‖(side i t : ℂ)‖ = 1 := by
  change ‖(Circle.exp (2 * Real.pi * ((i.val : ℝ) + t) / 8) : ℂ)‖ = 1
  exact Circle.norm_coe _

theorem side_injective (i : Side) : Function.Injective (side i) := by
  intro t u h
  have hC : Circle.exp (2 * Real.pi * ((i.val : ℝ) + t) / 8) =
      Circle.exp (2 * Real.pi * ((i.val : ℝ) + u) / 8) := by
    apply Circle.ext
    exact congrArg (fun x : Disk => (x : ℂ)) h
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hC
  have htu : (t : ℝ) = u + 8 * (m : ℝ) := by
    have h' := hm
    field_simp [Real.pi_ne_zero] at h'
    nlinarith [h']
  have hm0 : m = 0 := by
    by_contra hmne
    rcases lt_or_gt_of_ne hmne with hneg | hpos
    · have hle : (m : ℝ) ≤ -1 := by exact_mod_cast (show m ≤ -1 by omega)
      have hu1 := u.property.2
      have ht0 := t.property.1
      linarith [htu]
    · have hge : (m : ℝ) ≥ 1 := by exact_mod_cast (show m ≥ 1 by omega)
      have hu0 := u.property.1
      have ht1 := t.property.2
      linarith [htu]
  have : (t : ℝ) = u := by simpa [hm0] using htu
  exact Subtype.ext this

theorem side_eq_same_or_endpoints (i j : Side) (t u : unitInterval)
    (h : side i t = side j u) :
    (i = j ∧ t = u) ∨ ((t = 0 ∨ t = 1) ∧ (u = 0 ∨ u = 1)) := by
  have hC : Circle.exp (2 * Real.pi * ((i.val : ℝ) + t) / 8) =
      Circle.exp (2 * Real.pi * ((j.val : ℝ) + u) / 8) := by
    apply Circle.ext
    exact congrArg (fun x : Disk => (x : ℂ)) h
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hC
  have hang : (i.val : ℝ) + t = (j.val : ℝ) + u + 8 * (m : ℝ) := by
    have h' := hm
    field_simp [Real.pi_ne_zero] at h'
    nlinarith [h']
  have hi0 : (0 : ℝ) ≤ i.val := by exact_mod_cast (Nat.zero_le i.val)
  have hj0 : (0 : ℝ) ≤ j.val := by exact_mod_cast (Nat.zero_le j.val)
  have hi7 : (i.val : ℝ) ≤ 7 := by exact_mod_cast (Nat.le_of_lt_succ i.isLt)
  have hj7 : (j.val : ℝ) ≤ 7 := by exact_mod_cast (Nat.le_of_lt_succ j.isLt)
  have ht0 := t.property.1
  have ht1 := t.property.2
  have hu0 := u.property.1
  have hu1 := u.property.2
  by_cases hm0 : m = 0
  · simp only [hm0, Int.cast_zero, mul_zero, add_zero] at hang
    rcases lt_trichotomy i.val j.val with hij | hij | hij
    · have hgap : (i.val : ℝ) + 1 ≤ j.val := by
        exact_mod_cast (Nat.succ_le_iff.mpr hij)
      right
      constructor
      · right; apply Subtype.ext; change (t : ℝ) = 1; linarith
      · left; apply Subtype.ext; change (u : ℝ) = 0; linarith
    · left
      have htu : t = u := Subtype.ext (by simpa [hij] using hang)
      exact ⟨Fin.ext hij, htu⟩
    · have hgap : (j.val : ℝ) + 1 ≤ i.val := by
        exact_mod_cast (Nat.succ_le_iff.mpr hij)
      right
      constructor
      · left; apply Subtype.ext; change (t : ℝ) = 0; linarith
      · right; apply Subtype.ext; change (u : ℝ) = 1; linarith
  · rcases lt_or_gt_of_ne hm0 with hmneg | hmpos
    · have hmle : (m : ℝ) ≤ -1 := by
        exact_mod_cast (show m ≤ -1 by omega)
      right
      constructor
      · left; apply Subtype.ext; change (t : ℝ) = 0; linarith
      · right; apply Subtype.ext; change (u : ℝ) = 1; linarith
    · have hmge : (1 : ℝ) ≤ m := by
        exact_mod_cast (show 1 ≤ m by omega)
      right
      constructor
      · right; apply Subtype.ext; change (t : ℝ) = 1; linarith
      · left; apply Subtype.ext; change (u : ℝ) = 0; linarith

noncomputable def vertexPoint (i : Side) : Disk := side i 0

theorem side_end_next (i : Side) : side i 1 = vertexPoint (next i) := by
  apply Subtype.ext
  change (Circle.exp (2 * Real.pi * ((i.val : ℝ) + 1) / 8) : ℂ) =
    Circle.exp (2 * Real.pi * (((next i).val : ℝ) + 0) / 8)
  apply congrArg (fun z : Circle => (z : ℂ))
  apply Circle.exp_eq_exp.mpr
  fin_cases i
  · exact ⟨0, by norm_num [next]⟩
  · exact ⟨0, by norm_num [next]⟩
  · exact ⟨0, by norm_num [next]⟩
  · exact ⟨0, by norm_num [next]⟩
  · exact ⟨0, by norm_num [next]⟩
  · exact ⟨0, by norm_num [next]⟩
  · exact ⟨0, by norm_num [next]⟩
  · exact ⟨1, by norm_num [next]⟩

def vertexSet : Set Disk := Set.range vertexPoint

theorem side_endpoint_mem_vertexSet (i : Side) (t : unitInterval)
    (ht : t = 0 ∨ t = 1) : side i t ∈ vertexSet := by
  rcases ht with rfl | rfl
  · exact ⟨i, rfl⟩
  · exact ⟨next i, (side_end_next i).symm⟩

theorem side_mem_vertexSet_iff (i : Side) (t : unitInterval) :
    side i t ∈ vertexSet ↔ t = 0 ∨ t = 1 := by
  constructor
  · rintro ⟨j, hj⟩
    have h := side_eq_same_or_endpoints i j t 0 hj.symm
    rcases h with ⟨_, ht⟩ | ⟨ht, _⟩
    · exact Or.inl ht
    · exact ht
  · exact side_endpoint_mem_vertexSet i t

theorem vertexSet_isClosed : IsClosed vertexSet := by
  have hf : (vertexSet : Set Disk).Finite := Set.finite_range vertexPoint
  exact hf.isClosed

/-- A generating relation: identified sides are traversed in opposite directions. -/
def SideGlue (x y : Disk) : Prop :=
  ∃ i : Side, ∃ t : unitInterval,
    x = side i t ∧ y = side (pair i) (unitInterval.symm t)

def Pairing (x y : Disk) : Prop :=
  ∃ i : Side, ∃ t : unitInterval,
    x = side i t ∧ y = side (pair i) (unitInterval.symm t)

def NormalForm (x y : Disk) : Prop :=
  x = y ∨ (x ∈ vertexSet ∧ y ∈ vertexSet) ∨ Pairing x y

theorem sideGlue_eq_pairing {x y : Disk} : SideGlue x y ↔ Pairing x y := Iff.rfl

theorem pairing_symm {x y : Disk} (h : Pairing x y) : Pairing y x := by
  rcases h with ⟨i, t, rfl, rfl⟩
  refine ⟨pair i, unitInterval.symm t, ?_, ?_⟩
  · rfl
  · rw [unitInterval.symm_symm, pair_involutive]

theorem pairing_mem_vertexSet {x y : Disk} (h : Pairing x y) :
    x ∈ vertexSet ↔ y ∈ vertexSet := by
  rcases h with ⟨i, t, rfl, rfl⟩
  rw [side_mem_vertexSet_iff, side_mem_vertexSet_iff]
  simp [or_comm]

theorem sideGlue_normalForm {x y : Disk} (h : SideGlue x y) : NormalForm x y := by
  rcases h with ⟨i, t, rfl, rfl⟩
  by_cases ht : t = 0 ∨ t = 1
  · exact Or.inr (Or.inl ⟨side_endpoint_mem_vertexSet i t ht,
      side_endpoint_mem_vertexSet (pair i) (unitInterval.symm t) (by
        rcases ht with rfl | rfl <;> simp)⟩)
  · exact Or.inr (Or.inr ⟨i, t, rfl, rfl⟩)

theorem pairing_pairing_cancel {x y z : Disk} (hxy : Pairing x y) (hyz : Pairing y z) :
    NormalForm x z := by
  rcases hxy with ⟨i, t, rfl, rfl⟩
  rcases hyz with ⟨j, u, hjx, hjz⟩
  have hmid : side (pair i) (unitInterval.symm t) = side j u := hjx
  rcases side_eq_same_or_endpoints (pair i) j (unitInterval.symm t) u hmid with hsame | hend
  · rcases hsame with ⟨hij, htu⟩
    left
    rw [hjz, ← hij, ← htu]
    simp [unitInterval.symm_symm, pair_involutive]
  · right
    left
    constructor
    · exact side_endpoint_mem_vertexSet i t (by
        rcases hend.1 with h | h
        · right
          simpa using congrArg unitInterval.symm h
        · left
          simpa using congrArg unitInterval.symm h)
    · rw [hjz]
      exact side_endpoint_mem_vertexSet (pair j) (unitInterval.symm u) (by
        rcases hend.2 with h | h
        · right
          simpa using congrArg unitInterval.symm h
        · left
          simpa using congrArg unitInterval.symm h)

theorem normalForm_refl (x : Disk) : NormalForm x x := Or.inl rfl

theorem normalForm_symm {x y : Disk} (h : NormalForm x y) : NormalForm y x := by
  rcases h with rfl | ⟨hx, hy⟩ | hp
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨hy, hx⟩)
  · exact Or.inr (Or.inr (pairing_symm hp))

theorem normalForm_trans {x y z : Disk} (hxy : NormalForm x y) (hyz : NormalForm y z) :
    NormalForm x z := by
  rcases hxy with rfl | ⟨hx, hy⟩ | hxy
  · exact hyz
  · rcases hyz with rfl | ⟨_, hz⟩ | hyz
    · exact Or.inr (Or.inl ⟨hx, hy⟩)
    · exact Or.inr (Or.inl ⟨hx, hz⟩)
    · exact Or.inr (Or.inl ⟨hx, (pairing_mem_vertexSet hyz).mp hy⟩)
  · rcases hyz with rfl | ⟨hy, hz⟩ | hyz
    · exact Or.inr (Or.inr hxy)
    · exact Or.inr (Or.inl ⟨(pairing_mem_vertexSet hxy).mpr hy, hz⟩)
    · exact pairing_pairing_cancel hxy hyz

theorem eqvGen_normalForm {x y : Disk} (h : _root_.Relation.EqvGen SideGlue x y) :
    NormalForm x y := by
  induction h with
  | rel x y h => exact sideGlue_normalForm h
  | refl => exact normalForm_refl _
  | symm x y _ ih => exact normalForm_symm ih
  | trans x y z _ _ ih₁ ih₂ => exact normalForm_trans ih₁ ih₂

theorem sideGlue_graph_isClosed :
    IsClosed {p : Disk × Disk | SideGlue p.1 p.2} := by
  have heq : {p : Disk × Disk | SideGlue p.1 p.2} =
      ⋃ i : Side, Set.range (fun t : unitInterval =>
        (side i t, side (pair i) (unitInterval.symm t))) := by
    ext ⟨x, y⟩
    simp only [Set.mem_ofPred_eq, SideGlue, Set.mem_iUnion, Set.mem_range]
    constructor
    · rintro ⟨i, t, rfl, rfl⟩
      exact ⟨i, t, rfl⟩
    · rintro ⟨i, t, h⟩
      exact ⟨i, t, (Prod.mk.inj h).1.symm, (Prod.mk.inj h).2.symm⟩
  rw [heq]
  exact isClosed_iUnion_of_finite (fun i => side_pair_graph_isClosed i)

abbrev Relation : Setoid Disk := _root_.Relation.EqvGen.setoid SideGlue
abbrev Surface : Type := Quotient Relation

def mk : Disk → Surface := Quotient.mk Relation

theorem side_pairing (i : Side) (t : unitInterval) :
    mk (side i t) = mk (side (pair i) (unitInterval.symm t)) :=
  Quotient.sound (_root_.Relation.EqvGen.rel _ _ ⟨i, t, rfl, rfl⟩)

theorem side_pairing_reverse (i : Side) (t : unitInterval) :
    mk (side (pair i) t) = mk (side i (unitInterval.symm t)) := by
  simpa [pair_involutive] using side_pairing (pair i) t

theorem boundaryPair_quotient_invariant (p : Side × unitInterval) :
    mk (side p.1 p.2) = mk (side (boundaryPair p).1 (boundaryPair p).2) := by
  exact side_pairing p.1 p.2

theorem vertex_pair_start (i : Side) :
    mk (vertexPoint i) = mk (vertexPoint (next (pair i))) := by
  simpa [vertexPoint, unitInterval.symm_zero, side_end_next] using side_pairing i 0

theorem vertex_pair_end (i : Side) :
    mk (vertexPoint (next i)) = mk (vertexPoint (pair i)) := by
  calc
    mk (vertexPoint (next i)) = mk (side i 1) := congrArg mk (side_end_next i).symm
    _ = mk (side (pair i) (unitInterval.symm 1)) := side_pairing i 1
    _ = mk (vertexPoint (pair i)) := by simp [vertexPoint]

theorem continuous_mk : Continuous mk := continuous_quotient_mk'

theorem quotient_mk : Topology.IsQuotientMap mk := isQuotientMap_quotient_mk'

theorem respects_gluing {Y : Type*} (f : Disk → Y)
    (hside : ∀ i t, f (side i t) = f (side (pair i) (unitInterval.symm t)))
    {x y : Disk} (hxy : Relation.r x y) : f x = f y := by
  induction hxy with
  | rel x y h =>
    obtain ⟨i, t, rfl, rfl⟩ := h
    exact hside i t
  | refl => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ hxy hyz => exact hxy.trans hyz

/-- Universal property for maps invariant under the actual side identifications. -/
def lift {Y : Type*} (f : Disk → Y)
    (hside : ∀ i t, f (side i t) = f (side (pair i) (unitInterval.symm t))) :
    Surface → Y :=
  Quotient.lift f (fun _ _ h => respects_gluing f hside h)

theorem lift_mk {Y : Type*} (f : Disk → Y)
    (hside : ∀ i t, f (side i t) = f (side (pair i) (unitInterval.symm t)))
    (x : Disk) : lift f hside (mk x) = f x := rfl

theorem lift_unique {Y : Type*} (f : Disk → Y)
    (hside : ∀ i t, f (side i t) = f (side (pair i) (unitInterval.symm t)))
    (g : Surface → Y) (hg : ∀ x, g (mk x) = f x) : g = lift f hside := by
  funext q
  induction q using Quotient.inductionOn with
  | _ x => exact (hg x).trans (lift_mk f hside x).symm

theorem continuous_lift {Y : Type*} [TopologicalSpace Y] (f : Disk → Y)
    (hf : Continuous f)
    (hside : ∀ i t, f (side i t) = f (side (pair i) (unitInterval.symm t))) :
    Continuous (lift f hside) :=
  hf.quotient_lift (fun _ _ h => respects_gluing f hside h)

def diskInterior : Set Disk := {x | ‖(x : ℂ)‖ < 1}

theorem interior_iff_of_related {x y : Disk} (hxy : Relation.r x y) :
    x ∈ diskInterior ↔ y ∈ diskInterior := by
  induction hxy with
  | rel x y h =>
    obtain ⟨i, t, rfl, rfl⟩ := h
    simp [diskInterior, side_norm]
  | refl => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem mem_diskInterior_of_mk_eq_mk {x y : Disk}
    (hx : x ∈ diskInterior)
    (hxy : mk x = mk y) : x = y := by
  have hrel : Relation.r x y := Quotient.exact hxy
  induction hrel with
  | rel x y h =>
    obtain ⟨i, t, rfl, rfl⟩ := h
    have hxi := hx
    have hnorm := side_norm i t
    simp only [diskInterior, Set.mem_ofPred_eq] at hxi
    rw [hnorm] at hxi
    linarith
  | refl => rfl
  | symm x y h ih =>
    have hy : x ∈ diskInterior := (interior_iff_of_related h).mpr hx
    exact (ih hy (Quotient.sound h)).symm
  | trans x y z h₁ h₂ ih₁ ih₂ =>
    have hy : y ∈ diskInterior := (interior_iff_of_related h₁).mp hx
    exact (ih₁ hx (Quotient.sound h₁)).trans (ih₂ hy (Quotient.sound h₂))

theorem mk_injective_on_diskInterior :
    Set.InjOn mk diskInterior := by
  intro x hx y hy hxy
  exact mem_diskInterior_of_mk_eq_mk hx hxy

theorem mk_preimage_image_diskInterior :
    mk ⁻¹' (mk '' diskInterior) = diskInterior := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact (interior_iff_of_related (Quotient.exact hxy.symm)).mpr hy
  · intro hx
    exact ⟨x, hx, rfl⟩

instance : CompactSpace Surface := Quotient.compactSpace
instance : ConnectedSpace Disk := by
  exact isConnected_iff_connectedSpace.mp
    (Metric.isConnected_closedBall (show (0 : ℝ) ≤ 1 by norm_num))
instance : ConnectedSpace Surface := Quotient.instConnectedSpace

/-! The remaining manifold proof is intentionally separate: it requires a closed-relation
Hausdorff argument and explicit edge/vertex star homeomorphisms. -/

theorem diskInterior_isOpen : IsOpen diskInterior := by
  exact isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const

theorem mk_image_diskInterior_isOpen : IsOpen (mk '' diskInterior) := by
  apply (quotient_mk.isCoinducing.isOpen_preimage).mp
  rw [mk_preimage_image_diskInterior]
  exact diskInterior_isOpen

theorem interior_openEmbedding :
    Topology.IsOpenEmbedding (diskInterior.domRestrict mk) := by
  have hcont : Continuous (diskInterior.domRestrict mk) :=
    continuous_mk.comp continuous_subtype_val
  have hinj : Function.Injective (diskInterior.domRestrict mk) := by
    intro x y h
    exact Subtype.ext (mk_injective_on_diskInterior x.2 y.2 h)
  have hopen : IsOpenMap (diskInterior.domRestrict mk) := by
    intro s hs
    have hs' : IsOpen ((Subtype.val : diskInterior → Disk) '' s) :=
      diskInterior_isOpen.isOpenEmbedding_subtypeVal.isOpenMap s hs
    have hsubset : ((Subtype.val : diskInterior → Disk) '' s) ⊆ diskInterior := by
      rintro _ ⟨x, _, rfl⟩
      exact x.2
    have hsat : mk ⁻¹' (mk '' ((Subtype.val : diskInterior → Disk) '' s)) =
        ((Subtype.val : diskInterior → Disk) '' s) := by
      ext x
      constructor
      · rintro ⟨y, ⟨z, hz, rfl⟩, hxy⟩
        have hx : x ∈ diskInterior := by
          exact (interior_iff_of_related (Quotient.exact hxy)).mp z.2
        have hxeq := mk_injective_on_diskInterior hx z.2 hxy.symm
        subst x
        exact ⟨z, hz, rfl⟩
      · intro hx
        exact ⟨x, hx, rfl⟩
    have himage : diskInterior.domRestrict mk '' s =
        mk '' ((Subtype.val : diskInterior → Disk) '' s) := by
      ext x
      simp [Set.mem_image]
    rw [himage]
    apply (quotient_mk.isCoinducing.isOpen_preimage).mp
    rw [hsat]
    exact hs'
  exact Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hcont hinj hopen

/-
  The quotient is injective on the open disk. This is the reusable interior chart input.
-/

theorem interior_chart_input :
    Set.InjOn mk diskInterior ∧ IsOpen diskInterior ∧ Continuous mk :=
  ⟨mk_injective_on_diskInterior, diskInterior_isOpen, continuous_mk⟩

/-- Endpoint identifications of the eight sides, before topological completion. -/
def VertexGlue (i j : Side) : Prop :=
  ∃ s : Side,
    (i = s ∧ j = next (pair s)) ∨
    (i = next s ∧ j = pair s)

theorem vertex_glue_sound {i j : Side} (h : VertexGlue i j) :
    mk (vertexPoint i) = mk (vertexPoint j) := by
  obtain ⟨s, h | h⟩ := h
  · rcases h with ⟨hi, hj⟩
    rw [hi, hj]
    exact vertex_pair_start s
  · rcases h with ⟨hi, hj⟩
    rw [hi, hj]
    exact vertex_pair_end s

abbrev VertexRelation : Setoid Side := _root_.Relation.EqvGen.setoid VertexGlue
abbrev Vertex := Quotient VertexRelation
noncomputable instance : Fintype Vertex := Fintype.ofFinite Vertex

private theorem vertex_link {i j : Side} (h : VertexGlue i j) :
    VertexRelation.r i j := _root_.Relation.EqvGen.rel _ _ h

theorem vertex_orbit_all (i j : Side) : VertexRelation.r i j := by
  have h03 : VertexRelation.r 0 3 := vertex_link (⟨0, Or.inl ⟨rfl, rfl⟩⟩)
  have h32 : VertexRelation.r 3 2 :=
    _root_.Relation.EqvGen.symm 2 3 (vertex_link (⟨1, Or.inr ⟨rfl, rfl⟩⟩))
  have h21 : VertexRelation.r 2 1 :=
    _root_.Relation.EqvGen.symm 1 2 (vertex_link (⟨0, Or.inr ⟨rfl, rfl⟩⟩))
  have h14 : VertexRelation.r 1 4 := vertex_link (⟨1, Or.inl ⟨rfl, rfl⟩⟩)
  have h47 : VertexRelation.r 4 7 := vertex_link (⟨4, Or.inl ⟨rfl, rfl⟩⟩)
  have h76 : VertexRelation.r 7 6 :=
    _root_.Relation.EqvGen.symm 6 7 (vertex_link (⟨5, Or.inr ⟨rfl, rfl⟩⟩))
  have h65 : VertexRelation.r 6 5 :=
    _root_.Relation.EqvGen.symm 5 6 (vertex_link (⟨4, Or.inr ⟨rfl, rfl⟩⟩))
  have h02 := _root_.Relation.EqvGen.trans 0 3 2 h03 h32
  have h01 := _root_.Relation.EqvGen.trans 0 2 1 h02 h21
  have h04 := _root_.Relation.EqvGen.trans 0 1 4 h01 h14
  have h07 := _root_.Relation.EqvGen.trans 0 4 7 h04 h47
  have h06 := _root_.Relation.EqvGen.trans 0 7 6 h07 h76
  have h05 := _root_.Relation.EqvGen.trans 0 6 5 h06 h65
  have h0 : ∀ k : Side, VertexRelation.r 0 k := by
    intro k
    fin_cases k
    · exact _root_.Relation.EqvGen.refl 0
    · exact h01
    · exact h02
    · exact h03
    · exact h04
    · exact h05
    · exact h06
    · exact h07
  exact _root_.Relation.EqvGen.trans i 0 j
    (_root_.Relation.EqvGen.symm 0 i (h0 i)) (h0 j)

theorem all_geometric_vertices_equal (i j : Side) :
    mk (vertexPoint i) = mk (vertexPoint j) := by
  have h := vertex_orbit_all i j
  induction h with
  | rel _ _ h => exact vertex_glue_sound h
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ h₁ h₂ => exact h₁.trans h₂

theorem relation_iff_normalForm {x y : Disk} :
    Relation.r x y ↔ NormalForm x y := by
  constructor
  · exact eqvGen_normalForm
  · intro h
    rcases h with rfl | ⟨hx, hy⟩ | hp
    · exact _root_.Relation.EqvGen.refl _
    · rcases hx with ⟨i, rfl⟩
      rcases hy with ⟨j, rfl⟩
      exact Quotient.exact (all_geometric_vertices_equal i j)
    · rcases hp with ⟨i, t, rfl, rfl⟩
      exact _root_.Relation.EqvGen.rel _ _ ⟨i, t, rfl, rfl⟩

theorem relation_graph_isClosed :
    IsClosed {p : Disk × Disk | Relation.r p.1 p.2} := by
  have heq : {p : Disk × Disk | Relation.r p.1 p.2} =
      Set.diagonal Disk ∪ (vertexSet.prod vertexSet) ∪
        {p : Disk × Disk | SideGlue p.1 p.2} := by
    ext ⟨x, y⟩
    change Relation.r x y ↔ _
    rw [relation_iff_normalForm]
    simp only [NormalForm, Set.mem_union,
      Set.mem_ofPred_eq]
    change (x = y ∨ x ∈ vertexSet ∧ y ∈ vertexSet ∨ Pairing x y) ↔
      ((x = y ∨ x ∈ vertexSet ∧ y ∈ vertexSet) ∨ SideGlue x y)
    simp [sideGlue_eq_pairing, or_assoc]
  rw [heq]
  exact isClosed_diagonal.union
    (vertexSet_isClosed.prod vertexSet_isClosed) |>.union sideGlue_graph_isClosed

def relationClass (a : Disk) : Set Disk := {x | Relation.r x a}

theorem relationClass_isClosed (a : Disk) : IsClosed (relationClass a) := by
  have hc : Continuous (fun x : Disk => (x, a)) := continuous_id.prodMk continuous_const
  rw [show relationClass a = (fun x : Disk => (x, a)) ⁻¹'
      {p : Disk × Disk | Relation.r p.1 p.2} by rfl]
  exact relation_graph_isClosed.preimage hc

def saturation (s : Set Disk) : Set Disk :=
  {x | ∃ y, y ∈ s ∧ Relation.r x y}

theorem saturation_eq_fst_image (s : Set Disk) :
    saturation s = Prod.fst '' ({p : Disk × Disk |
      Relation.r p.1 p.2 ∧ p.2 ∈ s} : Set (Disk × Disk)) := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact ⟨(x, y), ⟨hxy, hy⟩, rfl⟩
  · rintro ⟨p, ⟨hrel, hs⟩, rfl⟩
    exact ⟨p.2, hs, hrel⟩

theorem isClosed_saturation {s : Set Disk} (hs : IsClosed s) :
    IsClosed (saturation s) := by
  rw [saturation_eq_fst_image]
  apply isClosedMap_fst_of_compactSpace _
  convert relation_graph_isClosed.inter (isClosed_univ.prod hs) using 1
  ext p
  simp

theorem saturation_mem_iff {s : Set Disk} {x : Disk} :
    x ∈ saturation s ↔ ∃ y ∈ s, Relation.r x y := Iff.rfl

theorem saturation_saturated {s : Set Disk} {x y : Disk}
    (hx : x ∈ saturation s) (hxy : Relation.r x y) : y ∈ saturation s := by
  rcases hx with ⟨z, hz, hzx⟩
  exact ⟨z, hz, _root_.Relation.EqvGen.trans y x z hxy.symm hzx⟩

theorem saturation_compl_open {U : Set Disk} (hU : IsOpen U) :
    IsOpen (saturation Uᶜ)ᶜ := isClosed_saturation hU.isClosed_compl |>.isOpen_compl

theorem saturation_compl_isSaturated {U : Set Disk} {x y : Disk}
    (hxy : Relation.r x y) :
    (x ∈ (saturation Uᶜ)ᶜ ↔ y ∈ (saturation Uᶜ)ᶜ) := by
  constructor
  · intro hx
    change y ∉ saturation Uᶜ
    intro hbad
    rcases hbad with ⟨z, hz, hyz⟩
    exact hx ⟨z, hz, _root_.Relation.EqvGen.trans x y z hxy hyz⟩
  · intro hy
    change x ∉ saturation Uᶜ
    intro hbad
    rcases hbad with ⟨z, hz, hxz⟩
    exact hy ⟨z, hz, _root_.Relation.EqvGen.trans y x z hxy.symm hxz⟩

theorem relationClass_subset_of_saturatedOpen {U : Set Disk} {a : Disk}
    (hUa : relationClass a ⊆ U) :
    relationClass a ⊆ (saturation Uᶜ)ᶜ := by
  intro x hx
  change ¬ x ∈ saturation Uᶜ
  rintro ⟨y, hy, hxy⟩
  have hya : Relation.r y a := _root_.Relation.EqvGen.trans y x a hxy.symm hx
  have hyU : y ∈ U := hUa hya
  exact hy hyU

theorem saturatedOpen_disjoint {U V : Set Disk}
    (hUV : Disjoint U V) : Disjoint (saturation Uᶜ)ᶜ (saturation Vᶜ)ᶜ := by
  apply Set.disjoint_left.mpr
  intro x hxU hxV
  have hxU' : x ∈ U := by
    by_contra h
    exact hxU ⟨x, h, _root_.Relation.EqvGen.refl x⟩
  have hxV' : x ∈ V := by
    by_contra h
    exact hxV ⟨x, h, _root_.Relation.EqvGen.refl x⟩
  exact Set.disjoint_left.mp hUV hxU' hxV'

theorem saturatedOpen_preimage_image {U : Set Disk} (_hU : IsOpen U) :
    mk ⁻¹' (mk '' (saturation Uᶜ)ᶜ) = (saturation Uᶜ)ᶜ := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact (saturation_compl_isSaturated (Quotient.exact hxy)).mp hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem saturatedOpen_image_isOpen {U : Set Disk} (hU : IsOpen U) :
    IsOpen (mk '' (saturation Uᶜ)ᶜ) := by
  apply (quotient_mk.isCoinducing.isOpen_preimage).mp
  rw [saturatedOpen_preimage_image hU]
  exact saturation_compl_open hU

theorem quotient_t2 : T2Space Surface := by
  refine ⟨?_⟩
  intro q₁ q₂ hq
  induction q₁ using Quotient.inductionOn with
  | _ a =>
    induction q₂ using Quotient.inductionOn with
    | _ b =>
      have hne : ¬ Relation.r a b := by
        intro hab
        exact hq (Quotient.sound hab)
      have hdisj : Disjoint (relationClass a) (relationClass b) := by
        apply Set.disjoint_left.mpr
        intro x hxa hxb
        exact hne (_root_.Relation.EqvGen.trans a x b hxa.symm hxb)
      have hsep := SeparatedNhds.of_isCompact_isCompact_isClosed
        (relationClass_isClosed a).isCompact (relationClass_isClosed b).isCompact
        (relationClass_isClosed b) hdisj
      rcases hsep with ⟨U, V, hUo, hVo, hUa, hVb, hUV⟩
      refine ⟨mk '' (saturation Uᶜ)ᶜ, mk '' (saturation Vᶜ)ᶜ,
        saturatedOpen_image_isOpen hUo, saturatedOpen_image_isOpen hVo,
        ?_, ?_, ?_⟩
      · have ha : a ∈ (saturation Uᶜ)ᶜ :=
          relationClass_subset_of_saturatedOpen hUa (_root_.Relation.EqvGen.refl a)
        exact ⟨a, ha, rfl⟩
      · have hb : b ∈ (saturation Vᶜ)ᶜ :=
          relationClass_subset_of_saturatedOpen hVb (_root_.Relation.EqvGen.refl b)
        exact ⟨b, hb, rfl⟩
      · apply Set.disjoint_left.mpr
        rintro q ⟨x, hxU, rfl⟩ ⟨y, hyV, hxy⟩
        have hyU : y ∈ (saturation Uᶜ)ᶜ :=
          (saturation_compl_isSaturated (Quotient.exact hxy)).mpr hxU
        exact Set.disjoint_left.mp (saturatedOpen_disjoint hUV) hyU hyV

theorem vertex_quotient_subsingleton : Subsingleton Vertex := by
  refine ⟨?_⟩
  intro x y
  induction x using Quotient.inductionOn with
  | _ i =>
    induction y using Quotient.inductionOn with
    | _ j => exact Quotient.sound (vertex_orbit_all i j)

theorem vertex_count : Fintype.card Vertex = 1 :=
  Fintype.card_eq_one_of_forall_eq (i := Quotient.mk VertexRelation 0) (by
    intro y
    induction y using Quotient.inductionOn with
    | _ j =>
      exact Quotient.sound (vertex_orbit_all j 0))

theorem edge_count : Fintype.card Edge = 4 := by decide
theorem face_count : Fintype.card PUnit = 1 := by decide

/-- The actual finite cell certificate: one vertex, four paired edges, one face. -/
theorem euler_characteristic :
    (Fintype.card Vertex : ℤ) - Fintype.card Edge + Fintype.card PUnit = -2 := by
  rw [vertex_count, edge_count, face_count]
  norm_num

theorem genus_two_numerical_certificate :
    2 - ((Fintype.card Vertex : ℤ) - Fintype.card Edge + Fintype.card PUnit) =
      2 * 2 := by
  rw [euler_characteristic]
  norm_num

end CurveComplex.Octagon
