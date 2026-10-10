import CurveComplexGenusTwo.Topology.ActualModelHomology.ActualOneBoundaryRawFiberNormalization

namespace CurveComplex.Hyperbolic.OneBoundaryRay

/-- Labels for the actual a/b handle pairings and the single actual c seam;
this is raw boundary bookkeeping, not a replacement graph space. -/
abbrev RawEdgeIndex (p : ℕ) := (Fin p × Bool) ⊕ Unit

noncomputable def rawEdgeSlot {p : ℕ} (k : RawEdgeIndex p) (e : Bool) : ℤ :=
  match k with
  | .inl (i,b) => 4*(i.val:ℤ)+(if b then 1 else 0)+(if e then 2 else 0)
  | .inr _ => if e then -3 else -1

noncomputable def rawEdgeFraction {p : ℕ} (k : RawEdgeIndex p)
    (t : unitInterval) (e : Bool) : ℝ :=
  match k with
  | .inl _ => if e then 1-(t:ℝ) else (t:ℝ)
  | .inr _ => if e then (t:ℝ) else 1-(t:ℝ)

noncomputable def rawEdgeNumerator {p : ℕ} (k : RawEdgeIndex p)
    (t : unitInterval) (e : Bool) : ℝ := (rawEdgeSlot k e:ℝ)+rawEdgeFraction k t e

noncomputable def rawEdgePoint {p : ℕ} (k : RawEdgeIndex p)
    (t : unitInterval) (e : Bool) : Complex.ClosedUnitDisc :=
  rawBoundaryPoint p (rawEdgeNumerator k t e)

theorem rawEdgeSlot_injective {p : ℕ} (k l : RawEdgeIndex p) (e f : Bool)
    (h : rawEdgeSlot k e=rawEdgeSlot l f) : k=l ∧ e=f := by
  cases k with
  | inl k =>
    rcases k with ⟨i,b⟩
    cases l with
    | inl l =>
      rcases l with ⟨j,c⟩
      cases b <;> cases c <;> cases e <;> cases f <;>
        simp_all [rawEdgeSlot,Fin.ext_iff] <;> omega
    | inr u =>
      cases u
      cases b <;> cases e <;> cases f <;> simp_all [rawEdgeSlot] <;> omega
  | inr u =>
    cases u
    cases l with
    | inl l =>
      rcases l with ⟨j,c⟩
      cases c <;> cases e <;> cases f <;> simp_all [rawEdgeSlot] <;> omega
    | inr u =>
      cases u
      cases e <;> cases f <;> simp_all [rawEdgeSlot]

theorem rawEdgeSlot_bounds {p : ℕ} (k : RawEdgeIndex p) (e : Bool) :
    -3≤rawEdgeSlot k e ∧ rawEdgeSlot k e<4*(p:ℤ) := by
  cases k with
  | inl k =>
    rcases k with ⟨i,b⟩
    have hi : (i.val:ℤ)<(p:ℤ) := by exact_mod_cast i.isLt
    cases b <;> cases e <;> simp_all [rawEdgeSlot] <;> omega
  | inr u =>
    cases e <;> simp [rawEdgeSlot] <;> omega

theorem rawEdgeFraction_bounds {p : ℕ} (k : RawEdgeIndex p) (t : unitInterval) (e : Bool) :
    0≤rawEdgeFraction k t e ∧ rawEdgeFraction k t e≤1 := by
  have ht0 := t.property.1
  have ht1 := t.property.2
  cases k <;> cases e <;> simp_all [rawEdgeFraction] <;> constructor <;> linarith

theorem rawEdgeFraction_strict {p : ℕ} (k : RawEdgeIndex p) (t : unitInterval)
    (ht0 : 0<(t:ℝ)) (ht1 : (t:ℝ)<1) (e : Bool) :
    0<rawEdgeFraction k t e ∧ rawEdgeFraction k t e<1 := by
  cases k <;> cases e <;> simp_all [rawEdgeFraction] <;> constructor <;> linarith

theorem rawEdgeNumerator_bounds {p : ℕ} (k : RawEdgeIndex p) (t : unitInterval) (e : Bool) :
    -3≤rawEdgeNumerator k t e ∧ rawEdgeNumerator k t e≤4*(p:ℝ) := by
  have hs := rawEdgeSlot_bounds k e
  have h0 : (-3:ℝ)≤(rawEdgeSlot k e:ℝ) := by exact_mod_cast hs.1
  have h1 : (rawEdgeSlot k e:ℝ)+1≤4*(p:ℝ) := by
    exact_mod_cast (show rawEdgeSlot k e+1≤4*(p:ℤ) by omega)
  have ht := rawEdgeFraction_bounds k t e
  unfold rawEdgeNumerator
  constructor <;> linarith

theorem rawEdgeNumerator_strict {p : ℕ} (k : RawEdgeIndex p) (t : unitInterval)
    (ht0 : 0<(t:ℝ)) (ht1 : (t:ℝ)<1) (e : Bool) :
    -3<rawEdgeNumerator k t e ∧ rawEdgeNumerator k t e<4*(p:ℝ) := by
  have hs := rawEdgeSlot_bounds k e
  have h0 : (-3:ℝ)≤(rawEdgeSlot k e:ℝ) := by exact_mod_cast hs.1
  have h1 : (rawEdgeSlot k e:ℝ)+1≤4*(p:ℝ) := by
    exact_mod_cast (show rawEdgeSlot k e+1≤4*(p:ℤ) by omega)
  have ht := rawEdgeFraction_strict k t ht0 ht1 e
  unfold rawEdgeNumerator
  constructor <;> linarith

theorem rawEdgePoint_eq_iff {p : ℕ} (k l : RawEdgeIndex p) (t x : unitInterval)
    (ht0 : 0<(t:ℝ)) (ht1 : (t:ℝ)<1) (e f : Bool) :
    rawEdgePoint k t e=rawEdgePoint l x f ↔ k=l ∧ t=x ∧ e=f := by
  constructor
  · intro he
    have ht := rawEdgeNumerator_strict k t ht0 ht1 e
    have hx := rawEdgeNumerator_bounds l x f
    have hn := rawBoundaryPoint_eq_of_interior_normalized p _ _ ht.1 ht.2 hx.1 hx.2 he
    have htf := rawEdgeFraction_strict k t ht0 ht1 e
    have hxf := rawEdgeFraction_bounds l x f
    obtain ⟨hslot,hfrac⟩ := integer_fraction_unique (rawEdgeSlot k e) (rawEdgeSlot l f)
      (rawEdgeFraction k t e) (rawEdgeFraction l x f) htf.1 htf.2 hxf.1 hxf.2 hn
    obtain ⟨hkl,hef⟩ := rawEdgeSlot_injective k l e f hslot
    subst l
    subst f
    have htx : t=x := by
      apply Subtype.ext
      cases k <;> cases e <;> simp [rawEdgeFraction] at hfrac <;> linarith
    exact ⟨rfl,htx,rfl⟩
  · rintro ⟨rfl,rfl,rfl⟩
    rfl

noncomputable def rawInteriorPair {p : ℕ} (k : RawEdgeIndex p) (t : unitInterval) :
    Set Complex.ClosedUnitDisc := {z | z=rawEdgePoint k t false ∨ z=rawEdgePoint k t true}

theorem rawEdgePoint_mem_interior_pair_iff {p : ℕ} (k l : RawEdgeIndex p) (t x : unitInterval)
    (ht0 : 0<(t:ℝ)) (ht1 : (t:ℝ)<1) (f : Bool) :
    rawEdgePoint l x f ∈ rawInteriorPair k t ↔ k=l ∧ t=x := by
  constructor
  · intro he
    rcases he with he|he
    · have h := (rawEdgePoint_eq_iff k l t x ht0 ht1 false f).mp he.symm
      exact ⟨h.1,h.2.1⟩
    · have h := (rawEdgePoint_eq_iff k l t x ht0 ht1 true f).mp he.symm
      exact ⟨h.1,h.2.1⟩
  · rintro ⟨rfl,rfl⟩
    cases f
    · exact Or.inl rfl
    · exact Or.inr rfl

 theorem rawEdgePoint_handle (p : ℕ) (i : Fin p) (b e : Bool) (t : unitInterval) :
    rawEdgePoint (.inl (i,b)) t e=rawBoundaryPoint p
      (if e then 4*(i:ℝ)+(if b then 4 else 3)-(t:ℝ)
       else 4*(i:ℝ)+(if b then 1 else 0)+(t:ℝ)) := by
  unfold rawEdgePoint
  congr 1
  cases b <;> cases e <;>
    simp [rawEdgeNumerator,rawEdgeSlot,rawEdgeFraction] <;> ring

 theorem rawEdgePoint_seam (p : ℕ) (e : Bool) (t : unitInterval) :
    rawEdgePoint (p:=p) (.inr ()) t e=rawBoundaryPoint p
      (if e then -(3-(t:ℝ)) else -(t:ℝ)) := by
  unfold rawEdgePoint
  congr 1
  cases e <;> simp [rawEdgeNumerator,rawEdgeSlot,rawEdgeFraction] <;> ring

 theorem rel_is_raw_edge_pair (p : ℕ) {z w : Complex.ClosedUnitDisc}
    (h : LeanEval.Topology.ClassificationOfSurfaces.OrientableRel p 1 z w) :
    ∃ k : RawEdgeIndex p, ∃ x : unitInterval,
      z=rawEdgePoint k x false ∧ w=rawEdgePoint k x true := by
  cases h with
  | a x i =>
    refine ⟨.inl (i,false),x,?_,?_⟩ <;> rw [rawEdgePoint_handle] <;>
      simp [rawBoundaryPoint,modelSideCount]
  | b x i =>
    refine ⟨.inl (i,true),x,?_,?_⟩ <;> rw [rawEdgePoint_handle] <;>
      simp [rawBoundaryPoint,modelSideCount]
  | c x i =>
    have hi : i=0 := Subsingleton.elim _ _
    subst i
    refine ⟨.inr (),x,?_,?_⟩ <;> rw [rawEdgePoint_seam] <;>
      simp [rawBoundaryPoint,modelSideCount]

theorem rawInteriorPair_rel_invariant {p : ℕ} (k : RawEdgeIndex p) (t : unitInterval)
    (ht0 : 0<(t:ℝ)) (ht1 : (t:ℝ)<1) {z w : Complex.ClosedUnitDisc}
    (h : LeanEval.Topology.ClassificationOfSurfaces.OrientableRel p 1 z w) :
    z ∈ rawInteriorPair k t ↔ w ∈ rawInteriorPair k t := by
  obtain ⟨l,x,rfl,rfl⟩ := rel_is_raw_edge_pair p h
  rw [rawEdgePoint_mem_interior_pair_iff k l t x ht0 ht1 false,
    rawEdgePoint_mem_interior_pair_iff k l t x ht0 ht1 true]

theorem rawInteriorPair_eqv_invariant {p : ℕ} (k : RawEdgeIndex p) (t : unitInterval)
    (ht0 : 0<(t:ℝ)) (ht1 : (t:ℝ)<1) {z w : Complex.ClosedUnitDisc}
    (h : Relation.EqvGen (LeanEval.Topology.ClassificationOfSurfaces.OrientableRel p 1) z w) :
    z ∈ rawInteriorPair k t ↔ w ∈ rawInteriorPair k t := by
  induction h with
  | rel z w h => exact rawInteriorPair_rel_invariant k t ht0 ht1 h
  | refl z => rfl
  | symm z w h ih => exact ih.symm
  | trans z w u h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

theorem raw_edge_points_related {p : ℕ} (k : RawEdgeIndex p) (t : unitInterval) :
    LeanEval.Topology.ClassificationOfSurfaces.OrientableRel p 1
      (rawEdgePoint k t false) (rawEdgePoint k t true) := by
  open LeanEval.Topology.ClassificationOfSurfaces in
  cases k with
  | inl k =>
    rcases k with ⟨i,b⟩
    cases b
    · simpa [rawEdgePoint_handle,rawBoundaryPoint,modelSideCount] using
        (OrientableRel.a (p:=p) (n:=1) t i)
    · simpa [rawEdgePoint_handle,rawBoundaryPoint,modelSideCount] using
        (OrientableRel.b (p:=p) (n:=1) t i)
  | inr u =>
    cases u
    simpa [rawEdgePoint_seam,rawBoundaryPoint,modelSideCount] using
      (OrientableRel.c (p:=p) (n:=1) t (0 : Fin 1))

theorem raw_quotient_interior_fiber {p : ℕ} (k : RawEdgeIndex p) (t : unitInterval)
    (ht0 : 0<(t:ℝ)) (ht1 : (t:ℝ)<1) (w : Complex.ClosedUnitDisc) :
    Quot.mk (LeanEval.Topology.ClassificationOfSurfaces.OrientableRel p 1) (rawEdgePoint k t false)=
      Quot.mk (LeanEval.Topology.ClassificationOfSurfaces.OrientableRel p 1) w ↔
      w=rawEdgePoint k t false ∨ w=rawEdgePoint k t true := by
  constructor
  · intro h
    exact (rawInteriorPair_eqv_invariant k t ht0 ht1 (Quot.eqvGen_exact h)).mp (Or.inl rfl)
  · rintro (rfl|rfl)
    · rfl
    · exact Quot.sound (raw_edge_points_related k t)

end CurveComplex.Hyperbolic.OneBoundaryRay
