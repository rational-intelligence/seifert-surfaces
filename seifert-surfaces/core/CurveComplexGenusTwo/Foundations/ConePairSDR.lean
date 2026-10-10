import Mathlib

set_option maxHeartbeats 1000000

namespace CurveComplex

open unitInterval

variable {X : Type*} [TopologicalSpace X]

/-- The unreduced cone quotient relation: only the top time face is collapsed. -/
def topologicalConeSetoid (X : Type*) : Setoid (I × X) where
  r p q := p = q ∨ p.1 = 1 ∧ q.1 = 1
  iseqv := by
    constructor
    · intro p
      exact Or.inl rfl
    · intro p q h
      rcases h with h | ⟨hp, hq⟩
      · exact Or.inl h.symm
      · exact Or.inr ⟨hq, hp⟩
    · intro p q r hpq hqr
      rcases hpq with h | ⟨hp, hq⟩
      · subst q
        exact hqr
      · rcases hqr with h | ⟨hq', hr⟩
        · subst r
          exact Or.inr ⟨hp, hq⟩
        · exact Or.inr ⟨hp, hr⟩

/-- The quotient of `I × X` that identifies the whole top face to the apex. -/
abbrev TopologicalCone (X : Type*) [TopologicalSpace X] :=
  Quotient (topologicalConeSetoid X)

/-- A cone point represented by height `t` and base coordinate `x`. -/
def topologicalConeMk (t : I) (x : X) : TopologicalCone X :=
  Quotient.mk _ (t, x)

/-- The base inclusion of a topological cone. -/
def topologicalConeBase (x : X) : TopologicalCone X :=
  topologicalConeMk 0 x

/-- The apex, using a chosen representative. -/
def topologicalConeApex (x : X) : TopologicalCone X :=
  topologicalConeMk 1 x

theorem topologicalConeApex_eq (x y : X) :
    topologicalConeApex x = topologicalConeApex y := by
  apply Quotient.sound
  exact Or.inr ⟨rfl, rfl⟩

theorem topologicalConeBase_injective :
    Function.Injective (topologicalConeBase : X → TopologicalCone X) := by
  intro x y h
  have h' : (topologicalConeSetoid X).r ((0 : I), x) ((0 : I), y) :=
    Quotient.exact h
  rcases h' with h' | ⟨h0, _⟩
  · exact congrArg Prod.snd h'
  · have : (0 : I) ≠ 1 := by norm_num
    exact False.elim (this h0)

theorem topologicalConeMk_continuous :
    Continuous (fun p : I × X => topologicalConeMk p.1 p.2) := by
  exact continuous_quotient_mk'

theorem topologicalConeBase_continuous :
    Continuous (topologicalConeBase : X → TopologicalCone X) := by
  exact topologicalConeMk_continuous.comp (continuous_const.prodMk continuous_id)

theorem topologicalConeMk_quotient :
    Topology.IsQuotientMap (fun p : I × X => topologicalConeMk p.1 p.2) := by
  exact isQuotientMap_quotient_mk'

/-- Descend a map that is constant on the collapsed top face. -/
def topologicalConeDesc {Y : Type*} (f : I × X → Y)
    (hf : ∀ x y : X, f (1, x) = f (1, y)) : TopologicalCone X → Y :=
  Quotient.lift f (by
    intro p q hpq
    rcases hpq with h | ⟨hp, hq⟩
    · exact congrArg f h
    · calc
        f p = f (1, p.2) := by rw [← hp]
        _ = f (1, q.2) := hf p.2 q.2
        _ = f q := by rw [← hq])

@[simp] theorem topologicalConeDesc_mk {Y : Type*} (f : I × X → Y)
    (hf : ∀ x y : X, f (1, x) = f (1, y)) (t : I) (x : X) :
    topologicalConeDesc f hf (topologicalConeMk t x) = f (t, x) := rfl

theorem topologicalConeDesc_continuous {Y : Type*} [TopologicalSpace Y]
    (f : I × X → Y) (hf : ∀ x y : X, f (1, x) = f (1, y))
    (hc : Continuous f) : Continuous (topologicalConeDesc f hf) := by
  apply (topologicalConeMk_quotient (X := X)).continuous_iff.mpr
  exact hc

/-- Descend a time-dependent map through the cone quotient in its second factor. -/
def topologicalConeDescTime {Y : Type*} (f : I × (I × X) → Y)
    (hf : ∀ (s : I) (x y : X), f (s, (1, x)) = f (s, (1, y))) :
    I × TopologicalCone X → Y :=
  fun p => topologicalConeDesc (fun q => f (p.1, q)) (hf p.1) p.2

@[simp] theorem topologicalConeDescTime_mk {Y : Type*} (f : I × (I × X) → Y)
    (hf : ∀ (s : I) (x y : X), f (s, (1, x)) = f (s, (1, y)))
    (s t : I) (x : X) :
    topologicalConeDescTime f hf (s, topologicalConeMk t x) = f (s, (t, x)) := rfl

theorem topologicalConeDescTime_continuous {Y : Type*} [TopologicalSpace Y]
    (f : I × (I × X) → Y)
    (hf : ∀ (s : I) (x y : X), f (s, (1, x)) = f (s, (1, y)))
    (hc : Continuous f) : Continuous (topologicalConeDescTime f hf) := by
  apply (topologicalConeMk_quotient (X := X)).continuous_lift_prod_right
  exact hc

/-- Progress of the base contraction in the first half of the cone SDR. -/
def coneContractProgress (s : I) : I :=
  ⟨min 1 (2 * (s : ℝ)), by
    constructor
    · exact le_min zero_le_one (mul_nonneg (by norm_num) s.2.1)
    · exact min_le_left _ _⟩

/-- Progress of the height collapse in the second half of the cone SDR. -/
def coneHeightFactor (s : I) : I :=
  ⟨min 1 (2 * (1 - (s : ℝ))), by
    constructor
    · exact le_min zero_le_one (mul_nonneg (by norm_num) (sub_nonneg.mpr s.2.2))
    · exact min_le_left _ _⟩

theorem coneContractProgress_continuous : Continuous coneContractProgress := by
  apply Continuous.subtype_mk
  fun_prop

theorem coneHeightFactor_continuous : Continuous coneHeightFactor := by
  apply Continuous.subtype_mk
  fun_prop

@[simp] theorem coneContractProgress_zero : coneContractProgress (0 : I) = 0 := by
  apply Subtype.ext
  simp [coneContractProgress]

@[simp] theorem coneContractProgress_one : coneContractProgress (1 : I) = 1 := by
  apply Subtype.ext
  simp [coneContractProgress]

@[simp] theorem coneHeightFactor_zero : coneHeightFactor (0 : I) = 1 := by
  apply Subtype.ext
  simp [coneHeightFactor]

@[simp] theorem coneHeightFactor_one : coneHeightFactor (1 : I) = 0 := by
  apply Subtype.ext
  simp [coneHeightFactor]

theorem coneHeightFactor_eq_one_of_le_half (s : I) (hs : (s : ℝ) ≤ 1 / 2) :
    coneHeightFactor s = 1 := by
  apply Subtype.ext
  change min 1 (2 * (1 - (s : ℝ))) = 1
  exact min_eq_left (by linarith)

theorem coneContractProgress_eq_one_of_half_le (s : I) (hs : 1 / 2 ≤ (s : ℝ)) :
    coneContractProgress s = 1 := by
  apply Subtype.ext
  change min 1 (2 * (s : ℝ)) = 1
  exact min_eq_left (by linarith)

variable {p : X}

/-- The terminal retraction induced by a contraction of the base. -/
noncomputable def topologicalConeRetraction
    (h : ContinuousMap.Homotopy (ContinuousMap.id X) (ContinuousMap.const X p)) :
    C(TopologicalCone X, X) :=
  ⟨topologicalConeDesc (fun q : I × X => h q)
    (by intro x y; exact (h.map_one_left x).trans (h.map_one_left y).symm),
    topologicalConeDesc_continuous _ _ h.continuous_toFun⟩

@[simp] theorem topologicalConeRetraction_mk
    (h : ContinuousMap.Homotopy (ContinuousMap.id X) (ContinuousMap.const X p))
    (t : I) (x : X) :
    topologicalConeRetraction h (topologicalConeMk t x) = h (t, x) := rfl

@[simp] theorem topologicalConeRetraction_base
    (h : ContinuousMap.Homotopy (ContinuousMap.id X) (ContinuousMap.const X p))
    (x : X) : topologicalConeRetraction h (topologicalConeBase x) = x := by
  exact h.map_zero_left x

/-- Continuous source lift of the two-phase cone deformation. -/
noncomputable def topologicalConeSDRLift
    (h : ContinuousMap.Homotopy (ContinuousMap.id X) (ContinuousMap.const X p)) :
    I × (I × X) → TopologicalCone X :=
  fun q => topologicalConeMk (coneHeightFactor q.1 * q.2.1)
    (h (coneContractProgress q.1 * q.2.1, q.2.2))

theorem topologicalConeSDRLift_continuous
    (h : ContinuousMap.Homotopy (ContinuousMap.id X) (ContinuousMap.const X p)) :
    Continuous (topologicalConeSDRLift h) := by
  have ht : Continuous (fun q : I × (I × X) => q.2.1) :=
    continuous_fst.comp continuous_snd
  have hc : Continuous (fun q : I × (I × X) =>
      coneContractProgress q.1 * q.2.1) :=
    (coneContractProgress_continuous.comp continuous_fst).mul ht
  have hh : Continuous (fun q : I × (I × X) =>
      coneHeightFactor q.1 * q.2.1) :=
    (coneHeightFactor_continuous.comp continuous_fst).mul ht
  exact topologicalConeMk_continuous.comp
    (hh.prodMk (h.continuous_toFun.comp (hc.prodMk (continuous_snd.comp continuous_snd))))

theorem topologicalConeSDRLift_apex
    (h : ContinuousMap.Homotopy (ContinuousMap.id X) (ContinuousMap.const X p))
    (s : I) (x y : X) :
    topologicalConeSDRLift h (s, (1, x)) =
      topologicalConeSDRLift h (s, (1, y)) := by
  by_cases hs : (s : ℝ) ≤ 1 / 2
  · simp only [topologicalConeSDRLift, coneHeightFactor_eq_one_of_le_half s hs, one_mul]
    exact topologicalConeApex_eq _ _
  · have hs' : 1 / 2 ≤ (s : ℝ) := le_of_lt (lt_of_not_ge hs)
    simp [topologicalConeSDRLift, coneContractProgress_eq_one_of_half_le s hs']

/-- The cone homotopy descended through the quotient in its cone factor. -/
noncomputable def topologicalConeSDRHomotopyMap
    (h : ContinuousMap.Homotopy (ContinuousMap.id X) (ContinuousMap.const X p)) :
    C(I × TopologicalCone X, TopologicalCone X) :=
  ⟨topologicalConeDescTime (topologicalConeSDRLift h)
    (topologicalConeSDRLift_apex h),
    topologicalConeDescTime_continuous _ _ (topologicalConeSDRLift_continuous h)⟩

@[simp] theorem topologicalConeSDRHomotopyMap_mk
    (h : ContinuousMap.Homotopy (ContinuousMap.id X) (ContinuousMap.const X p))
    (s t : I) (x : X) :
    topologicalConeSDRHomotopyMap h (s, topologicalConeMk t x) =
      topologicalConeSDRLift h (s, (t, x)) := rfl

theorem topologicalConeSDRHomotopyMap_zero
    (h : ContinuousMap.Homotopy (ContinuousMap.id X) (ContinuousMap.const X p))
    (z : TopologicalCone X) : topologicalConeSDRHomotopyMap h (0, z) = z := by
  refine Quotient.inductionOn z ?_
  rintro ⟨t, x⟩
  change topologicalConeSDRLift h (0, (t, x)) = topologicalConeMk t x
  simp [topologicalConeSDRLift]

theorem topologicalConeSDRHomotopyMap_one
    (h : ContinuousMap.Homotopy (ContinuousMap.id X) (ContinuousMap.const X p))
    (z : TopologicalCone X) :
    topologicalConeSDRHomotopyMap h (1, z) =
      topologicalConeBase (topologicalConeRetraction h z) := by
  refine Quotient.inductionOn z ?_
  rintro ⟨t, x⟩
  change topologicalConeSDRLift h (1, (t, x)) = topologicalConeMk 0 (h (t, x))
  simp [topologicalConeSDRLift]

theorem topologicalConeSDRHomotopyMap_base
    (h : ContinuousMap.Homotopy (ContinuousMap.id X) (ContinuousMap.const X p))
    (s : I) (x : X) :
    topologicalConeSDRHomotopyMap h (s, topologicalConeBase x) =
      topologicalConeBase x := by
  change topologicalConeSDRLift h (s, (0, x)) = topologicalConeMk 0 x
  simp [topologicalConeSDRLift]

/-- The base inclusion as a continuous map. -/
def topologicalConeBaseMap : C(X, TopologicalCone X) :=
  ⟨topologicalConeBase, topologicalConeBase_continuous⟩

/-- Data of a strong deformation retraction of the quotient cone onto its base.
The homotopy fixes every base point at every time. -/
structure TopologicalConeBaseSDR (X : Type*) [TopologicalSpace X] where
  retraction : C(TopologicalCone X, X)
  retraction_base : ∀ x : X, retraction (topologicalConeBase x) = x
  homotopy : ContinuousMap.Homotopy (ContinuousMap.id (TopologicalCone X))
    ((topologicalConeBaseMap (X := X)).comp retraction)
  homotopy_base_fixed : ∀ (t : I) (x : X),
    homotopy (t, topologicalConeBase x) = topologicalConeBase x

/-- A cone on a contractible base strongly deformation retracts onto its base. -/
theorem topologicalConeBase_sdr [ContractibleSpace X] :
    Nonempty (TopologicalConeBaseSDR X) := by
  obtain ⟨p, ⟨h⟩⟩ := (contractible_iff_id_nullhomotopic X).mp inferInstance
  let H : ContinuousMap.Homotopy (ContinuousMap.id (TopologicalCone X))
      ((topologicalConeBaseMap (X := X)).comp (topologicalConeRetraction h)) := {
    toFun := topologicalConeSDRHomotopyMap h
    continuous_toFun := (topologicalConeSDRHomotopyMap h).continuous
    map_zero_left := topologicalConeSDRHomotopyMap_zero h
    map_one_left := topologicalConeSDRHomotopyMap_one h
  }
  refine ⟨{
    retraction := topologicalConeRetraction h
    retraction_base := topologicalConeRetraction_base h
    homotopy := H
    homotopy_base_fixed := ?_
  }⟩
  exact topologicalConeSDRHomotopyMap_base h

end CurveComplex
