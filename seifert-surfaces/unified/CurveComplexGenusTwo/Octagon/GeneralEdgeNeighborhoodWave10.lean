import CurveComplexGenusTwo.Octagon.CollarCoordinatesWave10

namespace CurveComplex.Octagon

def localCollarParameters (r₀ a b : ℝ) : Set (CollarRadius × CollarAngle) :=
  {p | r₀ < (p.1 : ℝ) ∧ a < (p.2 : ℝ) ∧ (p.2 : ℝ) < b}

theorem localCollarParameters_isOpen (r₀ a b : ℝ) :
    IsOpen (localCollarParameters r₀ a b) := by
  have hr : Continuous (fun p : CollarRadius × CollarAngle => (p.1 : ℝ)) := by
    fun_prop
  have ht : Continuous (fun p : CollarRadius × CollarAngle => (p.2 : ℝ)) := by
    fun_prop
  exact (isOpen_lt continuous_const hr).inter
    ((isOpen_lt continuous_const ht).inter (isOpen_lt ht continuous_const))

def localOpenCollar (i : Side) (r₀ a b : ℝ) : Set Disk :=
  (fun p : CollarRadius × CollarAngle => collarPoint i p.1 p.2) ''
    localCollarParameters r₀ a b

theorem localOpenCollar_isOpen (i : Side) (r₀ a b : ℝ) :
    IsOpen (localOpenCollar i r₀ a b) := by
  have heq : localOpenCollar i r₀ a b =
      (Subtype.val : openCollar i → Disk) ''
        ((collarPointHomeomorph i) '' localCollarParameters r₀ a b) := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨collarPoint i p.1 p.2, collarPoint_mem_openCollar i p.1 p.2⟩,
        ⟨p, hp, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨p, hp, rfl⟩
  rw [heq]
  exact (openCollar_isOpen i).isOpenEmbedding_subtypeVal.isOpenMap _
    ((collarPointHomeomorph i).isOpenMap _
      (localCollarParameters_isOpen r₀ a b))

theorem localOpenCollar_subset_collar (i : Side) (r₀ a b : ℝ) :
    localOpenCollar i r₀ a b ⊆ openCollar i := by
  rintro x ⟨p, hp, rfl⟩
  exact collarPoint_mem_openCollar i p.1 p.2

theorem localOpenCollar_parameters_in_closed_intervals (i : Side)
    (r₀ a b : ℝ) {x : Disk} (hx : x ∈ localOpenCollar i r₀ a b) :
    ∃ p : CollarRadius × CollarAngle,
      collarPoint i p.1 p.2 = x ∧
      (p.1 : ℝ) ∈ Set.Icc r₀ 1 ∧ (p.2 : ℝ) ∈ Set.Icc a b := by
  obtain ⟨p, hp, rfl⟩ := hx
  exact ⟨p, rfl, ⟨le_of_lt hp.1, p.1.property.2⟩,
    ⟨le_of_lt hp.2.1, le_of_lt hp.2.2⟩⟩

def pairedLocalOpenCollars (i : Side) (u : unitInterval) (r₀ δ : ℝ) :
    Set Disk :=
  localOpenCollar i r₀ ((u : ℝ) - δ) ((u : ℝ) + δ) ∪
    localOpenCollar (pair i) r₀ (1 - (u : ℝ) - δ)
      (1 - (u : ℝ) + δ)

theorem pairedLocalOpenCollars_isOpen (i : Side) (u : unitInterval)
    (r₀ δ : ℝ) : IsOpen (pairedLocalOpenCollars i u r₀ δ) :=
  (localOpenCollar_isOpen i r₀ _ _).union
    (localOpenCollar_isOpen (pair i) r₀ _ _)

theorem pairedLocalOpenCollars_subset_openCollars (i : Side)
    (u : unitInterval) (r₀ δ : ℝ) :
    pairedLocalOpenCollars i u r₀ δ ⊆
      openCollar i ∪ openCollar (pair i) := by
  intro x hx
  rcases hx with hx | hx
  · exact Or.inl (localOpenCollar_subset_collar i r₀ _ _ hx)
  · exact Or.inr (localOpenCollar_subset_collar (pair i) r₀ _ _ hx)

theorem pairedLocalAngularIntervals_within_unit (u : unitInterval) (δ : ℝ)
    (hδlo : δ < (u : ℝ)) (hδhi : δ < 1 - (u : ℝ)) :
    Set.Icc ((u : ℝ) - δ) ((u : ℝ) + δ) ⊆ Set.Icc (0 : ℝ) 1 ∧
    Set.Icc (1 - (u : ℝ) - δ) (1 - (u : ℝ) + δ) ⊆
      Set.Icc (0 : ℝ) 1 := by
  constructor
  · intro θ hθ
    exact ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  · intro θ hθ
    exact ⟨by linarith [hθ.1], by linarith [hθ.2]⟩

theorem pairedLocalOpenCollars_parameters_in_closed_intervals
    (i : Side) (u : unitInterval) (r₀ δ : ℝ) {x : Disk}
    (hx : x ∈ pairedLocalOpenCollars i u r₀ δ) :
    (∃ p : CollarRadius × CollarAngle,
      collarPoint i p.1 p.2 = x ∧
      (p.1 : ℝ) ∈ Set.Icc r₀ 1 ∧
      (p.2 : ℝ) ∈ Set.Icc ((u : ℝ) - δ) ((u : ℝ) + δ)) ∨
    (∃ p : CollarRadius × CollarAngle,
      collarPoint (pair i) p.1 p.2 = x ∧
      (p.1 : ℝ) ∈ Set.Icc r₀ 1 ∧
      (p.2 : ℝ) ∈ Set.Icc (1 - (u : ℝ) - δ)
        (1 - (u : ℝ) + δ)) := by
  rcases hx with hx | hx
  · exact Or.inl (localOpenCollar_parameters_in_closed_intervals i r₀ _ _ hx)
  · exact Or.inr
      (localOpenCollar_parameters_in_closed_intervals (pair i) r₀ _ _ hx)

theorem pairedEdge_open_neighborhood_in_localCollars
    (i : Side) (u : unitInterval)
    (hu0 : 0 < (u : ℝ)) (hu1 : (u : ℝ) < 1)
    (r₀ δ : ℝ) (_hr0 : 0 < r₀) (hr1 : r₀ < 1)
    (hδ0 : 0 < δ) (_hδlo : δ < (u : ℝ))
    (_hδhi : δ < 1 - (u : ℝ)) :
    ∃ W : Set Surface, IsOpen W ∧ mk (side i u) ∈ W ∧
      mk ⁻¹' W ⊆ pairedLocalOpenCollars i u r₀ δ := by
  let t : CollarAngle := ⟨(u : ℝ), hu0, hu1⟩
  let tr : CollarAngle := collarReverseAngle t
  let r : CollarRadius := ⟨1, by norm_num⟩
  let U : Set Disk := pairedLocalOpenCollars i u r₀ δ
  have htu : collarToInterval t = u := by
    apply Subtype.ext
    rfl
  have htru : collarToInterval tr = unitInterval.symm u := by
    simp [tr, collarReverseAngle_toInterval, htu]
  have hparam : (r, t) ∈
      localCollarParameters r₀ ((u : ℝ) - δ) ((u : ℝ) + δ) := by
    dsimp [localCollarParameters, r, t]
    constructor
    · exact hr1
    constructor <;> linarith
  have hparamr : (r, tr) ∈
      localCollarParameters r₀ (1 - (u : ℝ) - δ)
        (1 - (u : ℝ) + δ) := by
    dsimp [localCollarParameters, r, tr, collarReverseAngle]
    constructor
    · exact hr1
    constructor <;> linarith
  have hfirst : side i u ∈
      localOpenCollar i r₀ ((u : ℝ) - δ) ((u : ℝ) + δ) := by
    refine ⟨(r, t), hparam, ?_⟩
    simpa [r] using
      (collarPoint_boundary i t).trans (congrArg (side i) htu)
  have hsecond : side (pair i) (unitInterval.symm u) ∈
      localOpenCollar (pair i) r₀ (1 - (u : ℝ) - δ)
        (1 - (u : ℝ) + δ) := by
    refine ⟨(r, tr), hparamr, ?_⟩
    simpa [r] using
      (collarPoint_boundary (pair i) tr).trans
        (congrArg (side (pair i)) htru)
  have hclass : relationClass (side i u) ⊆ U := by
    intro x hx
    have hmk : mk x = mk (side i u) := Quotient.sound hx
    have hmem : x ∈ mk ⁻¹' ({mk (side i u)} : Set Surface) := hmk
    have hu0' : u ≠ 0 := by
      intro h
      have hh := congrArg (fun z : unitInterval => (z : ℝ)) h
      dsimp at hh
      linarith
    have hu1' : u ≠ 1 := by
      intro h
      have hh := congrArg (fun z : unitInterval => (z : ℝ)) h
      dsimp at hh
      linarith
    rw [edge_interior_fiber_eq_pair i u hu0' hu1'] at hmem
    rcases Set.mem_insert_iff.mp hmem with h | h
    · exact Or.inl (h ▸ hfirst)
    · exact Or.inr ((Set.mem_singleton_iff.mp h) ▸ hsecond)
  exact exists_open_quotient_neighborhood_of_fiber
    (pairedLocalOpenCollars_isOpen i u r₀ δ) hclass

theorem pairedEdge_every_interior_point_has_localCollarNeighborhood
    (i : Side) (u : unitInterval)
    (hu0 : 0 < (u : ℝ)) (hu1 : (u : ℝ) < 1)
    (r₀ : ℝ) (hr0 : 0 < r₀) (hr1 : r₀ < 1) :
    ∃ (δ : ℝ) (W : Set Surface),
      0 < δ ∧ δ < (u : ℝ) ∧ δ < 1 - (u : ℝ) ∧
      IsOpen W ∧ mk (side i u) ∈ W ∧
      mk ⁻¹' W ⊆ pairedLocalOpenCollars i u r₀ δ := by
  let δ : ℝ := min (u : ℝ) (1 - (u : ℝ)) / 2
  have hmpos : 0 < min (u : ℝ) (1 - (u : ℝ)) :=
    lt_min hu0 (by linarith)
  have hδ0 : 0 < δ := by
    dsimp [δ]
    linarith
  have hδlo : δ < (u : ℝ) := by
    dsimp [δ]
    have h := min_le_left (u : ℝ) (1 - (u : ℝ))
    linarith
  have hδhi : δ < 1 - (u : ℝ) := by
    dsimp [δ]
    have h := min_le_right (u : ℝ) (1 - (u : ℝ))
    linarith
  obtain ⟨W, hWopen, huW, hpre⟩ :=
    pairedEdge_open_neighborhood_in_localCollars i u hu0 hu1
      r₀ δ hr0 hr1 hδ0 hδlo hδhi
  exact ⟨δ, W, hδ0, hδlo, hδhi, hWopen, huW, hpre⟩

def edgeInteriorQuotient : Set Surface :=
  {q | ∃ (i : Side) (u : unitInterval),
    0 < (u : ℝ) ∧ (u : ℝ) < 1 ∧ q = mk (side i u)}

theorem edgeInteriorQuotient_covered_by_localCollarNeighborhoods
    (r₀ : ℝ) (hr0 : 0 < r₀) (hr1 : r₀ < 1) :
    ∀ q ∈ edgeInteriorQuotient,
      ∃ (i : Side) (u : unitInterval) (δ : ℝ) (W : Set Surface),
        0 < δ ∧ δ < (u : ℝ) ∧ δ < 1 - (u : ℝ) ∧
        IsOpen W ∧ q ∈ W ∧
        mk ⁻¹' W ⊆ pairedLocalOpenCollars i u r₀ δ := by
  rintro q ⟨i, u, hu0, hu1, hq⟩
  obtain ⟨δ, W, hδ0, hδlo, hδhi, hWopen, huW, hpre⟩ :=
    pairedEdge_every_interior_point_has_localCollarNeighborhood
      i u hu0 hu1 r₀ hr0 hr1
  subst q
  exact ⟨i, u, δ, W, hδ0, hδlo, hδhi, hWopen, huW, hpre⟩

end CurveComplex.Octagon
