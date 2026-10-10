import CurveComplexGenusTwo.Octagon.WindowEdgeExplicit

namespace CurveComplex.Octagon

def signedRectangleInterior : Set SignedCollarRectangle :=
  {p | (-1 / 4 : ℝ) < (p.1 : ℝ) ∧ (p.1 : ℝ) < (1 / 4 : ℝ) ∧
    (1 / 4 : ℝ) < (p.2 : ℝ) ∧ (p.2 : ℝ) < (3 / 4 : ℝ)}

def openReferenceBox : Set (ℝ × ℝ) :=
  {p | (-1 / 4 : ℝ) < p.1 ∧ p.1 < (1 / 4 : ℝ) ∧
    (1 / 4 : ℝ) < p.2 ∧ p.2 < (3 / 4 : ℝ)}

theorem signedRectangleInterior_isOpen : IsOpen signedRectangleInterior := by
  have hr : Continuous (fun p : SignedCollarRectangle => (p.1 : ℝ)) := by
    fun_prop
  have ht : Continuous (fun p : SignedCollarRectangle => (p.2 : ℝ)) := by
    fun_prop
  exact (isOpen_lt continuous_const hr).inter
    ((isOpen_lt hr continuous_const).inter
      ((isOpen_lt continuous_const ht).inter
        (isOpen_lt ht continuous_const)))

theorem openReferenceBox_isOpen : IsOpen openReferenceBox := by
  have hr : Continuous (fun p : ℝ × ℝ => p.1) := continuous_fst
  have ht : Continuous (fun p : ℝ × ℝ => p.2) := continuous_snd
  exact (isOpen_lt continuous_const hr).inter
    ((isOpen_lt hr continuous_const).inter
      ((isOpen_lt continuous_const ht).inter
        (isOpen_lt ht continuous_const)))

noncomputable def planeToSignedInterior :
    openReferenceBox ≃ₜ signedRectangleInterior where
  toFun p := by
    refine ⟨(⟨p.1.1, le_of_lt p.2.1, le_of_lt p.2.2.1⟩,
      ⟨p.1.2, le_of_lt p.2.2.2.1, le_of_lt p.2.2.2.2⟩), ?_⟩
    exact p.2
  invFun p := ⟨((p.1.1 : ℝ), (p.1.2 : ℝ)), p.2⟩
  left_inv := by intro p; apply Subtype.ext; rfl
  right_inv := by intro p; apply Subtype.ext; apply Prod.ext <;> apply Subtype.ext <;> rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- An open chart in the signed closed rectangle becomes an ordinary
Euclidean-open chart at any point in its rectangular interior. -/
theorem refine_signed_chart_to_plane
    (U : Set SignedCollarRectangle) (W : Set Surface)
    (hUopen : IsOpen U) (hWopen : IsOpen W) (chart : U ≃ₜ W)
    (p : SignedCollarRectangle) (hpU : p ∈ U)
    (hpI : p ∈ signedRectangleInterior) :
    ∃ (V : Set (ℝ × ℝ)) (W' : Set Surface),
      IsOpen V ∧ ((p.1 : ℝ), (p.2 : ℝ)) ∈ V ∧
      IsOpen W' ∧ ((chart ⟨p, hpU⟩ : W) : Surface) ∈ W' ∧
      Nonempty (V ≃ₜ W') := by
  let I := signedRectangleInterior
  let B := openReferenceBox
  let eB := planeToSignedInterior
  let N : Set SignedCollarRectangle := U ∩ I
  have hNopen : IsOpen N := hUopen.inter signedRectangleInterior_isOpen
  have hNsubI : N ⊆ I := Set.inter_subset_right
  have hNsubU : N ⊆ U := Set.inter_subset_left
  let B₁ : Set B :=
    eB ⁻¹' ((Subtype.val : I → SignedCollarRectangle) ⁻¹' N)
  have hB₁open : IsOpen B₁ :=
    (hNopen.preimage continuous_subtype_val).preimage eB.continuous
  let V : Set (ℝ × ℝ) := (Subtype.val : B → ℝ × ℝ) '' B₁
  have hVopen : IsOpen V :=
    openReferenceBox_isOpen.isOpenMap_subtype_val B₁ hB₁open
  let T : Set U := (Subtype.val : U → SignedCollarRectangle) ⁻¹' N
  have hTopen : IsOpen T := hNopen.preimage continuous_subtype_val
  let W₀ : Set W := chart '' T
  have hW₀open : IsOpen W₀ := chart.isOpenMap T hTopen
  let W' : Set Surface := (Subtype.val : W → Surface) '' W₀
  have hW'open : IsOpen W' :=
    hWopen.isOpenMap_subtype_val W₀ hW₀open
  let e₁ : B₁ ≃ₜ V :=
    (Topology.IsEmbedding.subtypeVal :
      Topology.IsEmbedding (Subtype.val : B → ℝ × ℝ)).homeomorphImage B₁
  let e₂ : B₁ ≃ₜ ((Subtype.val : I → SignedCollarRectangle) ⁻¹' N) :=
    eB.sets rfl
  let e₃ : ((Subtype.val : I → SignedCollarRectangle) ⁻¹' N) ≃ₜ N :=
    (Topology.IsEmbedding.subtypeVal :
      Topology.IsEmbedding (Subtype.val : I → SignedCollarRectangle))
      |>.homeomorphOfSubsetRange (by simpa using hNsubI)
  let e₄ : T ≃ₜ N :=
    (Topology.IsEmbedding.subtypeVal :
      Topology.IsEmbedding (Subtype.val : U → SignedCollarRectangle))
      |>.homeomorphOfSubsetRange (by simpa using hNsubU)
  let e₅ : T ≃ₜ W₀ := chart.image T
  let e₆ : W₀ ≃ₜ W' :=
    (Topology.IsEmbedding.subtypeVal :
      Topology.IsEmbedding (Subtype.val : W → Surface)).homeomorphImage W₀
  let e : V ≃ₜ W' :=
    e₁.symm.trans (e₂.trans (e₃.trans (e₄.symm.trans (e₅.trans e₆))))
  have hpN : p ∈ N := ⟨hpU, hpI⟩
  let bp : B := eB.symm ⟨p, hpI⟩
  have hbp : bp ∈ B₁ := by
    change ((eB bp : I) : SignedCollarRectangle) ∈ N
    simpa [bp] using hpN
  have hpV : ((p.1 : ℝ), (p.2 : ℝ)) ∈ V := by
    refine ⟨bp, hbp, ?_⟩
    rfl
  have hT : (⟨p, hpU⟩ : U) ∈ T := hpN
  have hW₀ : chart ⟨p, hpU⟩ ∈ W₀ := ⟨⟨p,hpU⟩, hT, rfl⟩
  have hW' : ((chart ⟨p, hpU⟩ : W) : Surface) ∈ W' :=
    ⟨chart ⟨p,hpU⟩, hW₀, rfl⟩
  exact ⟨V, W', hVopen, hpV, hW'open, hW', ⟨e⟩⟩

/-- Every non-vertex point of a paired edge has an ambient-open local chart
modeled on an open subset of the Euclidean plane. -/
theorem pairedEdge_every_interior_point_euclidean_chart
    (i : Side) (u : unitInterval)
    (hu0 : 0 < (u : ℝ)) (hu1 : (u : ℝ) < 1) :
    ∃ (V : Set (ℝ × ℝ)) (W : Set Surface),
      IsOpen V ∧ IsOpen W ∧ mk (side i u) ∈ W ∧
      Nonempty (V ≃ₜ W) := by
  obtain ⟨δ, W, hδ0, hδlo, hδhi, hWopen, hmid, hpre⟩ :=
    pairedEdge_every_interior_point_has_localCollarNeighborhood
      i u hu0 hu1 (3 / 4) (by norm_num) (by norm_num)
  obtain ⟨w, hlo, hhi, hlocal⟩ :=
    pairedLocalOpenCollars_subset_windowSlab i u δ hδ0 hδlo hδhi
  have hWsub : W ⊆ Set.range (windowSlabMap w i) := by
    intro q hq
    induction q using Quotient.inductionOn with
    | _ x => exact hlocal (hpre hq)
  let e := windowExplicitSlabChart w i
  let U : Set SignedCollarRectangle :=
    e ⁻¹' ((Subtype.val : Set.range (windowSlabMap w i) → Surface) ⁻¹' W)
  have hUopen : IsOpen U :=
    (hWopen.preimage continuous_subtype_val).preimage e.continuous
  let e₁ : U ≃ₜ
      {q : Set.range (windowSlabMap w i) // (q : Surface) ∈ W} :=
    e.sets rfl
  have hWrange : W ⊆ Set.range
      (Subtype.val : Set.range (windowSlabMap w i) → Surface) := by
    intro q hq
    exact ⟨⟨q, hWsub hq⟩, rfl⟩
  let e₂ : {q : Set.range (windowSlabMap w i) // (q : Surface) ∈ W} ≃ₜ W :=
    (Topology.IsEmbedding.subtypeVal :
      Topology.IsEmbedding
        (Subtype.val : Set.range (windowSlabMap w i) → Surface))
      |>.homeomorphOfSubsetRange hWrange
  let chart : U ≃ₜ W := e₁.trans e₂
  have hulo : w.lo < (u : ℝ) := by rw [hlo]; linarith
  have huhi : (u : ℝ) < w.hi := by rw [hhi]; linarith
  obtain ⟨s, hslo, hshi, hseam⟩ :=
    windowExplicitSlabChart_seam w i u hulo huhi
  let p : SignedCollarRectangle :=
    (⟨0, by constructor <;> norm_num⟩, s)
  have hpU : p ∈ U := by
    change ((e p) : Surface) ∈ W
    rw [show ((e p) : Surface) = mk (side i u) from hseam]
    exact hmid
  have hpI : p ∈ signedRectangleInterior := by
    dsimp [signedRectangleInterior, p]
    constructor
    · norm_num
    constructor
    · norm_num
    exact ⟨hslo, hshi⟩
  obtain ⟨V, W', hVopen, hpV, hW'open, hpoint, hchart⟩ :=
    refine_signed_chart_to_plane U W hUopen hWopen chart p hpU hpI
  have heval : ((chart ⟨p, hpU⟩ : W) : Surface) = mk (side i u) := by
    exact hseam
  exact ⟨V, W', hVopen, hW'open, heval ▸ hpoint, hchart⟩

/-- Any Euclidean-open local chart can be shrunk to an open metric ball. -/
theorem restrict_plane_chart_to_ball
    (V : Set (ℝ × ℝ)) (W : Set Surface)
    (hVopen : IsOpen V) (hWopen : IsOpen W)
    (chart : V ≃ₜ W) (q : Surface) (hq : q ∈ W) :
    ∃ (c : ℝ × ℝ) (ε : ℝ) (W' : Set Surface),
      0 < ε ∧ IsOpen W' ∧ q ∈ W' ∧
      Nonempty ((Metric.ball c ε) ≃ₜ W') := by
  let z : V := chart.symm ⟨q, hq⟩
  let c : ℝ × ℝ := z
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hVopen c z.2
  let S : Set V :=
    (Subtype.val : V → ℝ × ℝ) ⁻¹' Metric.ball c ε
  have hSopen : IsOpen S := Metric.isOpen_ball.preimage continuous_subtype_val
  let T : Set W := chart '' S
  have hTopen : IsOpen T := chart.isOpenMap S hSopen
  let W' : Set Surface := (Subtype.val : W → Surface) '' T
  have hW'open : IsOpen W' := hWopen.isOpenMap_subtype_val T hTopen
  have hballrange : Metric.ball c ε ⊆
      Set.range (Subtype.val : V → ℝ × ℝ) := by
    intro x hx
    exact ⟨⟨x, hball hx⟩, rfl⟩
  let e₁ : S ≃ₜ Metric.ball c ε :=
    (Topology.IsEmbedding.subtypeVal :
      Topology.IsEmbedding (Subtype.val : V → ℝ × ℝ))
      |>.homeomorphOfSubsetRange hballrange
  let e₂ : S ≃ₜ T := chart.image S
  let e₃ : T ≃ₜ W' :=
    (Topology.IsEmbedding.subtypeVal :
      Topology.IsEmbedding (Subtype.val : W → Surface)).homeomorphImage T
  let e : Metric.ball c ε ≃ₜ W' := e₁.symm.trans (e₂.trans e₃)
  have hzS : z ∈ S := by
    change (z : ℝ × ℝ) ∈ Metric.ball c ε
    simp [c, Metric.mem_ball, hε]
  have hqW' : q ∈ W' := by
    refine ⟨chart z, ⟨z, hzS, rfl⟩, ?_⟩
    simp [z]
  exact ⟨c, ε, W', hε, hW'open, hqW', ⟨e⟩⟩

theorem pairedEdge_every_interior_point_ball_chart
    (i : Side) (u : unitInterval)
    (hu0 : 0 < (u : ℝ)) (hu1 : (u : ℝ) < 1) :
    ∃ (c : ℝ × ℝ) (ε : ℝ) (W : Set Surface),
      0 < ε ∧ IsOpen W ∧ mk (side i u) ∈ W ∧
      Nonempty ((Metric.ball c ε) ≃ₜ W) := by
  obtain ⟨V, W, hVopen, hWopen, hmid, ⟨chart⟩⟩ :=
    pairedEdge_every_interior_point_euclidean_chart i u hu0 hu1
  exact restrict_plane_chart_to_ball V W hVopen hWopen chart
    (mk (side i u)) hmid

theorem edgeInteriorQuotient_ball_chart_cover :
    ∀ q ∈ edgeInteriorQuotient,
      ∃ (c : ℝ × ℝ) (ε : ℝ) (W : Set Surface),
        0 < ε ∧ IsOpen W ∧ q ∈ W ∧
        Nonempty ((Metric.ball c ε) ≃ₜ W) := by
  rintro q ⟨i, u, hu0, hu1, rfl⟩
  exact pairedEdge_every_interior_point_ball_chart i u hu0 hu1

end CurveComplex.Octagon
