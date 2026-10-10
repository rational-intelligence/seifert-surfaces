import NativeBoundaryTrace

set_option autoImplicit false
noncomputable section
open Set Function Filter
open scoped Topology BigOperators ContDiff

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity

def normalReflection : E2 ≃ₗᵢ[ℝ] E2 :=
  LinearIsometryEquiv.piLpCongrRight 2
    (fun i : Fin 2 => if i = 0 then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)

def nativeOddExtension (v : E2 → ℝ) (x : E2) : ℝ :=
  if 0 ≤ x 0 then v x else -v (normalReflection x)

theorem normalReflection_zero (x : E2) : normalReflection x 0 = -x 0 := by
  simp [normalReflection]

theorem normalReflection_one (x : E2) : normalReflection x 1 = x 1 := by
  simp [normalReflection]

theorem normalReflection_involutive (x : E2) : normalReflection (normalReflection x) = x := by
  ext i
  fin_cases i <;> simp [normalReflection]

theorem normalReflection_flat {x : E2} (hx : x 0 = 0) : normalReflection x = x := by
  ext i
  fin_cases i <;> simp [normalReflection, hx]

theorem normalReflection_basis_zero : normalReflection (coordinateVector 2 0) =
    -coordinateVector 2 0 := by
  ext i
  fin_cases i <;> simp [normalReflection, coordinateVector]

theorem normalReflection_basis_one : normalReflection (coordinateVector 2 1) =
    coordinateVector 2 1 := by
  ext i
  fin_cases i <;> simp [normalReflection, coordinateVector]

theorem normalReflection_maps_ball (ρ : ℝ) :
    MapsTo normalReflection (Metric.ball 0 ρ) (Metric.ball 0 ρ) := by
  intro x hx
  simpa only [Metric.mem_ball, dist_zero_right, normalReflection.norm_map] using hx

theorem c1_zero_trace_tangential_derivative
    {ρ : ℝ} {v : E2 → ℝ} (hv : ContDiffOn ℝ 1 v (closedHalfDisc ρ))
    (hzero : ∀ x ∈ flatBoundary ρ, v x = 0) {x : E2} (hx : x ∈ flatBoundary ρ) :
    fderivWithin ℝ v (closedHalfDisc ρ) x (coordinateVector 2 1) = 0 := by
  have hud := (hv.differentiableOn (by norm_num) x
    (flatBoundary_subset_closedHalfDisc ρ hx)).hasFDerivWithinAt
  have hpath : HasDerivAt (fun t : ℝ => x + t • coordinateVector 2 1)
      (coordinateVector 2 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (coordinateVector 2 1)).const_add x
  have hupath : HasDerivAt (fun t : ℝ => v (x + t • coordinateVector 2 1))
      (fderivWithin ℝ v (closedHalfDisc ρ) x (coordinateVector 2 1)) 0 := by
    apply hud.comp_hasDerivAt_of_eq 0 hpath
    · exact (tangentPath_eventually_flatBoundary hx).mono
        (fun t ht => flatBoundary_subset_closedHalfDisc ρ ht)
    · simp
  have heq : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 0]
      (fun t : ℝ => v (x + t • coordinateVector 2 1)) :=
    (tangentPath_eventually_flatBoundary hx).mono (fun t ht => (hzero _ ht).symm)
  exact (hupath.congr_of_eventuallyEq heq).unique (hasDerivAt_const (0 : ℝ) (0 : ℝ))

theorem normalReflection_zero_tangent_clm {L : E2 →L[ℝ] ℝ}
    (hL : L (coordinateVector 2 1) = 0) :
    -L.comp normalReflection.toContinuousLinearEquiv.toContinuousLinearMap = L := by
  ext y
  have hy : y = y 0 • coordinateVector 2 0 + y 1 • coordinateVector 2 1 := by
    ext i
    fin_cases i <;> simp [coordinateVector]
  rw [hy]
  simp only [map_add, map_smul, ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply]
  change y 0 • -L (normalReflection (coordinateVector 2 0)) +
    y 1 • -L (normalReflection (coordinateVector 2 1)) = _
  rw [normalReflection_basis_zero, normalReflection_basis_one, map_neg, hL]
  simp

/-- A genuine C1 extension of the same zero-trace scalar function. The input
derivative is solely within the actual closed half-disc; off-domain values
of the original total function are irrelevant. -/
theorem c1_native_odd_extension
    {ρ : ℝ} (hρ : 0 < ρ) {v : E2 → ℝ}
    (hv : ContDiffOn ℝ 1 v (closedHalfDisc ρ))
    (hzero : ∀ x ∈ flatBoundary ρ, v x = 0) :
    ContDiffOn ℝ 1 (nativeOddExtension v) (Metric.ball 0 ρ) ∧
      (∀ x ∈ closedHalfDisc ρ, nativeOddExtension v x = v x) ∧
      (∀ x ∈ Metric.ball 0 ρ, fderiv ℝ (nativeOddExtension v) x =
        if 0 ≤ x 0 then fderivWithin ℝ v (closedHalfDisc ρ) x else
          -(fderivWithin ℝ v (closedHalfDisc ρ) (normalReflection x)).comp
            normalReflection.toContinuousLinearEquiv.toContinuousLinearMap) := by
  classical
  let D := fderivWithin ℝ v (closedHalfDisc ρ)
  let S := normalReflection.toContinuousLinearEquiv.toContinuousLinearMap
  let A := Metric.ball (0 : E2) ρ ∩ {x : E2 | 0 ≤ x 0}
  let B := Metric.ball (0 : E2) ρ ∩ {x : E2 | x 0 ≤ 0}
  have hupper : ∀ x ∈ Metric.ball (0 : E2) ρ, 0 ≤ x 0 → x ∈ closedHalfDisc ρ := by
    intro x hx hn
    exact ⟨Metric.ball_subset_closedBall hx, hn⟩
  have hlower : ∀ x ∈ Metric.ball (0 : E2) ρ, x 0 ≤ 0 →
      normalReflection x ∈ closedHalfDisc ρ := by
    intro x hx hn
    refine ⟨Metric.ball_subset_closedBall (normalReflection_maps_ball ρ hx), ?_⟩
    change 0 ≤ normalReflection x 0
    rw [normalReflection_zero]
    linarith
  have hAB : A ∪ B = Metric.ball (0 : E2) ρ := by
    ext x
    simp only [A, B, mem_union, mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro h
      rcases le_total 0 (x 0) with hh | hh
      · exact Or.inl ⟨h, hh⟩
      · exact Or.inr ⟨h, hh⟩
  have hoddUpper : ∀ x : E2, 0 ≤ x 0 → nativeOddExtension v x = v x :=
    fun x hx => if_pos hx
  have hoddLower : ∀ x ∈ Metric.ball (0 : E2) ρ, x 0 ≤ 0 →
      nativeOddExtension v x = -v (normalReflection x) := by
    intro x hx hn
    by_cases hz : x 0 = 0
    · rw [hoddUpper x hz.ge, normalReflection_flat hz, hzero x ⟨hx, hz⟩, neg_zero]
    · exact if_neg (by intro hp; exact hz (le_antisymm hn hp))
  have hflatD : ∀ x ∈ flatBoundary ρ, -(D (normalReflection x)).comp S = D x := by
    intro x hx
    rw [normalReflection_flat hx.2]
    exact normalReflection_zero_tangent_clm (c1_zero_trace_tangential_derivative hv hzero hx)
  have hderiv : ∀ x ∈ Metric.ball (0 : E2) ρ,
      HasFDerivAt (nativeOddExtension v)
        (if 0 ≤ x 0 then D x else -(D (normalReflection x)).comp S) x := by
    intro x hx
    rcases lt_trichotomy 0 (x 0) with hp | hz | hn
    · rw [if_pos hp.le]
      have hxopen : x ∈ openHalfDisc ρ := ⟨hx, hp⟩
      have hd := (hv.differentiableOn (by norm_num) x (hupper x hx hp.le)).hasFDerivWithinAt
        |>.hasFDerivAt (mem_of_superset ((openHalfDisc_isOpen ρ).mem_nhds hxopen)
          (openHalfDisc_subset_closedHalfDisc ρ))
      apply hd.congr_of_eventuallyEq
      have he : ∀ᶠ y : E2 in 𝓝 x, 0 < y 0 :=
        (isOpen_lt continuous_const (EuclideanSpace.proj (0 : Fin 2)).continuous).mem_nhds hp
      exact he.mono (fun y hy => hoddUpper y hy.le)
    · have hz' : x 0 = 0 := hz.symm
      rw [if_pos hz'.ge]
      have huD := (hv.differentiableOn (by norm_num) x (hupper x hx hz'.ge)).hasFDerivWithinAt
      have ha : HasFDerivWithinAt (nativeOddExtension v) (D x) A x := by
        apply (huD.mono (fun y hy => hupper y hy.1 hy.2)).congr
        · intro y hy
          exact hoddUpper y hy.2
        · exact hoddUpper x hz'.ge
      have hmap : MapsTo normalReflection B (closedHalfDisc ρ) :=
        fun y hy => hlower y hy.1 hy.2
      have huR : HasFDerivWithinAt v (D (normalReflection x)) (closedHalfDisc ρ)
          (normalReflection x) :=
        (hv.differentiableOn (by norm_num) _ (hlower x hx hz'.le)).hasFDerivWithinAt
      have hd := (huR.comp x S.hasFDerivAt.hasFDerivWithinAt hmap).neg
      change HasFDerivWithinAt (fun y => -v (normalReflection y))
        (-(D (normalReflection x)).comp S) B x at hd
      rw [hflatD x ⟨hx, hz'⟩] at hd
      have hb : HasFDerivWithinAt (nativeOddExtension v) (D x) B x := by
        apply hd.congr
        · intro y hy
          exact hoddLower y hy.1 hy.2
        · exact hoddLower x hx hz'.le
      have hd' := ha.union hb
      rw [hAB] at hd'
      exact hd'.hasFDerivAt (Metric.isOpen_ball.mem_nhds hx)
    · rw [if_neg (not_le.mpr hn)]
      have hRx : normalReflection x ∈ openHalfDisc ρ := by
        refine ⟨normalReflection_maps_ball ρ hx, ?_⟩
        change 0 < normalReflection x 0
        rw [normalReflection_zero]
        linarith
      have hdR := (hv.differentiableOn (by norm_num) _ (hlower x hx hn.le)).hasFDerivWithinAt
        |>.hasFDerivAt (mem_of_superset ((openHalfDisc_isOpen ρ).mem_nhds hRx)
          (openHalfDisc_subset_closedHalfDisc ρ))
      apply (hdR.comp x S.hasFDerivAt).neg.congr_of_eventuallyEq
      have he : ∀ᶠ y : E2 in 𝓝 x, y 0 < 0 :=
        (isOpen_lt (EuclideanSpace.proj (0 : Fin 2)).continuous continuous_const).mem_nhds hn
      exact he.mono (fun y hy => if_neg (not_le.mpr hy))
  have hclosedUpper : IsClosed {x : E2 | 0 ≤ x 0} :=
    isClosed_le continuous_const (EuclideanSpace.proj (0 : Fin 2)).continuous
  have hclosedLower : IsClosed {x : E2 | x 0 ≤ 0} :=
    isClosed_le (EuclideanSpace.proj (0 : Fin 2)).continuous continuous_const
  have hclLower : closure {x : E2 | ¬0 ≤ x 0} ⊆ {x : E2 | x 0 ≤ 0} :=
    closure_minimal (fun x hx => (not_le.mp hx).le) hclosedLower
  have hfront : ∀ x ∈ frontier {y : E2 | 0 ≤ y 0}, x 0 = 0 := by
    intro x hx
    have hp : 0 ≤ x 0 := by
      have hh := hx.1
      rwa [hclosedUpper.closure_eq] at hh
    have hn : x 0 ≤ 0 := hclLower (by
      change x ∈ closure ({y : E2 | 0 ≤ y 0}ᶜ)
      rw [closure_compl]
      exact hx.2)
    exact le_antisymm hn hp
  have hDc : ContinuousOn D (closedHalfDisc ρ) :=
    hv.continuousOn_fderivWithin (closedHalfDisc_uniqueDiffOn hρ) (by norm_num)
  have hpiece : ContinuousOn
      (fun x => if 0 ≤ x 0 then D x else -(D (normalReflection x)).comp S)
      (Metric.ball (0 : E2) ρ) := by
    apply ContinuousOn.if
    · intro x hx
      exact (hflatD x ⟨hx.1, hfront x hx.2⟩).symm
    · exact hDc.mono (fun x hx => hupper x hx.1 (by
        have hh := hx.2
        rwa [hclosedUpper.closure_eq] at hh))
    · have hm : MapsTo normalReflection
          (Metric.ball (0 : E2) ρ ∩ closure {x : E2 | ¬0 ≤ x 0}) (closedHalfDisc ρ) :=
        fun x hx => hlower x hx.1 (hclLower hx.2)
      exact ((hDc.comp normalReflection.continuous.continuousOn hm).clm_comp
        continuousOn_const).neg
  have hsmooth : ContDiffOn ℝ 1 (nativeOddExtension v) (Metric.ball (0 : E2) ρ) := by
    rw [show (1 : ℕ∞ω) = 0 + 1 from rfl, contDiffOn_succ_iff_fderiv_of_isOpen Metric.isOpen_ball]
    refine ⟨fun x hx => (hderiv x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    rw [contDiffOn_zero]
    exact hpiece.congr (fun x hx => (hderiv x hx).fderiv)
  exact ⟨hsmooth, (fun x hx => hoddUpper x hx.2), (fun x hx => (hderiv x hx).fderiv)⟩

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
