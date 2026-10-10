import ActualFiberCriticalResidualProbe
import NativeWeakJetLocality
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak
set_option autoImplicit false
set_option maxHeartbeats 0

private theorem multiplicity_of_injOn (u : E2 → E2) (S : Set E2) (hu : InjOn u S) :
    multiplicity u S = (u '' S).indicator (fun _ => (1 : ℝ≥0∞)) := by
  classical
  funext y
  by_cases hy : y ∈ u '' S
  · obtain ⟨x, hx, hxy⟩ := hy
    have hyimage : y ∈ u '' S := ⟨x, hx, hxy⟩
    rw [indicator_of_mem hyimage]
    let x₀ : {x : E2 // x ∈ S ∧ u x = y} := ⟨x, hx, hxy⟩
    unfold DirectWeak.multiplicity
    apply (tsum_eq_single x₀ _).trans (by rfl)
    intro z hz
    exfalso
    apply hz
    apply Subtype.ext
    exact hu z.2.1 hx (z.2.2.trans hxy.symm)
  · rw [indicator_of_notMem hy]
    have hempty : IsEmpty {x : E2 // x ∈ S ∧ u x = y} :=
      ⟨fun x => hy ⟨x.1, x.2.1, x.2.2⟩⟩
    letI := hempty
    simp [DirectWeak.multiplicity]

private theorem multiplicity_countable_disjoint_union
    (u : E2 → E2) (S : ℕ → Set E2) (hdisj : Pairwise (Disjoint on S)) (y : E2) :
    multiplicity u (⋃ n, S n) y = ∑' n, multiplicity u (S n) y := by
  let F : ℕ → Set E2 := fun n => {x | x ∈ S n ∧ u x = y}
  have hF : univ.PairwiseDisjoint F := by
    intro i _ j _ hij
    exact (hdisj hij).mono (fun _ hx => hx.1) (fun _ hx => hx.1)
  have hset : {x | x ∈ ⋃ n, S n ∧ u x = y} = ⋃ n, F n := by
    ext x
    simp only [F, mem_setOf_eq, mem_iUnion]
    constructor
    · rintro ⟨⟨n, hn⟩, he⟩
      exact ⟨n, hn, he⟩
    · rintro ⟨n, hn, he⟩
      exact ⟨⟨n, hn⟩, he⟩
  unfold DirectWeak.multiplicity
  change (∑' x : {x | x ∈ ⋃ n, S n ∧ u x = y}, (1 : ℝ≥0∞)) = _
  rw [hset]
  change (∑' x : ⋃ n, F n, (1 : ℝ≥0∞)) = ∑' n, ∑' x : F n, (1 : ℝ≥0∞)
  exact ENNReal.tsum_biUnion (f := fun _ => (1 : ℝ≥0∞)) hF

private theorem multiplicity_ignore_lusin_null
    (u : E2 → E2) (hu : LusinOnDisc u)
    (S T : Set E2) (hS : S ⊆ disc 1) (hT : T ⊆ S)
    (hnull : volume (S \ T) = 0) :
    multiplicity u S =ᵐ[volume] multiplicity u T := by
  have hn := hu (S \ T) (sdiff_subset.trans hS) hnull
  have hae : ∀ᵐ y ∂volume, y ∉ u '' (S \ T) := by
    apply ae_iff.mpr
    simp only [not_not]
    change volume (u '' (S \ T)) = 0
    exact hn
  filter_upwards [hae] with y hy
  have hs : {x | x ∈ S ∧ u x = y} = {x | x ∈ T ∧ u x = y} := by
    ext x
    constructor
    · intro hx
      refine ⟨?_, hx.2⟩
      by_contra hn
      exact hy ⟨x, ⟨hx.1, hn⟩, hx.2⟩
    · intro hx
      exact ⟨hT hx.1, hx.2⟩
  unfold DirectWeak.multiplicity
  change (∑' x : {x | x ∈ S ∧ u x = y}, (1 : ℝ≥0∞)) =
    ∑' x : {x | x ∈ T ∧ u x = y}, (1 : ℝ≥0∞)
  rw [hs]

private theorem countable_injective_piece_multiplicity_AE
    (u : E2 → E2) (hu : LusinOnDisc u)
    (P : ℕ → Set E2) (hdisj : Pairwise (Disjoint on P))
    (hinj : ∀ n, InjOn u (P n))
    (himages : ∀ n, ∀ S : Set E2, MeasurableSet S → MeasurableSet (u '' (S ∩ P n)))
    (hcover : volume (disc 1 \ ⋃ n, P n) = 0)
    (S : Set E2) (hS : MeasurableSet S) (hsub : S ⊆ disc 1) :
    AEMeasurable (multiplicity u S) volume ∧
    multiplicity u S =ᵐ[volume]
      (fun y => ∑' n, (u '' (S ∩ P n)).indicator (fun _ => (1 : ℝ≥0∞)) y) := by
  let T : Set E2 := ⋃ n, S ∩ P n
  have hT : T ⊆ S := iUnion_subset (fun _ => inter_subset_left)
  have hnull : volume (S \ T) = 0 := by
    apply measure_mono_null _ hcover
    intro x hx
    refine ⟨hsub hx.1, ?_⟩
    intro hp
    obtain ⟨n, hn⟩ := mem_iUnion.mp hp
    exact hx.2 (mem_iUnion.mpr ⟨n, hx.1, hn⟩)
  have hae := multiplicity_ignore_lusin_null u hu S T hsub hT hnull
  have hd : Pairwise (Disjoint on fun n => S ∩ P n) := by
    intro i j hij
    exact (hdisj hij).mono inter_subset_right inter_subset_right
  have hcount (y : E2) : multiplicity u T y =
      ∑' n, (u '' (S ∩ P n)).indicator (fun _ => (1 : ℝ≥0∞)) y := by
    rw [multiplicity_countable_disjoint_union u (fun n => S ∩ P n) hd y]
    apply tsum_congr
    intro n
    exact congrFun (multiplicity_of_injOn u (S ∩ P n) ((hinj n).mono inter_subset_right)) y
  have he := hae.trans (Filter.Eventually.of_forall hcount)
  have hm : AEMeasurable (fun y => ∑' n, (u '' (S ∩ P n)).indicator (fun _ => (1 : ℝ≥0∞)) y) volume := by
    apply AEMeasurable.tsum
    intro n
    exact (measurable_const.indicator (himages n S hS)).aemeasurable
  exact ⟨hm.congr he.symm, he⟩

#print axioms multiplicity_of_injOn
#print axioms multiplicity_countable_disjoint_union
#print axioms multiplicity_ignore_lusin_null
#print axioms countable_injective_piece_multiplicity_AE

private theorem every_subset_area_of_native_differentiable_pieces
    (u : E2 → E2) (d : Fin 2 → E2 → E2) (hu : LusinOnDisc u)
    (P : ℕ → Set E2) (hP : ∀ n, MeasurableSet (P n))
    (hdisj : Pairwise (Disjoint on P)) (hinj : ∀ n, InjOn u (P n))
    (D : ℕ → E2 → E2 →L[ℝ] E2)
    (hD : ∀ n x, x ∈ P n → HasFDerivWithinAt u (D n x) (P n) x)
    (hdet : ∀ n x, x ∈ P n → (D n x).det = Matrix.det (weakJacobian d x))
    (hcover : volume (disc 1 \ ⋃ n, P n) = 0)
    (w : E2 → ℝ≥0∞) (hw : Measurable w)
    (S : Set E2) (hS : MeasurableSet S) (hsub : S ⊆ disc 1) :
    AEMeasurable (multiplicity u S) volume ∧
    (∫⁻ x in S, w (u x) * ENNReal.ofReal |Matrix.det (weakJacobian d x)|) =
      ∫⁻ y, w y * multiplicity u S y := by
  classical
  have hpieceD (n : ℕ) : ∀ x ∈ S ∩ P n, HasFDerivWithinAt u (D n x) (S ∩ P n) x :=
    fun x hx => (hD n x hx.2).mono inter_subset_right
  have himages (n : ℕ) (S' : Set E2) (hS' : MeasurableSet S') : MeasurableSet (u '' (S' ∩ P n)) :=
    measurable_image_of_fderivWithin (hS'.inter (hP n))
      (fun x hx => (hD n x hx.2).mono inter_subset_right)
      ((hinj n).mono inter_subset_right)
  obtain ⟨hcount, hae⟩ := countable_injective_piece_multiplicity_AE u hu P hdisj hinj
    himages hcover S hS hsub
  refine ⟨hcount, ?_⟩
  let T : Set E2 := ⋃ n, S ∩ P n
  have hT : T ⊆ S := iUnion_subset (fun _ => inter_subset_left)
  have hnull : volume (S \ T) = 0 := by
    apply measure_mono_null _ hcover
    intro x hx
    refine ⟨hsub hx.1, ?_⟩
    intro hp
    obtain ⟨n, hn⟩ := mem_iUnion.mp hp
    exact hx.2 (mem_iUnion.mpr ⟨n, hx.1, hn⟩)
  have hST : S =ᵐ[volume] T := ae_eq_set.mpr ⟨hnull, by rw [sdiff_eq_empty.mpr hT, measure_empty]⟩
  have hpiece (n : ℕ) :
      (∫⁻ x in S ∩ P n, w (u x) * ENNReal.ofReal |Matrix.det (weakJacobian d x)|) =
      ∫⁻ y, w y * (u '' (S ∩ P n)).indicator (fun _ => (1 : ℝ≥0∞)) y := by
    calc
      _ = ∫⁻ x in S ∩ P n, ENNReal.ofReal |(D n x).det| * w (u x) := by
        apply setLIntegral_congr_fun (hS.inter (hP n))
        intro x hx
        dsimp
        rw [← hdet n x hx.2, mul_comm]
      _ = ∫⁻ y in u '' (S ∩ P n), w y :=
        (lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
          (hS.inter (hP n)) (hpieceD n) ((hinj n).mono inter_subset_right) w).symm
      _ = ∫⁻ y, w y * (u '' (S ∩ P n)).indicator (fun _ => (1 : ℝ≥0∞)) y := by
        rw [← lintegral_indicator (himages n S hS)]
        apply lintegral_congr
        intro y
        by_cases hy : y ∈ u '' (S ∩ P n) <;> simp [hy]
  have hd : Pairwise (Disjoint on fun n => S ∩ P n) := by
    intro i j hij
    exact (hdisj hij).mono inter_subset_right inter_subset_right
  calc
    _ = ∫⁻ x in T, w (u x) * ENNReal.ofReal |Matrix.det (weakJacobian d x)| := setLIntegral_congr hST
    _ = ∑' n, ∫⁻ x in S ∩ P n, w (u x) * ENNReal.ofReal |Matrix.det (weakJacobian d x)| :=
      lintegral_iUnion (fun n => hS.inter (hP n)) hd _
    _ = ∑' n, ∫⁻ y, w y * (u '' (S ∩ P n)).indicator (fun _ => (1 : ℝ≥0∞)) y :=
      tsum_congr hpiece
    _ = ∫⁻ y, ∑' n, w y * (u '' (S ∩ P n)).indicator (fun _ => (1 : ℝ≥0∞)) y := by
      symm
      apply lintegral_tsum
      intro n
      exact (hw.mul (measurable_const.indicator (himages n S hS))).aemeasurable
    _ = ∫⁻ y, w y * ∑' n, (u '' (S ∩ P n)).indicator (fun _ => (1 : ℝ≥0∞)) y := by
      apply lintegral_congr
      intro y
      exact ENNReal.tsum_mul_left
    _ = ∫⁻ y, w y * multiplicity u S y := by
      apply lintegral_congr_ae
      filter_upwards [hae] with y hy
      rw [hy]

#print axioms every_subset_area_of_native_differentiable_pieces

private theorem multiplicity_ignore_null_image
    (u : E2 → E2) (S T : Set E2) (hT : T ⊆ S)
    (himage : volume (u '' (S \ T)) = 0) :
    multiplicity u S =ᵐ[volume] multiplicity u T := by
  have hae : ∀ᵐ y ∂volume, y ∉ u '' (S \ T) := by
    apply ae_iff.mpr
    simpa only [not_not, Set.setOf_mem_eq] using himage
  filter_upwards [hae] with y hy
  have hs : {x | x ∈ S ∧ u x = y} = {x | x ∈ T ∧ u x = y} := by
    ext x
    constructor
    · intro hx
      refine ⟨?_, hx.2⟩
      by_contra hn
      exact hy ⟨x, ⟨hx.1, hn⟩, hx.2⟩
    · intro hx
      exact ⟨hT hx.1, hx.2⟩
  unfold DirectWeak.multiplicity
  change (∑' x : {x | x ∈ S ∧ u x = y}, (1 : ℝ≥0∞)) =
    ∑' x : {x | x ∈ T ∧ u x = y}, (1 : ℝ≥0∞)
  rw [hs]

private theorem lusin_of_differentiable_pieces_and_null_remainder_image
    (u : E2 → E2) (P : ℕ → Set E2)
    (D : ℕ → E2 → E2 →L[ℝ] E2)
    (hD : ∀ n x, x ∈ P n → HasFDerivWithinAt u (D n x) (P n) x)
    (himage : volume (u '' (disc 1 \ ⋃ n, P n)) = 0) :
    LusinOnDisc u := by
  intro E hE hnull
  have hpiece (n : ℕ) : volume (u '' (E ∩ P n)) = 0 := by
    apply addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    · intro x hx
      exact ((hD n x hx.2).mono inter_subset_right).differentiableWithinAt
    · exact measure_mono_null inter_subset_left hnull
  have hsubset : u '' E ⊆
      u '' (disc 1 \ ⋃ n, P n) ∪ ⋃ n, u '' (E ∩ P n) := by
    rintro y ⟨x, hx, rfl⟩
    by_cases hp : x ∈ ⋃ n, P n
    · obtain ⟨n, hn⟩ := mem_iUnion.mp hp
      exact Or.inr (mem_iUnion.mpr ⟨n, ⟨x, ⟨hx, hn⟩, rfl⟩⟩)
    · exact Or.inl ⟨x, ⟨hE hx, hp⟩, rfl⟩
  apply measure_mono_null hsubset
  apply measure_union_null himage
  exact measure_iUnion_null hpiece

private theorem every_subset_area_with_critical_remainder
    (u : E2 → E2) (d : Fin 2 → E2 → E2)
    (P : ℕ → Set E2) (hP : ∀ n, MeasurableSet (P n))
    (hdisj : Pairwise (Disjoint on P)) (hinj : ∀ n, InjOn u (P n))
    (D : ℕ → E2 → E2 →L[ℝ] E2)
    (hD : ∀ n x, x ∈ P n → HasFDerivWithinAt u (D n x) (P n) x)
    (hdet : ∀ n x, x ∈ P n → (D n x).det = Matrix.det (weakJacobian d x))
    (himage : volume (u '' (disc 1 \ ⋃ n, P n)) = 0)
    (hzero : ∀ᵐ x ∂volume, x ∈ disc 1 \ ⋃ n, P n → Matrix.det (weakJacobian d x) = 0)
    (w : E2 → ℝ≥0∞) (hw : Measurable w)
    (S : Set E2) (hS : MeasurableSet S) (hsub : S ⊆ disc 1) :
    AEMeasurable (multiplicity u S) volume ∧
    (∫⁻ x in S, w (u x) * ENNReal.ofReal |Matrix.det (weakJacobian d x)|) =
      ∫⁻ y, w y * multiplicity u S y := by
  run_tac do
    let n := (Lean.Name.num `_private.ActualFiberCriticalResidualProbe 0).str
      "every_subset_area_of_native_pieces_critical_residual"
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.withContext do
      let args ← ([`u, `d, `P, `hP, `hdisj, `hinj, `D, `hD, `hdet,
        `himage, `hzero, `w, `hw, `S, `hS, `hsub].toArray.mapM
        fun name => Lean.Elab.Term.elabTerm (Lean.mkIdent name) none)
      let body := Lean.mkAppN (.const n []) args
      Lean.Meta.checkWithKernel body
      goal.assign body
    Lean.Elab.Tactic.replaceMainGoal []

#print axioms multiplicity_ignore_null_image
#print axioms lusin_of_differentiable_pieces_and_null_remainder_image
#print axioms every_subset_area_with_critical_remainder

private theorem area_and_lusin_of_native_pieces_critical_residual
    (u : E2 → E2) (d : Fin 2 → E2 → E2)
    (P : ℕ → Set E2) (hP : ∀ n, MeasurableSet (P n))
    (hdisj : Pairwise (Disjoint on P)) (hinj : ∀ n, InjOn u (P n))
    (D : ℕ → E2 → E2 →L[ℝ] E2)
    (hD : ∀ n x, x ∈ P n → HasFDerivWithinAt u (D n x) (P n) x)
    (hdet : ∀ n x, x ∈ P n → (D n x).det = Matrix.det (weakJacobian d x))
    (himage : volume (u '' (disc 1 \ ⋃ n, P n)) = 0)
    (hzero : ∀ᵐ x ∂volume, x ∈ disc 1 \ ⋃ n, P n →
      Matrix.det (weakJacobian d x) = 0) :
    LusinOnDisc u ∧
    ∀ (w : E2 → ℝ≥0∞), Measurable w →
      ∀ S : Set E2, MeasurableSet S → S ⊆ disc 1 →
        AEMeasurable (multiplicity u S) volume ∧
        (∫⁻ x in S, w (u x) * ENNReal.ofReal |Matrix.det (weakJacobian d x)|) =
          ∫⁻ y, w y * multiplicity u S y := by
  classical
  have hformula : ∀ (w : E2 → ℝ≥0∞), Measurable w →
      ∀ S : Set E2, MeasurableSet S → S ⊆ disc 1 →
        AEMeasurable (multiplicity u S) volume ∧
        (∫⁻ x in S, w (u x) * ENNReal.ofReal |Matrix.det (weakJacobian d x)|) =
          ∫⁻ y, w y * multiplicity u S y := by
    intro w hw S hS hsub
    exact every_subset_area_with_critical_remainder u d P hP hdisj hinj D hD hdet
      himage hzero w hw S hS hsub
  have hLusin : LusinOnDisc u := by
    intro E hE hnull
    obtain ⟨T, hET, hT, hTnull⟩ := exists_measurable_superset_of_null hnull
    let S : Set E2 := T ∩ disc 1
    have hS : MeasurableSet S := hT.inter Metric.isOpen_ball.measurableSet
    have hSnull : volume S = 0 := measure_mono_null inter_subset_left hTnull
    obtain ⟨hcount, harea⟩ := hformula (fun _ => 1) measurable_const S hS inter_subset_right
    have hmeas : AEMeasurable (multiplicity u S) volume := hcount
    have hint : (∫⁻ y, multiplicity u S y) = 0 := by
      simp only [one_mul] at harea
      rw [← harea, Measure.restrict_eq_zero.mpr hSnull, lintegral_zero_measure]
    have hzero' : (multiplicity u S) =ᵐ[volume] 0 :=
      (lintegral_eq_zero_iff' hmeas).mp hint
    have havoid : ∀ᵐ y ∂volume, y ∉ u '' S := by
      filter_upwards [hzero'] with y hy
      intro himage'
      obtain ⟨x, hx, hxy⟩ := himage'
      have hpos : (0 : ℝ≥0∞) < multiplicity u S y := by
        exact lt_of_lt_of_le (by norm_num)
          (ENNReal.le_tsum (f := fun _ : {x : E2 // x ∈ S ∧ u x = y} =>
            (1 : ℝ≥0∞)) ⟨x, hx, hxy⟩)
      exact (ne_of_gt hpos) hy
    have hSimage : volume (u '' S) = 0 := by
      simpa only [not_not, Set.setOf_mem_eq] using ae_iff.mp havoid
    have hES : E ⊆ S := fun x hx => ⟨hET hx, hE hx⟩
    exact measure_mono_null (image_mono hES) hSimage
  exact ⟨hLusin, hformula⟩

#print axioms area_and_lusin_of_native_pieces_critical_residual

private theorem positive_injective_approximation_radius
    (A : E2 →L[ℝ] E2) (hA : A.det ≠ 0) :
    ∃ r : ℝ≥0, 0 < r ∧ ∀ (u : E2 → E2) (S : Set E2),
      ApproximatesLinearOn u A S r → InjOn u S := by
  let e : E2 ≃L[ℝ] E2 :=
    (LinearMap.equivOfIsUnitDet (f := A.toLinearMap) (isUnit_iff_ne_zero.mpr hA)).toContinuousLinearEquiv
  have he : (e : E2 →L[ℝ] E2) = A := by
    apply ContinuousLinearMap.ext
    intro x
    exact LinearMap.equivOfIsUnitDet_apply (R := ℝ) (f := A.toLinearMap)
      (isUnit_iff_ne_zero.mpr hA) x
  have hn : 0 < ‖(e.symm : E2 →L[ℝ] E2)‖₊ := by
    exact_mod_cast e.symm.norm_pos
  let r : ℝ≥0 := ‖(e.symm : E2 →L[ℝ] E2)‖₊⁻¹ / 2
  have hr : 0 < r := by dsimp [r]; positivity
  refine ⟨r, hr, ?_⟩
  intro u S hu
  rw [← he] at hu
  apply hu.injOn (Or.inr ?_)
  dsimp [r]
  exact half_lt_self (inv_pos.mpr hn)

private theorem noncritical_native_derivative_injective_partition
    (u : E2 → E2) (S : Set E2) (hS : MeasurableSet S)
    (D : E2 → E2 →L[ℝ] E2)
    (hD : ∀ x ∈ S, HasFDerivWithinAt u (D x) S x)
    (hnonzero : ∀ x ∈ S, (D x).det ≠ 0) :
    ∃ P : ℕ → Set E2,
      (∀ n, MeasurableSet (P n)) ∧ Pairwise (Disjoint on P) ∧
      (⋃ n, P n) = S ∧ (∀ n, P n ⊆ S) ∧ (∀ n, InjOn u (P n)) ∧
      ∀ n x, x ∈ P n → HasFDerivWithinAt u (D x) (P n) x := by
  classical
  rcases eq_empty_or_nonempty S with rfl | hs
  · refine ⟨fun _ => ∅, fun _ => MeasurableSet.empty,
      fun i j hij => by simp, by simp,
      fun _ => empty_subset _, fun _ => Set.injOn_empty _, ?_⟩
    intro n x hx
    exact hx.elim
  let r : (E2 →L[ℝ] E2) → ℝ≥0 := fun A =>
    if h : A.det ≠ 0 then (positive_injective_approximation_radius A h).choose else 1
  have hr : ∀ A, r A ≠ 0 := by
    intro A
    by_cases h : A.det ≠ 0
    · simp only [r, dif_pos h]
      exact (positive_injective_approximation_radius A h).choose_spec.1.ne'
    · simp only [r, dif_neg h]
      norm_num
  obtain ⟨t, A, hdisj, hmeas, hcover, happ, hvalues⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt u S D hD r hr
  let P : ℕ → Set E2 := fun n => S ∩ t n
  have hsub : ∀ n, P n ⊆ S := fun _ => inter_subset_left
  refine ⟨P, fun n => hS.inter (hmeas n), ?_, ?_, hsub, ?_, ?_⟩
  · intro i j hij
    exact (hdisj hij).mono inter_subset_right inter_subset_right
  · apply Subset.antisymm
    · exact iUnion_subset hsub
    · intro x hx
      obtain ⟨n, hn⟩ := mem_iUnion.mp (hcover hx)
      exact mem_iUnion.mpr ⟨n, hx, hn⟩
  · intro n
    obtain ⟨x, hx, he⟩ := hvalues hs n
    have hA : (A n).det ≠ 0 := he ▸ hnonzero x hx
    have h := (positive_injective_approximation_radius (A n) hA).choose_spec.2 u (P n)
    apply h
    simpa only [r, dif_pos hA] using happ n
  · intro n x hx
    exact (hD x hx.1).mono (hsub n)

#print axioms positive_injective_approximation_radius
#print axioms noncritical_native_derivative_injective_partition

private theorem area_and_lusin_of_actual_native_derivative_set
    (u : E2 → E2) (d : Fin 2 → E2 → E2)
    (Q : Set E2) (hQ : MeasurableSet Q)
    (D : E2 → E2 →L[ℝ] E2)
    (hD : ∀ x ∈ Q, HasFDerivWithinAt u (D x) Q x)
    (hDm : Measurable (fun x => (D x).det))
    (hdet : ∀ x ∈ Q, (D x).det = Matrix.det (weakJacobian d x))
    (himage : volume (u '' (disc 1 \ Q)) = 0)
    (hzero : ∀ᵐ x ∂volume, x ∈ disc 1 \ Q → Matrix.det (weakJacobian d x) = 0) :
    LusinOnDisc u ∧
    ∀ (w : E2 → ℝ≥0∞), Measurable w →
      ∀ S : Set E2, MeasurableSet S → S ⊆ disc 1 →
        AEMeasurable (multiplicity u S) volume ∧
        (∫⁻ x in S, w (u x) * ENNReal.ofReal |Matrix.det (weakJacobian d x)|) =
          ∫⁻ y, w y * multiplicity u S y := by
  classical
  let A : Set E2 := Q ∩ {x | (D x).det ≠ 0}
  let C : Set E2 := Q ∩ {x | (D x).det = 0}
  have hA : MeasurableSet A := hQ.inter ((hDm (measurableSet_singleton 0)).compl)
  have hAd : ∀ x ∈ A, HasFDerivWithinAt u (D x) A x :=
    fun x hx => (hD x hx.1).mono inter_subset_left
  obtain ⟨P, hP, hdisj, hcover, hPQ, hinj, hPD⟩ :=
    noncritical_native_derivative_injective_partition u A hA D hAd (fun x hx => hx.2)
  have hcritical : volume (u '' C) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (fun x hx => (hD x hx.1).mono inter_subset_left) (fun x hx => hx.2)
  have hremain : disc 1 \ ⋃ n, P n ⊆ (disc 1 \ Q) ∪ C := by
    intro x hx
    rw [hcover] at hx
    by_cases hxQ : x ∈ Q
    · exact Or.inr ⟨hxQ, by
        by_contra hn
        exact hx.2 ⟨hxQ, hn⟩⟩
    · exact Or.inl ⟨hx.1, hxQ⟩
  have himage' : volume (u '' (disc 1 \ ⋃ n, P n)) = 0 := by
    apply measure_mono_null (image_mono hremain)
    rw [image_union]
    exact measure_union_null himage hcritical
  have hzero' : ∀ᵐ x ∂volume,
      x ∈ disc 1 \ ⋃ n, P n → Matrix.det (weakJacobian d x) = 0 := by
    filter_upwards [hzero] with x hx
    intro hxp
    rcases hremain hxp with hbad | hcrit
    · exact hx hbad
    · exact (hdet x hcrit.1).symm.trans hcrit.2
  have hdet' : ∀ n x, x ∈ P n → (D x).det = Matrix.det (weakJacobian d x) :=
    fun n x hx => hdet x (hPQ n hx).1
  refine ⟨lusin_of_differentiable_pieces_and_null_remainder_image u P
    (fun _ => D) hPD himage', ?_⟩
  intro w hw S hS hsub
  exact every_subset_area_with_critical_remainder u d P hP hdisj hinj
    (fun _ => D) hPD hdet' himage' hzero' w hw S hS hsub

#print axioms area_and_lusin_of_actual_native_derivative_set

private theorem area_of_countable_native_derivative_pieces
    (u : E2 → E2) (d : Fin 2 → E2 → E2) (hu : LusinOnDisc u)
    (Q : ℕ → Set E2) (hQ : ∀ n, MeasurableSet (Q n))
    (hdisjQ : Pairwise (Disjoint on Q))
    (D : ℕ → E2 → E2 →L[ℝ] E2)
    (hD : ∀ n x, x ∈ Q n → HasFDerivWithinAt u (D n x) (Q n) x)
    (hDm : ∀ n, Measurable (fun x => (D n x).det))
    (hdet : ∀ n x, x ∈ Q n → (D n x).det = Matrix.det (weakJacobian d x))
    (hcover : volume (disc 1 \ ⋃ n, Q n) = 0)
    (w : E2 → ℝ≥0∞) (hw : Measurable w)
    (S : Set E2) (hS : MeasurableSet S) (hsub : S ⊆ disc 1) :
    AEMeasurable (multiplicity u S) volume ∧
    (∫⁻ x in S, w (u x) * ENNReal.ofReal |Matrix.det (weakJacobian d x)|) =
      ∫⁻ y, w y * multiplicity u S y := by
  classical
  let A : ℕ → Set E2 := fun n => Q n ∩ {x | (D n x).det ≠ 0}
  let C : ℕ → Set E2 := fun n => Q n ∩ {x | (D n x).det = 0}
  have hA : ∀ n, MeasurableSet (A n) := fun n =>
    (hQ n).inter (((hDm n) (measurableSet_singleton 0)).compl)
  have hparts (n : ℕ) : ∃ P : ℕ → Set E2,
      (∀ k, MeasurableSet (P k)) ∧ Pairwise (Disjoint on P) ∧
      (⋃ k, P k) = A n ∧ (∀ k, P k ⊆ A n) ∧ (∀ k, InjOn u (P k)) ∧
      ∀ k x, x ∈ P k → HasFDerivWithinAt u (D n x) (P k) x := by
    apply noncritical_native_derivative_injective_partition u (A n) (hA n) (D n)
    · exact fun x hx => (hD n x hx.1).mono inter_subset_left
    · exact fun x hx => hx.2
  choose P hP hdisj hPA hPsub hinj hPD using hparts
  let e : ℕ ≃ ℕ × ℕ := Nat.pairEquiv.symm
  let V : ℕ → Set E2 := fun k => P (e k).1 (e k).2
  let DV : ℕ → E2 → E2 →L[ℝ] E2 := fun k => D (e k).1
  have hV : ∀ k, MeasurableSet (V k) := fun k => hP (e k).1 (e k).2
  have hVQ (k : ℕ) : V k ⊆ Q (e k).1 :=
    (hPsub (e k).1 (e k).2).trans inter_subset_left
  have hVcover : (⋃ k, V k) = ⋃ n, A n := by
    ext x
    constructor
    · rintro hx
      obtain ⟨k, hk⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨(e k).1, hPsub (e k).1 (e k).2 hk⟩
    · rintro hx
      obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      rw [← hPA n] at hn
      obtain ⟨k, hk⟩ := mem_iUnion.mp hn
      refine mem_iUnion.mpr ⟨e.symm (n,k), ?_⟩
      simpa only [V, Equiv.apply_symm_apply] using hk
  have hVdisj : Pairwise (Disjoint on V) := by
    intro i j hij
    by_cases hn : (e i).1 = (e j).1
    · have hk : (e i).2 ≠ (e j).2 := by
        intro he
        exact hij (e.injective (Prod.ext hn he))
      have hdis := hdisj (e i).1 hk
      change Disjoint (P (e i).1 (e i).2) (P (e j).1 (e j).2)
      rw [← hn]
      exact hdis
    · exact (hdisjQ hn).mono (hVQ i) (hVQ j)
  have hVinj : ∀ k, InjOn u (V k) := fun k => hinj (e k).1 (e k).2
  have hVD : ∀ k x, x ∈ V k → HasFDerivWithinAt u (DV k x) (V k) x :=
    fun k => hPD (e k).1 (e k).2
  have hVdet : ∀ k x, x ∈ V k → (DV k x).det = Matrix.det (weakJacobian d x) :=
    fun k x hx => hdet (e k).1 x (hVQ k hx)
  have hcritical (n : ℕ) : volume (u '' C n) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (fun x hx => (hD n x hx.1).mono inter_subset_left) (fun x hx => hx.2)
  have hremain : disc 1 \ ⋃ k, V k ⊆ (disc 1 \ ⋃ n, Q n) ∪ ⋃ n, C n := by
    intro x hx
    rw [hVcover] at hx
    by_cases hq : x ∈ ⋃ n, Q n
    · obtain ⟨n, hn⟩ := mem_iUnion.mp hq
      refine Or.inr (mem_iUnion.mpr ⟨n, hn, ?_⟩)
      by_contra hne
      exact hx.2 (mem_iUnion.mpr ⟨n, hn, hne⟩)
    · exact Or.inl ⟨hx.1, hq⟩
  have hnullimage : volume (u '' (disc 1 \ ⋃ k, V k)) = 0 := by
    apply measure_mono_null (image_mono hremain)
    rw [image_union, image_iUnion]
    exact measure_union_null (hu _ sdiff_subset hcover) (measure_iUnion_null hcritical)
  have hbadAE : ∀ᵐ x ∂volume, x ∉ disc 1 \ ⋃ n, Q n := by
    apply ae_iff.mpr
    simpa only [not_not, Set.setOf_mem_eq] using hcover
  have hzero : ∀ᵐ x ∂volume,
      x ∈ disc 1 \ ⋃ k, V k → Matrix.det (weakJacobian d x) = 0 := by
    filter_upwards [hbadAE] with x hx
    intro hxp
    rcases hremain hxp with hbad | hcrit
    · exact (hx hbad).elim
    · obtain ⟨n, hn, he⟩ := mem_iUnion.mp hcrit
      exact (hdet n x hn).symm.trans he
  exact every_subset_area_with_critical_remainder u d V hV hVdisj hVinj DV hVD hVdet
    hnullimage hzero w hw S hS hsub

#print axioms area_of_countable_native_derivative_pieces


private theorem area_and_lusin_of_countable_native_derivative_pieces
    (u : E2 → E2) (d : Fin 2 → E2 → E2)
    (Q : ℕ → Set E2) (hQ : ∀ n, MeasurableSet (Q n))
    (hdisjQ : Pairwise (Disjoint on Q))
    (D : ℕ → E2 → E2 →L[ℝ] E2)
    (hD : ∀ n x, x ∈ Q n → HasFDerivWithinAt u (D n x) (Q n) x)
    (hDm : ∀ n, Measurable (fun x => (D n x).det))
    (hdet : ∀ n x, x ∈ Q n → (D n x).det = Matrix.det (weakJacobian d x))
    (himageQ : volume (u '' (disc 1 \ ⋃ n, Q n)) = 0)
    (hzeroQ : ∀ᵐ x ∂volume, x ∈ disc 1 \ ⋃ n, Q n →
      Matrix.det (weakJacobian d x) = 0) :
    LusinOnDisc u ∧
    ∀ (w : E2 → ℝ≥0∞), Measurable w →
      ∀ S : Set E2, MeasurableSet S → S ⊆ disc 1 →
        AEMeasurable (multiplicity u S) volume ∧
        (∫⁻ x in S, w (u x) * ENNReal.ofReal |Matrix.det (weakJacobian d x)|) =
          ∫⁻ y, w y * multiplicity u S y := by
  classical
  let A : ℕ → Set E2 := fun n => Q n ∩ {x | (D n x).det ≠ 0}
  let C : ℕ → Set E2 := fun n => Q n ∩ {x | (D n x).det = 0}
  have hA : ∀ n, MeasurableSet (A n) := fun n =>
    (hQ n).inter (((hDm n) (measurableSet_singleton 0)).compl)
  have hparts (n : ℕ) : ∃ P : ℕ → Set E2,
      (∀ k, MeasurableSet (P k)) ∧ Pairwise (Disjoint on P) ∧
      (⋃ k, P k) = A n ∧ (∀ k, P k ⊆ A n) ∧ (∀ k, InjOn u (P k)) ∧
      ∀ k x, x ∈ P k → HasFDerivWithinAt u (D n x) (P k) x := by
    apply noncritical_native_derivative_injective_partition u (A n) (hA n) (D n)
    · exact fun x hx => (hD n x hx.1).mono inter_subset_left
    · exact fun x hx => hx.2
  choose P hP hdisj hPA hPsub hinj hPD using hparts
  let e : ℕ ≃ ℕ × ℕ := Nat.pairEquiv.symm
  let V : ℕ → Set E2 := fun k => P (e k).1 (e k).2
  let DV : ℕ → E2 → E2 →L[ℝ] E2 := fun k => D (e k).1
  have hV : ∀ k, MeasurableSet (V k) := fun k => hP (e k).1 (e k).2
  have hVQ (k : ℕ) : V k ⊆ Q (e k).1 :=
    (hPsub (e k).1 (e k).2).trans inter_subset_left
  have hVcover : (⋃ k, V k) = ⋃ n, A n := by
    ext x
    constructor
    · rintro hx
      obtain ⟨k, hk⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨(e k).1, hPsub (e k).1 (e k).2 hk⟩
    · rintro hx
      obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      rw [← hPA n] at hn
      obtain ⟨k, hk⟩ := mem_iUnion.mp hn
      refine mem_iUnion.mpr ⟨e.symm (n,k), ?_⟩
      simpa only [V, Equiv.apply_symm_apply] using hk
  have hVdisj : Pairwise (Disjoint on V) := by
    intro i j hij
    by_cases hn : (e i).1 = (e j).1
    · have hk : (e i).2 ≠ (e j).2 := by
        intro he
        exact hij (e.injective (Prod.ext hn he))
      have hdis := hdisj (e i).1 hk
      change Disjoint (P (e i).1 (e i).2) (P (e j).1 (e j).2)
      rw [← hn]
      exact hdis
    · exact (hdisjQ hn).mono (hVQ i) (hVQ j)
  have hVinj : ∀ k, InjOn u (V k) := fun k => hinj (e k).1 (e k).2
  have hVD : ∀ k x, x ∈ V k → HasFDerivWithinAt u (DV k x) (V k) x :=
    fun k => hPD (e k).1 (e k).2
  have hVdet : ∀ k x, x ∈ V k → (DV k x).det = Matrix.det (weakJacobian d x) :=
    fun k x hx => hdet (e k).1 x (hVQ k hx)
  have hcritical (n : ℕ) : volume (u '' C n) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (fun x hx => (hD n x hx.1).mono inter_subset_left) (fun x hx => hx.2)
  have hremain : disc 1 \ ⋃ k, V k ⊆ (disc 1 \ ⋃ n, Q n) ∪ ⋃ n, C n := by
    intro x hx
    rw [hVcover] at hx
    by_cases hq : x ∈ ⋃ n, Q n
    · obtain ⟨n, hn⟩ := mem_iUnion.mp hq
      refine Or.inr (mem_iUnion.mpr ⟨n, hn, ?_⟩)
      by_contra hne
      exact hx.2 (mem_iUnion.mpr ⟨n, hn, hne⟩)
    · exact Or.inl ⟨hx.1, hq⟩
  have hnullimage : volume (u '' (disc 1 \ ⋃ k, V k)) = 0 := by
    apply measure_mono_null (image_mono hremain)
    rw [image_union, image_iUnion]
    exact measure_union_null himageQ (measure_iUnion_null hcritical)
  have hzero : ∀ᵐ x ∂volume,
      x ∈ disc 1 \ ⋃ k, V k → Matrix.det (weakJacobian d x) = 0 := by
    filter_upwards [hzeroQ] with x hx
    intro hxp
    rcases hremain hxp with hbad | hcrit
    · exact hx hbad
    · obtain ⟨n, hn, he⟩ := mem_iUnion.mp hcrit
      exact (hdet n x hn).symm.trans he
  exact area_and_lusin_of_native_pieces_critical_residual u d V hV hVdisj hVinj DV
    hVD hVdet hnullimage hzero


#print axioms area_and_lusin_of_countable_native_derivative_pieces

private theorem native_C1_coincidence_det
    (u : E2 → E2) (d : Fin 2 → E2 → E2)
    (hH1 : ∀ i, H1On (disc 1) (fun x => u x i) (d i))
    (v : E2 → E2) (hv : ContDiff ℝ 1 v) :
    ∀ᵐ x ∂volume.restrict (disc 1), u x = v x →
      (fderiv ℝ v x).det = Matrix.det (weakJacobian d x) := by
  run_tac do
    let n := (Lean.Name.num `_private.NativeWeakJetLocality 0).str
      "original_weak_det_on_C1_equal_set"
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.withContext do
      let args ← ([`u, `d, `hH1, `v, `hv].toArray.mapM
        fun name => Lean.Elab.Term.elabTerm (Lean.mkIdent name) none)
      let body := Lean.mkAppN (.const n []) args
      Lean.Meta.checkWithKernel body
      goal.assign body
    Lean.Elab.Tactic.replaceMainGoal []

private theorem area_and_lusin_of_countable_C1_coincidences
    (u : E2 → E2) (d : Fin 2 → E2 → E2)
    (hH1 : ∀ i, H1On (disc 1) (fun x => u x i) (d i))
    (huc : ContinuousOn u (closedDisc 1))
    (v : ℕ → E2 → E2) (hv : ∀ n, ContDiff ℝ 1 (v n))
    (hcover : volume (disc 1 \ ⋃ n, {x | u x = v n x}) = 0)
    (himage : volume (u '' (disc 1 \ ⋃ n, {x | u x = v n x})) = 0) :
    LusinOnDisc u ∧
    ∀ (w : E2 → ℝ≥0∞), Measurable w →
      ∀ S : Set E2, MeasurableSet S → S ⊆ disc 1 →
        AEMeasurable (multiplicity u S) volume ∧
        (∫⁻ x in S, w (u x) * ENNReal.ofReal |Matrix.det (weakJacobian d x)|) =
          ∫⁻ y, w y * multiplicity u S y := by
  classical
  let Q : ℕ → Set E2 := fun n => disc 1 ∩ {x | u x = v n x}
  let u0 : E2 → E2 := (closedDisc 1).indicator u
  have hu0 : Measurable u0 :=
    huc.measurable_piecewise continuousOn_const Metric.isClosed_closedBall.measurableSet
  have hQ (n : ℕ) : MeasurableSet (Q n) := by
    have he : Q n = disc 1 ∩ {x | u0 x = v n x} := by
      ext x
      constructor
      · intro hx
        refine ⟨hx.1, ?_⟩
        change (closedDisc 1).indicator u x = v n x
        have hxc : x ∈ closedDisc 1 := Metric.ball_subset_closedBall hx.1
        rw [indicator_of_mem hxc]
        exact hx.2
      · intro hx
        refine ⟨hx.1, ?_⟩
        have heq := hx.2
        change (closedDisc 1).indicator u x = v n x at heq
        have hxc : x ∈ closedDisc 1 := Metric.ball_subset_closedBall hx.1
        change u x = v n x
        simpa only [indicator_of_mem hxc] using heq
    rw [he]
    exact Metric.isOpen_ball.measurableSet.inter
      (measurableSet_eq_fun hu0 (hv n).continuous.measurable)
  have hQrem : disc 1 \ ⋃ n, Q n = disc 1 \ ⋃ n, {x | u x = v n x} := by
    simp only [Q, ← inter_iUnion]
    ext x
    simp only [Set.mem_sdiff, mem_inter_iff]
    tauto
  have hQD : ∀ n x, x ∈ Q n →
      HasFDerivWithinAt u (fderiv ℝ (v n) x) (Q n) x := by
    intro n x hx
    apply (((hv n).differentiable (by simp) x).hasFDerivAt.hasFDerivWithinAt).congr'
    · exact fun z hz => hz.2
    · exact hx
  have hL : LusinOnDisc u :=
    lusin_of_differentiable_pieces_and_null_remainder_image u Q
      (fun n x => fderiv ℝ (v n) x) hQD (by rw [hQrem]; exact himage)
  have hlocal : ∀ᵐ x ∂volume, ∀ n, x ∈ Q n →
      (fderiv ℝ (v n) x).det = Matrix.det (weakJacobian d x) := by
    apply ae_all_iff.mpr
    intro n
    have hn := (ae_restrict_iff' Metric.isOpen_ball.measurableSet).mp
      (native_C1_coincidence_det u d hH1 (v n) (hv n))
    filter_upwards [hn] with x hx hxn
    exact hx hxn.1 hxn.2
  obtain ⟨K, hKae, hKm, hK⟩ := hlocal.exists_measurable_mem
  let A : ℕ → Set E2 := fun n => Q n ∩ K
  let R : ℕ → Set E2 := disjointed A
  have hR (n : ℕ) : MeasurableSet (R n) :=
    MeasurableSet.disjointed (fun n => (hQ n).inter hKm) n
  have hRQ (n : ℕ) : R n ⊆ Q n :=
    (disjointed_le A n).trans inter_subset_left
  have hRK (n : ℕ) : R n ⊆ K :=
    (disjointed_le A n).trans inter_subset_right
  have hRcover : volume (disc 1 \ ⋃ n, R n) = 0 := by
    have hKn : volume Kᶜ = 0 := by
      exact mem_ae_iff.mp hKae
    apply measure_mono_null (show disc 1 \ ⋃ n, R n ⊆
      (disc 1 \ ⋃ n, Q n) ∪ Kᶜ from ?_)
      (measure_union_null (by rw [hQrem]; exact hcover) hKn)
    intro x hx
    by_cases hq : x ∈ ⋃ n, Q n
    · refine Or.inr ?_
      intro hk
      apply hx.2
      change x ∈ ⋃ n, disjointed A n
      rw [iUnion_disjointed]
      obtain ⟨n, hn⟩ := mem_iUnion.mp hq
      exact mem_iUnion.mpr ⟨n, hn, hk⟩
    · exact Or.inl ⟨hx.1, hq⟩
  have hzero : ∀ᵐ x ∂volume, x ∈ disc 1 \ ⋃ n, R n →
      Matrix.det (weakJacobian d x) = 0 := by
    have hn : ∀ᵐ x ∂volume, x ∉ disc 1 \ ⋃ n, R n := by
      apply ae_iff.mpr
      simpa only [not_not, Set.setOf_mem_eq] using hRcover
    filter_upwards [hn] with x hx hbad
    exact (hx hbad).elim
  apply area_and_lusin_of_countable_native_derivative_pieces u d R hR
    (disjoint_disjointed A) (fun n x => fderiv ℝ (v n) x)
  · exact fun n x hx => (hQD n x (hRQ n hx)).mono (hRQ n)
  · intro n
    exact (ContinuousLinearMap.continuous_det.comp
      ((hv n).continuous_fderiv (by simp))).measurable
  · exact fun n x hx => hK x (hRK n hx) n (hRQ n hx)
  · exact hL _ sdiff_subset hRcover
  · exact hzero

#print axioms native_C1_coincidence_det
#print axioms area_and_lusin_of_countable_C1_coincidences
