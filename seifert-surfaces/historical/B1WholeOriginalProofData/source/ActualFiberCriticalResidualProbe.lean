import B1L1DirectWeakLower
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

private theorem multiplicity_ignore_null_target_image
    (u : E2 → E2)
    (S T : Set E2) (hT : T ⊆ S)
    (hn : volume (u '' (S \ T)) = 0) :
    multiplicity u S =ᵐ[volume] multiplicity u T := by
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


private theorem countable_injective_piece_multiplicity_target_null_AE
    (u : E2 → E2)
    (P : ℕ → Set E2) (hdisj : Pairwise (Disjoint on P))
    (hinj : ∀ n, InjOn u (P n))
    (himages : ∀ n, ∀ S : Set E2, MeasurableSet S → MeasurableSet (u '' (S ∩ P n)))
    (hcover : volume (u '' (disc 1 \ ⋃ n, P n)) = 0)
    (S : Set E2) (hS : MeasurableSet S) (hsub : S ⊆ disc 1) :
    AEMeasurable (multiplicity u S) volume ∧
    multiplicity u S =ᵐ[volume]
      (fun y => ∑' n, (u '' (S ∩ P n)).indicator (fun _ => (1 : ℝ≥0∞)) y) := by
  let T : Set E2 := ⋃ n, S ∩ P n
  have hT : T ⊆ S := iUnion_subset (fun _ => inter_subset_left)
  have hnull : volume (u '' (S \ T)) = 0 := by
    apply measure_mono_null (Set.image_mono ?_) hcover
    intro x hx
    refine ⟨hsub hx.1, ?_⟩
    intro hp
    obtain ⟨n, hn⟩ := mem_iUnion.mp hp
    exact hx.2 (mem_iUnion.mpr ⟨n, hx.1, hn⟩)
  have hae := multiplicity_ignore_null_target_image u S T hT hnull
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


private theorem every_subset_area_of_native_pieces_critical_residual
    (u : E2 → E2) (d : Fin 2 → E2 → E2)
    (P : ℕ → Set E2) (hP : ∀ n, MeasurableSet (P n))
    (hdisj : Pairwise (Disjoint on P)) (hinj : ∀ n, InjOn u (P n))
    (D : ℕ → E2 → E2 →L[ℝ] E2)
    (hD : ∀ n x, x ∈ P n → HasFDerivWithinAt u (D n x) (P n) x)
    (hdet : ∀ n x, x ∈ P n → (D n x).det = Matrix.det (weakJacobian d x))
    (hcover : volume (u '' (disc 1 \ ⋃ n, P n)) = 0)
    (hcritical : ∀ᵐ x ∂volume, x ∈ disc 1 \ ⋃ n, P n → Matrix.det (weakJacobian d x) = 0)
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
  obtain ⟨hcount, hae⟩ := countable_injective_piece_multiplicity_target_null_AE u P hdisj hinj
    himages hcover S hS hsub
  refine ⟨hcount, ?_⟩
  let T : Set E2 := ⋃ n, S ∩ P n
  have hT : T ⊆ S := iUnion_subset (fun _ => inter_subset_left)
  have hTmeas : MeasurableSet T := MeasurableSet.iUnion (fun n => hS.inter (hP n))
  have hzero : (∫⁻ x in S \ T, w (u x) * ENNReal.ofReal |Matrix.det (weakJacobian d x)|) = 0 := by
    have hz : (fun x => w (u x) * ENNReal.ofReal |Matrix.det (weakJacobian d x)|) =ᵐ[volume.restrict (S \ T)]
        (fun _ => (0 : ℝ≥0∞)) := by
      filter_upwards [ae_restrict_mem (hS.diff hTmeas), hcritical.filter_mono (ae_mono Measure.restrict_le_self)] with x hx hc
      have hxK : x ∈ disc 1 \ ⋃ n, P n := by
        refine ⟨hsub hx.1, ?_⟩
        intro hp
        obtain ⟨n, hn⟩ := mem_iUnion.mp hp
        exact hx.2 (mem_iUnion.mpr ⟨n, hx.1, hn⟩)
      simp only [hc hxK, abs_zero, ENNReal.ofReal_zero, mul_zero]
    rw [lintegral_congr_ae hz, lintegral_zero]
  have hrestrict : (∫⁻ x in S, w (u x) * ENNReal.ofReal |Matrix.det (weakJacobian d x)|) =
      ∫⁻ x in T, w (u x) * ENNReal.ofReal |Matrix.det (weakJacobian d x)| := by
    have hsplit := lintegral_inter_add_sdiff (μ := volume) (fun x => w (u x) * ENNReal.ofReal |Matrix.det (weakJacobian d x)|) S hTmeas
    rw [inter_eq_right.mpr hT, hzero, add_zero] at hsplit
    exact hsplit.symm
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
    _ = ∫⁻ x in T, w (u x) * ENNReal.ofReal |Matrix.det (weakJacobian d x)| := hrestrict
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


#print axioms every_subset_area_of_native_pieces_critical_residual
