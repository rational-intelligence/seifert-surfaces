import UnsignedCriticalAssembly
import NativeLipschitzWeakJetLocality
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Measure.Haar.Unique

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

private theorem native_lipschitz_null_image
    (v : E2 → E2) (C : ℝ≥0) (hv : LipschitzWith C v)
    (E : Set E2) (hE : volume E = 0) : volume (v '' E) = 0 := by
  letI : (μH[2] : Measure E2).IsAddHaarMeasure := by
    convert (MeasureTheory.isAddHaarMeasure_hausdorffMeasure (E := E2)) using 1 <;> simp
  have hH : (μH[2] : Measure E2) ≪ volume :=
    Measure.absolutelyContinuous_isAddHaarMeasure _ _
  have hV : (volume : Measure E2) ≪ μH[2] :=
    Measure.absolutelyContinuous_isAddHaarMeasure _ _
  apply hV
  have hle := hv.hausdorffMeasure_image_le (d := 2) (by norm_num) E
  rw [hH hE, mul_zero] at hle
  exact le_antisymm hle zero_le

private theorem native_lipschitz_coincidence_det
    (u : E2 → E2) (d : Fin 2 → E2 → E2)
    (hH1 : ∀ i, H1On (disc 1) (fun x => u x i) (d i))
    (v : E2 → E2) (C : ℝ≥0) (hv : LipschitzWith C v) :
    ∀ᵐ x ∂volume.restrict (disc 1), u x = v x →
      (fderiv ℝ v x).det = Matrix.det (weakJacobian d x) := by
  run_tac do
    let n := (Lean.Name.num `_private.NativeLipschitzWeakJetLocality 0).str
      "original_weak_det_on_lipschitz_equal_set"
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.withContext do
      let args ← ([`u, `d, `hH1, `v, `C, `hv].toArray.mapM
        fun name => Lean.Elab.Term.elabTerm (Lean.mkIdent name) none)
      let body := Lean.mkAppN (.const n []) args
      Lean.Meta.checkWithKernel body
      goal.assign body
    Lean.Elab.Tactic.replaceMainGoal []

private theorem area_and_lusin_of_countable_lipschitz_coincidences
    (u : E2 → E2) (d : Fin 2 → E2 → E2)
    (hH1 : ∀ i, H1On (disc 1) (fun x => u x i) (d i))
    (huc : ContinuousOn u (closedDisc 1))
    (v : ℕ → E2 → E2) (C : ℕ → ℝ≥0) (hv : ∀ n, LipschitzWith (C n) (v n))
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
  have hL : LusinOnDisc u := by
    intro E hE hnull
    have hpiece (n : ℕ) : volume (u '' (E ∩ Q n)) = 0 := by
      have he : u '' (E ∩ Q n) = v n '' (E ∩ Q n) := by
        apply image_congr
        exact fun x hx => hx.2.2
      rw [he]
      exact native_lipschitz_null_image _ _ (hv n) _
        (measure_mono_null inter_subset_left hnull)
    have hrem : volume (u '' (E \ ⋃ n, Q n)) = 0 := by
      apply measure_mono_null (image_mono (sdiff_subset_sdiff hE Subset.rfl))
      rw [hQrem]
      exact himage
    have hsub : E ⊆ (E \ ⋃ n, Q n) ∪ ⋃ n, (E ∩ Q n) := by
      intro x hx
      by_cases hq : x ∈ ⋃ n, Q n
      · obtain ⟨n, hn⟩ := mem_iUnion.mp hq
        exact Or.inr (mem_iUnion.mpr ⟨n, hx, hn⟩)
      · exact Or.inl ⟨hx, hq⟩
    apply measure_mono_null (image_mono hsub)
    rw [image_union, image_iUnion]
    exact measure_union_null hrem (measure_iUnion_null hpiece)
  have hlocal : ∀ᵐ x ∂volume, ∀ n,
      DifferentiableAt ℝ (v n) x ∧ (x ∈ Q n →
        (fderiv ℝ (v n) x).det = Matrix.det (weakJacobian d x)) := by
    apply ae_all_iff.mpr
    intro n
    have hn := (ae_restrict_iff' Metric.isOpen_ball.measurableSet).mp
      (native_lipschitz_coincidence_det u d hH1 (v n) (C n) (hv n))
    filter_upwards [hn, (hv n).ae_differentiableAt (μ := volume)] with x hx hd
    refine ⟨hd, ?_⟩
    exact fun hxn => hx hxn.1 hxn.2
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
    have hKn : volume Kᶜ = 0 := mem_ae_iff.mp hKae
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
  have hD : ∀ n x, x ∈ R n →
      HasFDerivWithinAt u (fderiv ℝ (v n) x) (R n) x := by
    intro n x hx
    have hd := (hK x (hRK n hx) n).1
    apply hd.hasFDerivAt.hasFDerivWithinAt.congr'
    · exact fun z hz => (hRQ n hz).2
    · exact hx
  have hDm : ∀ n, Measurable (fun x => (fderiv ℝ (v n) x).det) :=
    fun n => ContinuousLinearMap.continuous_det.measurable.comp (measurable_fderiv ℝ (v n))
  have hdet : ∀ n x, x ∈ R n →
      (fderiv ℝ (v n) x).det = Matrix.det (weakJacobian d x) :=
    fun n x hx => (hK x (hRK n hx) n).2 (hRQ n hx)
  have hdisj : Pairwise (Disjoint on R) := disjoint_disjointed A
  have hnullimage : volume (u '' (disc 1 \ ⋃ n, R n)) = 0 := hL _ sdiff_subset hRcover
  have hzero : ∀ᵐ x ∂volume, x ∈ disc 1 \ ⋃ n, R n →
      Matrix.det (weakJacobian d x) = 0 := by
    have hn : ∀ᵐ x ∂volume, x ∉ disc 1 \ ⋃ n, R n := by
      apply ae_iff.mpr
      simpa only [not_not, Set.setOf_mem_eq] using hRcover
    filter_upwards [hn] with x hx hbad
    exact (hx hbad).elim
  run_tac do
    let n := (Lean.Name.num `_private.UnsignedCriticalAssembly 0).str
      "area_and_lusin_of_countable_native_derivative_pieces"
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      exact $(Lean.mkIdent n) $(Lean.mkIdent `u) $(Lean.mkIdent `d)
        $(Lean.mkIdent `R) $(Lean.mkIdent `hR) $(Lean.mkIdent `hdisj)
        (fun n x => fderiv ℝ ($(Lean.mkIdent `v) n) x)
        $(Lean.mkIdent `hD) $(Lean.mkIdent `hDm) $(Lean.mkIdent `hdet)
        $(Lean.mkIdent `hnullimage) $(Lean.mkIdent `hzero)))

#print axioms native_lipschitz_null_image
#print axioms native_lipschitz_coincidence_det
#print axioms area_and_lusin_of_countable_lipschitz_coincidences
