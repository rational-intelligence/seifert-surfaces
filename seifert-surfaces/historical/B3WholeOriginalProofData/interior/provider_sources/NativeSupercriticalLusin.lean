import NativeMorreyVector
import NativeMorreyMeasure
import NativeAllCentersLusin
noncomputable section
open Set Topology Function MeasureTheory Filter Metric
open scoped ContDiff BigOperators NNReal ENNReal
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.L1Independent
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak
open DifferentialGeometry.Analysis.Sobolev.EuclideanMorrey
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Lean Elab Term
elab "nativeMorrey% " n:ident : term => do
  Lean.Meta.mkConstWithFreshMVarLevels ((Lean.Name.num `_private.NativeMorreyVector 0) ++ n.getId)
elab "morreyMeasure%" : term => do
  Lean.Meta.mkConstWithFreshMVarLevels ((Lean.Name.num `_private.NativeMorreyMeasure 0) ++ `morrey_image_measure_bound)
elab "allCenters%" : term => do
  Lean.Meta.mkConstWithFreshMVarLevels ((Lean.Name.num `_private.NativeAllCentersLusin 0) ++ `all_centers_image_null)
private theorem native_local_supercritical_lusin {p : ℝ} (hp : 2 < p)
    {u : E2 → E2} {d : Fin 2 → E2 → E2}
    (hH1 : ∀ i, H1On (disc 1) (fun z => u z i) (d i))
    (hu : ContinuousOn u (closedDisc 1))
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hdp : ∀ i, MemLp (d i) (ENNReal.ofReal p) (volume.restrict (disc t))) :
    ∀ E : Set E2, E ⊆ disc t → volume E = 0 → volume (u '' E) = 0 := by
  classical
  let g := fun z => Real.sqrt (euclideanJetDensity d z)
  have hg := (nativeMorrey% native_density_memLp) hdp
  have hp0 : 0 < p := by linarith
  let μ := volume.restrict (disc t)
  let ν := μ.withDensity (fun z => ENNReal.ofReal ‖g z‖ ^ p)
  letI : IsFiniteMeasure μ := ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  letI : IsFiniteMeasure ν := isFiniteMeasure_withDensity (by
    rw [DeGiorgi.lintegral_rpow_norm_eq_eLpNorm_pow hp0 hg.aestronglyMeasurable]
    exact ENNReal.rpow_ne_top_of_nonneg hp0.le hg.eLpNorm_ne_top)
  let μν := μ+ν
  letI : IsFiniteMeasure μν := inferInstance
  let M := 8*smoothHolderConst 2 p
  have hM : 0 ≤ M := mul_nonneg (by norm_num) (smoothHolderConst_nonneg hp)
  have hD : disc t ⊆ disc 1 := ball_subset_ball ht1.le
  have hb : ∀ a r, 0 < r → closedBall a r ⊆ disc t →
      volume (u '' ball a r) ≤ ENNReal.ofReal (Real.pi*M^2)*μν (ball a r) := by
    intro a r hr hB
    have hBsub := ball_subset_closedBall.trans hB
    have hosc := (nativeMorrey% native_ball_morrey_lp) hp hH1 hu isOpen_ball hD hdp hr hB
    have hh := (morreyMeasure%) hp hg hM hr hBsub hosc
    have hμB : μ (ball a r) = volume (ball a r) := by
      rw [Measure.restrict_apply isOpen_ball.measurableSet,inter_eq_left.mpr hBsub]
    simpa only [μν,Measure.add_apply,hμB,ν,μ,M,g] using hh
  intro E hE hzero
  have hμE : μ E = 0 := le_antisymm ((Measure.restrict_apply_le _ _).trans (le_of_eq hzero)) bot_le
  have hνE : ν E = 0 := withDensity_absolutelyContinuous μ _ hμE
  have hμνE : μν E = 0 := by simp only [μν,Measure.add_apply,hμE,hνE,zero_add]
  exact (allCenters%) isOpen_ball μν ENNReal.ofReal_ne_top hb hE hμνE
private theorem native_supercritical_lusin {p : ℝ} (hp : 2 < p)
    {u : E2 → E2} {d : Fin 2 → E2 → E2}
    (hH1 : ∀ i, H1On (disc 1) (fun z => u z i) (d i))
    (hu : ContinuousOn u (closedDisc 1))
    (hdp : ∀ t : ℝ, 0 < t → t < 1 → ∀ i,
      MemLp (d i) (ENNReal.ofReal p) (volume.restrict (disc t))) :
    LusinOnDisc u := by
  classical
  intro E hED hEzero
  let t : ℕ → ℝ := fun n => 1-1/((n:ℝ)+2)
  have ht (n : ℕ) : 0 < t n := by
    dsimp [t]
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
    have hh : 1/((n:ℝ)+2) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
    linarith
  have ht1 (n : ℕ) : t n < 1 := by
    dsimp [t]
    have hh : 0 < 1/((n:ℝ)+2) := by positivity
    linarith
  have hcover : E ⊆ ⋃ n : ℕ, E ∩ disc (t n) := by
    intro x hx
    have hdist : dist x 0 < 1 := hED hx
    obtain ⟨n,hn⟩ := exists_nat_one_div_lt (by linarith : 0 < 1-dist x 0)
    apply mem_iUnion.mpr
    refine ⟨n,hx,?_⟩
    change dist x 0 < 1-1/((n:ℝ)+2)
    have hden : 1/((n:ℝ)+2) ≤ 1/((n:ℝ)+1) := one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  have hn (n : ℕ) : volume (u '' (E ∩ disc (t n))) = 0 :=
    native_local_supercritical_lusin hp hH1 hu (ht n) (ht1 n) (hdp _ (ht n) (ht1 n))
      _ inter_subset_right (measure_mono_null inter_subset_left hEzero)
  apply measure_mono_null (image_mono hcover)
  rw [image_iUnion]
  exact measure_iUnion_null hn
private theorem native_supercritical_morrey {p : ℝ} (hp : 2 < p)
    {u : E2 → E2} {d : Fin 2 → E2 → E2}
    (hH1 : ∀ i, H1On (disc 1) (fun z => u z i) (d i))
    (hu : ContinuousOn u (closedDisc 1))
    (hdp : ∀ t : ℝ, 0 < t → t < 1 → ∀ i,
      MemLp (d i) (ENNReal.ofReal p) (volume.restrict (disc t)))
    {a : E2} {r : ℝ} (hr : 0 < r) (hB : closedBall a r ⊆ disc 1) :
    ∀ x ∈ ball a r, ∀ y ∈ ball a r,
      ‖u x-u y‖ ≤ 8*smoothHolderConst 2 p*r^(1-2/p)*
        (∫ z in ball a r, (Real.sqrt (euclideanJetDensity d z))^p)^(1/p) := by
  obtain ⟨t,ht,hBt⟩ := exists_pos_lt_subset_ball (show (0:ℝ)<1 by norm_num) isClosed_closedBall hB
  have hd := hdp t ht.1 ht.2
  have hh := (nativeMorrey% native_ball_morrey_lp) hp hH1 hu isOpen_ball (ball_subset_ball ht.2.le) hd hr hBt
  have hg := (nativeMorrey% native_density_memLp) hd
  have hgB := hg.mono_measure (Measure.restrict_mono (ball_subset_closedBall.trans hBt) le_rfl)
  have hp0 : 0 < p := by linarith
  have hnorm : (eLpNorm (fun z => Real.sqrt (euclideanJetDensity d z)) (ENNReal.ofReal p)
      (volume.restrict (ball a r))).toReal =
      (∫ z in ball a r, (Real.sqrt (euclideanJetDensity d z))^p)^(1/p) := by
    rw [hgB.eLpNorm_eq_integral_rpow_norm (ne_of_gt (ENNReal.ofReal_pos.mpr hp0)) ENNReal.ofReal_ne_top]
    simp only [ENNReal.toReal_ofReal hp0.le,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),one_div]
    rw [ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg (fun z => Real.rpow_nonneg (Real.sqrt_nonneg _) _)) _)]
  simpa only [hnorm] using hh
private theorem actual_representative_supercritical_bundle {p : ℝ} (hp : 2 < p)
    {u : E2 → E2} {d : Fin 2 → E2 → E2}
    (hH1 : ∀ i, H1On (disc 1) (fun z => u z i) (d i))
    (hu : ContinuousOn u (closedDisc 1))
    (hdp : ∀ t : ℝ, 0 < t → t < 1 → ∀ i,
      MemLp (d i) (ENNReal.ofReal p) (volume.restrict (disc t))) :
    (∀ a r, 0 < r → closedBall a r ⊆ disc 1 →
      ∀ x ∈ ball a r, ∀ y ∈ ball a r,
        ‖u x-u y‖ ≤ 8*smoothHolderConst 2 p*r^(1-2/p)*
          (∫ z in ball a r, (Real.sqrt (euclideanJetDensity d z))^p)^(1/p)) ∧
    LusinOnDisc u :=
  ⟨fun _ _ hr hB => native_supercritical_morrey hp hH1 hu hdp hr hB,
    native_supercritical_lusin hp hH1 hu hdp⟩
private theorem same_holder_supercritical_lusin {R : ℝ} {Ω : SmoothFlatJordanDomain R}
    {f : E2 → E2} {d : Fin 2 → E2 → E2} {theta : ℝ → ℝ} {sigma : ℝ} {beta : ℝ≥0}
    (P : SameHolderRepresentative Ω f d theta sigma beta)
    (hderived : ∃ p : ℝ, 2 < p ∧ ∀ t : ℝ, 0 < t → t < 1 → ∀ i,
      MemLp (d i) (ENNReal.ofReal p) (volume.restrict (disc t))) : LusinOnDisc P.u := by
  obtain ⟨p,hp,hdp⟩ := hderived
  exact native_supercritical_lusin hp P.same_H1 P.continuous hdp
private theorem same_holder_supercritical_bundle {R : ℝ} {Ω : SmoothFlatJordanDomain R}
    {f : E2 → E2} {d : Fin 2 → E2 → E2} {theta : ℝ → ℝ} {sigma : ℝ} {beta : ℝ≥0}
    (P : SameHolderRepresentative Ω f d theta sigma beta)
    (hderived : ∃ p : ℝ, 2 < p ∧ ∀ t : ℝ, 0 < t → t < 1 → ∀ i,
      MemLp (d i) (ENNReal.ofReal p) (volume.restrict (disc t))) :
    ∃ p C : ℝ, 2 < p ∧ 0 < C ∧
      (∀ a r, 0 < r → closedBall a r ⊆ disc 1 →
        ∀ x ∈ ball a r, ∀ y ∈ ball a r,
          ‖P.u x-P.u y‖ ≤ C*r^(1-2/p)*
            (∫ z in ball a r, (Real.sqrt (euclideanJetDensity d z))^p)^(1/p)) ∧
      LusinOnDisc P.u := by
  obtain ⟨p,hp,hdp⟩ := hderived
  have hc := smoothHolderConst_nonneg hp
  refine ⟨p,8*smoothHolderConst 2 p+1,hp,by positivity,?_,native_supercritical_lusin hp P.same_H1 P.continuous hdp⟩
  intro a r hr hB x hx y hy
  have hh := native_supercritical_morrey hp P.same_H1 P.continuous hdp hr hB x hx y hy
  apply hh.trans
  have hI : 0 ≤ ∫ z in ball a r, (Real.sqrt (euclideanJetDensity d z))^p :=
    integral_nonneg (fun z => Real.rpow_nonneg (Real.sqrt_nonneg _) _)
  have hf : 0 ≤ r^(1-2/p)*(∫ z in ball a r, (Real.sqrt (euclideanJetDensity d z))^p)^(1/p) :=
    mul_nonneg (Real.rpow_nonneg hr.le _) (Real.rpow_nonneg hI _)
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (show 8*smoothHolderConst 2 p ≤ 8*smoothHolderConst 2 p+1 by linarith) hf
#print axioms native_local_supercritical_lusin
#print axioms native_supercritical_lusin
#print axioms native_supercritical_morrey
#print axioms actual_representative_supercritical_bundle
#print axioms same_holder_supercritical_lusin

#print axioms same_holder_supercritical_bundle
