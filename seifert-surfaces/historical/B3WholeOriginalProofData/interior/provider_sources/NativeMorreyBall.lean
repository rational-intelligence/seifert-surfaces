import NativeContinuousApprox
noncomputable section
open Set Topology Function MeasureTheory Filter Metric
open scoped ContDiff BigOperators NNReal ENNReal
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
open DifferentialGeometry.Analysis.Sobolev.EuclideanMorrey
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Lean Elab Term
elab "morreyPremise% " n:ident : term => do
  let nm := (Lean.Name.num `_private.DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.Morrey.Basic 0) ++ `DifferentialGeometry.Analysis.Sobolev.EuclideanMorrey ++ n.getId
  Lean.Meta.mkConstWithFreshMVarLevels nm
elab "approxPremise% " n:ident : term => do
  Lean.Meta.mkConstWithFreshMVarLevels ((Lean.Name.num `_private.NativeContinuousApprox 0) ++ n.getId)
elab "cutoffPremise%" : term => do
  Lean.Meta.mkConstWithFreshMVarLevels ((Lean.Name.num `_private.DifferentialGeometry.External.DeGiorgi.SobolevSpace.Approximation 0) ++ `DeGiorgi.exists_smooth_cutoff)

private theorem actual_scalar_ball_morrey {p : ℝ} (hp : 2 < p)
    {Ω : Set E2} (hΩ : IsOpen Ω) {u : E2 → ℝ}
    (hw : DeGiorgi.MemW1pWitness (ENNReal.ofReal p) u Ω)
    (hu : ContinuousOn u Ω) {a : E2} {r : ℝ} (hr : 0 < r)
    (hball : closedBall a r ⊆ Ω) :
    ∀ x ∈ ball a r, ∀ y ∈ ball a r,
      ‖u x-u y‖ ≤ 2 * smoothHolderConst 2 p * r ^ (1-2/p) *
        ∑ j : Fin 2, (eLpNorm (fun z => hw.weakGrad z j) (ENNReal.ofReal p)
          (volume.restrict (ball a r))).toReal := by
  classical
  have hp1 : 1 < p := by linarith
  have hpp : 1 ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp1.le
  obtain ⟨η,hη,hηc,hηrange,hηone,hηsupp⟩ :=
    (cutoffPremise%) (d := 2) (isCompact_closedBall a r) hΩ hball
  let hv := (morreyPremise% cutoffWitness) hp1.le hΩ hw hη hηc hηrange
  obtain ⟨ψ,hψ,hψc,hψsupp,hψfun,hψgrad⟩ :=
    (morreyPremise% exists_smooth_cutoff_approx) hp1 hΩ hηc hηsupp hw hη hηc hηrange (Subset.refl _)
  have hv0 : DeGiorgi.MemW01p (ENNReal.ofReal p) (fun z => η z * u z) Ω :=
    ⟨hv.memW1p, hv, ψ,hψ,hψc,hψsupp,hψfun,hψgrad⟩
  let he := DeGiorgi.zeroExtendMemW1pWitnessP hΩ hp1 hv0 hv
  have heq : Ω.indicator (fun z => η z*u z) = (fun z => η z*u z) := by
    funext z
    by_cases hz : z ∈ Ω
    · simp [hz]
    · simp [hz,image_eq_zero_of_notMem_tsupport (fun h => hz (hηsupp h))]
  have hcont : Continuous (fun z => η z*u z) := by
    rw [continuous_iff_continuousAt]
    intro z
    by_cases hz : z ∈ Ω
    · exact hη.continuous.continuousAt.mul (hu.continuousAt (hΩ.mem_nhds hz))
    · have hn : z ∉ tsupport η := fun h => hz (hηsupp h)
      have hh : (fun y => η y*u y) =ᶠ[𝓝 z] (fun _ => 0) := by
        filter_upwards [isClosed_tsupport η |>.isOpen_compl.mem_nhds hn] with y hy
        simp [image_eq_zero_of_notMem_tsupport hy]
      exact continuousAt_const.congr hh.symm
  obtain ⟨φ,hφ,hφc,hφuniform,-,-,hφgrad⟩ :=
    (approxPremise% global_cont_W12_uniform_smooth_approx) hp1 he
      (by rw [heq]; exact hηc.mul_right) (by rw [heq]; exact hcont)
  let B := ball a r
  have hBΩ : B ⊆ Ω := ball_subset_closedBall.trans hball
  have hηB : ∀ z ∈ B, η z = 1 := fun z hz => hηone z (ball_subset_closedBall hz)
  have hgrad (j : Fin 2) (z : E2) (hz : z ∈ B) : he.weakGrad z j = hw.weakGrad z j := by
    change (Ω.indicator (fun z => hv.weakGrad z j)) z = hw.weakGrad z j
    rw [Set.indicator_of_mem (hBΩ hz)]
    exact (morreyPremise% cutoffWitness_weakGrad_eq_on_open) hp1.le hΩ hw hη hηc hηrange isOpen_ball hηB j z hz
  have hgrLp (j : Fin 2) : MemLp (fun z => hw.weakGrad z j) (ENNReal.ofReal p) (volume.restrict B) :=
    (hw.weakGrad_component_memLp j).mono_measure (Measure.restrict_mono hBΩ le_rfl)
  have hgconv (j : Fin 2) : Tendsto
      (fun n => eLpNorm (fun z => fderiv ℝ (φ n) z (EuclideanSpace.single j 1)-hw.weakGrad z j)
        (ENNReal.ofReal p) (volume.restrict B)) atTop (𝓝 0) := by
    have h0 := hφgrad j
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0
    · intro n; exact bot_le
    · intro n
      calc
        _ = eLpNorm (fun z => fderiv ℝ (φ n) z (EuclideanSpace.single j 1)-he.weakGrad z j)
          (ENNReal.ofReal p) (volume.restrict B) := by
            apply eLpNorm_congr_ae
            filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with z hz
            rw [hgrad j z hz]
        _ ≤ _ := eLpNorm_mono_measure _ Measure.restrict_le_self
  have hgLp (j : Fin 2) (n : ℕ) : MemLp
      (fun z => fderiv ℝ (φ n) z (EuclideanSpace.single j 1)) (ENNReal.ofReal p) (volume.restrict B) := by
    have hc : Continuous (fun z => fderiv ℝ (φ n) z (EuclideanSpace.single j 1)) :=
      (hφ n).continuous_fderiv (by simp) |>.clm_apply continuous_const
    letI : IsFiniteMeasure (volume.restrict B) := ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
    obtain ⟨M,hM⟩ := (isCompact_closedBall a r).exists_bound_of_continuousOn hc.continuousOn
    exact MemLp.of_bound hc.aestronglyMeasurable.restrict M (by
      filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with z hz
      exact hM z (ball_subset_closedBall hz))
  have hnorm (j : Fin 2) : Tendsto
      (fun n => (eLpNorm (fun z => fderiv ℝ (φ n) z (EuclideanSpace.single j 1))
        (ENNReal.ofReal p) (volume.restrict B)).toReal) atTop
      (𝓝 ((eLpNorm (fun z => hw.weakGrad z j) (ENNReal.ofReal p) (volume.restrict B)).toReal)) :=
    (morreyPremise% tendsto_eLpNorm_toReal_of_diff_tendsto_zero) hpp (hgrLp j) (hgLp j) (hgconv j)
  have hsum : Tendsto (fun n => ∑ j : Fin 2,
      (eLpNorm (fun z => fderiv ℝ (φ n) z (EuclideanSpace.single j 1))
        (ENNReal.ofReal p) (volume.restrict B)).toReal) atTop
      (𝓝 (∑ j : Fin 2, (eLpNorm (fun z => hw.weakGrad z j) (ENNReal.ofReal p) (volume.restrict B)).toReal)) :=
    tendsto_finsetSum _ (fun j _ => hnorm j)
  intro x hx y hy
  have hval (z : E2) (hz : z ∈ B) : Tendsto (fun n => φ n z) atTop (𝓝 (u z)) := by
    have hv := hφuniform.tendsto_at z
    simpa only [heq, hηB z hz, one_mul] using hv
  have hlim := ((hval x hx).sub (hval y hy)).norm
  have hrhs : Tendsto (fun n => 2 * smoothHolderConst 2 p * r ^ (1-2/p) *
      ∑ j : Fin 2, (eLpNorm (fun z => fderiv ℝ (φ n) z (EuclideanSpace.single j 1))
        (ENNReal.ofReal p) (volume.restrict B)).toReal) atTop
      (𝓝 (2 * smoothHolderConst 2 p * r ^ (1-2/p) *
        ∑ j : Fin 2, (eLpNorm (fun z => hw.weakGrad z j) (ENNReal.ofReal p) (volume.restrict B)).toReal)) :=
    tendsto_const_nhds.mul hsum
  apply le_of_tendsto_of_tendsto hlim hrhs
  filter_upwards with n
  let S := ∑ j : Fin 2, (eLpNorm (fun z => fderiv ℝ (φ n) z (EuclideanSpace.single j 1))
    (ENNReal.ofReal p) (volume.restrict B)).toReal
  have hb (z : E2) (hz : z ∈ B) : ‖φ n z-⨍w in B, φ n w‖ ≤ smoothHolderConst 2 p*r^(1-2/p)*S := by
    have hh := (morreyPremise% smooth_pointwise_holder_bound_components) hp hr (hφ n) hz
    have hfin (j : Fin 2) : eLpNorm (fun z => fderiv ℝ (φ n) z (EuclideanSpace.single j 1))
      (ENNReal.ofReal p) (volume.restrict B) ≠ ⊤ := (hgLp j n).eLpNorm_ne_top
    have hfin0 := hfin (0 : Fin 2)
    have hfin1 := hfin (1 : Fin 2)
    have hadd : (eLpNorm (fun y => (fderiv ℝ (φ n) y) (EuclideanSpace.single 0 1))
          (ENNReal.ofReal p) (volume.restrict B) +
        eLpNorm (fun y => (fderiv ℝ (φ n) y) (EuclideanSpace.single 1 1))
          (ENNReal.ofReal p) (volume.restrict B)).toReal =
        (eLpNorm (fun y => (fderiv ℝ (φ n) y) (EuclideanSpace.single 0 1))
          (ENNReal.ofReal p) (volume.restrict B)).toReal +
        (eLpNorm (fun y => (fderiv ℝ (φ n) y) (EuclideanSpace.single 1 1))
          (ENNReal.ofReal p) (volume.restrict B)).toReal := ENNReal.toReal_add hfin0 hfin1
    simpa [B, S, Fin.sum_univ_two, hadd] using hh
  calc
    ‖φ n x-φ n y‖ ≤ ‖φ n x-⨍w in B,φ n w‖ + ‖φ n y-⨍w in B,φ n w‖ := by
      simpa only [norm_sub_rev] using
        (norm_sub_le_norm_sub_add_norm_sub (φ n x) (⨍w in B, φ n w) (φ n y))
    _ ≤ smoothHolderConst 2 p*r^(1-2/p)*S + smoothHolderConst 2 p*r^(1-2/p)*S := add_le_add (hb x hx) (hb y hy)
    _ = _ := by dsimp [S]; ring

#print axioms actual_scalar_ball_morrey
