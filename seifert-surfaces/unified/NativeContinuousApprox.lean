import B1L1DirectWeakLower
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.Morrey.Basic
noncomputable section
open Set Topology Function MeasureTheory
open scoped ContDiff BigOperators NNReal ENNReal
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
set_option autoImplicit false
set_option maxHeartbeats 0
open Lean Elab Term
elab "existingApproxPremise% " n:ident : term => do
  let actual := Name.str (Name.str
    (Name.num `_private.DifferentialGeometry.External.DeGiorgi.SobolevSpace.Approximation 0)
    "DeGiorgi") n.getId.toString
  Lean.Meta.mkConstWithFreshMVarLevels actual
open Filter Metric
open scoped Convolution
private theorem global_cont_W12_uniform_smooth_approx {d : ℕ} [NeZero d]
    {p : ℝ} (hp : 1 < p)
    {u : (EuclideanSpace ℝ (Fin d)) → ℝ}
    (hw : DeGiorgi.MemW1pWitness (ENNReal.ofReal p) u Set.univ)
    (hu_compact : HasCompactSupport u) (hu_cont : Continuous u) :
    ∃ φ : ℕ → (EuclideanSpace ℝ (Fin d)) → ℝ,
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (φ n)) ∧
      (∀ n, HasCompactSupport (φ n)) ∧
      TendstoUniformly φ u Filter.atTop ∧
      (∀ n,
        tsupport (φ n) ⊆
          Metric.cthickening ((existingApproxPremise% shrinkingBump) (d := d) n).rOut (tsupport u)) ∧
      Tendsto
        (fun n => eLpNorm (fun x => φ n x - u x) (ENNReal.ofReal p) volume)
        atTop (nhds 0) ∧
      (∀ i : Fin d,
        Tendsto
          (fun n =>
            eLpNorm
              (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
              (ENNReal.ofReal p) volume)
          atTop (nhds 0)) := by
  let _ := (inferInstance : NeZero d)
  have hp_le : 1 ≤ p := le_of_lt hp
  have hp_enn : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using (ENNReal.ofReal_le_ofReal hp_le : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal p)
  have hu_memLp : MemLp u (ENNReal.ofReal p) volume := by
    simpa [Measure.restrict_univ] using hw.memLp
  let φ : ℕ → (EuclideanSpace ℝ (Fin d)) → ℝ := fun n =>
    (((existingApproxPremise% shrinkingBump) (d := d) n).normed volume
      ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u)
  refine ⟨φ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact ((existingApproxPremise% shrinkingBump) (d := d) n).hasCompactSupport_normed.contDiff_convolution_left
      (L := ContinuousLinearMap.lsmul ℝ ℝ)
      (((existingApproxPremise% shrinkingBump) (d := d) n).contDiff_normed)
      (hu_memLp.locallyIntegrable hp_enn)
  · intro n
    apply HasCompactSupport.intro'
      (K := Metric.cthickening ((existingApproxPremise% shrinkingBump) (d := d) n).rOut (tsupport u))
      (hu_compact.isCompact.cthickening (r := ((existingApproxPremise% shrinkingBump) (d := d) n).rOut))
      (hu_compact.isCompact.cthickening (r := ((existingApproxPremise% shrinkingBump) (d := d) n).rOut)).isClosed
    intro x hx
    exact DeGiorgi.zero_outside_of_tsupport_subset
      (Ω := Metric.cthickening ((existingApproxPremise% shrinkingBump) (d := d) n).rOut (tsupport u))
      ((existingApproxPremise% tsupport_normed_convolution_subset_cthickening)
        (d := d) ((existingApproxPremise% shrinkingBump) (d := d) n) hu_compact)
      hx
  · apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuous_iff.mp
      (hu_compact.uniformContinuous_of_continuous hu_cont) (ε / 2) (by positivity)
    have hb := (existingApproxPremise% tendsto_shrinkingBump_rOut) (d := d)
    filter_upwards [Filter.Tendsto.eventually_lt_const hδ hb] with n hn
    intro x
    rw [dist_comm]
    apply lt_of_le_of_lt (((existingApproxPremise% shrinkingBump) (d := d) n).dist_normed_convolution_le
      hu_cont.aestronglyMeasurable (fun y hy => ?_)) (by linarith : ε / 2 < ε)
    exact (hclose (Metric.mem_ball.mp hy |>.trans hn)).le
  · intro n
    exact (existingApproxPremise% tsupport_normed_convolution_subset_cthickening)
      (d := d) ((existingApproxPremise% shrinkingBump) (d := d) n) hu_compact
  · simpa [φ] using
      (existingApproxPremise% tendsto_eLpNorm_normedConvolution_sub) (d := d) hp_le hu_memLp
  · intro i
    have hGi_memLp : MemLp (fun y => hw.weakGrad y i) (ENNReal.ofReal p) volume := by
      simpa [Measure.restrict_univ] using hw.weakGrad_component_memLp i
    have hEq :
        (fun n =>
          eLpNorm
            (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
            (ENNReal.ofReal p) volume) =
          fun n =>
            eLpNorm
              (fun x =>
                (((existingApproxPremise% shrinkingBump) (d := d) n).normed volume
                  ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun y => hw.weakGrad y i)) x -
                  hw.weakGrad x i)
              (ENNReal.ofReal p) volume := by
      funext n
      refine eLpNorm_congr_ae ?_
      filter_upwards with x
      let bump : (EuclideanSpace ℝ (Fin d)) → ℝ := ((existingApproxPremise% shrinkingBump) (d := d) n).normed volume
      let Dbump : (EuclideanSpace ℝ (Fin d)) → (EuclideanSpace ℝ (Fin d)) →L[ℝ] ℝ := fderiv ℝ bump
      let ei : (EuclideanSpace ℝ (Fin d)) := EuclideanSpace.single i 1
      have hbump1 : ContDiff ℝ 1 bump := by
        simpa [bump] using
          (((existingApproxPremise% shrinkingBump) (d := d) n).contDiff_normed : ContDiff ℝ 1
            (((existingApproxPremise% shrinkingBump) (d := d) n).normed volume))
      have hfd :=
        ((existingApproxPremise% shrinkingBump) (d := d) n).hasCompactSupport_normed.hasFDerivAt_convolution_left
          (L := ContinuousLinearMap.lsmul ℝ ℝ)
          hbump1
          (hu_memLp.locallyIntegrable hp_enn) x
      have hDbump_cont : Continuous Dbump := by
        simpa [Dbump, bump] using hbump1.continuous_fderiv one_ne_zero
      have hDbump_compact : HasCompactSupport Dbump := by
        simpa [Dbump, bump] using
          (((existingApproxPremise% shrinkingBump) (d := d) n).hasCompactSupport_normed.fderiv (𝕜 := ℝ))
      have hfd' :
          (fderiv ℝ (φ n) x) ei =
            (((Dbump ⋆[
                ContinuousLinearMap.precompL (EuclideanSpace ℝ (Fin d)) (ContinuousLinearMap.lsmul ℝ ℝ), volume] u) x)
                ei) := by
        simpa [φ, bump, Dbump, ei] using
          congrArg (fun A : (EuclideanSpace ℝ (Fin d)) →L[ℝ] ℝ => A ei) hfd.fderiv
      have hconv_apply :
          (((Dbump ⋆[
              ContinuousLinearMap.precompL (EuclideanSpace ℝ (Fin d)) (ContinuousLinearMap.lsmul ℝ ℝ), volume] u) x) ei) =
            (((fun y => (fderiv ℝ bump y) ei)
              ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x) := by
        calc
          (((Dbump ⋆[
              ContinuousLinearMap.precompL (EuclideanSpace ℝ (Fin d)) (ContinuousLinearMap.lsmul ℝ ℝ), volume] u) x) ei)
              =
            ((u ⋆[
              ContinuousLinearMap.precompR (EuclideanSpace ℝ (Fin d)) (ContinuousLinearMap.lsmul ℝ ℝ).flip, volume] Dbump) x)
                ei := by
                simpa [ContinuousLinearMap.precompL, Dbump] using
                  congrArg (fun F => F x ei)
                    (MeasureTheory.convolution_flip
                      (L := ContinuousLinearMap.precompR (EuclideanSpace ℝ (Fin d)) (ContinuousLinearMap.lsmul ℝ ℝ).flip)
                      (μ := volume) (f := u) (g := Dbump))
          _ = (u ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, volume] (fun y => Dbump y ei)) x := by
                simpa [Dbump, bump] using
                  (MeasureTheory.convolution_precompR_apply
                    (L := (ContinuousLinearMap.lsmul ℝ ℝ).flip)
                    (μ := volume) (f := u) (g := Dbump)
                    (hf := hu_memLp.locallyIntegrable hp_enn)
                    (hcg := hDbump_compact) (hg := hDbump_cont) (x₀ := x) (x := ei))
          _ = (((fun y => Dbump y ei) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x) := by
                simpa [smul_eq_mul, mul_comm] using
                  congrArg (fun F => F x)
                    ((MeasureTheory.convolution_flip
                      (L := (ContinuousLinearMap.lsmul ℝ ℝ).flip)
                      (μ := volume) (f := u) (g := fun y => Dbump y ei)).symm)
      calc
        (fderiv ℝ (φ n) x) ei - hw.weakGrad x i
          = (((Dbump ⋆[
                ContinuousLinearMap.precompL (EuclideanSpace ℝ (Fin d)) (ContinuousLinearMap.lsmul ℝ ℝ), volume] u) x)
                ei) - hw.weakGrad x i := by
                  rw [hfd']
        _ = (((fun y =>
              (fderiv ℝ bump y) ei)
                ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x) - hw.weakGrad x i := by
                  rw [hconv_apply]
        _ = ((bump)
              ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun y => hw.weakGrad y i)) x -
                hw.weakGrad x i := by
                  simpa [ei] using
                    congrArg (fun z => z - hw.weakGrad x i)
                      ((existingApproxPremise% convolution_fderiv_eq_convolution_weakPartial_univ)
                        (d := d) (i := i) (u := u) (g := fun y => hw.weakGrad y i)
                        (φ := bump)
                        (hw.isWeakGrad i)
                        (by
                          simpa [bump] using
                            (((existingApproxPremise% shrinkingBump) (d := d) n).contDiff_normed :
                              ContDiff ℝ (⊤ : ℕ∞) (((existingApproxPremise% shrinkingBump) (d := d) n).normed volume)))
                        (((existingApproxPremise% shrinkingBump) (d := d) n).hasCompactSupport_normed) x)
    exact hEq ▸ (existingApproxPremise% tendsto_eLpNorm_normedConvolution_sub) (d := d) hp_le hGi_memLp

#print axioms global_cont_W12_uniform_smooth_approx
