import NativeMorreyBall
noncomputable section
open Set Topology Function MeasureTheory Filter Metric
open scoped ContDiff BigOperators NNReal ENNReal
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.L1Independent
open DifferentialGeometry.Analysis.Sobolev.EuclideanMorrey
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Lean Elab Term
elab "scalarMorrey%" : term => do
  Lean.Meta.mkConstWithFreshMVarLevels ((Lean.Name.num `_private.NativeMorreyBall 0) ++ `actual_scalar_ball_morrey)
private def native_to_W12 (U : Set E2) (u : E2 → ℝ) (du : E2 → E2)
    (hu : H1On U u du) : DeGiorgi.MemW1pWitness 2 u U where
  memLp := hu.2.1
  weakGrad := du
  weakGrad_component_memLp := fun j => hu.2.2.eval_piLp j
  isWeakGrad := by
    intro j phi hp hc hs
    have hbasis : EuclideanSpace.single j 1 = coordinateVector 2 j := by
      ext k
      simp [coordinateVector, EuclideanSpace.single]
    rw [hbasis]
    exact hu.1.2.2 phi hp hc hs j
private theorem native_density_memLp {p : ℝ} {Ω : Set E2} {d : Fin 2 → E2 → E2}
    (hdp : ∀ i, MemLp (d i) (ENNReal.ofReal p) (volume.restrict Ω)) :
    MemLp (fun z => Real.sqrt (euclideanJetDensity d z)) (ENNReal.ofReal p) (volume.restrict Ω) := by
  let g := fun z => Real.sqrt (euclideanJetDensity d z)
  have hg_nonneg : ∀ z, 0 ≤ g z := fun z => Real.sqrt_nonneg _
  have hm := ((hdp 0).norm.add (hdp 1).norm)
  apply MemLp.of_le hm (by
    apply AEMeasurable.aestronglyMeasurable
    simpa [g,euclideanJetDensity,Fin.sum_univ_two] using (((hdp 0).norm.aestronglyMeasurable.aemeasurable.pow_const 2).add
      ((hdp 1).norm.aestronglyMeasurable.aemeasurable.pow_const 2)).sqrt)
  filter_upwards with z
  have hs : Real.sqrt (‖d 0 z‖^2+‖d 1 z‖^2) ≤ ‖d 0 z‖+‖d 1 z‖ := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [norm_nonneg (d 0 z),norm_nonneg (d 1 z)]
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs,abs_of_nonneg (hg_nonneg z),Real.norm_eq_abs,abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  simpa [g,euclideanJetDensity,Fin.sum_univ_two] using hs
private theorem native_ball_morrey_lp {p : ℝ} (hp : 2 < p)
    {u : E2 → E2} {d : Fin 2 → E2 → E2}
    (hH1 : ∀ i, H1On (disc 1) (fun z => u z i) (d i))
    (hu : ContinuousOn u (closedDisc 1))
    {Ω : Set E2} (hΩ : IsOpen Ω) (hΩD : Ω ⊆ disc 1)
    (hdp : ∀ i, MemLp (d i) (ENNReal.ofReal p) (volume.restrict Ω))
    {a : E2} {r : ℝ} (hr : 0 < r) (hball : closedBall a r ⊆ Ω) :
    ∀ x ∈ ball a r, ∀ y ∈ ball a r,
      ‖u x-u y‖ ≤ 8 * smoothHolderConst 2 p * r ^ (1-2/p) *
        (eLpNorm (fun z => Real.sqrt (euclideanJetDensity d z))
          (ENNReal.ofReal p) (volume.restrict (ball a r))).toReal := by
  classical
  let g := fun z => Real.sqrt (euclideanJetDensity d z)
  have hg_nonneg : ∀ z, 0 ≤ g z := fun z => Real.sqrt_nonneg _
  have hdg (i : Fin 2) (z : E2) : ‖d i z‖ ≤ g z := by
    apply (Real.le_sqrt (norm_nonneg _) (Finset.sum_nonneg (fun j _ => sq_nonneg ‖d j z‖))).mpr
    exact Finset.single_le_sum (fun j _ => sq_nonneg ‖d j z‖) (Finset.mem_univ i)
  have hgLp := native_density_memLp hdp
  have hBΩ : ball a r ⊆ Ω := ball_subset_closedBall.trans hball
  have hgB := hgLp.mono_measure (Measure.restrict_mono hBΩ le_rfl)
  let G := (eLpNorm g (ENNReal.ofReal p) (volume.restrict (ball a r))).toReal
  have hGp : 0 ≤ G := ENNReal.toReal_nonneg
  have hcp : 0 ≤ smoothHolderConst 2 p := smoothHolderConst_nonneg hp
  have hfactor : 0 ≤ 2*smoothHolderConst 2 p*r^(1-2/p) := by positivity
  have hUΩ : ContinuousOn u Ω := hu.mono (hΩD.trans ball_subset_closedBall)
  have hscalar (i : Fin 2) : ∀ x ∈ ball a r, ∀ y ∈ ball a r,
      ‖u x i-u y i‖ ≤ 4*smoothHolderConst 2 p*r^(1-2/p)*G := by
    let hw2 := (native_to_W12 (disc 1) (fun z => u z i) (d i) (hH1 i)) |> DeGiorgi.MemW1pWitness.restrict hΩ hΩD
    have hval : MemLp (fun z => u z i) (ENNReal.ofReal p) (volume.restrict Ω) := by
      letI : IsFiniteMeasure (volume.restrict Ω) := ⟨by
        rw [Measure.restrict_apply_univ]
        exact lt_of_le_of_lt (measure_mono hΩD) (by exact measure_ball_lt_top)⟩
      have hc : ContinuousOn (fun z => u z i) (closedDisc 1) := (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp_continuousOn hu
      obtain ⟨M,hM⟩ := (isCompact_closedBall (0:E2) 1).exists_bound_of_continuousOn hc
      exact MemLp.of_bound ((hH1 i).2.1.aestronglyMeasurable.mono_measure
        (Measure.restrict_mono hΩD le_rfl)) M (by
        filter_upwards [ae_restrict_mem hΩ.measurableSet] with z hz
        exact hM z (ball_subset_closedBall (hΩD hz)))
    let hw : DeGiorgi.MemW1pWitness (ENNReal.ofReal p) (fun z => u z i) Ω := {
      memLp := hval
      weakGrad := d i
      weakGrad_component_memLp := fun j => (hdp i).eval_piLp j
      isWeakGrad := hw2.isWeakGrad }
    have hjG (j : Fin 2) : (eLpNorm (fun z => d i z j) (ENNReal.ofReal p)
        (volume.restrict (ball a r))).toReal ≤ G := by
      apply ENNReal.toReal_mono hgB.eLpNorm_ne_top
      apply eLpNorm_mono_ae ((hdp i).eval_piLp j |>.mono_measure (Measure.restrict_mono hBΩ le_rfl) |>.aestronglyMeasurable)
      filter_upwards with z
      simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)] using (PiLp.norm_apply_le (d i z) j).trans (hdg i z)
    intro x hx y hy
    have hh := (scalarMorrey%) hp hΩ hw ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp_continuousOn hUΩ) hr hball x hx y hy
    change ‖u x i-u y i‖ ≤ 2*smoothHolderConst 2 p*r^(1-2/p)*
      ∑ j : Fin 2, (eLpNorm (fun z => d i z j) (ENNReal.ofReal p) (volume.restrict (ball a r))).toReal at hh
    have hsum : (∑ j : Fin 2, (eLpNorm (fun z => d i z j) (ENNReal.ofReal p)
        (volume.restrict (ball a r))).toReal) ≤ 2*G := by
      simp only [Fin.sum_univ_two]
      linarith [hjG 0,hjG 1]
    exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_left hsum hfactor])
  intro x hx y hy
  have hnorm : ‖u x-u y‖ ≤ ∑ i : Fin 2, |(u x-u y) i| := (morreyPremise% euclidean_norm_le_sum_abs) _
  have h0 := hscalar 0 x hx y hy
  have h1 := hscalar 1 x hx y hy
  simp only [Fin.sum_univ_two,PiLp.sub_apply] at hnorm
  simp only [Real.norm_eq_abs] at h0 h1
  change ‖u x-u y‖ ≤ 8*smoothHolderConst 2 p*r^(1-2/p)*G
  linarith
#print axioms native_ball_morrey_lp
