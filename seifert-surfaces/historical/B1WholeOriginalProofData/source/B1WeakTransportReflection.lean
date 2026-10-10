import B1TangencyReflection

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped Manifold ContDiff BigOperators NNReal ENNReal

namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.WeakTransport
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
universe v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}

def weakIntegrand (a : E2 → Mat2) (b : E2 → E2) (c u : E2 → ℝ)
    (du : E2 → E2) (ψ : E2 → ℝ) (x : E2) : ℝ :=
  inner ℝ (matrixAction (a x) (du x)) (planarGradient ψ x) -
    (inner ℝ (b x) (du x) + c x * u x) * ψ x

def laplaceDriftIntegrand (b : E2 → E2) (u ψ : E2 → ℝ) (x : E2) : ℝ :=
  inner ℝ (planarGradient u x) (planarGradient ψ x) -
    inner ℝ (b x) (planarGradient u x) * ψ x

def transportSource {D : B1OriginalData g J} {s : Circle}
    {W : CollarWindow D s} {N : PositiveNormalization W}
    (F : BoundaryIsothermalPatch N) : Set E2 :=
  {x ∈ halfDisc F.sourceR | x ∈ F.chart.source ∧ F.chart x ∈ halfDisc F.targetR}

def pullbackTest {D : B1OriginalData g J} {s : Circle}
    {W : CollarWindow D s} {N : PositiveNormalization W}
    (F : BoundaryIsothermalPatch N) (φ : E2 → ℝ) (x : E2) : ℝ :=
  @ite ℝ (x ∈ transportSource F) (Classical.propDecidable _) (φ (F.chart x)) 0

def stripTest (η : ℝ → ℝ) (ε : ℝ) (ψ : E2 → ℝ) (x : E2) : ℝ :=
  η (x 1 / ε) * ψ x

def reflectedTest (φ : E2 → ℝ) (x : E2) : ℝ := φ x - φ (reflectPoint x)

theorem same_chart_first_jets_H1 (D : B1OriginalData g J) (s : Circle)
    (W : CollarWindow D s) (N : PositiveNormalization W)
    (F : BoundaryIsothermalPatch N) :
    (∃ U : Set E2, IsOpen U ∧ closedHalfDisc F.sourceR ⊆ U ∧
      ContDiffOn ℝ ∞ N.v U) ∧
    BoundedOn N.v (closedHalfDisc F.sourceR) ∧
    BoundedOn (planarGradient N.v) (closedHalfDisc F.sourceR) ∧
    (∀ x ∈ closedHalfDisc F.sourceR, DifferentiableAt ℝ F.chart x) ∧
    (∀ z ∈ closedHalfDisc F.targetR, DifferentiableAt ℝ F.chart.symm z) ∧
    (∀ z ∈ closedHalfDisc F.targetR, DifferentiableAt ℝ F.vhat z) ∧
    (∀ z ∈ closedHalfDisc F.targetR,
      planarGradient F.vhat z = matrixAction (jacobian F.chart.symm z).transpose
        (planarGradient N.v (F.chart.symm z))) ∧
    ContinuousOn F.vhat (closedHalfDisc F.targetR) ∧
    ContinuousOn (planarGradient F.vhat) (closedHalfDisc F.targetR) ∧
    BoundedOn F.vhat (closedHalfDisc F.targetR) ∧
    BoundedOn (planarGradient F.vhat) (closedHalfDisc F.targetR) ∧
    H1On (halfDisc F.targetR) F.vhat (planarGradient F.vhat) := by
  classical
  have hsub (a b : ℝ) (hab : a ≤ b) : closedHalfDisc a ⊆ closedHalfDisc b := by
    intro x hx
    exact ⟨Metric.closedBall_subset_closedBall hab hx.1, hx.2⟩
  have hhalf (r : ℝ) : halfDisc r ⊆ closedHalfDisc r := by
    intro x hx
    exact ⟨Metric.ball_subset_closedBall hx.1, hx.2.le⟩
  have hcompact (r : ℝ) : IsCompact (closedHalfDisc r) := by
    change IsCompact (Metric.closedBall (0 : E2) r ∩ {x : E2 | 0 ≤ x 1})
    exact (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const (by fun_prop))
  have hsourceN : closedHalfDisc F.sourceR ⊆ closedHalfDisc (N.R / 2) :=
    hsub _ _ F.sourceR_inside.le
  have hsourceR : closedHalfDisc F.sourceR ⊆ closedHalfDisc N.R :=
    hsub _ _ (by linarith [F.sourceR_inside, N.R_pos])
  have hsourceW : closedHalfDisc F.sourceR ⊆ closedHalfDisc W.R :=
    hsub _ _ (by linarith [F.sourceR_inside, N.R_pos, N.R_inside])
  let U : Set E2 := W.U ∩ (N.N ∩ N.h ⁻¹' ({0}ᶜ : Set ℝ))
  have hU : IsOpen U := W.U_open.inter
    (N.h_smooth_near_base.continuousOn.isOpen_inter_preimage N.N_open isOpen_compl_singleton)
  have hcontains : closedHalfDisc F.sourceR ⊆ U := by
    intro x hx
    refine ⟨W.U_contains (hsourceW hx), N.N_contains (hsourceN hx), ?_⟩
    exact ne_of_gt (lt_of_lt_of_le (by norm_num) (N.h_lower_bound x (hsourceR hx)))
  have hv : ContDiffOn ℝ ∞ N.v U := by
    exact (W.height_smooth.mono (fun _ hx => hx.1)).div
      (N.h_smooth_near_base.mono (fun _ hx => hx.2.1)) (fun _ hx => hx.2.2)
  have hvdiff (x : E2) (hx : x ∈ closedHalfDisc F.sourceR) : DifferentiableAt ℝ N.v x :=
    ((hv x (hcontains hx)).contDiffAt (hU.mem_nhds (hcontains hx))).differentiableAt (by simp)
  have hvc : ContinuousOn N.v (closedHalfDisc F.sourceR) := hv.continuousOn.mono hcontains
  have hgradU : ContinuousOn (planarGradient N.v) U := by
    have hdu := hv.continuousOn_fderiv_of_isOpen hU (by simp)
    unfold planarGradient
    apply continuousOn_finsetSum
    intro i hi
    exact (hdu.clm_apply continuousOn_const).smul continuousOn_const
  have hgrad : ContinuousOn (planarGradient N.v) (closedHalfDisc F.sourceR) :=
    hgradU.mono hcontains
  have hbound {V : Type} [NormedAddCommGroup V] (u : E2 → V) (r : ℝ)
      (hc : ContinuousOn u (closedHalfDisc r)) : BoundedOn u (closedHalfDisc r) := by
    obtain ⟨C, hC⟩ := (hcompact r).exists_bound_of_continuousOn hc
    exact ⟨max C 0, le_max_right _ _, fun x hx => (hC x hx).trans (le_max_left _ _)⟩
  have hdifferentiable (f : E2 → E2) (x : E2) (hdet : Matrix.det (jacobian f x) ≠ 0) :
      DifferentiableAt ℝ f x := by
    by_contra hh
    have hz : fderiv ℝ f x = 0 := fderiv_zero_of_not_differentiableAt hh
    apply hdet
    change Matrix.det (fun i j : Fin 2 => (fderiv ℝ f x (coordinateVector 2 j)) i) = 0
    rw [hz]
    change Matrix.det (0 : Mat2) = 0
    exact Matrix.det_zero
  have hforward (x : E2) (hx : x ∈ closedHalfDisc F.sourceR) :
      DifferentiableAt ℝ F.chart x :=
    hdifferentiable F.chart x (F.forward_det x (F.source_contains hx))
  have hinverse (z : E2) (hz : z ∈ closedHalfDisc F.targetR) :
      DifferentiableAt ℝ F.chart.symm z :=
    hdifferentiable F.chart.symm z (F.inverse_det z (F.target_contains hz))
  have hvhat (z : E2) (hz : z ∈ closedHalfDisc F.targetR) :
      DifferentiableAt ℝ F.vhat z :=
    (hvdiff _ (F.inverse_half_disc z hz)).comp z (hinverse z hz)
  have hgradcoord (u : E2 → ℝ) (x : E2) (i : Fin 2) :
      planarGradient u x i = fderiv ℝ u x (coordinateVector 2 i) := by
    fin_cases i <;> simp [planarGradient, coordinateVector, Fin.sum_univ_two]
  have hgradchain (z : E2) (hz : z ∈ closedHalfDisc F.targetR) :
      planarGradient F.vhat z = matrixAction (jacobian F.chart.symm z).transpose
        (planarGradient N.v (F.chart.symm z)) := by
    ext i
    rw [hgradcoord]
    change fderiv ℝ (N.v ∘ F.chart.symm) z (coordinateVector 2 i) = _
    rw [fderiv_comp z (hvdiff _ (F.inverse_half_disc z hz)) (hinverse z hz)]
    change fderiv ℝ N.v (F.chart.symm z) (fderiv ℝ F.chart.symm z (coordinateVector 2 i)) = _
    have hexp (w : E2) : w = ∑ j : Fin 2, w j • coordinateVector 2 j := by
      ext j
      fin_cases j <;> simp [coordinateVector, Fin.sum_univ_two]
    rw [hexp (fderiv ℝ F.chart.symm z (coordinateVector 2 i)), map_sum]
    simp only [map_smul, smul_eq_mul]
    change (∑ j : Fin 2, (fderiv ℝ F.chart.symm z (coordinateVector 2 i)) j *
      fderiv ℝ N.v (F.chart.symm z) (coordinateVector 2 j)) =
      ∑ j : Fin 2, (fderiv ℝ F.chart.symm z (coordinateVector 2 i)) j *
        planarGradient N.v (F.chart.symm z) j
    simp only [hgradcoord]
  have hinc : ContinuousOn F.chart.symm (closedHalfDisc F.targetR) :=
    F.inverse_C1.continuousOn.mono F.target_contains
  have hvhatc : ContinuousOn F.vhat (closedHalfDisc F.targetR) :=
    hvc.comp hinc F.inverse_half_disc
  have hgradcomp : ContinuousOn (fun z => planarGradient N.v (F.chart.symm z))
      (closedHalfDisc F.targetR) := hgrad.comp hinc F.inverse_half_disc
  have hjac (i j : Fin 2) : ContinuousOn (fun z => jacobian F.chart.symm z i j)
      (closedHalfDisc F.targetR) := by
    obtain ⟨C, hC⟩ := F.inverse_holder i j
    exact hC.continuousOn F.alpha_pos
  have hgradchat : ContinuousOn (planarGradient F.vhat) (closedHalfDisc F.targetR) := by
    have hm : ContinuousOn (fun z => matrixAction (jacobian F.chart.symm z).transpose
        (planarGradient N.v (F.chart.symm z))) (closedHalfDisc F.targetR) := by
      change ContinuousOn (fun z => (EuclideanSpace.equiv (Fin 2) ℝ).symm
        (fun i => ∑ j, (jacobian F.chart.symm z).transpose i j *
          planarGradient N.v (F.chart.symm z) j)) _
      apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp_continuousOn
      apply continuousOn_pi.mpr
      intro i
      apply continuousOn_finsetSum
      intro j hj
      exact (hjac j i).mul ((show Continuous (fun x : E2 => x j) from by fun_prop).comp_continuousOn hgradcomp)
    exact hm.congr (fun z hz => hgradchain z hz)
  refine ⟨⟨U, hU, hcontains, hv⟩, hbound _ _ hvc, hbound _ _ hgrad,
    hforward, hinverse, hvhat, hgradchain, hvhatc, hgradchat,
    hbound _ _ hvhatc, hbound _ _ hgradchat, ?_⟩
  have hopen : IsOpen (halfDisc F.targetR) := by
    change IsOpen (Metric.ball (0 : E2) F.targetR ∩ {x : E2 | 0 < x 1})
    exact Metric.isOpen_ball.inter (isOpen_lt continuous_const (by fun_prop))
  have huc := hvhatc.mono (hhalf F.targetR)
  have hgc := hgradchat.mono (hhalf F.targetR)
  have hweak : WeakGradientOn (halfDisc F.targetR) F.vhat (planarGradient F.vhat) := by
    refine ⟨huc.locallyIntegrableOn hopen.measurableSet,
      hgc.locallyIntegrableOn hopen.measurableSet, ?_⟩
    intro φ hφ hc hs i
    have hpartial : ContinuousOn (fun x => fderiv ℝ F.vhat x (coordinateVector 2 i))
        (halfDisc F.targetR) := by
      exact ((show Continuous (fun x : E2 => x i) from by fun_prop).comp_continuousOn hgc).congr
        (fun x hx => (hgradcoord F.vhat x i).symm)
    have integral_product (f ψ : E2 → ℝ) (hf : ContinuousOn f (halfDisc F.targetR))
        (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
        (hψs : tsupport ψ ⊆ halfDisc F.targetR) : Integrable (fun x => f x * ψ x) := by
      apply (integrableOn_iff_integrable_of_support_subset ?_).mp
        (((hf.mono hψs).mul hψ.continuousOn).integrableOn_compact hψc)
      intro x hx
      exact subset_tsupport ψ ((mul_ne_zero_iff.mp hx).2)
    have hi1 : Integrable (fun x => fderiv ℝ F.vhat x (coordinateVector 2 i) * φ x) :=
      integral_product _ _ hpartial hφ.continuous hc hs
    have hi2 : Integrable (fun x => F.vhat x * fderiv ℝ φ x (coordinateVector 2 i)) :=
      integral_product _ _ huc ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
        (hc.fderiv_apply ℝ _) ((tsupport_fderiv_apply_subset ℝ _).trans hs)
    have hi3 : Integrable (fun x => F.vhat x * φ x) :=
      integral_product _ _ huc hφ.continuous hc hs
    have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hi1 hi2 hi3
      (fun x hx => hvhat x (hhalf _ (hs hx)))
      (fun x _ => hφ.differentiable (by simp) x)
    simp_rw [hgradcoord]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero,
      setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact hibp
    · intro x hx
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), mul_zero]
    · intro x hx
      rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (hs h))]
      simp
  have hfinite : volume (halfDisc F.targetR) < ⊤ :=
    lt_of_le_of_lt (measure_mono (hhalf _)) (hcompact F.targetR).measure_lt_top
  letI : IsFiniteMeasure (volume.restrict (halfDisc F.targetR)) :=
    isFiniteMeasure_restrict.mpr hfinite.ne
  refine ⟨hweak, ?_, ?_⟩
  · obtain ⟨C, hC, hboundC⟩ := hbound _ _ hvhatc
    exact MemLp.of_bound (huc.aestronglyMeasurable hopen.measurableSet) C
      ((ae_restrict_mem hopen.measurableSet).mono (fun x hx => hboundC x (hhalf _ hx)))
  · obtain ⟨C, hC, hboundC⟩ := hbound _ _ hgradchat
    exact MemLp.of_bound (hgc.aestronglyMeasurable hopen.measurableSet) C
      ((ae_restrict_mem hopen.measurableSet).mono (fun x hx => hboundC x (hhalf _ hx)))


theorem compact_C1_test_extension (U : Set E2) (hU : IsOpen U)
    (a : E2 → Mat2) (b : E2 → E2) (c u : E2 → ℝ) (du : E2 → E2)
    (heq : WeakLinearEquationOn U a b c u du)
    (hflux : LocallyIntegrableOn (fun x => matrixAction (a x) (du x)) U)
    (hlower : LocallyIntegrableOn (fun x => inner ℝ (b x) (du x) + c x * u x) U)
    (ψ : E2 → ℝ) (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ) (hψsupport : tsupport ψ ⊆ U) :
    (∃ K' : Set E2, IsCompact K' ∧ K' ⊆ U ∧ tsupport ψ ⊆ interior K' ∧
      ∃ ψn : ℕ → E2 → ℝ,
        (∀ n, ContDiff ℝ ∞ (ψn n) ∧ HasCompactSupport (ψn n) ∧ tsupport (ψn n) ⊆ K') ∧
        TendstoUniformly ψn ψ atTop ∧
        TendstoUniformly (fun n x => fderiv ℝ (ψn n) x) (fderiv ℝ ψ) atTop) ∧
    IntegrableOn (weakIntegrand a b c u du ψ) U ∧
    (∫ x in U, weakIntegrand a b c u du ψ x) = 0 := by
  exact (open Metric in open scoped Convolution Pointwise in by
    have approximation (U : Set E2) (hU : IsOpen U) (ψ : E2 → ℝ) (hψ : ContDiff ℝ 1 ψ)
        (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ U) :
        ∃ K' : Set E2, IsCompact K' ∧ K' ⊆ U ∧ tsupport ψ ⊆ interior K' ∧
          ∃ ψn : ℕ → E2 → ℝ,
            (∀ n, ContDiff ℝ ∞ (ψn n) ∧ HasCompactSupport (ψn n) ∧ tsupport (ψn n) ⊆ K') ∧
            TendstoUniformly ψn ψ atTop ∧
            TendstoUniformly (fun n x => fderiv ℝ (ψn n) x) (fderiv ℝ ψ) atTop := by
      classical
      obtain ⟨r,hr,hrU⟩ := hc.isCompact.exists_cthickening_subset_open hU hs
      let K' := cthickening r (tsupport ψ)
      have hK : IsCompact K' := hc.isCompact.cthickening
      have hinterior : tsupport ψ ⊆ interior K' := (self_subset_thickening hr _).trans (thickening_subset_interior_cthickening r _)
      have huc : UniformContinuous ψ := hψ.continuous.uniformContinuous_of_tendsto_cocompact hc.is_zero_at_infty
      have hdcont : Continuous (fderiv ℝ ψ) := hψ.continuous_fderiv one_ne_zero
      have hduc : UniformContinuous (fderiv ℝ ψ) := hdcont.uniformContinuous_of_tendsto_cocompact (hc.fderiv ℝ).is_zero_at_infty
      have approx (e : ℝ) (he : 0 < e) : ∃ p : E2 → ℝ,
          ContDiff ℝ ∞ p ∧ HasCompactSupport p ∧ tsupport p ⊆ K' ∧
          (∀ x,dist (p x) (ψ x) ≤ e) ∧ (∀ x,dist (fderiv ℝ p x) (fderiv ℝ ψ x) ≤ e) := by
        obtain ⟨d,hd,hdψ⟩ := Metric.uniformContinuous_iff.mp huc e he
        obtain ⟨d',hd',hddψ⟩ := Metric.uniformContinuous_iff.mp hduc e he
        let ρ := min r (min d d') / 2
        have hρ : 0 < ρ := half_pos (lt_min hr (lt_min hd hd'))
        have hρr : ρ < r := by dsimp [ρ];linarith [min_le_left r (min d d')]
        have hρd : ρ < d := by dsimp [ρ];linarith [min_le_right r (min d d'),min_le_left d d']
        have hρd' : ρ < d' := by dsimp [ρ];linarith [min_le_right r (min d d'),min_le_right d d']
        let φ : ContDiffBump (0:E2) := ⟨ρ/2,ρ,half_pos hρ,half_lt_self hρ⟩
        let p := MeasureTheory.convolution (φ.normed volume) ψ (ContinuousLinearMap.lsmul ℝ ℝ) volume
        have hp : ContDiff ℝ ∞ p := φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed hψ.continuous.locallyIntegrable
        have hsp : tsupport p ⊆ K' := by
          apply closure_minimal _ isClosed_cthickening
          intro x hx
          have hadd := support_convolution_subset (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume) hx
          obtain ⟨y,hy,z,hz,rfl⟩ := hadd
          have hy' : ‖y‖ < ρ := by simpa only [φ.support_normed_eq,mem_ball,dist_zero_right] using hy
          apply mem_cthickening_of_dist_le (y+z) z r (tsupport ψ) (subset_tsupport ψ hz)
          simpa only [dist_eq_norm,add_sub_cancel_right] using hy'.le.trans hρr.le
        have hd : ∀ x, fderiv ℝ p x = (MeasureTheory.convolution (φ.normed volume) (fderiv ℝ ψ) (ContinuousLinearMap.lsmul ℝ ℝ) volume) x := by
          intro x
          have hφ : ContDiff ℝ ∞ (φ.normed volume) := φ.contDiff_normed
          have hder := hc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) (hφ.continuous.locallyIntegrable (μ := volume)) hψ x
          rw [hder.fderiv]
          rfl
        refine ⟨p,hp,hK.of_isClosed_subset (isClosed_tsupport _) hsp,hsp,?_,?_⟩
        · intro x
          exact φ.dist_normed_convolution_le hψ.continuous.aestronglyMeasurable (fun y hy => (hdψ (hy.trans hρd)).le)
        · intro x
          rw [hd x]
          exact φ.dist_normed_convolution_le hdcont.aestronglyMeasurable (fun y hy => (hddψ (hy.trans hρd')).le)
      let e : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
      have he (n : ℕ) : 0 < e n := by dsimp [e];positivity
      choose p hp using fun n => approx (e n) (he n)
      refine ⟨K',hK,hrU,hinterior,p,fun n => ⟨(hp n).1,(hp n).2.1,(hp n).2.2.1⟩,?_,?_⟩
      all_goals
        apply Metric.tendstoUniformly_iff.mpr
        intro η hη
        have he0 : Tendsto e atTop (𝓝 0) := by exact tendsto_one_div_add_atTop_nhds_zero_nat
        filter_upwards [he0.eventually (gt_mem_nhds hη)] with n hn
        intro x
      · rw [dist_comm]
        exact ((hp n).2.2.2.1 x).trans_lt hn
      · rw [dist_comm]
        exact ((hp n).2.2.2.2 x).trans_lt hn
    have extension (U : Set E2) (hU : IsOpen U)
        (a : E2 → Mat2) (b : E2 → E2) (c u : E2 → ℝ) (du : E2 → E2)
        (heq : WeakLinearEquationOn U a b c u du)
        (hflux : LocallyIntegrableOn (fun x => matrixAction (a x) (du x)) U)
        (hlower : LocallyIntegrableOn (fun x => inner ℝ (b x) (du x) + c x * u x) U)
        (ψ : E2 → ℝ) (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ)
        (K' : Set E2) (hK : IsCompact K') (hKU : K' ⊆ U) (hψK : tsupport ψ ⊆ K')
        (ψn : ℕ → E2 → ℝ)
        (hn : ∀ n,ContDiff ℝ ∞ (ψn n) ∧ HasCompactSupport (ψn n) ∧ tsupport (ψn n) ⊆ K')
        (hval : TendstoUniformly ψn ψ atTop)
        (hder : TendstoUniformly (fun n x => fderiv ℝ (ψn n) x) (fderiv ℝ ψ) atTop) :
        IntegrableOn (weakIntegrand a b c u du ψ) U ∧
        (∫ x in U, weakIntegrand a b c u du ψ x) = 0 := by
      classical
      let P : (E2 →L[ℝ] ℝ) →L[ℝ] E2 := ∑ i : Fin 2,
        (ContinuousLinearMap.apply ℝ ℝ (coordinateVector 2 i)).smulRight (coordinateVector 2 i)
      have hP (f : E2 → ℝ) (x : E2) : P (fderiv ℝ f x) = planarGradient f x := by
        simp [P,planarGradient]
      have gradient_cont (f : E2 → ℝ) (hf : ContDiff ℝ 1 f) : Continuous (planarGradient f) := by
        have hh := P.continuous.comp (hf.continuous_fderiv one_ne_zero)
        simpa only [Function.comp_def,hP] using hh
      have gradient_zero (f : E2 → ℝ) (hf : tsupport f ⊆ K') (x : E2) (hx : x ∉ K') : planarGradient f x = 0 := by
        rw [← hP,fderiv_of_notMem_tsupport ℝ (fun ht => hx (hf ht)),map_zero]
      have integrand_zero (f : E2 → ℝ) (hf : tsupport f ⊆ K') (x : E2) (hx : x ∉ K') :
          weakIntegrand a b c u du f x = 0 := by
        simp only [weakIntegrand,gradient_zero f hf x hx,inner_zero_right,
          image_eq_zero_of_notMem_tsupport (fun ht => hx (hf ht)),mul_zero,sub_self]
      have hmeas (f : E2 → ℝ) (hf : ContDiff ℝ 1 f) : AEStronglyMeasurable (weakIntegrand a b c u du f) (volume.restrict U) :=
        (hflux.aestronglyMeasurable.inner (gradient_cont f hf).aestronglyMeasurable).sub
          (hlower.aestronglyMeasurable.mul hf.continuous.aestronglyMeasurable)
      obtain ⟨M,hM⟩ := hc.exists_bound_of_continuous hψ.continuous
      obtain ⟨D,hD⟩ := (hc.fderiv ℝ).exists_bound_of_continuous (hψ.continuous_fderiv one_ne_zero)
      let M' := max M 0 + 1
      let D' := max D 0 + 1
      have hM' : 0 ≤ M' := by dsimp [M'];positivity
      have hD' : 0 ≤ D' := by dsimp [D'];positivity
      have hψM (x : E2) : ‖ψ x‖ ≤ M' := (hM x).trans ((le_max_left M 0).trans (le_add_of_nonneg_right zero_le_one))
      have hψD (x : E2) : ‖fderiv ℝ ψ x‖ ≤ D' := (hD x).trans ((le_max_left D 0).trans (le_add_of_nonneg_right zero_le_one))
      have hnbound : ∀ᶠ n in atTop,∀ x,‖ψn n x‖ ≤ M' ∧ ‖fderiv ℝ (ψn n) x‖ ≤ D' := by
        filter_upwards [Metric.tendstoUniformly_iff.mp hval 1 zero_lt_one,
          Metric.tendstoUniformly_iff.mp hder 1 zero_lt_one] with n hv hd
        intro x
        constructor
        · have hh := (norm_sub_norm_le (ψn n x) (ψ x))
          have hvx := hv x
          rw [dist_comm,dist_eq_norm] at hvx
          change ‖ψn n x‖ ≤ max M 0 + 1
          calc
            ‖ψn n x‖ ≤ ‖ψn n x - ψ x‖ + ‖ψ x‖ := by linarith only [hh]
            _ ≤ 1 + M := add_le_add hvx.le (hM x)
            _ ≤ max M 0 + 1 := by linarith only [le_max_left M 0]
        · have hh := (norm_sub_norm_le (fderiv ℝ (ψn n) x) (fderiv ℝ ψ x))
          have hdx := hd x
          rw [dist_comm,dist_eq_norm] at hdx
          dsimp [D'];linarith [hD x,le_max_left D 0]
      let bound : E2 → ℝ := K'.indicator (fun x => ‖matrixAction (a x) (du x)‖ * (‖P‖ * D') +
        ‖inner ℝ (b x) (du x) + c x * u x‖ * M')
      have hbound : Integrable bound (volume.restrict U) := by
        apply Integrable.mono_measure (ν := volume)
        · rw [integrable_indicator_iff hK.measurableSet]
          exact (((hflux.integrableOn_compact_subset hKU hK).norm.mul_const _).add
            ((hlower.integrableOn_compact_subset hKU hK).norm.mul_const _))
        · exact Measure.restrict_le_self
      have bound_le (f : E2 → ℝ) (hf : tsupport f ⊆ K')
          (hv : ∀ x,‖f x‖ ≤ M') (hd : ∀ x,‖fderiv ℝ f x‖ ≤ D') (x : E2) :
          ‖weakIntegrand a b c u du f x‖ ≤ bound x := by
        by_cases hx : x ∈ K'
        · rw [show bound x = ‖matrixAction (a x) (du x)‖ * (‖P‖ * D') + ‖inner ℝ (b x) (du x) + c x * u x‖ * M' from indicator_of_mem hx _]
          have hg : ‖planarGradient f x‖ ≤ ‖P‖ * D' := by
            rw [← hP]
            exact (P.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hd x) (norm_nonneg _))
          calc
            ‖weakIntegrand a b c u du f x‖ ≤ ‖inner ℝ (matrixAction (a x) (du x)) (planarGradient f x)‖ + ‖(inner ℝ (b x) (du x) + c x * u x) * f x‖ := norm_sub_le _ _
            _ ≤ ‖matrixAction (a x) (du x)‖ * ‖planarGradient f x‖ + ‖inner ℝ (b x) (du x) + c x * u x‖ * ‖f x‖ := by
              rw [norm_mul]
              exact add_le_add (norm_inner_le_norm _ _) le_rfl
            _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hg (norm_nonneg _)) (mul_le_mul_of_nonneg_left (hv x) (norm_nonneg _))
        · rw [integrand_zero f hf x hx,show bound x = 0 from indicator_of_notMem hx _]
          simp
      have hi : IntegrableOn (weakIntegrand a b c u du ψ) U :=
        hbound.mono' (hmeas ψ hψ) (Eventually.of_forall (bound_le ψ hψK hψM hψD))
      have hlim : ∀ x : E2,Tendsto (fun n => weakIntegrand a b c u du (ψn n) x) atTop (𝓝 (weakIntegrand a b c u du ψ x)) := by
        intro x
        have hg : Tendsto (fun n => planarGradient (ψn n) x) atTop (𝓝 (planarGradient ψ x)) := by
          simpa only [Function.comp_def,hP] using P.continuous.continuousAt.tendsto.comp (hder.tendsto_at x)
        exact (tendsto_const_nhds.inner hg).sub (tendsto_const_nhds.mul (hval.tendsto_at x))
      have hint := tendsto_integral_filter_of_dominated_convergence bound
        (Eventually.of_forall (fun n => hmeas (ψn n) ((hn n).1.of_le (by norm_num))))
        (hnbound.mono (fun n hn' => Eventually.of_forall (bound_le (ψn n) (hn n).2.2 (fun x => (hn' x).1) (fun x => (hn' x).2))))
        hbound (Eventually.of_forall hlim)
      have hzero (n : ℕ) : (∫ x in U,weakIntegrand a b c u du (ψn n) x) = 0 :=
        (heq.2 (ψn n) (hn n).1 (hn n).2.1 ((hn n).2.2.trans hKU)).2
      refine ⟨hi,?_⟩
      have hh : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 (∫ x in U,weakIntegrand a b c u du ψ x)) := by simpa only [hzero] using hint
      exact tendsto_nhds_unique hh tendsto_const_nhds
    obtain ⟨K',hK,hKU,hψK,p,hp,hv,hd⟩ := approximation U hU ψ hψ hψcompact hψsupport
    refine ⟨⟨K',hK,hKU,hψK,p,hp,hv,hd⟩,?_⟩
    exact extension U hU a b c u du heq hflux hlower ψ hψ hψcompact K' hK hKU
      (hψK.trans interior_subset) p hp hv hd
  )

theorem same_density_test_transport (D : B1OriginalData g J) (s : Circle)
    (W : CollarWindow D s) (N : PositiveNormalization W)
    (F : BoundaryIsothermalPatch N)
    (heq : WeakLinearEquationOn (halfDisc (N.R / 2)) N.normalizedA N.normalizedB
      (fun _ => 0) N.v (planarGradient N.v))
    (helliptic : SmoothEllipticOn N.normalizedA N.normalizedB (fun _ => 0)
      (closedHalfDisc (N.R / 2)))
    (hb : BoundedOn N.normalizedB (closedHalfDisc (N.R / 2)))
    (hdet : ∀ x ∈ closedHalfDisc (N.R / 2), Matrix.det (N.normalizedA x) = 1)
    (htrace : ∀ x ∈ flatArc (N.R / 2), N.v x = 0) :
    MeasurableSet (transportSource F) ∧
    F.chart '' transportSource F = halfDisc F.targetR ∧
    (∀ z ∈ halfDisc F.targetR,
      jacobian F.chart (F.chart.symm z) * jacobian F.chart.symm z = 1 ∧
      jacobian F.chart.symm z * jacobian F.chart (F.chart.symm z) = 1 ∧
      planarGradient N.v (F.chart.symm z) =
        matrixAction (jacobian F.chart (F.chart.symm z)).transpose (planarGradient F.vhat z)) ∧
    (∀ x ∈ transportSource F,
      (fderiv ℝ F.chart x).toLinearMap.det = Matrix.det (jacobian F.chart x)) ∧
    (∀ φ : E2 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ halfDisc F.targetR →
      ContDiff ℝ 1 (pullbackTest F φ) ∧ HasCompactSupport (pullbackTest F φ) ∧
      tsupport (pullbackTest F φ) ⊆ halfDisc F.sourceR ∧
      (∀ x ∈ transportSource F,
        planarGradient (pullbackTest F φ) x =
          matrixAction (jacobian F.chart x).transpose (planarGradient φ (F.chart x))) ∧
      IntegrableOn (weakIntegrand N.normalizedA N.normalizedB (fun _ => 0) N.v
        (planarGradient N.v) (pullbackTest F φ)) (halfDisc (N.R / 2)) ∧
      IntegrableOn (weakIntegrand
        (fun z => densityLeading N.normalizedA F.chart (F.chart.symm z)) F.bhat
        (fun _ => 0) F.vhat (planarGradient F.vhat) φ) (halfDisc F.targetR) ∧
      (∫ x in halfDisc (N.R / 2), weakIntegrand N.normalizedA N.normalizedB
        (fun _ => 0) N.v (planarGradient N.v) (pullbackTest F φ) x) =
      (∫ z in halfDisc F.targetR, weakIntegrand
        (fun z => densityLeading N.normalizedA F.chart (F.chart.symm z)) F.bhat
        (fun _ => 0) F.vhat (planarGradient F.vhat) φ z)) ∧
    (∀ z ∈ closedHalfDisc F.targetR,
      densityLeading N.normalizedA F.chart (F.chart.symm z) = 1) ∧
    ContinuousOn F.bhat (closedHalfDisc F.targetR) ∧
    BoundedOn F.bhat (closedHalfDisc F.targetR) ∧
    MemLp F.bhat ⊤ (volume.restrict (halfDisc F.targetR)) ∧
    (∀ z ∈ flatArc F.targetR, F.vhat z = 0) ∧
    WeakLinearEquationOn (halfDisc F.targetR) (fun _ => 1) F.bhat (fun _ => 0)
      F.vhat (planarGradient F.vhat) := by
  classical
  have hhc (r : ℝ) : halfDisc r ⊆ closedHalfDisc r := by
    intro x hx
    exact ⟨Metric.mem_closedBall.mpr (Metric.mem_ball.mp hx.1).le, hx.2.le⟩
  have hop (r : ℝ) : IsOpen (halfDisc r) :=
    Metric.isOpen_ball.inter (isOpen_lt continuous_const (EuclideanSpace.proj (1 : Fin 2)).continuous)
  have hsrc : halfDisc F.sourceR ⊆ F.chart.source :=
    (hhc F.sourceR).trans F.source_contains
  have htgt : halfDisc F.targetR ⊆ F.chart.target :=
    (hhc F.targetR).trans F.target_contains
  have heqsrc : transportSource F = halfDisc F.sourceR ∩ F.chart ⁻¹' halfDisc F.targetR := by
    ext x
    exact ⟨fun hx => ⟨hx.1, hx.2.2⟩, fun hx => ⟨hx.1, hsrc hx.1, hx.2⟩⟩
  have hopen : IsOpen (transportSource F) := by
    rw [heqsrc]
    exact (F.chart.continuousOn.mono hsrc).isOpen_inter_preimage (hop _) (hop _)
  have himg : F.chart '' transportSource F = halfDisc F.targetR := by
    apply Set.Subset.antisymm
    · rintro z ⟨x, hx, rfl⟩
      exact hx.2.2
    · intro z hz
      refine ⟨F.chart.symm z, ⟨F.inverse_interior z hz, F.chart.map_target (htgt hz), ?_⟩,
        F.chart.right_inv (htgt hz)⟩
      simpa only [F.chart.right_inv (htgt hz)] using hz
  have hjac (f : E2 → E2) (x : E2) :
      LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis (fderiv ℝ f x).toLinearMap = jacobian f x := by
    ext i j
    simp [LinearMap.toMatrix_apply, jacobian, coordinateVector, EuclideanSpace.basisFun_apply]
  have hdetbridge (x : E2) :
      (fderiv ℝ F.chart x).toLinearMap.det = Matrix.det (jacobian F.chart x) := by
    rw [← hjac]
    exact (LinearMap.det_toMatrix _ _).symm
  have hfd (x : E2) (hx : x ∈ halfDisc F.sourceR) : DifferentiableAt ℝ F.chart x :=
    ((F.forward_C1.differentiableOn (by simp)).mono hsrc x hx).differentiableAt ((hop _).mem_nhds hx)
  have hid (z : E2) (hz : z ∈ halfDisc F.targetR) : DifferentiableAt ℝ F.chart.symm z :=
    ((F.inverse_C1.differentiableOn (by simp)).mono htgt z hz).differentiableAt ((hop _).mem_nhds hz)
  have hmat (z : E2) (hz : z ∈ halfDisc F.targetR) :
      jacobian F.chart (F.chart.symm z) * jacobian F.chart.symm z = 1 := by
    have hcomp := (hfd _ (F.inverse_interior z hz)).hasFDerivAt.comp z (hid z hz).hasFDerivAt
    have hevent : (fun x : E2 => x) =ᶠ[𝓝 z] F.chart ∘ F.chart.symm := by
      filter_upwards [(hop _).mem_nhds hz] with y hy
      exact (F.chart.right_inv (htgt hy)).symm
    have hidder := hcomp.congr_of_eventuallyEq hevent
    have heqder := hidder.unique (hasFDerivAt_id z)
    have heqlin := congrArg ContinuousLinearMap.toLinearMap heqder
    have hmatrix := congrArg (LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis) heqlin
    change LinearMap.toMatrix _ _ ((fderiv ℝ F.chart (F.chart.symm z)).toLinearMap.comp
      (fderiv ℝ F.chart.symm z).toLinearMap) = LinearMap.toMatrix _ _ LinearMap.id at hmatrix
    rw [LinearMap.toMatrix_comp _ (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis _, hjac, hjac,
      LinearMap.toMatrix_id] at hmatrix
    exact hmatrix
  have hvdiff (x : E2) (hx : x ∈ halfDisc F.sourceR) : DifferentiableAt ℝ N.v x := by
    have hxN : x ∈ closedHalfDisc (N.R / 2) :=
      ⟨Metric.closedBall_subset_closedBall F.sourceR_inside.le (hhc _ hx).1, hx.2.le⟩
    have hxR : x ∈ closedHalfDisc N.R :=
      ⟨Metric.closedBall_subset_closedBall (by linarith [N.R_pos]) hxN.1, hx.2.le⟩
    have hxW : x ∈ closedHalfDisc W.R :=
      ⟨Metric.closedBall_subset_closedBall N.R_inside.le hxR.1, hx.2.le⟩
    have hnum : ContDiffAt ℝ ∞ (localHeight D s) x :=
      ((W.height_smooth x (W.U_contains hxW)).contDiffAt
        (W.U_open.mem_nhds (W.U_contains hxW)))
    have hden : ContDiffAt ℝ ∞ N.h x :=
      ((N.h_smooth_near_base x (N.N_contains hxN)).contDiffAt
        (N.N_open.mem_nhds (N.N_contains hxN)))
    exact (hnum.div hden (ne_of_gt (lt_of_lt_of_le (by norm_num) (N.h_lower_bound x hxR)))).differentiableAt (by simp)
  have hvhatdiff (z : E2) (hz : z ∈ halfDisc F.targetR) : DifferentiableAt ℝ F.vhat z :=
    (hvdiff _ (F.inverse_interior z hz)).comp z (hid z hz)
  have hgradcoord (u : E2 → ℝ) (x : E2) (i : Fin 2) :
      planarGradient u x i = fderiv ℝ u x (coordinateVector 2 i) := by
    fin_cases i <;> simp [planarGradient, coordinateVector, Fin.sum_univ_two]
  have hchain (u : E2 → ℝ) (f : E2 → E2) (x : E2)
      (hu : DifferentiableAt ℝ u (f x)) (hf : DifferentiableAt ℝ f x) :
      planarGradient (u ∘ f) x = matrixAction (jacobian f x).transpose (planarGradient u (f x)) := by
    ext i
    rw [hgradcoord, fderiv_comp x hu hf]
    have he (w : E2) : w = ∑ j : Fin 2, w j • coordinateVector 2 j := by
      ext j
      fin_cases j <;> simp [coordinateVector, Fin.sum_univ_two]
    change fderiv ℝ u (f x) (fderiv ℝ f x (coordinateVector 2 i)) = _
    rw [he (fderiv ℝ f x (coordinateVector 2 i)), map_sum]
    simp only [map_smul, smul_eq_mul, matrixAction, Matrix.transpose_apply, jacobian, hgradcoord]
    rfl
  have hgradient (z : E2) (hz : z ∈ halfDisc F.targetR) :
      planarGradient N.v (F.chart.symm z) =
        matrixAction (jacobian F.chart (F.chart.symm z)).transpose (planarGradient F.vhat z) := by
    have hx := F.inverse_interior z hz
    have hevent : N.v =ᶠ[𝓝 (F.chart.symm z)] F.vhat ∘ F.chart := by
      filter_upwards [(hop _).mem_nhds hx] with x hx'
      exact congrArg N.v (F.chart.left_inv (hsrc hx')).symm
    have hg : planarGradient N.v (F.chart.symm z) =
        planarGradient (F.vhat ∘ F.chart) (F.chart.symm z) := by
      unfold planarGradient
      rw [hevent.fderiv_eq]
    rw [hg, hchain F.vhat F.chart _ (by simpa only [F.chart.right_inv (htgt hz)] using hvhatdiff z hz)
      (hfd _ hx), F.chart.right_inv (htgt hz)]
  have hsmall : closedHalfDisc F.sourceR ⊆ closedHalfDisc (N.R / 2) := by
    intro x hx
    exact ⟨Metric.closedBall_subset_closedBall F.sourceR_inside.le hx.1, hx.2⟩
  have hdensity (z : E2) (hz : z ∈ closedHalfDisc F.targetR) :
      densityLeading N.normalizedA F.chart (F.chart.symm z) = 1 := by
    let x := F.chart.symm z
    let A := N.normalizedA x
    let M := jacobian F.chart x
    have hx : x ∈ closedHalfDisc F.sourceR := F.inverse_half_disc z hz
    have ha : A.det = 1 := hdet x (hsmall hx)
    have hau : IsUnit A.det := by rw [ha]; exact isUnit_one
    have hm : M.det ≠ 0 := F.forward_det x (F.source_contains hx)
    have hmu : IsUnit M.det := isUnit_iff_ne_zero.mpr hm
    obtain ⟨lam, hlam, hi⟩ := F.conformalInverseMetric x hx
    change A⁻¹ = lam • (M.transpose * M) at hi
    have he : lam • (M * A * M.transpose) = 1 := by
      calc
        _ = M * (A * A⁻¹) * M⁻¹ := by
          rw [hi]
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc,
            Matrix.mul_nonsing_inv M hmu, Matrix.mul_one]
        _ = 1 := by rw [Matrix.mul_nonsing_inv A hau, Matrix.mul_one, Matrix.mul_nonsing_inv M hmu]
    have hdetinv : A⁻¹.det = 1 := by
      simpa only [ha, mul_one] using Matrix.det_nonsing_inv_mul_det A hau
    have hh := congrArg Matrix.det hi
    rw [hdetinv, Matrix.det_smul, Matrix.det_mul, Matrix.det_transpose] at hh
    have hprod : lam * |M.det| = 1 := by
      have hn : 0 ≤ lam * |M.det| := mul_nonneg hlam.le (abs_nonneg _)
      have hsq : (lam * |M.det|) ^ 2 = 1 := by
        simpa only [Fintype.card_fin, mul_pow, sq_abs, ← pow_two] using hh.symm
      nlinarith
    have hlam_eq : lam = |M.det|⁻¹ := by
      simpa only [one_div] using (eq_div_iff (abs_ne_zero.mpr hm)).mpr hprod
    change |M.det|⁻¹ • (M * A * M.transpose) = 1
    rw [← hlam_eq]
    exact he
  have hcompact (r : ℝ) : IsCompact (closedHalfDisc r) :=
    (isCompact_closedBall _ _).inter_right
      (isClosed_le continuous_const (EuclideanSpace.proj (1 : Fin 2)).continuous)
  have hbcont : ContinuousOn F.bhat (closedHalfDisc F.targetR) := by
    have hj (i j : Fin 2) : ContinuousOn (fun x => jacobian F.chart x i j)
        (closedHalfDisc F.sourceR) := by
      obtain ⟨C, hC⟩ := F.forward_holder i j
      exact hC.continuousOn F.alpha_pos
    have hjdet : ContinuousOn (fun x => Matrix.det (jacobian F.chart x))
        (closedHalfDisc F.sourceR) := by
      simp only [Matrix.det_fin_two]
      exact ((hj 0 0).mul (hj 1 1)).sub ((hj 0 1).mul (hj 1 0))
    have hfactor : ContinuousOn (fun x => |Matrix.det (jacobian F.chart x)|⁻¹)
        (closedHalfDisc F.sourceR) :=
      hjdet.abs.inv₀ (fun x hx => abs_ne_zero.mpr (F.forward_det x (F.source_contains hx)))
    have hbc := helliptic.2.1.continuousOn.mono hsmall
    have haction : ContinuousOn (fun x => matrixAction (jacobian F.chart x) (N.normalizedB x))
        (closedHalfDisc F.sourceR) := by
      unfold matrixAction
      apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp_continuousOn
      apply continuousOn_pi.mpr
      intro i
      apply continuousOn_finsetSum
      intro j hj'
      exact (hj i j).mul ((EuclideanSpace.proj j).continuous.comp_continuousOn hbc)
    exact (hfactor.smul haction).comp
      (F.chart.symm.continuousOn.mono F.target_contains) F.inverse_half_disc
  have hbbound : BoundedOn F.bhat (closedHalfDisc F.targetR) := by
    obtain ⟨C, hC⟩ := (hcompact _).exists_bound_of_continuousOn hbcont
    exact ⟨max C 0, le_max_right _ _, fun x hx => (hC x hx).trans (le_max_left _ _)⟩
  have hbLp : MemLp F.bhat ⊤ (volume.restrict (halfDisc F.targetR)) := by
    letI : IsFiniteMeasure (volume.restrict (halfDisc F.targetR)) :=
      isFiniteMeasure_restrict.mpr ((measure_mono (hhc _)).trans_lt (hcompact _).measure_lt_top).ne
    obtain ⟨C, hC, hbC⟩ := hbbound
    exact MemLp.of_bound ((hbcont.mono (hhc _)).aestronglyMeasurable (hop _).measurableSet) C
      ((ae_restrict_mem (hop _).measurableSet).mono (fun x hx => hbC x (hhc _ hx)))
  have hNv : ContDiffOn ℝ ∞ N.v (halfDisc (N.R / 2)) := by
    have hNR : closedHalfDisc (N.R / 2) ⊆ closedHalfDisc N.R := by
      intro x hx
      exact ⟨Metric.closedBall_subset_closedBall (by linarith [N.R_pos]) hx.1, hx.2⟩
    have hNW : closedHalfDisc (N.R / 2) ⊆ closedHalfDisc W.R := by
      intro x hx
      exact ⟨Metric.closedBall_subset_closedBall N.R_inside.le (hNR hx).1, hx.2⟩
    exact (W.height_smooth.mono ((hhc _).trans (hNW.trans W.U_contains))).div
      (N.h_smooth_near_base.mono ((hhc _).trans N.N_contains))
      (fun x hx => ne_of_gt (lt_of_lt_of_le (by norm_num) (N.h_lower_bound x (hNR (hhc _ hx)))))
  have hgradcontinuous (u : E2 → ℝ) (U : Set E2) (ho : IsOpen U) (hu : ContDiffOn ℝ 1 u U) :
      ContinuousOn (planarGradient u) U := by
    have hd := hu.continuousOn_fderiv_of_isOpen ho (by simp)
    unfold planarGradient
    apply continuousOn_finsetSum
    intro i hi
    exact (hd.clm_apply continuousOn_const).smul continuousOn_const
  have hNg := hgradcontinuous N.v _ (hop _) (hNv.of_le (by simp))
  have hflux : ContinuousOn (fun x => matrixAction (N.normalizedA x) (planarGradient N.v x))
      (halfDisc (N.R / 2)) := by
    unfold matrixAction
    apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp_continuousOn
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_finsetSum
    intro j hj
    exact ((helliptic.1 i j).continuousOn.mono (hhc _)).mul
      ((EuclideanSpace.proj j).continuous.comp_continuousOn hNg)
  have hlower : ContinuousOn (fun x => inner ℝ (N.normalizedB x) (planarGradient N.v x))
      (halfDisc (N.R / 2)) :=
    (helliptic.2.1.continuousOn.mono (hhc _)).inner hNg
  have hvg : ContinuousOn (planarGradient F.vhat) (halfDisc F.targetR) := by
    apply hgradcontinuous _ _ (hop _)
    exact (hNv.of_le (by simp)).comp (F.inverse_C1.mono htgt) (fun z hz =>
      ⟨Metric.ball_subset_ball F.sourceR_inside.le (F.inverse_interior z hz).1,
        (F.inverse_interior z hz).2⟩)
  have hint (U : Set E2) (q : E2 → E2) (r ψ : E2 → ℝ)
      (hq : ContinuousOn q U) (hr : ContinuousOn r U) (hψ : ContDiff ℝ 1 ψ)
      (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ U) :
      Integrable (fun x => inner ℝ (q x) (planarGradient ψ x) - r x * ψ x) := by
    have hgc : Continuous (planarGradient ψ) := by
      rw [← continuousOn_univ]
      exact hgradcontinuous ψ Set.univ isOpen_univ hψ.contDiffOn
    apply (integrableOn_iff_integrable_of_support_subset ?_).mp
      ((((hq.mono hs).inner hgc.continuousOn).sub
        ((hr.mono hs).mul hψ.continuous.continuousOn)).integrableOn_compact hc)
    intro x hx
    by_contra hn
    have hz := image_eq_zero_of_notMem_tsupport hn
    have hdz := fderiv_of_notMem_tsupport ℝ hn
    apply hx
    simp [planarGradient, hz, hdz]
  have htests : (∀ φ : E2 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ halfDisc F.targetR →
      ContDiff ℝ 1 (pullbackTest F φ) ∧ HasCompactSupport (pullbackTest F φ) ∧
      tsupport (pullbackTest F φ) ⊆ halfDisc F.sourceR ∧
      (∀ x ∈ transportSource F,
        planarGradient (pullbackTest F φ) x =
          matrixAction (jacobian F.chart x).transpose (planarGradient φ (F.chart x))) ∧
      IntegrableOn (weakIntegrand N.normalizedA N.normalizedB (fun _ => 0) N.v
        (planarGradient N.v) (pullbackTest F φ)) (halfDisc (N.R / 2)) ∧
      IntegrableOn (weakIntegrand
        (fun z => densityLeading N.normalizedA F.chart (F.chart.symm z)) F.bhat
        (fun _ => 0) F.vhat (planarGradient F.vhat) φ) (halfDisc F.targetR) ∧
      (∫ x in halfDisc (N.R / 2), weakIntegrand N.normalizedA N.normalizedB
        (fun _ => 0) N.v (planarGradient N.v) (pullbackTest F φ) x) =
      (∫ z in halfDisc F.targetR, weakIntegrand
        (fun z => densityLeading N.normalizedA F.chart (F.chart.symm z)) F.bhat
        (fun _ => 0) F.vhat (planarGradient F.vhat) φ z)) := by
    intro φ hφ hc hs
    let C : Set E2 := F.chart.symm '' tsupport φ
    have hC : IsCompact C := hc.image_of_continuousOn
      (F.chart.symm.continuousOn.mono (hs.trans htgt))
    have hCsrc : C ⊆ transportSource F := by
      rintro x ⟨z, hz, rfl⟩
      exact ⟨F.inverse_interior z (hs hz), F.chart.map_target (htgt (hs hz)),
        by simpa only [F.chart.right_inv (htgt (hs hz))] using hs hz⟩
    have hsupp : Function.support (pullbackTest F φ) ⊆ C := by
      intro x hx
      change pullbackTest F φ x ≠ 0 at hx
      by_cases hxS : x ∈ transportSource F
      · have hn : φ (F.chart x) ≠ 0 := by simpa only [pullbackTest, if_pos hxS] using hx
        exact ⟨F.chart x, subset_tsupport φ hn, F.chart.left_inv hxS.2.1⟩
      · exact False.elim (hx (by simp only [pullbackTest, if_neg hxS]))
    have htsupp : tsupport (pullbackTest F φ) ⊆ C := closure_minimal hsupp hC.isClosed
    have htsrc : tsupport (pullbackTest F φ) ⊆ transportSource F := htsupp.trans hCsrc
    have hlocal (x : E2) (hx : x ∈ transportSource F) :
        pullbackTest F φ =ᶠ[𝓝 x] φ ∘ F.chart := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      simp only [pullbackTest, if_pos hy, Function.comp_apply]
    have hC1 : ContDiff ℝ 1 (pullbackTest F φ) := by
      apply contDiff_iff_contDiffAt.mpr
      intro x
      by_cases hx : x ∈ transportSource F
      · apply (((hφ.of_le (by norm_num : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω))).contDiffAt).comp x
          ((F.forward_C1 x hx.2.1).contDiffAt
            (Filter.mem_of_superset ((hop _).mem_nhds hx.1) hsrc))).congr_of_eventuallyEq
        exact hlocal x hx
      · exact contDiffAt_const.congr_of_eventuallyEq
          (notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (htsrc h)))
    have hgrad (x : E2) (hx : x ∈ transportSource F) :
        planarGradient (pullbackTest F φ) x =
          matrixAction (jacobian F.chart x).transpose (planarGradient φ (F.chart x)) := by
      have he : planarGradient (pullbackTest F φ) x = planarGradient (φ ∘ F.chart) x := by
        unfold planarGradient
        rw [(hlocal x hx).fderiv_eq]
      rw [he]
      exact hchain φ F.chart x (hφ.differentiable (by simp) _) (hfd x hx.1)
    have hψsrc : tsupport (pullbackTest F φ) ⊆ halfDisc (N.R / 2) := by
      intro x hx
      have h := (htsrc hx).1
      exact ⟨Metric.ball_subset_ball F.sourceR_inside.le h.1, h.2⟩
    have hiSource : IntegrableOn (weakIntegrand N.normalizedA N.normalizedB (fun _ => 0) N.v
        (planarGradient N.v) (pullbackTest F φ)) (halfDisc (N.R / 2)) := by
      unfold weakIntegrand
      simp only [zero_mul, add_zero]
      exact (hint _ _ _ _ hflux hlower hC1 (hC.of_isClosed_subset isClosed_closure htsupp) hψsrc).integrableOn
    have hone (p : E2) : matrixAction (1 : Mat2) p = p := by
      ext i
      simp [matrixAction, Matrix.one_apply]
    have hiTarget : IntegrableOn (weakIntegrand
        (fun z => densityLeading N.normalizedA F.chart (F.chart.symm z)) F.bhat
        (fun _ => 0) F.vhat (planarGradient F.vhat) φ) (halfDisc F.targetR) := by
      apply ((hint _ _ _ φ hvg ((hbcont.mono (hhc _)).inner hvg)
        (hφ.of_le (by simp)) hc hs).integrableOn).congr
      filter_upwards [ae_restrict_mem (hop F.targetR).measurableSet] with z hz
      simp only [weakIntegrand, hdensity z (hhc _ hz), hone, zero_mul, add_zero]
    have hpoint (x : E2) (hx : x ∈ transportSource F) :
        weakIntegrand N.normalizedA N.normalizedB (fun _ => 0) N.v
          (planarGradient N.v) (pullbackTest F φ) x =
        |(fderiv ℝ F.chart x).toLinearMap.det| • weakIntegrand
          (fun z => densityLeading N.normalizedA F.chart (F.chart.symm z)) F.bhat
          (fun _ => 0) F.vhat (planarGradient F.vhat) φ (F.chart x) := by
      have hg := hgradient (F.chart x) hx.2.2
      rw [F.chart.left_inv hx.2.1] at hg
      have hnonzero : |Matrix.det (jacobian F.chart x)| ≠ 0 :=
        abs_ne_zero.mpr (F.forward_det x hx.2.1)
      simp only [weakIntegrand, zero_mul, add_zero, hgrad x hx, hg, pullbackTest,
        if_pos hx, hdetbridge, BoundaryIsothermalPatch.bhat, densityDrift, densityLeading,
        F.chart.left_inv hx.2.1, smul_eq_mul]
      simp [PiLp.inner_apply, matrixAction, Matrix.mul_apply, Matrix.transpose_apply,
        Fin.sum_univ_two]
      field_simp
      <;> ring
    have hzero (x : E2) (hx : x ∉ transportSource F) :
        weakIntegrand N.normalizedA N.normalizedB (fun _ => 0) N.v
          (planarGradient N.v) (pullbackTest F φ) x = 0 := by
      have hnot : x ∉ tsupport (pullbackTest F φ) := fun h => hx (htsrc h)
      simp [weakIntegrand, planarGradient, fderiv_of_notMem_tsupport ℝ hnot,
        image_eq_zero_of_notMem_tsupport hnot]
    have hsubstitution := integral_image_eq_integral_abs_det_fderiv_smul volume hopen.measurableSet
      (fun x hx => (hfd x hx.1).hasFDerivAt.hasFDerivWithinAt)
      (F.chart.injOn.mono (fun x hx => hx.2.1))
      (weakIntegrand (fun z => densityLeading N.normalizedA F.chart (F.chart.symm z)) F.bhat
        (fun _ => 0) F.vhat (planarGradient F.vhat) φ)
    rw [himg] at hsubstitution
    have htransport :
        (∫ x in halfDisc (N.R / 2), weakIntegrand N.normalizedA N.normalizedB
          (fun _ => 0) N.v (planarGradient N.v) (pullbackTest F φ) x) =
        (∫ z in halfDisc F.targetR, weakIntegrand
          (fun z => densityLeading N.normalizedA F.chart (F.chart.symm z)) F.bhat
          (fun _ => 0) F.vhat (planarGradient F.vhat) φ z) := by
      rw [hsubstitution, ← setIntegral_congr_fun hopen.measurableSet hpoint]
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
        setIntegral_eq_integral_of_forall_compl_eq_zero]
      intro x hx
      apply hzero x
      intro hxS
      exact hx ⟨Metric.ball_subset_ball F.sourceR_inside.le hxS.1.1, hxS.1.2⟩
    exact ⟨hC1, hC.of_isClosed_subset isClosed_closure htsupp,
      htsrc.trans (fun x hx => hx.1), hgrad, hiSource, hiTarget, htransport⟩
  refine ⟨hopen.measurableSet, himg, ?_, fun x _ => hdetbridge x, htests,
    hdensity, hbcont, hbbound, hbLp, ?_, ?_⟩
  · intro z hz
    exact ⟨hmat z hz, (mul_eq_one_comm.mp (hmat z hz)), hgradient z hz⟩
  · intro z hz
    change N.v (F.chart.symm z) = 0
    apply htrace
    have hflat := F.inverse_flat z hz
    exact ⟨Metric.ball_subset_ball F.sourceR_inside.le hflat.1, hflat.2⟩
  · have hvcont : ContinuousOn F.vhat (halfDisc F.targetR) :=
      (show DifferentiableOn ℝ F.vhat (halfDisc F.targetR) from
        fun z hz => (hvhatdiff z hz).differentiableWithinAt).continuousOn
    have hweak : WeakGradientOn (halfDisc F.targetR) F.vhat (planarGradient F.vhat) := by
      refine ⟨hvcont.locallyIntegrableOn (hop _).measurableSet,
        hvg.locallyIntegrableOn (hop _).measurableSet, ?_⟩
      intro φ hφ hc hs i
      have hp (f ψ : E2 → ℝ) (hf : ContinuousOn f (halfDisc F.targetR))
          (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ ⊆ halfDisc F.targetR) :
          Integrable (fun x => f x * ψ x) := by
        apply (integrableOn_iff_integrable_of_support_subset ?_).mp
          (((hf.mono hsψ).mul hψ.continuousOn).integrableOn_compact hcψ)
        intro x hx
        exact subset_tsupport ψ ((mul_ne_zero_iff.mp hx).2)
      have hpartial : ContinuousOn (fun z => fderiv ℝ F.vhat z (coordinateVector 2 i))
          (halfDisc F.targetR) :=
        ((EuclideanSpace.proj i).continuous.comp_continuousOn hvg).congr
          (fun z hz => (hgradcoord F.vhat z i).symm)
      have hi := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        (hp _ _ hpartial hφ.continuous hc hs)
        (hp _ _ hvcont ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
          (hc.fderiv_apply ℝ _) ((tsupport_fderiv_apply_subset ℝ _).trans hs))
        (hp _ _ hvcont hφ.continuous hc hs)
        (fun z hz => hvhatdiff z (hs hz)) (fun z hz => hφ.differentiable (by simp) z)
      simp_rw [hgradcoord]
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero,
        setIntegral_eq_integral_of_forall_compl_eq_zero]
      · exact hi
      · intro z hz
        rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hs h)), mul_zero]
      · intro z hz
        rw [fderiv_of_notMem_tsupport ℝ (fun h => hz (hs h))]
        simp
    refine ⟨hweak, ?_⟩
    intro φ hφ hc hs
    obtain ⟨hψC1, hψcompact, hψsupport, hψgrad, hiSource, hiTarget, htransport⟩ := htests φ hφ hc hs
    have hone (p : E2) : matrixAction (1 : Mat2) p = p := by
      ext i
      simp [matrixAction, Matrix.one_apply]
    have htargeteq : Set.EqOn
        (weakIntegrand (fun z => densityLeading N.normalizedA F.chart (F.chart.symm z)) F.bhat
          (fun _ => 0) F.vhat (planarGradient F.vhat) φ)
        (weakIntegrand (fun _ => 1) F.bhat (fun _ => 0) F.vhat (planarGradient F.vhat) φ)
        (halfDisc F.targetR) := by
      intro z hz
      simp only [weakIntegrand, hdensity z (hhc _ hz)]
    change IntegrableOn (weakIntegrand (fun _ => 1) F.bhat (fun _ => 0) F.vhat
      (planarGradient F.vhat) φ) (halfDisc F.targetR) ∧ _
    refine ⟨hiTarget.congr ((ae_restrict_mem (hop _).measurableSet).mono (fun z hz => htargeteq hz)), ?_⟩
    change (∫ z in halfDisc F.targetR, weakIntegrand (fun _ => 1) F.bhat (fun _ => 0) F.vhat
      (planarGradient F.vhat) φ z) = 0
    rw [← setIntegral_congr_fun (hop _).measurableSet htargeteq, ← htransport]
    have hC1extension (U : Set E2) (hU : IsOpen U)
        (a : E2 → Mat2) (b : E2 → E2) (c u : E2 → ℝ) (du : E2 → E2)
        (heq : WeakLinearEquationOn U a b c u du)
        (hflux : LocallyIntegrableOn (fun x => matrixAction (a x) (du x)) U)
        (hlower : LocallyIntegrableOn (fun x => inner ℝ (b x) (du x) + c x * u x) U)
        (ψ : E2 → ℝ) (hψ : ContDiff ℝ 1 ψ)
        (hψcompact : HasCompactSupport ψ) (hψsupport : tsupport ψ ⊆ U) :
        (∃ K' : Set E2, IsCompact K' ∧ K' ⊆ U ∧ tsupport ψ ⊆ interior K' ∧
          ∃ ψn : ℕ → E2 → ℝ,
            (∀ n, ContDiff ℝ ∞ (ψn n) ∧ HasCompactSupport (ψn n) ∧ tsupport (ψn n) ⊆ K') ∧
            TendstoUniformly ψn ψ atTop ∧
            TendstoUniformly (fun n x => fderiv ℝ (ψn n) x) (fderiv ℝ ψ) atTop) ∧
        IntegrableOn (weakIntegrand a b c u du ψ) U ∧
        (∫ x in U, weakIntegrand a b c u du ψ x) = 0 := by
      exact (open Metric in open scoped Convolution Pointwise in by
        have approximation (U : Set E2) (hU : IsOpen U) (ψ : E2 → ℝ) (hψ : ContDiff ℝ 1 ψ)
            (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ U) :
            ∃ K' : Set E2, IsCompact K' ∧ K' ⊆ U ∧ tsupport ψ ⊆ interior K' ∧
              ∃ ψn : ℕ → E2 → ℝ,
                (∀ n, ContDiff ℝ ∞ (ψn n) ∧ HasCompactSupport (ψn n) ∧ tsupport (ψn n) ⊆ K') ∧
                TendstoUniformly ψn ψ atTop ∧
                TendstoUniformly (fun n x => fderiv ℝ (ψn n) x) (fderiv ℝ ψ) atTop := by
          classical
          obtain ⟨r,hr,hrU⟩ := hc.isCompact.exists_cthickening_subset_open hU hs
          let K' := cthickening r (tsupport ψ)
          have hK : IsCompact K' := hc.isCompact.cthickening
          have hinterior : tsupport ψ ⊆ interior K' := (self_subset_thickening hr _).trans (thickening_subset_interior_cthickening r _)
          have huc : UniformContinuous ψ := hψ.continuous.uniformContinuous_of_tendsto_cocompact hc.is_zero_at_infty
          have hdcont : Continuous (fderiv ℝ ψ) := hψ.continuous_fderiv one_ne_zero
          have hduc : UniformContinuous (fderiv ℝ ψ) := hdcont.uniformContinuous_of_tendsto_cocompact (hc.fderiv ℝ).is_zero_at_infty
          have approx (e : ℝ) (he : 0 < e) : ∃ p : E2 → ℝ,
              ContDiff ℝ ∞ p ∧ HasCompactSupport p ∧ tsupport p ⊆ K' ∧
              (∀ x,dist (p x) (ψ x) ≤ e) ∧ (∀ x,dist (fderiv ℝ p x) (fderiv ℝ ψ x) ≤ e) := by
            obtain ⟨d,hd,hdψ⟩ := Metric.uniformContinuous_iff.mp huc e he
            obtain ⟨d',hd',hddψ⟩ := Metric.uniformContinuous_iff.mp hduc e he
            let ρ := min r (min d d') / 2
            have hρ : 0 < ρ := half_pos (lt_min hr (lt_min hd hd'))
            have hρr : ρ < r := by dsimp [ρ];linarith [min_le_left r (min d d')]
            have hρd : ρ < d := by dsimp [ρ];linarith [min_le_right r (min d d'),min_le_left d d']
            have hρd' : ρ < d' := by dsimp [ρ];linarith [min_le_right r (min d d'),min_le_right d d']
            let φ : ContDiffBump (0:E2) := ⟨ρ/2,ρ,half_pos hρ,half_lt_self hρ⟩
            let p := MeasureTheory.convolution (φ.normed volume) ψ (ContinuousLinearMap.lsmul ℝ ℝ) volume
            have hp : ContDiff ℝ ∞ p := φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed hψ.continuous.locallyIntegrable
            have hsp : tsupport p ⊆ K' := by
              apply closure_minimal _ isClosed_cthickening
              intro x hx
              have hadd := support_convolution_subset (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume) hx
              obtain ⟨y,hy,z,hz,rfl⟩ := hadd
              have hy' : ‖y‖ < ρ := by simpa only [φ.support_normed_eq,mem_ball,dist_zero_right] using hy
              apply mem_cthickening_of_dist_le (y+z) z r (tsupport ψ) (subset_tsupport ψ hz)
              simpa only [dist_eq_norm,add_sub_cancel_right] using hy'.le.trans hρr.le
            have hd : ∀ x, fderiv ℝ p x = (MeasureTheory.convolution (φ.normed volume) (fderiv ℝ ψ) (ContinuousLinearMap.lsmul ℝ ℝ) volume) x := by
              intro x
              have hφ : ContDiff ℝ ∞ (φ.normed volume) := φ.contDiff_normed
              have hder := hc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) (hφ.continuous.locallyIntegrable (μ := volume)) hψ x
              rw [hder.fderiv]
              rfl
            refine ⟨p,hp,hK.of_isClosed_subset (isClosed_tsupport _) hsp,hsp,?_,?_⟩
            · intro x
              exact φ.dist_normed_convolution_le hψ.continuous.aestronglyMeasurable (fun y hy => (hdψ (hy.trans hρd)).le)
            · intro x
              rw [hd x]
              exact φ.dist_normed_convolution_le hdcont.aestronglyMeasurable (fun y hy => (hddψ (hy.trans hρd')).le)
          let e : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
          have he (n : ℕ) : 0 < e n := by dsimp [e];positivity
          choose p hp using fun n => approx (e n) (he n)
          refine ⟨K',hK,hrU,hinterior,p,fun n => ⟨(hp n).1,(hp n).2.1,(hp n).2.2.1⟩,?_,?_⟩
          all_goals
            apply Metric.tendstoUniformly_iff.mpr
            intro η hη
            have he0 : Tendsto e atTop (𝓝 0) := by exact tendsto_one_div_add_atTop_nhds_zero_nat
            filter_upwards [he0.eventually (gt_mem_nhds hη)] with n hn
            intro x
          · rw [dist_comm]
            exact ((hp n).2.2.2.1 x).trans_lt hn
          · rw [dist_comm]
            exact ((hp n).2.2.2.2 x).trans_lt hn
        have extension (U : Set E2) (hU : IsOpen U)
            (a : E2 → Mat2) (b : E2 → E2) (c u : E2 → ℝ) (du : E2 → E2)
            (heq : WeakLinearEquationOn U a b c u du)
            (hflux : LocallyIntegrableOn (fun x => matrixAction (a x) (du x)) U)
            (hlower : LocallyIntegrableOn (fun x => inner ℝ (b x) (du x) + c x * u x) U)
            (ψ : E2 → ℝ) (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ)
            (K' : Set E2) (hK : IsCompact K') (hKU : K' ⊆ U) (hψK : tsupport ψ ⊆ K')
            (ψn : ℕ → E2 → ℝ)
            (hn : ∀ n,ContDiff ℝ ∞ (ψn n) ∧ HasCompactSupport (ψn n) ∧ tsupport (ψn n) ⊆ K')
            (hval : TendstoUniformly ψn ψ atTop)
            (hder : TendstoUniformly (fun n x => fderiv ℝ (ψn n) x) (fderiv ℝ ψ) atTop) :
            IntegrableOn (weakIntegrand a b c u du ψ) U ∧
            (∫ x in U, weakIntegrand a b c u du ψ x) = 0 := by
          classical
          let P : (E2 →L[ℝ] ℝ) →L[ℝ] E2 := ∑ i : Fin 2,
            (ContinuousLinearMap.apply ℝ ℝ (coordinateVector 2 i)).smulRight (coordinateVector 2 i)
          have hP (f : E2 → ℝ) (x : E2) : P (fderiv ℝ f x) = planarGradient f x := by
            simp [P,planarGradient]
          have gradient_cont (f : E2 → ℝ) (hf : ContDiff ℝ 1 f) : Continuous (planarGradient f) := by
            have hh := P.continuous.comp (hf.continuous_fderiv one_ne_zero)
            simpa only [Function.comp_def,hP] using hh
          have gradient_zero (f : E2 → ℝ) (hf : tsupport f ⊆ K') (x : E2) (hx : x ∉ K') : planarGradient f x = 0 := by
            rw [← hP,fderiv_of_notMem_tsupport ℝ (fun ht => hx (hf ht)),map_zero]
          have integrand_zero (f : E2 → ℝ) (hf : tsupport f ⊆ K') (x : E2) (hx : x ∉ K') :
              weakIntegrand a b c u du f x = 0 := by
            simp only [weakIntegrand,gradient_zero f hf x hx,inner_zero_right,
              image_eq_zero_of_notMem_tsupport (fun ht => hx (hf ht)),mul_zero,sub_self]
          have hmeas (f : E2 → ℝ) (hf : ContDiff ℝ 1 f) : AEStronglyMeasurable (weakIntegrand a b c u du f) (volume.restrict U) :=
            (hflux.aestronglyMeasurable.inner (gradient_cont f hf).aestronglyMeasurable).sub
              (hlower.aestronglyMeasurable.mul hf.continuous.aestronglyMeasurable)
          obtain ⟨M,hM⟩ := hc.exists_bound_of_continuous hψ.continuous
          obtain ⟨D,hD⟩ := (hc.fderiv ℝ).exists_bound_of_continuous (hψ.continuous_fderiv one_ne_zero)
          let M' := max M 0 + 1
          let D' := max D 0 + 1
          have hM' : 0 ≤ M' := by dsimp [M'];positivity
          have hD' : 0 ≤ D' := by dsimp [D'];positivity
          have hψM (x : E2) : ‖ψ x‖ ≤ M' := (hM x).trans ((le_max_left M 0).trans (le_add_of_nonneg_right zero_le_one))
          have hψD (x : E2) : ‖fderiv ℝ ψ x‖ ≤ D' := (hD x).trans ((le_max_left D 0).trans (le_add_of_nonneg_right zero_le_one))
          have hnbound : ∀ᶠ n in atTop,∀ x,‖ψn n x‖ ≤ M' ∧ ‖fderiv ℝ (ψn n) x‖ ≤ D' := by
            filter_upwards [Metric.tendstoUniformly_iff.mp hval 1 zero_lt_one,
              Metric.tendstoUniformly_iff.mp hder 1 zero_lt_one] with n hv hd
            intro x
            constructor
            · have hh := (norm_sub_norm_le (ψn n x) (ψ x))
              have hvx := hv x
              rw [dist_comm,dist_eq_norm] at hvx
              change ‖ψn n x‖ ≤ max M 0 + 1
              calc
                ‖ψn n x‖ ≤ ‖ψn n x - ψ x‖ + ‖ψ x‖ := by linarith only [hh]
                _ ≤ 1 + M := add_le_add hvx.le (hM x)
                _ ≤ max M 0 + 1 := by linarith only [le_max_left M 0]
            · have hh := (norm_sub_norm_le (fderiv ℝ (ψn n) x) (fderiv ℝ ψ x))
              have hdx := hd x
              rw [dist_comm,dist_eq_norm] at hdx
              dsimp [D'];linarith [hD x,le_max_left D 0]
          let bound : E2 → ℝ := K'.indicator (fun x => ‖matrixAction (a x) (du x)‖ * (‖P‖ * D') +
            ‖inner ℝ (b x) (du x) + c x * u x‖ * M')
          have hbound : Integrable bound (volume.restrict U) := by
            apply Integrable.mono_measure (ν := volume)
            · rw [integrable_indicator_iff hK.measurableSet]
              exact (((hflux.integrableOn_compact_subset hKU hK).norm.mul_const _).add
                ((hlower.integrableOn_compact_subset hKU hK).norm.mul_const _))
            · exact Measure.restrict_le_self
          have bound_le (f : E2 → ℝ) (hf : tsupport f ⊆ K')
              (hv : ∀ x,‖f x‖ ≤ M') (hd : ∀ x,‖fderiv ℝ f x‖ ≤ D') (x : E2) :
              ‖weakIntegrand a b c u du f x‖ ≤ bound x := by
            by_cases hx : x ∈ K'
            · rw [show bound x = ‖matrixAction (a x) (du x)‖ * (‖P‖ * D') + ‖inner ℝ (b x) (du x) + c x * u x‖ * M' from indicator_of_mem hx _]
              have hg : ‖planarGradient f x‖ ≤ ‖P‖ * D' := by
                rw [← hP]
                exact (P.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hd x) (norm_nonneg _))
              calc
                ‖weakIntegrand a b c u du f x‖ ≤ ‖inner ℝ (matrixAction (a x) (du x)) (planarGradient f x)‖ + ‖(inner ℝ (b x) (du x) + c x * u x) * f x‖ := norm_sub_le _ _
                _ ≤ ‖matrixAction (a x) (du x)‖ * ‖planarGradient f x‖ + ‖inner ℝ (b x) (du x) + c x * u x‖ * ‖f x‖ := by
                  rw [norm_mul]
                  exact add_le_add (norm_inner_le_norm _ _) le_rfl
                _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hg (norm_nonneg _)) (mul_le_mul_of_nonneg_left (hv x) (norm_nonneg _))
            · rw [integrand_zero f hf x hx,show bound x = 0 from indicator_of_notMem hx _]
              simp
          have hi : IntegrableOn (weakIntegrand a b c u du ψ) U :=
            hbound.mono' (hmeas ψ hψ) (Eventually.of_forall (bound_le ψ hψK hψM hψD))
          have hlim : ∀ x : E2,Tendsto (fun n => weakIntegrand a b c u du (ψn n) x) atTop (𝓝 (weakIntegrand a b c u du ψ x)) := by
            intro x
            have hg : Tendsto (fun n => planarGradient (ψn n) x) atTop (𝓝 (planarGradient ψ x)) := by
              simpa only [Function.comp_def,hP] using P.continuous.continuousAt.tendsto.comp (hder.tendsto_at x)
            exact (tendsto_const_nhds.inner hg).sub (tendsto_const_nhds.mul (hval.tendsto_at x))
          have hint := tendsto_integral_filter_of_dominated_convergence bound
            (Eventually.of_forall (fun n => hmeas (ψn n) ((hn n).1.of_le (by norm_num))))
            (hnbound.mono (fun n hn' => Eventually.of_forall (bound_le (ψn n) (hn n).2.2 (fun x => (hn' x).1) (fun x => (hn' x).2))))
            hbound (Eventually.of_forall hlim)
          have hzero (n : ℕ) : (∫ x in U,weakIntegrand a b c u du (ψn n) x) = 0 :=
            (heq.2 (ψn n) (hn n).1 (hn n).2.1 ((hn n).2.2.trans hKU)).2
          refine ⟨hi,?_⟩
          have hh : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 (∫ x in U,weakIntegrand a b c u du ψ x)) := by simpa only [hzero] using hint
          exact tendsto_nhds_unique hh tendsto_const_nhds
        obtain ⟨K',hK,hKU,hψK,p,hp,hv,hd⟩ := approximation U hU ψ hψ hψcompact hψsupport
        refine ⟨⟨K',hK,hKU,hψK,p,hp,hv,hd⟩,?_⟩
        exact extension U hU a b c u du heq hflux hlower ψ hψ hψcompact K' hK hKU
          (hψK.trans interior_subset) p hp hv hd
      )
    have hψsource : tsupport (pullbackTest F φ) ⊆ halfDisc (N.R / 2) := by
      intro x hx
      exact ⟨Metric.ball_subset_ball F.sourceR_inside.le (hψsupport hx).1, (hψsupport hx).2⟩
    exact (hC1extension (halfDisc (N.R / 2)) (hop _) N.normalizedA N.normalizedB
      (fun _ => 0) N.v (planarGradient N.v) heq
      (hflux.locallyIntegrableOn (hop _).measurableSet)
      (by simpa only [zero_mul, add_zero] using hlower.locallyIntegrableOn (hop _).measurableSet)
      (pullbackTest F φ) hψC1 hψcompact hψsource).2.2


theorem odd_first_jet_paste_H1 (R : ℝ) (hR : 0 < R) (u : E2 → ℝ) (b : E2 → E2)
    (hu : ContinuousOn u (closedHalfDisc R))
    (hdu : ContinuousOn (planarGradient u) (closedHalfDisc R))
    (hdiff : ∀ x ∈ closedHalfDisc R, DifferentiableAt ℝ u x)
    (htrace : ∀ x ∈ flatArc R, u x = 0)
    (hub : BoundedOn u (closedHalfDisc R))
    (hdub : BoundedOn (planarGradient u) (closedHalfDisc R))
    (hbb : BoundedOn b (closedHalfDisc R))
    (hbmeas : AEStronglyMeasurable b (volume.restrict (closedHalfDisc R))) :
    (∀ x ∈ flatArc R, planarGradient u x 0 = 0) ∧
    (∀ x ∈ disc R, planarGradient (oddReflect u) x =
      if 0 ≤ x 1 then planarGradient u x else -reflectPoint (planarGradient u (reflectPoint x))) ∧
    ContDiffOn ℝ 1 (oddReflect u) (disc R) ∧
    H1On (disc R) (oddReflect u) (planarGradient (oddReflect u)) ∧
    BoundedOn (oddReflect u) (disc R) ∧
    BoundedOn (planarGradient (oddReflect u)) (disc R) ∧
    BoundedOn (driftReflect b) (disc R) ∧
    MemLp (driftReflect b) ⊤ (volume.restrict (disc R)) := by
  classical
  have hcoord (f : E2 → ℝ) (x : E2) (i : Fin 2) :
      planarGradient f x i = fderiv ℝ f x (coordinateVector 2 i) := by
    fin_cases i <;> simp [planarGradient, coordinateVector, Fin.sum_univ_two]
  let S : E2 →L[ℝ] E2 :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi (fun i : Fin 2 =>
        (if i = 0 then (1 : ℝ) else -1) • EuclideanSpace.proj i))
  have hS (x : E2) : S x = reflectPoint x := by
    ext i
    fin_cases i <;> dsimp only [reflectPoint] <;> simp [S]
  have hS0 (x : E2) : reflectPoint x 0 = x 0 := by rfl
  have hS1 (x : E2) : reflectPoint x 1 = -x 1 := by rfl
  have hSS (x : E2) : reflectPoint (reflectPoint x) = x := by
    ext i
    fin_cases i <;> dsimp only [reflectPoint] <;> simp
  have hSnorm (x : E2) : ‖reflectPoint x‖ = ‖x‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    dsimp only [reflectPoint]
    simp [Fin.sum_univ_two]
  have hSdiff (x : E2) : HasFDerivAt reflectPoint S x := by
    convert S.hasFDerivAt using 1
    exact (funext hS).symm
  have hSdisc (x : E2) (hx : x ∈ disc R) : reflectPoint x ∈ disc R := by
    change dist (reflectPoint x) 0 < R
    rw [dist_zero_right, hSnorm, ← dist_zero_right]
    exact hx
  have hupper (x : E2) (hx : x ∈ disc R) (hpos : 0 ≤ x 1) :
      x ∈ closedHalfDisc R := ⟨Metric.ball_subset_closedBall hx, hpos⟩
  have hlower (x : E2) (hx : x ∈ disc R) (hneg : x 1 ≤ 0) :
      reflectPoint x ∈ closedHalfDisc R :=
    hupper _ (hSdisc x hx) (by rw [hS1]; linarith)
  have htan : ∀ x ∈ flatArc R, planarGradient u x 0 = 0 := by
    intro x hx
    have hxU : x ∈ closedHalfDisc R := hupper x hx.1 (by rw [hx.2])
    let l : ℝ → E2 := fun t => x + t • coordinateVector 2 0
    have hl : HasDerivAt l (coordinateVector 2 0) 0 := by
      simpa [l] using ((hasDerivAt_id (0 : ℝ)).smul_const (coordinateVector 2 0)).const_add x
    have hlu : HasDerivAt (u ∘ l) (fderiv ℝ u x (coordinateVector 2 0)) 0 := by
      have hd : HasFDerivAt u (fderiv ℝ u x) (l 0) := by
        simpa [l] using (hdiff x hxU).hasFDerivAt
      exact hd.comp_hasDerivAt 0 hl
    have hzero : (u ∘ l) =ᶠ[𝓝 0] (fun _ => (0 : ℝ)) := by
      have hball : ∀ᶠ t in 𝓝 (0 : ℝ), l t ∈ disc R :=
        (hl.continuousAt.preimage_mem_nhds ((show IsOpen (disc R) from Metric.isOpen_ball).mem_nhds
          (by simpa [l] using hx.1)))
      filter_upwards [hball] with t ht
      apply htrace (l t)
      refine ⟨ht, ?_⟩
      simp [l, coordinateVector, hx.2]
    have hd := hlu.congr_of_eventuallyEq hzero.symm
    have hz := hd.deriv
    simpa [hcoord] using hz.symm
  have hSbasis0 : S (coordinateVector 2 0) = coordinateVector 2 0 := by
    rw [hS]
    ext i
    fin_cases i <;> dsimp only [reflectPoint] <;> simp [coordinateVector]
  have hSbasis1 : S (coordinateVector 2 1) = -coordinateVector 2 1 := by
    rw [hS]
    ext i
    fin_cases i <;> dsimp only [reflectPoint] <;> simp [coordinateVector]
  have hSflat (x : E2) (hx : x 1 = 0) : reflectPoint x = x := by
    ext i
    fin_cases i <;> dsimp only [reflectPoint] <;> simp [hx]
  have hoddUpper (x : E2) (hx : 0 ≤ x 1) : oddReflect u x = u x := by
    dsimp only [oddReflect]
    exact ite_eq_left hx
  have hoddLower (x : E2) (hx : x ∈ disc R) (hneg : x 1 ≤ 0) :
      oddReflect u x = -u (reflectPoint x) := by
    by_cases hz : x 1 = 0
    · rw [hoddUpper x (by rw [hz]), hSflat x hz, htrace x ⟨hx, hz⟩]
      simp
    · dsimp only [oddReflect]
      exact ite_eq_right (show ¬0 ≤ x 1 by intro hh; exact hz (le_antisymm hneg hh))
  let A : Set E2 := {x ∈ disc R | 0 ≤ x 1}
  let B : Set E2 := {x ∈ disc R | x 1 ≤ 0}
  have hAB : A ∪ B = disc R := by
    ext x
    change ((x ∈ disc R ∧ 0 ≤ x 1) ∨ (x ∈ disc R ∧ x 1 ≤ 0)) ↔ x ∈ disc R
    constructor
    · rintro (h | h) <;> exact h.1
    · intro h
      rcases le_total 0 (x 1) with hp | hn
      · exact Or.inl ⟨h, hp⟩
      · exact Or.inr ⟨h, hn⟩
  have hflatDeriv (x : E2) (hx : x ∈ flatArc R) :
      -(fderiv ℝ u (reflectPoint x)).comp S = fderiv ℝ u x := by
    rw [hSflat x hx.2]
    have hzero : fderiv ℝ u x (coordinateVector 2 0) = 0 := by
      rw [← hcoord]
      exact htan x hx
    apply ContinuousLinearMap.ext
    intro y
    have hy : y = y 0 • coordinateVector 2 0 + y 1 • coordinateVector 2 1 := by
      ext i
      fin_cases i <;> simp [coordinateVector]
    rw [hy]
    simp [hSbasis0, hSbasis1, hzero]
  have hderiv (x : E2) (hx : x ∈ disc R) :
      HasFDerivAt (oddReflect u)
        (if 0 ≤ x 1 then fderiv ℝ u x else -(fderiv ℝ u (reflectPoint x)).comp S) x := by
    rcases lt_trichotomy 0 (x 1) with hp | hz | hn
    · rw [if_pos hp.le]
      apply ((hdiff x (hupper x hx hp.le)).hasFDerivAt).congr_of_eventuallyEq
      have he : ∀ᶠ y in 𝓝 x, 0 < y 1 :=
        (isOpen_lt continuous_const (by fun_prop)).mem_nhds hp
      filter_upwards [he] with y hy
      exact hoddUpper y hy.le
    · have hz' : x 1 = 0 := hz.symm
      rw [if_pos (by rw [hz'])]
      have ha : HasFDerivWithinAt (oddReflect u) (fderiv ℝ u x) A x := by
        apply ((hdiff x (hupper x hx (by rw [hz']))).hasFDerivAt.hasFDerivWithinAt).congr
        · intro y hy
          exact hoddUpper y hy.2
        · exact hoddUpper x (by rw [hz'])
      have hb : HasFDerivWithinAt (oddReflect u) (fderiv ℝ u x) B x := by
        have hd := ((hdiff (reflectPoint x) (hlower x hx (by rw [hz']))).hasFDerivAt.comp x
          (hSdiff x)).neg.hasFDerivWithinAt (s := B)
        rw [hflatDeriv x ⟨hx, hz'⟩] at hd
        apply hd.congr
        · intro y hy
          exact hoddLower y hy.1 hy.2
        · exact hoddLower x hx (by rw [hz'])
      have hd := ha.union hb
      rw [hAB] at hd
      exact hd.hasFDerivAt ((show IsOpen (disc R) from Metric.isOpen_ball).mem_nhds hx)
    · rw [if_neg (not_le.mpr hn)]
      apply (((hdiff (reflectPoint x) (hlower x hx hn.le)).hasFDerivAt.comp x (hSdiff x)).neg).congr_of_eventuallyEq
      have he : ∀ᶠ y in 𝓝 x, y 1 < 0 :=
        (isOpen_lt (by fun_prop) continuous_const).mem_nhds hn
      filter_upwards [he] with y hy
      dsimp only [oddReflect]
      exact ite_eq_right (not_le.mpr hy)
  have hjet : ∀ x ∈ disc R, planarGradient (oddReflect u) x =
      if 0 ≤ x 1 then planarGradient u x else -reflectPoint (planarGradient u (reflectPoint x)) := by
    intro x hx
    by_cases hp : 0 ≤ x 1
    · rw [if_pos hp]
      ext i
      rw [hcoord, hcoord, (hderiv x hx).fderiv, if_pos hp]
    · rw [if_neg hp]
      ext i
      rw [hcoord, (hderiv x hx).fderiv, if_neg hp]
      fin_cases i <;> dsimp only [reflectPoint] <;> simp [hSbasis0, hSbasis1, hcoord]
  have hclosedUpper : IsClosed {x : E2 | 0 ≤ x 1} :=
    isClosed_le continuous_const (by fun_prop)
  have hclosedLower : IsClosed {x : E2 | x 1 ≤ 0} :=
    isClosed_le (by fun_prop) continuous_const
  have hclLower : closure {x : E2 | ¬0 ≤ x 1} ⊆ {x : E2 | x 1 ≤ 0} :=
    closure_minimal (fun _ hx => (not_le.mp hx).le) hclosedLower
  have hfront (x : E2) (hx : x ∈ frontier {y : E2 | 0 ≤ y 1}) : x 1 = 0 := by
    have hp : 0 ≤ x 1 := by
      have hh := hx.1
      rwa [hclosedUpper.closure_eq] at hh
    have hn : x 1 ≤ 0 := hclLower (by
      change x ∈ closure ({y : E2 | 0 ≤ y 1}ᶜ)
      rw [closure_compl]
      exact hx.2)
    exact le_antisymm hn hp
  have hgradc : ContinuousOn (planarGradient (oddReflect u)) (disc R) := by
    have hc : ContinuousOn (fun x => if 0 ≤ x 1 then planarGradient u x
        else -reflectPoint (planarGradient u (reflectPoint x))) (disc R) := by
      apply ContinuousOn.if
      · intro x hx
        have hz := hfront x hx.2
        rw [hSflat x hz]
        ext i
        fin_cases i <;> dsimp only [reflectPoint] <;> simp [htan x ⟨hx.1, hz⟩]
      · exact hdu.mono (fun x hx => hupper x hx.1 (by
          have hh := hx.2
          rwa [hclosedUpper.closure_eq] at hh))
      · have hm : MapsTo reflectPoint (disc R ∩ closure {x : E2 | ¬0 ≤ x 1})
            (closedHalfDisc R) := fun x hx => hlower x hx.1 (hclLower hx.2)
        have hd := hdu.comp (S.continuous.continuousOn.congr (fun x _ => (hS x).symm)) hm
        exact (S.continuous.comp_continuousOn hd).neg.congr (fun x _ => by
          change -reflectPoint _ = -S _
          simp only [hS, Function.comp_apply])
    exact hc.congr (fun x hx => hjet x hx)
  have hdual (f : E2 → ℝ) (x : E2) :
      (InnerProductSpace.toDual ℝ E2) (planarGradient f x) = fderiv ℝ f x := by
    ext y
    have hy : y = y 0 • coordinateVector 2 0 + y 1 • coordinateVector 2 1 := by
      ext i
      fin_cases i <;> simp [coordinateVector]
    rw [hy]
    simp [InnerProductSpace.toDual_apply_apply, inner_add_right, inner_smul_right,
      coordinateVector, EuclideanSpace.inner_single_right, hcoord]
  have hC1 : ContDiffOn ℝ 1 (oddReflect u) (disc R) := by
    rw [show (1 : ℕ∞ω) = 0 + 1 from rfl,
      contDiffOn_succ_iff_fderiv_of_isOpen (show IsOpen (disc R) from Metric.isOpen_ball)]
    refine ⟨fun x hx => (hderiv x hx).differentiableAt.differentiableWithinAt, ?_, ?_⟩
    · simp
    · rw [contDiffOn_zero]
      exact ((InnerProductSpace.toDual ℝ E2).continuous.comp_continuousOn hgradc).congr
        (fun x _ => (hdual _ x).symm)
  have hubOdd : BoundedOn (oddReflect u) (disc R) := by
    obtain ⟨C, hC, hc⟩ := hub
    refine ⟨C, hC, fun x hx => ?_⟩
    by_cases hp : 0 ≤ x 1
    · rw [hoddUpper x hp]
      exact hc x (hupper x hx hp)
    · rw [hoddLower x hx (not_le.mp hp).le, norm_neg]
      exact hc _ (hlower x hx (not_le.mp hp).le)
  have hdubOdd : BoundedOn (planarGradient (oddReflect u)) (disc R) := by
    obtain ⟨C, hC, hc⟩ := hdub
    refine ⟨C, hC, fun x hx => ?_⟩
    rw [hjet x hx]
    by_cases hp : 0 ≤ x 1
    · rw [if_pos hp]
      exact hc x (hupper x hx hp)
    · rw [if_neg hp, norm_neg, hSnorm]
      exact hc _ (hlower x hx (not_le.mp hp).le)
  have hbOdd : BoundedOn (driftReflect b) (disc R) := by
    obtain ⟨C, hC, hc⟩ := hbb
    refine ⟨C, hC, fun x hx => ?_⟩
    change ‖if 0 ≤ x 1 then b x else reflectPoint (b (reflectPoint x))‖ ≤ C
    by_cases hp : 0 ≤ x 1
    · rw [if_pos hp]
      exact hc x (hupper x hx hp)
    · rw [if_neg hp, hSnorm]
      exact hc _ (hlower x hx (not_le.mp hp).le)
  refine ⟨htan, hjet, hC1, ?_, hubOdd, hdubOdd, hbOdd, ?_⟩
  · have hdisc : IsOpen (disc R) := Metric.isOpen_ball
    have hfinite : volume (disc R) < ⊤ := Metric.isBounded_ball.measure_lt_top
    letI : IsFiniteMeasure (volume.restrict (disc R)) := ⟨by
      simpa using hfinite⟩
    have hLp {V : Type} [NormedAddCommGroup V] (f : E2 → V)
        (hf : ContinuousOn f (disc R)) (hb : BoundedOn f (disc R)) :
        MemLp f 2 (volume.restrict (disc R)) := by
      obtain ⟨C, hC, hc⟩ := hb
      exact MemLp.of_bound (hf.aestronglyMeasurable hdisc.measurableSet) C
        ((ae_restrict_mem hdisc.measurableSet).mono (fun x hx => hc x hx))
    refine ⟨?_, hLp _ hC1.continuousOn hubOdd, hLp _ hgradc hdubOdd⟩
    refine ⟨hC1.continuousOn.locallyIntegrableOn hdisc.measurableSet,
      hgradc.locallyIntegrableOn hdisc.measurableSet, ?_⟩
    intro ψ hψ hψcompact hψsupport i
    have hfdc : ContinuousOn (fderiv ℝ (oddReflect u)) (disc R) :=
      hC1.continuousOn_fderiv_of_isOpen hdisc (by simp)
    have hints (f : E2 → ℝ) (hf : ContinuousOn f (disc R))
        (hsupp : support f ⊆ tsupport ψ) : Integrable f := by
      apply (integrableOn_iff_integrable_of_support_subset hsupp).mp
      exact (hf.mono hψsupport).integrableOn_compact hψcompact
    have hl : Integrable (fun x => oddReflect u x * fderiv ℝ ψ x (coordinateVector 2 i)) := by
      apply hints
      · exact hC1.continuousOn.mul
          ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).continuousOn
      · intro x hx
        by_contra hh
        apply hx
        simp [fderiv_of_notMem_tsupport ℝ hh]
    have hr : Integrable (fun x => fderiv ℝ (oddReflect u) x (coordinateVector 2 i) * ψ x) := by
      apply hints
      · exact (hfdc.clm_apply continuousOn_const).mul hψ.continuous.continuousOn
      · intro x hx
        by_contra hh
        apply hx
        simp [image_eq_zero_of_notMem_tsupport hh]
    have hp : Integrable (fun x => oddReflect u x * ψ x) := by
      apply hints
      · exact hC1.continuousOn.mul hψ.continuous.continuousOn
      · intro x hx
        by_contra hh
        apply hx
        simp [image_eq_zero_of_notMem_tsupport hh]
    have hid := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hr hl hp
      (fun x hx => (hderiv x (hψsupport hx)).differentiableAt)
      (fun x _ => hψ.differentiable (by simp) x)
    have hsupportL : support (fun x => oddReflect u x * fderiv ℝ ψ x (coordinateVector 2 i))
        ⊆ disc R := by
      intro x hx
      apply hψsupport
      by_contra hh
      apply hx
      simp [fderiv_of_notMem_tsupport ℝ hh]
    have hsupportR : support (fun x => fderiv ℝ (oddReflect u) x (coordinateVector 2 i) * ψ x)
        ⊆ disc R := by
      intro x hx
      apply hψsupport
      by_contra hh
      apply hx
      simp [image_eq_zero_of_notMem_tsupport hh]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx =>
        notMem_support.mp (fun h => hx (hsupportL h))),
      show (fun x => planarGradient (oddReflect u) x i * ψ x) =
        (fun x => fderiv ℝ (oddReflect u) x (coordinateVector 2 i) * ψ x) by
          funext x; rw [hcoord],
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx =>
        notMem_support.mp (fun h => hx (hsupportR h)))]
    exact hid
  · let Q : E2 ≃ₗᵢ[ℝ] E2 :=
      { toLinearEquiv :=
          { toLinearMap := S.toLinearMap
            invFun := S
            left_inv := fun x => by change S (S x) = x; rw [hS, hS, hSS]
            right_inv := fun x => by change S (S x) = x; rw [hS, hS, hSS] }
        norm_map' := fun x => by change ‖S x‖ = ‖x‖; rw [hS, hSnorm] }
    have hQ (x : E2) : Q x = reflectPoint x := hS x
    have hcmeas : MeasurableSet (closedHalfDisc R) := by
      exact Metric.isClosed_closedBall.measurableSet.inter hclosedUpper.measurableSet
    have hmeasure := Q.measurePreserving.restrict_preimage hcmeas
    have hbcomp : AEStronglyMeasurable (fun x => b (reflectPoint x))
        (volume.restrict (reflectPoint ⁻¹' closedHalfDisc R)) := by
      have hh := hbmeas.comp_measurePreserving hmeasure
      have hQeq : (Q : E2 → E2) = reflectPoint := funext hQ
      simpa only [Function.comp_def, hQeq] using hh
    have hmb : AEStronglyMeasurable (driftReflect b) (volume.restrict (disc R)) := by
      have hs : MeasurableSet {x : E2 | 0 ≤ x 1} := hclosedUpper.measurableSet
      apply AEStronglyMeasurable.piecewise hs.nullMeasurableSet
      · rw [Measure.restrict_restrict hs]
        exact hbmeas.mono_measure (Measure.restrict_mono (fun x hx => hupper x hx.2 hx.1) le_rfl)
      · have hm : AEStronglyMeasurable (fun x => reflectPoint (b (reflectPoint x)))
            (volume.restrict (reflectPoint ⁻¹' closedHalfDisc R)) := by
          exact (S.continuous.comp_aestronglyMeasurable hbcomp).congr (by
            filter_upwards [] with x
            exact hS _)
        rw [Measure.restrict_restrict hs.compl]
        exact hm.mono_measure (Measure.restrict_mono (fun x hx =>
          hlower x hx.2 (not_le.mp hx.1).le) le_rfl)
    obtain ⟨C, hC, hc⟩ := hbOdd
    exact memLp_top_of_bound hmb C ((ae_restrict_mem Metric.isOpen_ball.measurableSet).mono
      (fun x hx => hc x hx))


theorem zero_flat_tests_strip_limit (R : ℝ) (hR : 0 < R)
    (u : E2 → ℝ) (b : E2 → E2)
    (heq : WeakLinearEquationOn (halfDisc R) (fun _ => 1) b (fun _ => 0)
      u (planarGradient u))
    (hbmeas : AEStronglyMeasurable b (volume.restrict (halfDisc R)))
    (hlocal : ∀ K' : Set E2, IsCompact K' → K' ⊆ disc R →
      BoundedOn (planarGradient u) (K' ∩ closedHalfDisc R) ∧
      BoundedOn b (K' ∩ closedHalfDisc R))
    (ψ : E2 → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hψcompact : HasCompactSupport ψ) (hψsupport : tsupport ψ ⊆ disc R)
    (hψflat : ∀ x ∈ flatArc R, ψ x = 0) :
    (∃ η : ℝ → ℝ, ContDiff ℝ ∞ η ∧ (∀ t, 0 ≤ η t ∧ η t ≤ 1) ∧
      (∀ t, t ≤ 1 → η t = 0) ∧ (∀ t, 2 ≤ t → η t = 1) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ t, |deriv η t| ≤ C) ∧
      ∃ ε : ℕ → ℝ, (∀ n, 0 < ε n) ∧ Tendsto ε atTop (nhds 0) ∧
        (∀ n, ContDiff ℝ ∞ (stripTest η (ε n) ψ) ∧
          HasCompactSupport (stripTest η (ε n) ψ) ∧
          tsupport (stripTest η (ε n) ψ) ⊆ halfDisc R) ∧
        Tendsto (fun n => ∫ x in halfDisc R,
          |stripTest η (ε n) ψ x - ψ x| ^ 2 +
          ‖planarGradient (stripTest η (ε n) ψ) x - planarGradient ψ x‖ ^ 2)
          atTop (nhds 0)) ∧
    IntegrableOn (laplaceDriftIntegrand b u ψ) (halfDisc R) ∧
    (∫ x in halfDisc R, laplaceDriftIntegrand b u ψ x) = 0 := by
  classical
  let η : ℝ → ℝ := fun t => Real.smoothTransition (t - 1)
  have hη : ContDiff ℝ ∞ η := Real.smoothTransition.contDiff.comp
    (contDiff_id.sub contDiff_const)
  have hηrange : ∀ t, 0 ≤ η t ∧ η t ≤ 1 := fun t =>
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hη0 : ∀ t, t ≤ 1 → η t = 0 := fun t ht =>
    Real.smoothTransition.zero_of_nonpos (by linarith)
  have hη1 : ∀ t, 2 ≤ t → η t = 1 := fun t ht =>
    Real.smoothTransition.one_of_one_le (by linarith)
  have hηd0 : ∀ t, t ≤ 1 → deriv η t = 0 := by
    intro t ht
    apply IsLocalMin.deriv_eq_zero
    filter_upwards with y
    rw [hη0 t ht]
    exact (hηrange y).1
  have hηd1 : ∀ t, 2 ≤ t → deriv η t = 0 := by
    intro t ht
    apply IsLocalMax.deriv_eq_zero
    filter_upwards with y
    rw [hη1 t ht]
    exact (hηrange y).2
  obtain ⟨C0, hC0⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((hη.of_le (by simp) : ContDiff ℝ 1 η).continuous_deriv_one.continuousOn)
      (s := Icc (1 : ℝ) 2)
  let C : ℝ := max C0 0
  have hC : 0 ≤ C := le_max_right _ _
  have hηd : ∀ t, |deriv η t| ≤ C := by
    intro t
    by_cases ht0 : t ≤ 1
    · rw [hηd0 t ht0, abs_zero]; exact hC
    by_cases ht1 : 2 ≤ t
    · rw [hηd1 t ht1, abs_zero]; exact hC
    exact (show |deriv η t| ≤ C0 by
      simpa [Real.norm_eq_abs] using hC0 t ⟨(not_le.mp ht0).le, (not_le.mp ht1).le⟩).trans
      (le_max_left _ _)
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε : ∀ n, 0 < ε n := fun n => one_div_pos.mpr (by positivity)
  have hεlim : Tendsto ε atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hdiffψ : Differentiable ℝ ψ := hψ.differentiable (by simp)
  obtain ⟨A0, hA0⟩ := (hψcompact.fderiv ℝ).exists_bound_of_continuous
    (hψ.continuous_fderiv (by simp))
  let A : ℝ := max A0 0
  have hA : 0 ≤ A := le_max_right _ _
  have hDA : ∀ x, ‖fderiv ℝ ψ x‖ ≤ A := fun x => (hA0 x).trans (le_max_left _ _)
  have hflatall : ∀ x : E2, x 1 = 0 → ψ x = 0 := by
    intro x hx
    by_cases hd : x ∈ disc R
    · exact hψflat x ⟨hd, hx⟩
    · exact image_eq_zero_of_notMem_tsupport (fun hs => hd (hψsupport hs))
  have hheight : ∀ x : E2, |ψ x| ≤ A * |x 1| := by
    intro x
    let y : E2 := x - EuclideanSpace.single 1 (x 1)
    have hy : y 1 = 0 := by simp [y, EuclideanSpace.single_apply]
    have hnorm : ‖x - y‖ = |x 1| := by
      rw [show x - y = EuclideanSpace.single 1 (x 1) by dsimp [y]; abel,
        EuclideanSpace.norm_single, Real.norm_eq_abs]
    have hmv := (convex_univ : Convex ℝ (univ : Set E2)).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hdiffψ z) (fun z _ => hDA z) (mem_univ y) (mem_univ x)
    simpa [hflatall y hy, hnorm, Real.norm_eq_abs] using hmv
  have hcoord : ContDiff ℝ ∞ (fun x : E2 => x 1) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 1).contDiff
  have hstrip : ∀ n, ContDiff ℝ ∞ (stripTest η (ε n) ψ) := by
    intro n
    exact (hη.comp (hcoord.div_const (ε n))).mul hψ
  have hcompact : ∀ n, HasCompactSupport (stripTest η (ε n) ψ) := by
    intro n
    exact hψcompact.mul_left
  have hsup : ∀ n, tsupport (stripTest η (ε n) ψ) ⊆ tsupport ψ := by
    intro n
    exact tsupport_mul_subset_right
  have hsupport : ∀ n, tsupport (stripTest η (ε n) ψ) ⊆ halfDisc R := by
    intro n x hx
    refine ⟨hψsupport (hsup n hx), ?_⟩
    have hzero : ∀ y : E2, y 1 < ε n → stripTest η (ε n) ψ y = 0 := by
      intro y hy
      rw [stripTest, hη0 _ ((div_le_one (hε n)).mpr hy.le), zero_mul]
    have hclosed : IsClosed {y : E2 | ε n ≤ y 1} := isClosed_le continuous_const hcoord.continuous
    have hts : tsupport (stripTest η (ε n) ψ) ⊆ {y : E2 | ε n ≤ y 1} := by
      apply closure_minimal _ hclosed
      intro y hy
      by_contra hn
      exact hy (hzero y (not_le.mp hn))
    exact (hε n).trans_le (hts hx)
  have hhalfopen : IsOpen (halfDisc R) := Metric.isOpen_ball.inter (isOpen_lt continuous_const hcoord.continuous)
  have hhalfmeas : MeasurableSet (halfDisc R) := hhalfopen.measurableSet
  haveI : IsFiniteMeasure (volume.restrict (halfDisc R)) :=
    isFiniteMeasure_restrict.mpr
      ((Metric.isBounded_ball (x := (0 : E2)) (r := R)).subset
        (fun x hx => hx.1)).measure_lt_top.ne
  have hgradmeas : AEStronglyMeasurable (planarGradient u) (volume.restrict (halfDisc R)) :=
    heq.1.2.1.aestronglyMeasurable
  obtain ⟨P0, hP0⟩ := hψcompact.exists_bound_of_continuous hψ.continuous
  let P : ℝ := max P0 0
  have hP : 0 ≤ P := le_max_right _ _
  have hψP : ∀ x, |ψ x| ≤ P := fun x =>
    (show |ψ x| ≤ P0 by simpa [Real.norm_eq_abs] using hP0 x).trans (le_max_left _ _)
  let q : E2 →L[ℝ] ℝ := EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 1
  have hq : ‖q‖ ≤ 1 := by
    apply q.opNorm_le_bound (by norm_num)
    intro x
    simpa [q] using PiLp.norm_apply_le x (1 : Fin 2)
  have hderivstrip : ∀ n x, fderiv ℝ (stripTest η (ε n) ψ) x =
      η (x 1 / ε n) • fderiv ℝ ψ x +
      (ψ x * (deriv η (x 1 / ε n) / ε n)) • q := by
    intro n x
    have hqdiff : HasFDerivAt (fun y : E2 => y 1 / ε n) ((ε n)⁻¹ • q) x := by
      convert q.hasFDerivAt.const_smul ((ε n)⁻¹) using 1
      ext y
      simp [q, div_eq_mul_inv, mul_comm]
    have hc := ((hη.differentiable (by simp) (x 1 / ε n)).hasDerivAt).comp_hasFDerivAt x hqdiff
    change fderiv ℝ (fun y : E2 => η (y 1 / ε n) * ψ y) x = _
    simpa only [Pi.mul_def, Function.comp_def, div_eq_mul_inv,
      smul_smul, mul_comm, mul_left_comm, mul_assoc] using
      (hc.mul (hdiffψ x).hasFDerivAt).fderiv
  have hcoeff : ∀ n x, 0 ≤ x 1 →
      |ψ x * (deriv η (x 1 / ε n) / ε n)| ≤ 2 * A * C := by
    intro n x hx
    by_cases ht : 2 ≤ x 1 / ε n
    · rw [hηd1 _ ht, zero_div, mul_zero, abs_zero]
      positivity
    have hxl : x 1 < 2 * ε n := (div_lt_iff₀ (hε n)).mp (not_le.mp ht)
    have hp : |ψ x| / ε n ≤ 2 * A := by
      apply (div_le_iff₀ (hε n)).mpr
      have hh := hheight x
      rw [abs_of_nonneg hx] at hh
      nlinarith
    calc
      _ = (|ψ x| / ε n) * |deriv η (x 1 / ε n)| := by
        rw [abs_mul, abs_div, abs_of_pos (hε n)]; ring
      _ ≤ (2 * A) * C := mul_le_mul hp (hηd _) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  let G : ℝ := 2 * (A + 2 * A * C)
  have hG : 0 ≤ G := by positivity
  have hgradstrip : ∀ n x, 0 ≤ x 1 → ‖planarGradient (stripTest η (ε n) ψ) x‖ ≤ G := by
    intro n x hx
    apply (norm_planarGradient_le _ _).trans
    change 2 * ‖fderiv ℝ (stripTest η (ε n) ψ) x‖ ≤ 2 * (A + 2 * A * C)
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    rw [hderivstrip]
    calc
      _ ≤ ‖η (x 1 / ε n) • fderiv ℝ ψ x‖ +
          ‖(ψ x * (deriv η (x 1 / ε n) / ε n)) • q‖ := norm_add_le _ _
      _ = |η (x 1 / ε n)| * ‖fderiv ℝ ψ x‖ +
          |ψ x * (deriv η (x 1 / ε n) / ε n)| * ‖q‖ := by
            simp only [norm_smul, Real.norm_eq_abs, abs_mul, abs_div]
      _ ≤ 1 * A + (2 * A * C) * 1 := add_le_add
        (mul_le_mul (by simpa [abs_of_nonneg (hηrange _).1] using (hηrange _).2)
          (hDA x) (norm_nonneg _) (by norm_num))
        (mul_le_mul (hcoeff n x hx) hq (norm_nonneg _) (by positivity))
      _ = _ := by ring
  have hvalstrip : ∀ n x, |stripTest η (ε n) ψ x| ≤ P := by
    intro n x
    rw [stripTest, abs_mul, abs_of_nonneg (hηrange _).1]
    exact (mul_le_mul (hηrange _).2 (hψP x) (abs_nonneg _) (by norm_num)).trans (by simp)
  have hgradψ : ∀ x, ‖planarGradient ψ x‖ ≤ 2 * A := fun x =>
    (norm_planarGradient_le _ _).trans (mul_le_mul_of_nonneg_left (hDA x) (by norm_num))
  have hevent : ∀ x ∈ halfDisc R, ∀ᶠ n in atTop,
      stripTest η (ε n) ψ x = ψ x ∧
      planarGradient (stripTest η (ε n) ψ) x = planarGradient ψ x := by
    intro x hx
    filter_upwards [hεlim.eventually (gt_mem_nhds (half_pos hx.2))] with n hn
    have hineq : 2 * ε n < x 1 := by linarith
    have heqnear : stripTest η (ε n) ψ =ᶠ[nhds x] ψ := by
      have hopen : {y : E2 | 2 * ε n < y 1} ∈ nhds x :=
        (isOpen_lt continuous_const hcoord.continuous).mem_nhds hineq
      filter_upwards [hopen] with y hy
      rw [stripTest, hη1 _ ((le_div_iff₀ (hε n)).mpr hy.le), one_mul]
    exact ⟨heqnear.eq_of_nhds, by simp only [planarGradient, heqnear.fderiv_eq]⟩
  have hl2 : Tendsto (fun n => ∫ x in halfDisc R,
      |stripTest η (ε n) ψ x - ψ x| ^ 2 +
      ‖planarGradient (stripTest η (ε n) ψ) x - planarGradient ψ x‖ ^ 2)
      atTop (nhds 0) := by
    have hm (n : ℕ) : Continuous (fun x => |stripTest η (ε n) ψ x - ψ x| ^ 2 +
        ‖planarGradient (stripTest η (ε n) ψ) x - planarGradient ψ x‖ ^ 2) :=
      (((hstrip n).continuous.sub hψ.continuous).abs.pow 2).add
        (((continuous_planarGradient (hstrip n)).sub (continuous_planarGradient hψ)).norm.pow 2)
    have hbnd (n : ℕ) : ∀ᵐ x ∂volume.restrict (halfDisc R),
        ‖|stripTest η (ε n) ψ x - ψ x| ^ 2 +
          ‖planarGradient (stripTest η (ε n) ψ) x - planarGradient ψ x‖ ^ 2‖ ≤
          (2 * P) ^ 2 + (G + 2 * A) ^ 2 := by
      filter_upwards [ae_restrict_mem hhalfmeas] with x hx
      have hv : |stripTest η (ε n) ψ x - ψ x| ≤ 2 * P :=
        (abs_sub _ _).trans (by linarith [hvalstrip n x, hψP x])
      have hg : ‖planarGradient (stripTest η (ε n) ψ) x - planarGradient ψ x‖ ≤ G + 2 * A :=
        (norm_sub_le _ _).trans (add_le_add (hgradstrip n x hx.2.le) (hgradψ x))
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact add_le_add (pow_le_pow_left₀ (abs_nonneg _) hv 2)
        (pow_le_pow_left₀ (norm_nonneg _) hg 2)
    have hlim : ∀ᵐ x ∂volume.restrict (halfDisc R),
        Tendsto (fun n => |stripTest η (ε n) ψ x - ψ x| ^ 2 +
          ‖planarGradient (stripTest η (ε n) ψ) x - planarGradient ψ x‖ ^ 2) atTop (nhds (0 : ℝ)) := by
      filter_upwards [ae_restrict_mem hhalfmeas] with x hx
      apply tendsto_const_nhds.congr'
      filter_upwards [hevent x hx] with n hn
      simp [hn.1, hn.2]
    simpa using tendsto_integral_of_dominated_convergence
      (fun _ : E2 => (2 * P) ^ 2 + (G + 2 * A) ^ 2)
      (fun n => (hm n).aestronglyMeasurable) (integrable_const _) hbnd hlim
  refine ⟨⟨η, hη, hηrange, hη0, hη1, ⟨C, hC, hηd⟩,
    ε, hε, hεlim, fun n => ⟨hstrip n, hcompact n, hsupport n⟩, hl2⟩, ?_⟩
  obtain ⟨⟨U, hU, hUb⟩, ⟨B, hB, hBb⟩⟩ := hlocal (tsupport ψ) hψcompact hψsupport
  have hclosedhalf : ∀ x ∈ halfDisc R, x ∈ closedHalfDisc R := by
    intro x hx
    exact ⟨by exact mem_closedBall_zero_iff.mpr (mem_ball_zero_iff.mp hx.1).le, hx.2.le⟩
  have hintegrandmeas (φ : E2 → ℝ) (hφ : ContDiff ℝ ∞ φ) :
      AEStronglyMeasurable (laplaceDriftIntegrand b u φ) (volume.restrict (halfDisc R)) :=
    (hgradmeas.inner (continuous_planarGradient hφ).aestronglyMeasurable).sub
      ((hbmeas.inner hgradmeas).mul hφ.continuous.aestronglyMeasurable)
  have hbound (φ : E2 → ℝ) (hs : tsupport φ ⊆ tsupport ψ)
      (hv : ∀ x, |φ x| ≤ P) (hg : ∀ x, 0 ≤ x 1 → ‖planarGradient φ x‖ ≤ G + 2 * A) :
      ∀ᵐ x ∂volume.restrict (halfDisc R),
        ‖laplaceDriftIntegrand b u φ x‖ ≤ U * (G + 2 * A) + B * U * P := by
    filter_upwards [ae_restrict_mem hhalfmeas] with x hx
    by_cases hxs : x ∈ tsupport φ
    · have hxk : x ∈ tsupport ψ ∩ closedHalfDisc R := ⟨hs hxs, hclosedhalf x hx⟩
      have hgu := hUb x hxk
      have hbb := hBb x hxk
      calc
        _ ≤ ‖inner ℝ (planarGradient u x) (planarGradient φ x)‖ +
            ‖inner ℝ (b x) (planarGradient u x) * φ x‖ := norm_sub_le _ _
        _ ≤ ‖planarGradient u x‖ * ‖planarGradient φ x‖ +
            (‖b x‖ * ‖planarGradient u x‖) * |φ x| := by
          gcongr
          · exact norm_inner_le_norm (𝕜 := ℝ) _ _
          · simpa [norm_mul, Real.norm_eq_abs] using
              mul_le_mul_of_nonneg_right (norm_inner_le_norm (𝕜 := ℝ) (b x) (planarGradient u x))
                (norm_nonneg (φ x))
        _ ≤ _ := add_le_add
          (mul_le_mul hgu (hg x hx.2.le) (norm_nonneg _) hU)
          (mul_le_mul (mul_le_mul hbb hgu (norm_nonneg _) hB) (hv x)
            (abs_nonneg _) (by positivity))
    · simp [laplaceDriftIntegrand, planarGradient_eq_zero_off_support φ hxs,
        image_eq_zero_of_notMem_tsupport hxs]
      positivity
  have hboundψ := hbound ψ Subset.rfl hψP (fun x _ => (hgradψ x).trans (by linarith))
  have hint : IntegrableOn (laplaceDriftIntegrand b u ψ) (halfDisc R) :=
    (integrable_const (U * (G + 2 * A) + B * U * P)).mono' (hintegrandmeas ψ hψ) hboundψ
  have hintlim : Tendsto (fun n => ∫ x in halfDisc R,
      laplaceDriftIntegrand b u (stripTest η (ε n) ψ) x) atTop
      (nhds (∫ x in halfDisc R, laplaceDriftIntegrand b u ψ x)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun _ : E2 => U * (G + 2 * A) + B * U * P)
      (fun n => hintegrandmeas _ (hstrip n)) (integrable_const _)
      (fun n => hbound _ (hsup n) (hvalstrip n)
        (fun x hx => (hgradstrip n x hx).trans (by linarith)))
    filter_upwards [ae_restrict_mem hhalfmeas] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [hevent x hx] with n hn
    simp [laplaceDriftIntegrand, hn.1, hn.2]
  have hzero : ∀ n, (∫ x in halfDisc R,
      laplaceDriftIntegrand b u (stripTest η (ε n) ψ) x) = 0 := by
    intro n
    have ht := (heq.2 _ (hstrip n) (hcompact n) (hsupport n)).2
    simpa [laplaceDriftIntegrand, matrixAction, Matrix.one_apply] using ht
  exact ⟨hint, tendsto_nhds_unique hintlim (by simpa only [hzero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0)))⟩


theorem reflected_weak_test_assembly (R : ℝ) (hR : 0 < R)
    (u : E2 → ℝ) (b : E2 → E2)
    (heq : WeakLinearEquationOn (halfDisc R) (fun _ => 1) b (fun _ => 0)
      u (planarGradient u))
    (hH1 : H1On (disc R) (oddReflect u) (planarGradient (oddReflect u)))
    (hjet : ∀ x ∈ disc R, planarGradient (oddReflect u) x =
      if 0 ≤ x 1 then planarGradient u x else -reflectPoint (planarGradient u (reflectPoint x)))
    (hbmeas : AEStronglyMeasurable b (volume.restrict (halfDisc R)))
    (hlocal : ∀ K' : Set E2, IsCompact K' → K' ⊆ disc R →
      BoundedOn (planarGradient u) (K' ∩ closedHalfDisc R) ∧
      BoundedOn b (K' ∩ closedHalfDisc R)) :
    (∀ φ : E2 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ disc R →
      IntegrableOn (laplaceDriftIntegrand (driftReflect b) (oddReflect u) φ) (disc R) ∧
      IntegrableOn (laplaceDriftIntegrand b u (reflectedTest φ)) (halfDisc R) ∧
      (∫ x in disc R, laplaceDriftIntegrand (driftReflect b) (oddReflect u) φ x) =
        (∫ x in halfDisc R, laplaceDriftIntegrand b u (reflectedTest φ) x)) ∧
    WeakLinearEquationOn (disc R) (fun _ => 1) (driftReflect b) (fun _ => 0)
      (oddReflect u) (planarGradient (oddReflect u)) := by
  classical
  have hrr (x : E2) : reflectPoint (reflectPoint x) = x := by
    ext i; fin_cases i <;> simp [reflectPoint]
  let e : E2 ≃ₗᵢ[ℝ] E2 :=
    { toFun := reflectPoint
      invFun := reflectPoint
      left_inv := hrr
      right_inv := hrr
      map_add' := by intros; ext i; fin_cases i <;> simp [reflectPoint] <;> ring
      map_smul' := by intros; ext i; fin_cases i <;> simp [reflectPoint] <;> ring
      norm_map' := by
        intro x
        change ‖reflectPoint x‖ = ‖x‖
        have hh : ‖reflectPoint x‖ ^ 2 = ‖x‖ ^ 2 := by
          simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, reflectPoint]
        nlinarith [norm_nonneg (reflectPoint x), norm_nonneg x] }
  have he (x : E2) : e x = reflectPoint x := rfl
  have hnorm (x : E2) : ‖reflectPoint x‖ = ‖x‖ := e.norm_map x
  have hdisc (x : E2) : reflectPoint x ∈ disc R ↔ x ∈ disc R := by
    simp [disc, Metric.mem_ball, dist_zero_right, hnorm]
  have hhalf : MeasurableSet (halfDisc R) :=
    Metric.isOpen_ball.measurableSet.inter (isOpen_lt continuous_const (show Continuous (fun x : E2 => x 1) by fun_prop)).measurableSet
  have hlower : MeasurableSet {x : E2 | x ∈ disc R ∧ x 1 < 0} :=
    Metric.isOpen_ball.measurableSet.inter (isOpen_lt (show Continuous (fun x : E2 => x 1) by fun_prop) continuous_const).measurableSet
  have hemb : MeasurableEmbedding reflectPoint := e.toHomeomorph.measurableEmbedding
  have hmp : MeasurePreserving reflectPoint volume volume := e.measurePreserving
  have hflat : volume {x : E2 | x 1 = 0} = 0 := by
    have hm := PiLp.volume_preserving_ofLp (Fin 2)
    calc
      volume {x : E2 | x 1 = 0} = volume {x : Fin 2 → ℝ | x 1 = 0} :=
        hm.measure_preimage (s := {x : Fin 2 → ℝ | x 1 = 0})
          ((isClosed_eq (continuous_apply 1) continuous_const).measurableSet.nullMeasurableSet)
      _ = 0 := Measure.pi_hyperplane (fun _ : Fin 2 => volume (α := ℝ)) 1 0
  have hpartition : disc R =ᵐ[volume]
      halfDisc R ∪ {x : E2 | x ∈ disc R ∧ x 1 < 0} := by
    have hne : ∀ᵐ x : E2 ∂volume, x 1 ≠ 0 := by
      simpa only [ae_iff, not_not] using hflat
    filter_upwards [hne] with x hx
    simp only [Set.mem_union, halfDisc, Set.mem_setOf_eq]
    apply propext
    constructor
    · intro hd; rcases lt_or_gt_of_ne hx with h | h
      · exact Or.inr ⟨hd, h⟩
      · exact Or.inl ⟨hd, h⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  have himage : reflectPoint '' halfDisc R = {x : E2 | x ∈ disc R ∧ x 1 < 0} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(hdisc y).2 hy.1, by simpa [reflectPoint] using neg_neg_of_pos hy.2⟩
    · intro hx
      refine ⟨reflectPoint x, ⟨(hdisc x).2 hx.1, ?_⟩, hrr x⟩
      simpa [reflectPoint] using neg_pos.mpr hx.2
  have hgrad (ψ : E2 → ℝ) (x : E2) (i : Fin 2) :
      planarGradient ψ x i = fderiv ℝ ψ x (coordinateVector 2 i) := by
    fin_cases i <;> simp [planarGradient, Fin.sum_univ_two, coordinateVector]
  have hcompgrad (ψ : E2 → ℝ) (hψ : ContDiff ℝ ∞ ψ) (x : E2) :
      planarGradient (ψ ∘ reflectPoint) x = reflectPoint (planarGradient ψ (reflectPoint x)) := by
    have hh := ((hψ.differentiable (by simp)).differentiableAt.hasFDerivAt).comp x
      e.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt
    change HasFDerivAt (ψ ∘ reflectPoint)
      ((fderiv ℝ ψ (reflectPoint x)).comp e.toContinuousLinearEquiv.toContinuousLinearMap) x at hh
    have h0 : e (coordinateVector 2 0) =
        coordinateVector 2 0 := by ext i; fin_cases i <;> simp [e, reflectPoint, coordinateVector]
    have h1 : e (coordinateVector 2 1) =
        -coordinateVector 2 1 := by ext i; fin_cases i <;> simp [e, reflectPoint, coordinateVector]
    ext i
    rw [hgrad, hh.fderiv]
    fin_cases i <;> simp only [ContinuousLinearMap.comp_apply, h0, h1, map_neg] <;>
      simp [reflectPoint, hgrad, h0, h1]
  have hsubgrad (ψ χ : E2 → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ)
      (x : E2) : planarGradient (fun y => ψ y - χ y) x =
        planarGradient ψ x - planarGradient χ x := by
    ext i
    simp only [hgrad, PiLp.sub_apply]
    change (fderiv ℝ (ψ - χ) x) (coordinateVector 2 i) = _
    rw [fderiv_sub (hψ.differentiable (by simp)).differentiableAt
      (hχ.differentiable (by simp)).differentiableAt]
    rfl
  have hsmooth (ψ : E2 → ℝ) (hψ : ContDiff ℝ ∞ ψ) :
      ContDiff ℝ ∞ (ψ ∘ reflectPoint) := hψ.comp e.toContinuousLinearEquiv.toContinuousLinearMap.contDiff
  have hsupport (ψ : E2 → ℝ) (hs : tsupport ψ ⊆ disc R) :
      tsupport (ψ ∘ reflectPoint) ⊆ disc R := by
    rw [tsupport, support_comp_eq_preimage]
    change closure (e.toHomeomorph ⁻¹' support ψ) ⊆ disc R
    rw [← e.toHomeomorph.preimage_closure]
    intro x hx
    exact (hdisc x).1 (hs hx)
  have hfold (ψ : E2 → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
      (hs : tsupport ψ ⊆ disc R) :
      ContDiff ℝ ∞ (reflectedTest ψ) ∧ HasCompactSupport (reflectedTest ψ) ∧
      tsupport (reflectedTest ψ) ⊆ disc R ∧
      (∀ x ∈ flatArc R, reflectedTest ψ x = 0) := by
    refine ⟨hψ.sub (hsmooth ψ hψ), hc.sub (hc.comp_homeomorph e.toHomeomorph),
      (tsupport_sub _ _).trans (union_subset hs (hsupport ψ hs)), ?_⟩
    intro x hx
    have hrx : reflectPoint x = x := by
      ext i; fin_cases i <;> simp [reflectPoint, hx.2]
    simp [reflectedTest, hrx]
  have hint (ψ : E2 → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
      (hs : tsupport ψ ⊆ disc R) :
      IntegrableOn (laplaceDriftIntegrand b u ψ) (halfDisc R) := by
    have hgcont : Continuous (planarGradient ψ) := by
      unfold planarGradient
      exact continuous_finset_sum _ fun i _ =>
        ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).smul continuous_const
    have hgmeas := heq.1.2.1.aestronglyMeasurable
    have hmeas : AEStronglyMeasurable (laplaceDriftIntegrand b u ψ)
        (volume.restrict (halfDisc R)) :=
      (hgmeas.inner hgcont.aestronglyMeasurable).sub
        ((hbmeas.inner hgmeas).mul hψ.continuous.aestronglyMeasurable)
    obtain ⟨A, hA, huA⟩ := (hlocal (tsupport ψ) hc hs).1
    obtain ⟨B, hB, hbB⟩ := (hlocal (tsupport ψ) hc hs).2
    obtain ⟨C, hC⟩ := hc.isCompact.exists_bound_of_continuousOn hψ.continuous.continuousOn
    obtain ⟨D, hD⟩ := hc.isCompact.exists_bound_of_continuousOn hgcont.continuousOn
    letI : IsFiniteMeasure (volume.restrict (halfDisc R)) :=
      isFiniteMeasure_restrict.mpr ((measure_mono (show halfDisc R ⊆ disc R from
        fun _ h => h.1)).trans_lt measure_ball_lt_top).ne
    refine Integrable.of_bound hmeas (A * max D 0 + (B * A) * max C 0) ?_
    filter_upwards [ae_restrict_mem hhalf] with x hx
    by_cases hxs : x ∈ tsupport ψ
    · have hxclosed : x ∈ closedHalfDisc R := ⟨Metric.ball_subset_closedBall hx.1, le_of_lt hx.2⟩
      have hux := huA x ⟨hxs, hxclosed⟩
      have hbx := hbB x ⟨hxs, hxclosed⟩
      calc
        ‖laplaceDriftIntegrand b u ψ x‖ ≤
            ‖inner ℝ (planarGradient u x) (planarGradient ψ x)‖ +
            ‖inner ℝ (b x) (planarGradient u x) * ψ x‖ := norm_sub_le _ _
        _ ≤ (‖planarGradient u x‖ * ‖planarGradient ψ x‖) +
            (‖b x‖ * ‖planarGradient u x‖) * ‖ψ x‖ := by
          gcongr
          · exact norm_inner_le_norm _ _
          · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
              (norm_inner_le_norm _ _) (norm_nonneg _))
        _ ≤ A * max D 0 + (B * A) * max C 0 := by
          gcongr
          · exact (hD x hxs).trans (le_max_left _ _)
          · exact (hC x hxs).trans (le_max_left _ _)
    · have hz := image_eq_zero_of_notMem_tsupport hxs
      have hdz : planarGradient ψ x = 0 := by
        ext i
        simp [hgrad, fderiv_of_notMem_tsupport ℝ hxs]
      simp only [laplaceDriftIntegrand, hz, hdz, inner_zero_right, mul_zero, sub_zero, norm_zero]
      positivity
  have hplus (ψ : E2 → ℝ) (x : E2) (hx : x ∈ halfDisc R) :
      laplaceDriftIntegrand (driftReflect b) (oddReflect u) ψ x = laplaceDriftIntegrand b u ψ x := by
    simp [laplaceDriftIntegrand, hjet x hx.1, driftReflect, le_of_lt hx.2]
  have hminus (ψ : E2 → ℝ) (hψ : ContDiff ℝ ∞ ψ) (x : E2) (hx : x ∈ halfDisc R) :
      laplaceDriftIntegrand (driftReflect b) (oddReflect u) ψ (reflectPoint x) =
        -laplaceDriftIntegrand b u (ψ ∘ reflectPoint) x := by
    have hn : ¬ 0 ≤ (reflectPoint x) 1 := by simpa [reflectPoint] using not_le.mpr (neg_neg_of_pos hx.2)
    rw [laplaceDriftIntegrand, hjet _ ((hdisc x).2 hx.1), if_neg hn]
    simp only [driftReflect, hn, if_false, hrr]
    rw [laplaceDriftIntegrand, hcompgrad ψ hψ x]
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two,
      reflectPoint, Function.comp_apply]
    ring
  have hsplit (φ : E2 → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
      (hs : tsupport φ ⊆ disc R) :
      IntegrableOn (laplaceDriftIntegrand (driftReflect b) (oddReflect u) φ) (disc R) ∧
      IntegrableOn (laplaceDriftIntegrand b u (reflectedTest φ)) (halfDisc R) ∧
      (∫ x in disc R, laplaceDriftIntegrand (driftReflect b) (oddReflect u) φ x) =
        (∫ x in halfDisc R, laplaceDriftIntegrand b u (reflectedTest φ) x) := by
    let f := laplaceDriftIntegrand (driftReflect b) (oddReflect u) φ
    have ha := hint φ hφ hc hs
    have hc' := hc.comp_homeomorph e.toHomeomorph
    have hs' := hsupport φ hs
    have hb' := hint (φ ∘ reflectPoint) (hsmooth φ hφ) hc' hs'
    have hup : IntegrableOn f (halfDisc R) :=
      ha.congr_fun (fun x hx => (hplus φ x hx).symm) hhalf
    have hcomp : IntegrableOn (f ∘ reflectPoint) (halfDisc R) :=
      hb'.neg.congr_fun (fun x hx => (hminus φ hφ x hx).symm) hhalf
    have hlo : IntegrableOn f {x : E2 | x ∈ disc R ∧ x 1 < 0} := by
      rw [← himage]
      exact ((hmp.restrict_image_emb hemb (halfDisc R)).integrable_comp_emb hemb).1 hcomp
    have hfull : IntegrableOn f (disc R) :=
      (integrableOn_congr_set_ae hpartition).2 (integrableOn_union.mpr ⟨hup, hlo⟩)
    have hf := hfold φ hφ hc hs
    refine ⟨hfull, hint _ hf.1 hf.2.1 hf.2.2.1, ?_⟩
    change (∫ x in disc R, f x) = _
    rw [setIntegral_congr_set hpartition,
      setIntegral_union (by
        apply Set.disjoint_left.mpr
        intro x hx hy
        exact (not_lt_of_gt hx.2) hy.2) hlower hup hlo]
    rw [← himage, hmp.setIntegral_image_emb hemb]
    rw [setIntegral_congr_fun hhalf (hplus φ),
      setIntegral_congr_fun hhalf (hminus φ hφ)]
    rw [integral_neg, ← sub_eq_add_neg, ← integral_sub ha hb']
    apply setIntegral_congr_fun hhalf
    intro x hx
    dsimp only [Pi.sub_apply, laplaceDriftIntegrand]
    change _ = inner ℝ (planarGradient u x)
      (planarGradient (fun y => φ y - (φ ∘ reflectPoint) y) x) -
      inner ℝ (b x) (planarGradient u x) * (φ x - (φ ∘ reflectPoint) x)
    rw [hsubgrad φ (φ ∘ reflectPoint) hφ (hsmooth φ hφ)]
    simp only [inner_sub_right, Function.comp_apply]
    ring
  refine ⟨hsplit, hH1.1, ?_⟩
  intro φ hφ hc hs
  have hf := hfold φ hφ hc hs
  have hz := (zero_flat_tests_strip_limit R hR u b heq hbmeas hlocal
    (reflectedTest φ) hf.1 hf.2.1 hf.2.2.1 hf.2.2.2).2.2
  have hm (x : E2) : matrixAction (1 : Mat2) x = x := by
    ext i; simp [matrixAction, Matrix.one_apply, Finset.sum_ite_eq']
  simp only [hm, zero_mul, add_zero]
  exact And.intro (hsplit φ hφ hc hs).1 ((hsplit φ hφ hc hs).2.2.trans hz)

theorem C1_real_weak_to_vekua (R : ℝ) (hR : 0 < R) (u : E2 → ℝ) (b : E2 → E2)
    (hu : ContDiffOn ℝ 1 u (disc R))
    (heq : WeakLinearEquationOn (disc R) (fun _ => 1) b (fun _ => 0)
      u (planarGradient u))
    (hb : BoundedOn b (disc R))
    (hbLp : MemLp b ⊤ (volume.restrict (disc R))) :
    ContinuousOn (complexGradient u) (Metric.ball (0 : ℂ) R) ∧
    WeakVekuaOn (Metric.ball (0 : ℂ) R) (complexGradient u) (vekuaA b) (vekuaB b) ∧
    (∀ z ∈ Metric.ball (0 : ℂ) R,
      vekuaA b z * complexGradient u z + vekuaB b z * star (complexGradient u z) =
        -((inner ℝ (b (complexPoint z)) (planarGradient u (complexPoint z)) : ℝ) : ℂ) / 2) ∧
    ∀ p : ℝ, 2 < p →
      MemLp (vekuaA b) (ENNReal.ofReal p) (volume.restrict (Metric.ball (0 : ℂ) R)) ∧
      MemLp (vekuaB b) (ENNReal.ofReal p) (volume.restrict (Metric.ball (0 : ℂ) R)) := by
  classical
  have hbasic :
      ContinuousOn (complexGradient u) (Metric.ball (0 : ℂ) R) ∧
      (∀ z : ℂ, vekuaA b z * complexGradient u z +
        vekuaB b z * star (complexGradient u z) =
        -((inner ℝ (b (complexPoint z)) (planarGradient u (complexPoint z)) : ℝ) : ℂ) / 2) ∧
      ∀ p : ℝ, 2 < p →
        MemLp (vekuaA b) (ENNReal.ofReal p) (volume.restrict (Metric.ball (0 : ℂ) R)) ∧
        MemLp (vekuaB b) (ENNReal.ofReal p) (volume.restrict (Metric.ball (0 : ℂ) R)) := by
    let e : ℂ ≃ₗᵢ[ℝ] E2 := Complex.orthonormalBasisOneI.repr
    have he : ∀ z, e z = complexPoint z := by intro z; rfl
    have hball : e ⁻¹' disc R = Metric.ball (0 : ℂ) R := by
      ext z
      simp [disc, Metric.mem_ball, dist_zero_right, ← he]
    have hg : ∀ i : Fin 2, ∀ x, planarGradient u x i =
        fderiv ℝ u x (coordinateVector 2 i) := by
      intro i x
      fin_cases i <;> simp [planarGradient, coordinateVector, Fin.sum_univ_two, PiLp.single_apply]
    have hcont : ContinuousOn (fderiv ℝ u) (disc R) :=
      hu.continuousOn_fderiv_of_isOpen Metric.isOpen_ball le_rfl
    have hcoord : ∀ i : Fin 2, ContinuousOn
        (fun z => planarGradient u (complexPoint z) i) (Metric.ball (0 : ℂ) R) := by
      intro i
      simp_rw [hg]
      exact (hcont.clm_apply continuousOn_const).comp e.continuous.continuousOn
        (by intro z hz; change e z ∈ disc R; change z ∈ e ⁻¹' disc R; rwa [hball])
    have hc : ContinuousOn (complexGradient u) (Metric.ball (0 : ℂ) R) := by
      exact (Complex.continuous_ofReal.comp_continuousOn (hcoord 0)).sub
        (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn (hcoord 1)))
    refine ⟨hc, ?_, ?_⟩
    · intro z
      simp only [vekuaA, vekuaB, complexGradient]
      apply Complex.ext <;> simp [PiLp.inner_apply, Fin.sum_univ_two] <;> ring
    · intro p hp
      letI : IsFiniteMeasure (volume.restrict (Metric.ball (0 : ℂ) R)) :=
        isFiniteMeasure_restrict.mpr (ne_of_lt (measure_ball_lt_top))
      have hemb : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
      have hmp : MeasurePreserving e (volume.restrict (Metric.ball (0 : ℂ) R))
          (volume.restrict (disc R)) := by
        simpa only [hball] using e.measurePreserving.restrict_preimage_emb hemb (disc R)
      have hb' : MemLp (fun z => b (e z)) ⊤ (volume.restrict (Metric.ball (0 : ℂ) R)) :=
        hbLp.comp_measurePreserving hmp
      have hbi : ∀ i : Fin 2, MemLp (fun z => (b (complexPoint z) i : ℂ)) ⊤
          (volume.restrict (Metric.ball (0 : ℂ) R)) := by
        intro i
        have hi : MemLp (fun z => b (e z) i) ⊤
            (volume.restrict (Metric.ball (0 : ℂ) R)) := by
          exact hb'.of_le ((PiLp.continuous_apply (2 : ENNReal) (fun _ : Fin 2 => ℝ) i).comp_aestronglyMeasurable hb'.aestronglyMeasurable) (Filter.Eventually.of_forall fun z =>
            PiLp.norm_apply_le (b (e z)) i)
        exact hi.ofReal
      constructor
      · exact (((hbi 0).add ((hbi 1).const_mul Complex.I)).const_mul (-(1/4 : ℂ))).mono_exponent le_top
      · exact (((hbi 0).sub ((hbi 1).const_mul Complex.I)).const_mul (-(1/4 : ℂ))).mono_exponent le_top
  have hreal
      (ψ : E2 → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
      (hs : tsupport ψ ⊆ disc R) :
      (∀ i j : Fin 2, IntegrableOn (fun x => planarGradient u x i *
        fderiv ℝ ψ x (coordinateVector 2 j)) (disc R)) ∧
      IntegrableOn (fun x => inner ℝ (b x) (planarGradient u x) * ψ x) (disc R) ∧
      (∫ x in disc R, planarGradient u x 0 * fderiv ℝ ψ x (coordinateVector 2 0) +
        planarGradient u x 1 * fderiv ℝ ψ x (coordinateVector 2 1)) =
        (∫ x in disc R, inner ℝ (b x) (planarGradient u x) * ψ x) ∧
      (∫ x in disc R, planarGradient u x 0 * fderiv ℝ ψ x (coordinateVector 2 1)) =
        (∫ x in disc R, planarGradient u x 1 * fderiv ℝ ψ x (coordinateVector 2 0)) := by
    have hgrad (f : E2 → ℝ) (x : E2) (i : Fin 2) :
        planarGradient f x i = fderiv ℝ f x (coordinateVector 2 i) := by
      fin_cases i <;> simp [planarGradient, coordinateVector, Fin.sum_univ_two]
    have hcont (i : Fin 2) : ContinuousOn (fun x => planarGradient u x i) (disc R) := by
      simp_rw [hgrad]
      exact (hu.continuousOn_fderiv_of_isOpen Metric.isOpen_ball le_rfl).clm_apply continuousOn_const
    have hint (f χ : E2 → ℝ) (hf : ContinuousOn f (disc R)) (hχ : Continuous χ)
        (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ disc R) :
        IntegrableOn (fun x => f x * χ x) (disc R) := by
      have ht : IntegrableOn (fun x => f x * χ x) (tsupport χ) :=
        ContinuousOn.integrableOn_compact hcχ ((hf.mono hsχ).mul hχ.continuousOn)
      exact ((integrableOn_iff_integrable_of_support_subset
        ((support_mul_subset_right f χ).trans (subset_tsupport χ))).mp ht).integrableOn
    let d (i : Fin 2) : E2 → ℝ := fun x => fderiv ℝ ψ x (coordinateVector 2 i)
    have hd (i : Fin 2) : ContDiff ℝ ∞ (d i) :=
      (hψ.fderiv_right (by simp)).clm_apply contDiff_const
    have hdc (i : Fin 2) : HasCompactSupport (d i) :=
      (hc.fderiv ℝ).comp_left (g := fun f : E2 →L[ℝ] ℝ => f (coordinateVector 2 i)) rfl
    have hds (i : Fin 2) : tsupport (d i) ⊆ disc R := by
      apply subset_trans _ ((tsupport_fderiv_subset ℝ (f := ψ)).trans hs)
      exact closure_mono (support_comp_subset (g := fun f : E2 →L[ℝ] ℝ => f (coordinateVector 2 i)) rfl (fderiv ℝ ψ))
    have hdi (i j : Fin 2) : IntegrableOn (fun x => planarGradient u x i * d j x) (disc R) :=
      hint _ _ (hcont i) (hd j).continuous (hdc j) (hds j)
    have hmatrix (p : E2) : matrixAction (1 : Mat2) p = p := by
      ext i
      simp [matrixAction, Matrix.one_apply]
    have hl := heq.2 ψ hψ hc hs
    simp only [hmatrix, zero_mul, add_zero] at hl
    have hdot (x : E2) : inner ℝ (planarGradient u x) (planarGradient ψ x) =
        planarGradient u x 0 * d 0 x + planarGradient u x 1 * d 1 x := by
      simp [PiLp.inner_apply, Fin.sum_univ_two, hgrad, d, real_inner_comm, mul_comm]
    simp_rw [hdot] at hl
    have hq : IntegrableOn (fun x => inner ℝ (b x) (planarGradient u x) * ψ x) (disc R) := by
      have h := ((hdi 0 0).add (hdi 1 1)).sub hl.1
      convert h using 1
      ext x
      dsimp
      ring
    refine ⟨hdi, hq, ?_⟩
    constructor
    · have h := hl.2
      have hsum : IntegrableOn (fun x => planarGradient u x 0 * d 0 x + planarGradient u x 1 * d 1 x) (disc R) := (hdi 0 0).add (hdi 1 1)
      rw [integral_sub hsum hq] at h
      exact sub_eq_zero.mp h
    · have h0 := heq.1.2.2 (d 1) (hd 1) (hdc 1) (hds 1) 0
      have h1 := heq.1.2.2 (d 0) (hd 0) (hdc 0) (hds 0) 1
      have hsym (x : E2) : fderiv ℝ (d 1) x (coordinateVector 2 0) =
          fderiv ℝ (d 0) x (coordinateVector 2 1) := by
        dsimp [d]
        rw [fderiv_clm_apply ((hψ.fderiv_right (m := 1) (by simp)).differentiable (by norm_num)).differentiableAt
          (differentiableAt_const _),
          fderiv_clm_apply ((hψ.fderiv_right (m := 1) (by simp)).differentiable (by norm_num)).differentiableAt
          (differentiableAt_const _)]
        simpa using hψ.contDiffAt.isSymmSndFDerivAt (by simp) (coordinateVector 2 0) (coordinateVector 2 1)
      simp_rw [hsym] at h0
      exact neg_injective (h0.symm.trans h1)
  let e : ℂ ≃ₗᵢ[ℝ] E2 := Complex.orthonormalBasisOneI.repr
  have he (z : ℂ) : e z = complexPoint z := rfl
  have htransport (φ : ℂ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
      (hs : tsupport φ ⊆ Metric.ball (0 : ℂ) R) (l : ℂ →L[ℝ] ℝ) :
      ContDiff ℝ ∞ (fun x => l (φ (e.symm x))) ∧
      HasCompactSupport (fun x => l (φ (e.symm x))) ∧
      tsupport (fun x => l (φ (e.symm x))) ⊆ disc R ∧
      ∀ x i, fderiv ℝ (fun x => l (φ (e.symm x))) x (coordinateVector 2 i) =
        l (fderiv ℝ φ (e.symm x) (if i = 0 then 1 else Complex.I)) := by
    have hcomp : ContDiff ℝ ∞ (φ ∘ e.symm) :=
      hφ.comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff
    have hsupport : tsupport (φ ∘ e.symm) ⊆ disc R := by
      rw [tsupport, support_comp_eq_preimage]
      change closure (e.symm.toHomeomorph ⁻¹' support φ) ⊆ disc R
      rw [← e.symm.toHomeomorph.preimage_closure]
      intro x hx
      have hh := hs hx
      simpa [disc, Metric.mem_ball, dist_zero_right] using hh
    refine ⟨l.contDiff.comp hcomp,
      (hc.comp_homeomorph e.symm.toHomeomorph).comp_left (map_zero l),
      (tsupport_comp_subset (map_zero l) _).trans hsupport, ?_⟩
    intro x i
    have hf : fderiv ℝ (fun x => l (φ (e.symm x))) x =
        l.comp ((fderiv ℝ φ (e.symm x)).comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap) := by
      exact (l.hasFDerivAt.comp x
        ((hφ.differentiable (by simp)).differentiableAt.hasFDerivAt.comp x
          e.symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt)).fderiv
    rw [hf]
    have he (i : Fin 2) : e.symm (coordinateVector 2 i) = if i = 0 then 1 else Complex.I := by
      fin_cases i <;> simp [e, coordinateVector]
    exact congrArg (fun z => l ((fderiv ℝ φ (e.symm x)) z)) (he i)
  refine ⟨hbasic.1, ?_, (fun z _ => hbasic.2.1 z), hbasic.2.2⟩
  refine ⟨hbasic.1.locallyIntegrableOn Metric.isOpen_ball.measurableSet, ?_⟩
  intro φ hφ hc hs
  have hr := htransport φ hφ hc hs Complex.reCLM
  have hi := htransport φ hφ hc hs Complex.imCLM
  have hrr := hreal _ hr.1 hr.2.1 hr.2.2.1
  have hir := hreal _ hi.1 hi.2.1 hi.2.2.1
  simp only [Complex.reCLM_apply] at hr hrr
  simp only [Complex.imCLM_apply] at hi hir
  let V : Fin 2 → ℂ := fun i => if i = 0 then 1 else Complex.I
  let P (i j : Fin 2) (x : E2) : ℂ :=
    (planarGradient u x i : ℂ) * fderiv ℝ φ (e.symm x) (V j)
  let Q (x : E2) : ℂ := (inner ℝ (b x) (planarGradient u x) : ℂ) * φ (e.symm x)
  have hPr (i j : Fin 2) (x : E2) : (P i j x).re =
      planarGradient u x i * fderiv ℝ (fun x => (φ (e.symm x)).re) x (coordinateVector 2 j) := by
    rw [hr.2.2.2]
    simp [P, V]
  have hPi (i j : Fin 2) (x : E2) : (P i j x).im =
      planarGradient u x i * fderiv ℝ (fun x => (φ (e.symm x)).im) x (coordinateVector 2 j) := by
    rw [hi.2.2.2]
    simp [P, V]
  have hP (i j : Fin 2) : IntegrableOn (P i j) (disc R) := by
    have h1 : IntegrableOn (fun x => (P i j x).re) (disc R) := by
      simpa only [hPr] using hrr.1 i j
    have h2 : IntegrableOn (fun x => (P i j x).im) (disc R) := by
      simpa only [hPi] using hir.1 i j
    convert h1.ofReal.add (h2.ofReal.mul_const Complex.I) using 1
    ext x
    exact (Complex.re_add_im (P i j x)).symm
  have hQ : IntegrableOn Q (disc R) := by
    convert hrr.2.1.ofReal.add (hir.2.1.ofReal.mul_const Complex.I) using 1
    ext x
    dsimp [Q]
    rw [Complex.ofReal_mul, Complex.ofReal_mul]
    rw [mul_assoc, ← mul_add, Complex.re_add_im]
  have hreInt (f : E2 → ℂ) (hf : IntegrableOn f (disc R)) :
      (∫ x in disc R, f x).re = ∫ x in disc R, (f x).re := (integral_re hf).symm
  have himInt (f : E2 → ℂ) (hf : IntegrableOn f (disc R)) :
      (∫ x in disc R, f x).im = ∫ x in disc R, (f x).im := (integral_im hf).symm
  have hsum : IntegrableOn (fun x => P 0 0 x + P 1 1 x) (disc R) := (hP 0 0).add (hP 1 1)
  have hdot : (∫ x in disc R, P 0 0 x + P 1 1 x) = ∫ x in disc R, Q x := by
    apply Complex.ext
    · rw [hreInt _ hsum, hreInt _ hQ]
      simpa only [Complex.add_re, hPr, Q, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero, Complex.reCLM_apply] using hrr.2.2.1
    · rw [himInt _ hsum, himInt _ hQ]
      simpa only [Complex.add_im, hPi, Q, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero, Complex.imCLM_apply] using hir.2.2.1
  have hcross : (∫ x in disc R, P 0 1 x) = ∫ x in disc R, P 1 0 x := by
    apply Complex.ext
    · rw [hreInt _ (hP 0 1), hreInt _ (hP 1 0)]
      simpa only [hPr] using hrr.2.2.2
    · rw [himInt _ (hP 0 1), himInt _ (hP 1 0)]
      simpa only [hPi] using hir.2.2.2
  let L (z : ℂ) : ℂ := complexGradient u z * dbarTest φ z
  let N (z : ℂ) : ℂ :=
    (vekuaA b z * complexGradient u z + vekuaB b z * star (complexGradient u z)) * φ z
  have hpoint (x : E2) : complexPoint (e.symm x) = x := by
    rw [← he, e.apply_symm_apply]
  have hLeq (x : E2) : L (e.symm x) =
      (P 0 0 x + P 1 1 x + Complex.I * (P 0 1 x - P 1 0 x)) / 2 := by
    dsimp only [L, complexGradient, dbarTest]
    rw [hpoint]
    apply Complex.ext <;> simp [P, V] <;> ring
  have hNeq (x : E2) : N (e.symm x) = -Q x / 2 := by
    dsimp only [N]
    rw [hbasic.2.1, hpoint]
    dsimp only [Q]
    ring
  have hcrossI : IntegrableOn (fun x => P 0 1 x - P 1 0 x) (disc R) :=
    (hP 0 1).sub (hP 1 0)
  have hLI : IntegrableOn (L ∘ e.symm) (disc R) := by
    have hh : IntegrableOn (fun x =>
        (P 0 0 x + P 1 1 x + Complex.I * (P 0 1 x - P 1 0 x)) / 2) (disc R) :=
      (hsum.add (hcrossI.const_mul Complex.I)).div_const 2
    exact hh.congr (Filter.Eventually.of_forall fun x => (hLeq x).symm)
  have hNI : IntegrableOn (N ∘ e.symm) (disc R) := by
    exact (hQ.neg.div_const 2).congr (Filter.Eventually.of_forall fun x => (hNeq x).symm)
  have hball : e.symm ⁻¹' Metric.ball (0 : ℂ) R = disc R := by
    ext x
    simp [disc, Metric.mem_ball, dist_zero_right]
  have hemb : MeasurableEmbedding e.symm := e.symm.toHomeomorph.measurableEmbedding
  have hmp : MeasurePreserving e.symm (volume.restrict (disc R))
      (volume.restrict (Metric.ball (0 : ℂ) R)) := by
    simpa only [hball] using e.symm.measurePreserving.restrict_preimage_emb hemb (Metric.ball (0 : ℂ) R)
  refine ⟨(hmp.integrable_comp_emb hemb).1 hLI, (hmp.integrable_comp_emb hemb).1 hNI, ?_⟩
  change (∫ z in Metric.ball (0 : ℂ) R, L z) = -(∫ z in Metric.ball (0 : ℂ) R, N z)
  rw [← hmp.integral_comp hemb L, ← hmp.integral_comp hemb N]
  simp_rw [hLeq, hNeq]
  rw [integral_div, integral_add hsum (hcrossI.const_mul Complex.I),
    integral_const_mul, integral_sub (hP 0 1) (hP 1 0), hcross, sub_self,
    mul_zero, add_zero, hdot, integral_div, integral_neg, neg_div, neg_neg]

end SeifertSurfaces.OriginalEndpoints.B1Tangency.WeakTransport
