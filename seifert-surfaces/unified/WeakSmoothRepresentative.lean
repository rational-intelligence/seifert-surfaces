import ConstantEquationTransport
import DifferentialGeometry.Analysis.Elliptic.Euclidean.Regularity.Harmonic

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace SeifertSurfaces.WeakSchauder

/-- Continuous factors may be multiplied by a test with support inside their domain. -/
theorem continuousOn_mul_test (Ω : Set V) (hΩ : IsOpen Ω)
    (f g : V → ℝ) (hf : ContinuousOn f Ω) (hg : Continuous g)
    (hgΩ : tsupport g ⊆ Ω) : Continuous (fun x => f x * g x) := by
  apply continuous_of_tsupport
  intro x hx
  have hxΩ : x ∈ Ω := hgΩ (tsupport_mul_subset_right hx)
  exact (hf.continuousAt (hΩ.mem_nhds hxΩ)).mul hg.continuousAt

/-- Integration by parts only requires smoothness on the open test domain. -/
theorem weak_partial_of_contDiffOn (Ω : Set V) (hΩ : IsOpen Ω)
    (f : V → ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω) (i : Fin 3) :
    DeGiorgi.HasWeakPartialDeriv i
      (fun x => (fderiv ℝ f x) (EuclideanSpace.single i 1)) f Ω := by
  intro φ hφ hφc hφΩ
  let v := EuclideanSpace.single i (1 : ℝ)
  have hdΩ : tsupport (fun x => (fderiv ℝ φ x) v) ⊆ Ω :=
    (tsupport_fderiv_apply_subset ℝ v).trans hφΩ
  have hdφ : Continuous (fun x => (fderiv ℝ φ x) v) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdf : ContinuousOn (fun x => (fderiv ℝ f x) v) Ω :=
    (hf.continuousOn_fderiv_of_isOpen hΩ (by simp)).clm_apply continuousOn_const
  have he := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    ((continuousOn_mul_test Ω hΩ _ φ hdf hφ.continuous hφΩ).integrable_of_hasCompactSupport
      hφc.mul_left)
    ((continuousOn_mul_test Ω hΩ f _ hf.continuousOn hdφ hdΩ).integrable_of_hasCompactSupport
      (hφc.fderiv_apply (𝕜 := ℝ) v).mul_left)
    ((continuousOn_mul_test Ω hΩ f φ hf.continuousOn hφ.continuous hφΩ).integrable_of_hasCompactSupport
      hφc.mul_left)
    (fun x hx => ((hf x (hφΩ hx)).contDiffAt (hΩ.mem_nhds (hφΩ hx))).differentiableAt (by simp))
    (fun x _ => hφ.differentiable (by simp) x)
  change (∫ x in Ω, f x * (fderiv ℝ φ x) v) = -∫ x in Ω, (fderiv ℝ f x) v * φ x
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero,
    setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact he
  · intro x hx
    rw [show φ x = 0 from  image_eq_zero_of_notMem_tsupport (fun h => hx (hφΩ h)), mul_zero]
  · intro x hx
    rw [show (fderiv ℝ φ x) v = 0 from image_eq_zero_of_notMem_tsupport (f := fun x => (fderiv ℝ φ x) v) (fun h => hx (hdΩ h)), mul_zero]

/-- A smooth representative has the supplied weak gradient almost everywhere. -/
theorem classicalGradient_ae_eq_of_smooth_representative
    (Ω : Set V) (hΩ : IsOpen Ω) (h f : V → ℝ) (hh : H1Witness h Ω)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω) (hfh : f =ᵐ[volume.restrict Ω] h) :
    classicalGradient f =ᵐ[volume.restrict Ω] hh.weakGrad := by
  have heach (i : Fin 3) :
      (fun x => classicalGradient f x i) =ᵐ[volume.restrict Ω] (fun x => hh.weakGrad x i) := by
    let g : V → ℝ := fun x => (fderiv ℝ f x) (EuclideanSpace.single i 1)
    have hgc : ContinuousOn g Ω :=
      (hf.continuousOn_fderiv_of_isOpen hΩ (by simp)).clm_apply continuousOn_const
    have hgw := weak_partial_of_contDiffOn Ω hΩ f hf i
    have hhw := (hh.isWeakGrad i).congr_ae hfh.symm EventuallyEq.rfl
    suffices hz : ∀ᵐ x ∂volume.restrict Ω, g x - hh.weakGrad x i = 0 by
      filter_upwards [hz] with x hx
      exact sub_eq_zero.mp hx
    rw [ae_restrict_iff' hΩ.measurableSet]
    apply IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hΩ
    · exact hgc.locallyIntegrableOn hΩ.measurableSet |>.sub
        (locallyIntegrableOn_of_locallyIntegrable_restrict
          ((hh.weakGrad_component_memLp i).locallyIntegrable (by norm_num)))
    · intro φ hφ hφc hφΩ
      have heq : (∫ x in Ω, g x * φ x) = ∫ x in Ω, hh.weakGrad x i * φ x := by
        have h1 := hgw φ hφ hφc hφΩ
        have h2 := hhw φ hφ hφc hφΩ
        linarith
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ω)
        (fun x hx => show φ x • (g x - hh.weakGrad x i) = 0 by
          rw [ image_eq_zero_of_notMem_tsupport (fun ht => hx (hφΩ ht)), zero_smul])]
      simp only [smul_eq_mul, mul_sub]
      rw [integral_sub]
      · simpa only [mul_comm (φ _), heq, sub_self]
      · exact ((continuousOn_mul_test Ω hΩ g φ hgc hφ.continuous hφΩ).integrable_of_hasCompactSupport
          hφc.mul_left).restrict (s := Ω) |>.congr (Eventually.of_forall fun x => mul_comm _ _)
      · simpa only [smul_eq_mul] using
          ((hh.weakGrad_component_memLp i).locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
            hφ.continuous hφc
  filter_upwards [ae_all_iff.mpr heach] with x hx
  exact PiLp.ext fun i => hx i

/-- Glue compatible almost-everywhere smooth representatives on an open cover.
The construction follows the checked Iterated embedding provider's gluing argument. -/
theorem exists_glued_smooth_ae (Ω : Set V) (u : V → ℝ)
    (hloc : ∀ x : Ω, ∃ r : ℝ, 0 < r ∧ Metric.ball (x : V) r ⊆ Ω ∧
      ∃ f : V → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) f (Metric.ball (x : V) r) ∧
        u =ᵐ[volume.restrict (Metric.ball (x : V) r)] f) :
    ∃ f : V → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) f Ω ∧ u =ᵐ[volume.restrict Ω] f := by
  classical
  choose rad hrad_pos hball_subset frep hfrep_cdiff hfrep_ae using hloc
  set S : Ω → Set V := fun x => Metric.ball (x : V) (rad x) with hS_def
  have hS_open : ∀ x : Ω, IsOpen (S x) := fun x => Metric.isOpen_ball
  have hS_subset : ∀ x : Ω, S x ⊆ Ω := hball_subset
  have hx_mem_S : ∀ x : Ω, (x : V) ∈ S x := fun x => by
    rw [hS_def]; exact Metric.mem_ball_self (hrad_pos x)
  have hΩ_subset_iUnion : Ω ⊆ ⋃ x : Ω, S x := fun y hy =>
    Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hx_mem_S ⟨y, hy⟩⟩
  have hfrep_cont : ∀ x : Ω, ContinuousOn (frep x) (S x) := fun x =>
    (hfrep_cdiff x).continuousOn
  have h_consistent : ∀ (x y : Ω) (z : V) (hzx : z ∈ S x) (hzy : z ∈ S y),
      frep x z = frep y z := by
    intro x y z hzx hzy
    set W : Set V := S x ∩ S y with hW_def
    have hW_open : IsOpen W := (hS_open x).inter (hS_open y)
    have hW_sub_x : W ⊆ S x := Set.inter_subset_left
    have hW_sub_y : W ⊆ S y := Set.inter_subset_right
    have hae_x : u =ᵐ[volume.restrict W] frep x :=
      ae_restrict_of_ae_restrict_of_subset hW_sub_x (hfrep_ae x)
    have hae_y : u =ᵐ[volume.restrict W] frep y :=
      ae_restrict_of_ae_restrict_of_subset hW_sub_y (hfrep_ae y)
    have hae_xy : frep x =ᵐ[volume.restrict W] frep y := (hae_x.symm).trans hae_y
    have h_eqOn : Set.EqOn (frep x) (frep y) W :=
      MeasureTheory.Measure.eqOn_open_of_ae_eq hae_xy hW_open
        ((hfrep_cont x).mono hW_sub_x) ((hfrep_cont y).mono hW_sub_y)
    exact h_eqOn ⟨hzx, hzy⟩
  set gΩ : ↥Ω → ℝ :=
    Set.iUnionLift S (fun x z => frep x (z : V))
      (fun x y z hzx hzy => h_consistent x y z hzx hzy) Ω hΩ_subset_iUnion
    with hgΩ_def
  set u_smooth : V → ℝ := fun y => if h : y ∈ Ω then gΩ ⟨y, h⟩ else 0
    with hu_smooth_def
  have h_u_smooth_eq : ∀ (x : Ω) (z : V), z ∈ S x →
      u_smooth z = frep x z := by
    intro x z hz
    have hz_Ω : z ∈ Ω := hS_subset x hz
    have h_lift : gΩ ⟨z, hz_Ω⟩ = frep x (z : V) :=
      Set.iUnionLift_of_mem (S := S) (T := (Ω : Set V)) ⟨z, hz_Ω⟩ hz
    rw [hu_smooth_def]
    simp only [hz_Ω, dite_eq_left]
    exact h_lift
  refine ⟨u_smooth, ?_, ?_⟩
  · refine contDiffOn_of_locally_contDiffOn ?_
    intro y hy
    refine ⟨S ⟨y, hy⟩, hS_open ⟨y, hy⟩, hx_mem_S ⟨y, hy⟩, ?_⟩
    refine ((hfrep_cdiff ⟨y, hy⟩).mono (Set.inter_subset_right)).congr ?_
    intro z hz
    exact h_u_smooth_eq ⟨y, hy⟩ z hz.2
  · obtain ⟨T, hT_countable, hT_cover⟩ :=
      TopologicalSpace.isOpen_iUnion_countable S hS_open
    have hΩ_sub_biUnion : Ω ⊆ ⋃ x ∈ T, S x := by
      rw [hT_cover]; exact hΩ_subset_iUnion
    have hae_each : ∀ x ∈ T, u =ᵐ[volume.restrict (S x)] u_smooth := by
      intro x _hxT
      have h1 : u =ᵐ[volume.restrict (S x)] frep x := hfrep_ae x
      refine h1.trans ?_
      refine (ae_restrict_iff' (hS_open x).measurableSet).mpr ?_
      exact Filter.Eventually.of_forall fun z hz => (h_u_smooth_eq x z hz).symm
    have hae_biUnion :
        u =ᵐ[volume.restrict (⋃ x ∈ T, S x)] u_smooth :=
      (MeasureTheory.ae_eq_restrict_biUnion_iff S hT_countable u u_smooth).mpr
        hae_each
    exact hae_biUnion.filter_mono
      (MeasureTheory.ae_mono (Measure.restrict_mono hΩ_sub_biUnion le_rfl))

/-- The weak equation supplies the test identity required by the reviewed Weyl provider. -/
theorem laplace_smooth_test_identity (Ω : Set V) (hΩ : IsOpen Ω)
    (h : V → ℝ) (hh : H1Witness h Ω)
    (hweak : WeakEquation (fun _ => (1 : Mat)) hh)
    (φ : V → ℝ) (hφ : DeGiorgi.IsSmoothTestOn Ω φ) :
    (∫ x in Ω, inner ℝ (hh.weakGrad x) (DeGiorgi.smoothGradField φ x)) = 0 := by
  have he := constant_weak_smooth_integral 1 Ω hΩ h hh hweak φ hφ.1 hφ.2.1 hφ.2.2
  simpa only [DeGiorgi.smoothGradField, gradient_pairing_clm,
    DeGiorgi.matMulE, Matrix.one_mulVec, WithLp.toLp_ofLp] using he

/-- Actual weak Laplace regularity (Weyl lemma) on an open domain. It is a
named analytic proof obligation, with no harmonic-regularity oracle field. -/
theorem weak_laplace_smooth_representative (Ω : Set V) (hΩ : IsOpen Ω)
    (h : V → ℝ) (hh : H1Witness h Ω)
    (hweak : WeakEquation (fun _ => (1 : Mat)) hh) :
    ∃ h' : V → ℝ, h' =ᵐ[volume.restrict Ω] h ∧
      ContDiffOn ℝ (⊤ : ℕ∞) h' Ω ∧
      (classicalGradient h' =ᵐ[volume.restrict Ω] hh.weakGrad) := by
  have hloc : ∀ x : Ω, ∃ r : ℝ, 0 < r ∧ Metric.ball (x : V) r ⊆ Ω ∧
      ∃ f : V → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) f (Metric.ball (x : V) r) ∧
        h =ᵐ[volume.restrict (Metric.ball (x : V) r)] f := by
    intro x
    obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hΩ x x.2
    have hcsub : closure (Metric.ball (x : V) (r / 2)) ⊆ Ω :=
      (Metric.closure_ball_subset_closedBall.trans (Metric.closedBall_subset_ball (by linarith))).trans hsub
    obtain ⟨f, hf, hae⟩ :=
      DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_contDiffOn_ae_eq_of_integral_inner_weakGrad_smoothGrad_eq_zero
        hΩ Metric.isOpen_ball
        ((isCompact_closedBall (x : V) (r / 2)).of_isClosed_subset isClosed_closure
          Metric.closure_ball_subset_closedBall)
        hcsub hh (laplace_smooth_test_identity Ω hΩ h hh hweak)
    exact ⟨r / 2, by linarith, subset_closure.trans hcsub, f, hf, hae⟩
  obtain ⟨f, hf, hae⟩ := exists_glued_smooth_ae Ω h hloc
  exact ⟨f, hae.symm, hf,
    classicalGradient_ae_eq_of_smooth_representative Ω hΩ h f hh hf hae.symm⟩

end SeifertSurfaces.WeakSchauder
