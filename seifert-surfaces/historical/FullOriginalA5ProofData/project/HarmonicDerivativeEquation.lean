import HarmonicScalarBounds

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace SeifertSurfaces.WeakSchauder

theorem smooth_memLp_on_precompact (Ω U : Set V) (hΩ : IsOpen Ω) (hU : IsOpen U)
    (hUc : IsCompact (closure U)) (hUΩ : closure U ⊆ Ω)
    (f : V → ℝ) (hf : ContinuousOn f Ω) : MemLp f 2 (volume.restrict U) := by
  have hc : ContinuousOn f (closure U) := hf.mono hUΩ
  have hi := (hc.pow 2).integrableOn_compact (μ := volume) hUc
  apply (memLp_two_iff_integrable_sq
    ((hf.mono (subset_closure.trans hUΩ)).aestronglyMeasurable hU.measurableSet)).mpr
  exact hi.mono_set subset_closure

def smooth_witness_on_precompact (Ω U : Set V) (hΩ : IsOpen Ω) (hU : IsOpen U)
    (hUc : IsCompact (closure U)) (hUΩ : closure U ⊆ Ω)
    (f : V → ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω) : H1Witness f U where
  memLp := smooth_memLp_on_precompact Ω U hΩ hU hUc hUΩ f hf.continuousOn
  weakGrad := classicalGradient f
  weakGrad_component_memLp i := smooth_memLp_on_precompact Ω U hΩ hU hUc hUΩ _
    ((hf.continuousOn_fderiv_of_isOpen hΩ (by simp)).clm_apply continuousOn_const)
  isWeakGrad i := weak_partial_of_contDiffOn U hU f
    (hf.mono (subset_closure.trans hUΩ)) i

theorem identity_solution_of_weak (Ω : Set V) (hΩ : IsOpen Ω)
    (u : V → ℝ) (hu : H1Witness u Ω) (hw : WeakEquation (fun _ => (1 : Mat)) hu) :
    DeGiorgi.IsSolution (identityCoeff Ω).1 u := by
  apply DeGiorgi.isHomogeneousWeakSolution_isSolution
  refine ⟨hu.memW1p, ?_⟩
  intro hu' φ hφ hφw
  have hg : hu.weakGrad =ᵐ[volume.restrict Ω] hu'.weakGrad := by
    have he (i : Fin 3) := (hu.isWeakGrad i).ae_eq hΩ (hu'.isWeakGrad i)
      ((hu.weakGrad_component_memLp i).locallyIntegrable (by norm_num))
      ((hu'.weakGrad_component_memLp i).locallyIntegrable (by norm_num))
    filter_upwards [ae_all_iff.mpr he] with x hx
    exact PiLp.ext fun i => hx i
  have he := (hw φ hφ hφw).2
  change (∫ x in Ω, inner ℝ (DeGiorgi.matMulE (1 : Mat) (hu'.weakGrad x)) (hφw.weakGrad x)) = 0
  rw [← he]
  apply integral_congr_ae
  filter_upwards [hg] with x hx
  rw [hx]

theorem identity_weak_of_div_zero (Ω : Set V) (hΩ : IsOpen Ω)
    (u : V → ℝ) (hu : H1Witness u Ω)
    (hd : DeGiorgi.HasWeakDiv (fun _ => 0) hu.weakGrad Ω) :
    WeakEquation (fun _ => (1 : Mat)) hu := by
  apply constant_weak_of_smooth_integral 1 Ω hΩ u hu
  intro φ hφ hφc hφΩ
  have he := hd φ hφ hφc hφΩ
  have hone (v : V) : DeGiorgi.matMulE (1 : Mat) v = v := by
    ext i
    simp [DeGiorgi.matMulE]
  simp only [zero_mul, integral_zero, neg_zero] at he
  calc
    _ = ∫ x in Ω, ∑ i : Fin 3, hu.weakGrad x i * (fderiv ℝ φ x) (EuclideanSpace.single i 1) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by dsimp only; rw [hone, clm_coordinate_sum]
    _ = 0 := he

/-- The weak Laplace equation is preserved by a coordinate derivative on a
precompact subdomain, using commutation of distributional derivatives. -/
theorem smooth_partial_identity_equation (Ω U : Set V) (hΩ : IsOpen Ω) (hU : IsOpen U)
    (hUc : IsCompact (closure U)) (hUΩ : closure U ⊆ Ω)
    (f : V → ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω)
    (hd : DeGiorgi.HasWeakDiv (fun _ => 0) (classicalGradient f) U) (k : Fin 3) :
    let g := fun x => (fderiv ℝ f x) (EuclideanSpace.single k 1)
    ∃ hg : H1Witness g U,
      (∀ x, hg.weakGrad x = classicalGradient g x) ∧
      WeakEquation (fun _ => (1 : Mat)) hg := by
  dsimp only
  let g : V → ℝ := fun x => (fderiv ℝ f x) (EuclideanSpace.single k 1)
  have hg : ContDiffOn ℝ (⊤ : ℕ∞) g Ω :=
    (hf.fderiv_of_isOpen hΩ (by simp)).clm_apply contDiffOn_const
  let wf := smooth_witness_on_precompact Ω U hΩ hU hUc hUΩ f hf
  let wg := smooth_witness_on_precompact Ω U hΩ hU hUc hUΩ g hg
  refine ⟨wg, fun _ => rfl, identity_weak_of_div_zero U hU g wg ?_⟩
  apply hd.comm (l := k)
  · simpa using DeGiorgi.HasWeakPartialDeriv.of_contDiff (i := k) hU
      (contDiff_const : ContDiff ℝ 1 (fun _ : V => (0 : ℝ)))
  · intro i
    exact (wf.isWeakGrad i).comm (wf.isWeakGrad k) (wg.isWeakGrad i)
  · exact fun i => (wf.weakGrad_component_memLp i).locallyIntegrable (by norm_num)
  · exact fun i => (wg.weakGrad_component_memLp i).locallyIntegrable (by norm_num)

theorem div_zero_restrict (Ω U : Set V) (hsub : U ⊆ Ω) (G : V → V)
    (hd : DeGiorgi.HasWeakDiv (fun _ => 0) G Ω) :
    DeGiorgi.HasWeakDiv (fun _ => 0) G U := by
  intro φ hφ hφc hφU
  have he := hd φ hφ hφc (hφU.trans hsub)
  have hz (x : V) (hx : x ∉ U) :
      (∑ i : Fin 3, G x i * (fderiv ℝ φ x) (EuclideanSpace.single i 1)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [image_eq_zero_of_notMem_tsupport (f := fun y => (fderiv ℝ φ y) (EuclideanSpace.single i 1))
      (fun ht => hx (hφU ((tsupport_fderiv_apply_subset ℝ _ ) ht))), mul_zero]
  simp only [zero_mul, integral_zero, neg_zero] at he ⊢
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => hz x (fun h => hx (hsub h)))]
  exact he

theorem smooth_rep_div_zero (Ω : Set V) (hΩ : IsOpen Ω)
    (h f : V → ℝ) (hh : H1Witness h Ω)
    (hw : WeakEquation (fun _ => (1 : Mat)) hh)
    (hgrad : classicalGradient f =ᵐ[volume.restrict Ω] hh.weakGrad) :
    DeGiorgi.HasWeakDiv (fun _ => 0) (classicalGradient f) Ω := by
  intro φ hφ hφc hφΩ
  have he := laplace_smooth_test_identity Ω hΩ h hh hw φ ⟨hφ, hφc, hφΩ⟩
  simp only [zero_mul, integral_zero, neg_zero]
  rw [← he]
  apply integral_congr_ae
  filter_upwards [hgrad] with x hx
  rw [hx]
  simp [DeGiorgi.smoothGradField, PiLp.inner_apply, mul_comm]

end SeifertSurfaces.WeakSchauder
