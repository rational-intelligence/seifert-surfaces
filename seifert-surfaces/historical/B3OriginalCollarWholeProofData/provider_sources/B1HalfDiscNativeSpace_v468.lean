import B1SmallDomainCoercivity_v468
noncomputable section
open Set Topology Function MeasureTheory
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open ChartMetricProvider.Variational.IsothermalPDELower.NativeDirichlet
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem halfdisc_native_smooth_h10_v468 (R : ℝ)
    (φ : E2 → ℝ) (hs : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (ht : tsupport φ ⊆ halfDisc R) :
    H10On (halfDisc R) φ (planarGradient φ) := by
  classical
  have hgcont : Continuous (planarGradient φ) := continuous_planarGradient hs
  have hgcompact : HasCompactSupport (planarGradient φ) := by
    apply hc.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ (isClosed_tsupport φ)
    intro x hx
    by_contra h
    exact hx (planarGradient_eq_zero_off_support φ h)
  have huLp : MemLp φ 2 (volume.restrict (halfDisc R)) :=
    (hs.continuous.memLp_of_hasCompactSupport (μ := volume) hc).restrict _
  have hgLp : MemLp (planarGradient φ) 2 (volume.restrict (halfDisc R)) :=
    (hgcont.memLp_of_hasCompactSupport (μ := volume) hgcompact).restrict _
  refine ⟨⟨?_, huLp, hgLp⟩, ?_⟩
  · refine ⟨hs.continuous.locallyIntegrable.locallyIntegrableOn _,
      hgcont.locallyIntegrable.locallyIntegrableOn _, ?_⟩
    intro ψ hψ hcψ htψ i
    have hcoord (x : E2) : planarGradient φ x i = fderiv ℝ φ x (coordinateVector 2 i) := by
      fin_cases i <;> simp [planarGradient, Fin.sum_univ_two, coordinateVector]
    have hdψ : Continuous (fun x => fderiv ℝ ψ x (coordinateVector 2 i)) :=
      (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hdφ : Continuous (fun x => fderiv ℝ φ x (coordinateVector 2 i)) :=
      (hs.continuous_fderiv (by simp)).clm_apply continuous_const
    have hi := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
      ((hdφ.mul hψ.continuous).integrable_of_hasCompactSupport hcψ.mul_left)
      ((hs.continuous.mul hdψ).integrable_of_hasCompactSupport (hcψ.fderiv_apply (𝕜 := ℝ) (coordinateVector 2 i)).mul_left)
      ((hs.continuous.mul hψ.continuous).integrable_of_hasCompactSupport hcψ.mul_left)
      (fun x _ => hs.differentiable (by simp) x)
      (fun x _ => hψ.differentiable (by simp) x)
    simp_rw [hcoord]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero,
      setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact hi
    · intro x hx
      rw [show ψ x = 0 from image_eq_zero_of_notMem_tsupport (fun h => hx (htψ h)), mul_zero]
    · intro x hx
      have hdsub : tsupport (fun x => fderiv ℝ ψ x (coordinateVector 2 i)) ⊆ halfDisc R :=
        (tsupport_fderiv_apply_subset ℝ (coordinateVector 2 i)).trans htψ
      rw [show fderiv ℝ ψ x (coordinateVector 2 i) = 0 from
        image_eq_zero_of_notMem_tsupport (f := fun x => fderiv ℝ ψ x (coordinateVector 2 i))
          (fun h => hx (hdsub h)), mul_zero]
  · intro ε hε
    refine ⟨φ, hs, hc, ht, ?_⟩
    simpa using hε

private theorem halfdisc_smoothGraph_span_v468 (R : ℝ) :
    (Submodule.span ℝ (SmoothGraph (halfDisc R)) : Set (Pair (halfDisc R))) =
      SmoothGraph (halfDisc R) := by
  let U := halfDisc R; have hzero : (0 : Pair U) ∈ SmoothGraph U := by { have hg : planarGradient (0 : E2 → ℝ) = 0 := by { funext x; simp [planarGradient] }; have hglp : MemLp (planarGradient (0 : E2 → ℝ)) 2 (volume.restrict U) := by { rw [hg]; exact MemLp.zero }; refine ⟨0, MemLp.zero, hglp, contDiff_const, HasCompactSupport.zero, ?_, ?_⟩; { simp }; { unfold pack; simp only [hg, MemLp.toLp_zero]; rfl } }; have hadd : ∀ p q : Pair U, p ∈ SmoothGraph U → q ∈ SmoothGraph U → p + q ∈ SmoothGraph U := by { rintro p q ⟨φ, hφ, hgφ, hsφ, hcφ, htφ, rfl⟩ ⟨ψ, hψ, hgψ, hsψ, hcψ, htψ, rfl⟩; have hg : planarGradient (φ + ψ) = planarGradient φ + planarGradient ψ := by { funext x; unfold planarGradient; rw [fderiv_add (hsφ.differentiable (by simp) x) (hsψ.differentiable (by simp) x)]; simp only [ContinuousLinearMap.add_apply, add_smul, Finset.sum_add_distrib, Pi.add_apply] }; have hglp : MemLp (planarGradient (φ + ψ)) 2 (volume.restrict U) := by { rw [hg]; exact hgφ.add hgψ }; refine ⟨φ + ψ, hφ.add hψ, hglp, hsφ.add hsψ, hcφ.add hcψ, ?_, ?_⟩; { exact (tsupport_add φ ψ).trans (union_subset htφ htψ) }; { unfold pack; simp only [hg]; rfl } }; have hsmul : ∀ (a : ℝ) (p : Pair U), p ∈ SmoothGraph U → a • p ∈ SmoothGraph U := by { rintro a p ⟨φ, hφ, hgφ, hsφ, hcφ, htφ, rfl⟩; have hg : planarGradient (a • φ) = a • planarGradient φ := by { funext x; unfold planarGradient; rw [fderiv_const_smul (hsφ.differentiable (by simp) x)]; simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, Pi.smul_apply, mul_smul, Finset.smul_sum] }; have hglp : MemLp (planarGradient (a • φ)) 2 (volume.restrict U) := by { rw [hg]; exact hgφ.const_smul a }; refine ⟨a • φ, hφ.const_smul a, hglp, contDiff_const.smul hsφ, hcφ.smul_left, ?_, ?_⟩; { exact (tsupport_smul_subset_right (fun _ : E2 => a) φ).trans htφ }; { unfold pack; simp only [hg]; rfl } }; let S : Submodule ℝ (Pair U) := { carrier := SmoothGraph U, zero_mem' := hzero, add_mem' := hadd _ _, smul_mem' := hsmul }; exact congrArg (fun T : Submodule ℝ (Pair U) => (T : Set (Pair U))) (Submodule.span_eq S)

private theorem halfdisc_nativeH10_iff_pair_mem_v468 (R : ℝ)
    (u : E2 → ℝ) (du : E2 → E2)
    (hu : MemLp u 2 (volume.restrict (halfDisc R)))
    (hdu : MemLp du 2 (volume.restrict (halfDisc R))) :
    H10On (halfDisc R) u du ↔
      pack (halfDisc R) u du hu hdu ∈ space (halfDisc R) := by
  classical
  let U := halfDisc R
  let μ := volume.restrict U
  let p : Pair U := pack U u du hu hdu
  have space_eq : (space U : Set (Pair U)) = closure (SmoothGraph U) := by
    rw [Submodule.topologicalClosure_coe, halfdisc_smoothGraph_span_v468 R]
  have energy (φ : E2 → ℝ) (hφ : MemLp φ 2 μ)
      (hg : MemLp (planarGradient φ) 2 μ) :
      dist p (pack U φ (planarGradient φ) hφ hg) ^ 2 =
        ∫ x in U, |u x - φ x| ^ 2 + ‖du x - planarGradient φ x‖ ^ 2 := by
    have scalar_sq : ‖hu.toLp u - hφ.toLp φ‖ ^ 2 = ∫ x, |u x - φ x| ^ 2 ∂μ := by
      rw [← MemLp.toLp_sub, ← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [(hu.sub hφ).coeFn_toLp] with x hx
      rw [hx, Real.inner_apply]
      change (u x - φ x) * (u x - φ x) = |u x - φ x| ^ 2
      rw [sq_abs]
      ring
    have vector_sq : ‖hdu.toLp du - hg.toLp (planarGradient φ)‖ ^ 2 =
        ∫ x, ‖du x - planarGradient φ x‖ ^ 2 ∂μ := by
      rw [← MemLp.toLp_sub, ← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [(hdu.sub hg).coeFn_toLp] with x hx
      rw [hx, real_inner_self_eq_norm_sq]
      rfl
    rw [dist_eq_norm, WithLp.prod_norm_sq_eq_of_L2]
    change ‖hu.toLp u - hφ.toLp φ‖ ^ 2 + ‖hdu.toLp du - hg.toLp (planarGradient φ)‖ ^ 2 = _
    rw [scalar_sq, vector_sq]
    have hs : Integrable (fun x => |u x - φ x| ^ 2) μ := by
      exact ((hu.sub hφ).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).congr
        (Filter.Eventually.of_forall fun x => by simp only [Real.norm_eq_abs, Pi.sub_apply])
    have hv : Integrable (fun x => ‖du x - planarGradient φ x‖ ^ 2) μ :=
      (hdu.sub hg).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
    exact (integral_add hs hv).symm
  constructor
  · intro hn
    change p ∈ (space U : Set (Pair U))
    rw [space_eq]
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨φ, hs, hc, ht, herr⟩ := hn.2 (ε ^ 2) (sq_pos_of_pos hε)
    have hφ := (halfdisc_native_smooth_h10_v468 R φ hs hc ht).1.2.1
    have hg := (halfdisc_native_smooth_h10_v468 R φ hs hc ht).1.2.2
    refine ⟨pack U φ (planarGradient φ) hφ hg, ⟨φ, hφ, hg, hs, hc, ht, rfl⟩, ?_⟩
    have hh : dist p (pack U φ (planarGradient φ) hφ hg) ^ 2 < ε ^ 2 := by
      rw [energy φ hφ hg]
      exact herr
    exact (sq_lt_sq₀ (dist_nonneg) hε.le).mp hh
  · intro hp
    have hclosure : p ∈ closure (SmoothGraph U) := by
      rw [← space_eq]
      exact hp
    refine ⟨⟨?_, hu, hdu⟩, ?_⟩
    · refine ⟨locallyIntegrableOn_of_locallyIntegrable_restrict (hu.locallyIntegrable (by norm_num)),
        locallyIntegrableOn_of_locallyIntegrable_restrict (hdu.locallyIntegrable (by norm_num)), ?_⟩
      intro ψ hs hc ht i
      let dψ : E2 → ℝ := fun x => fderiv ℝ ψ x (coordinateVector 2 i)
      have hψ : MemLp ψ 2 μ := (hs.continuous.memLp_of_hasCompactSupport (μ := volume) hc).restrict U
      have hdψ : MemLp dψ 2 μ :=
        (((hs.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
          (μ := volume) (hc.fderiv_apply ℝ (coordinateVector 2 i))).restrict U
      let project : Lp E2 2 μ →L[ℝ] Lp ℝ 2 μ := (EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 μ
      let F : Pair U → ℝ := fun q =>
        inner ℝ q.fst (hdψ.toLp dψ) + inner ℝ (project q.snd) (hψ.toLp ψ)
      have cf : Continuous (fun q : Pair U => q.fst) := WithLp.continuous_fst 2 (Lp ℝ 2 μ) (Lp E2 2 μ)
      have cs : Continuous (fun q : Pair U => q.snd) := WithLp.continuous_snd 2 (Lp ℝ 2 μ) (Lp E2 2 μ)
      have cF : Continuous F := (cf.inner continuous_const).add
        ((project.continuous.comp cs).inner continuous_const)
      have eqF (v : E2 → ℝ) (dv : E2 → E2) (hv : MemLp v 2 μ) (hdv : MemLp dv 2 μ) :
          F (pack U v dv hv hdv) =
            (∫ x in U, v x * fderiv ℝ ψ x (coordinateVector 2 i)) +
              ∫ x in U, dv x i * ψ x := by
        have first : inner ℝ (hv.toLp v) (hdψ.toLp dψ) = ∫ x, v x * dψ x ∂μ := by
          rw [L2.inner_def]
          apply integral_congr_ae
          filter_upwards [hv.coeFn_toLp, hdψ.coeFn_toLp] with x hx hdx
          rw [hx, hdx, Real.inner_apply]
        have second : inner ℝ (project (hdv.toLp dv)) (hψ.toLp ψ) = ∫ x, dv x i * ψ x ∂μ := by
          rw [L2.inner_def]
          apply integral_congr_ae
          filter_upwards [(EuclideanSpace.proj (𝕜 := ℝ) i).coeFn_compLpL (p := 2) (μ := μ) (hdv.toLp dv),
            hdv.coeFn_toLp, hψ.coeFn_toLp] with x hx hdx hψx
          change inner ℝ (((EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 μ (hdv.toLp dv)) x)
            ((hψ.toLp ψ) x) = _
          rw [hx, hdx, hψx, Real.inner_apply]
          rfl
        change inner ℝ (hv.toLp v) (hdψ.toLp dψ) +
          inner ℝ (project (hdv.toLp dv)) (hψ.toLp ψ) = _
        rw [first, second]
      have zero_on : SmoothGraph U ⊆ {q : Pair U | F q = 0} := by
        rintro q ⟨φ, hφ, hg, hφs, hφc, hφt, rfl⟩
        change F (pack U φ (planarGradient φ) hφ hg) = 0
        rw [eqF]
        have hw := (halfdisc_native_smooth_h10_v468 R φ hφs hφc hφt).1.1.2.2 ψ hs hc ht i
        linarith
      have zero_at : F p = 0 := (closure_minimal zero_on (isClosed_eq cF continuous_const)) hclosure
      change F (pack U u du hu hdu) = 0 at zero_at
      rw [eqF] at zero_at
      linarith
    · intro ε hε
      obtain ⟨q, hq, hdist⟩ := Metric.mem_closure_iff.mp hclosure (Real.sqrt ε) (Real.sqrt_pos.mpr hε)
      obtain ⟨φ, hφ, hg, hs, hc, ht, rfl⟩ := hq
      refine ⟨φ, hs, hc, ht, ?_⟩
      rw [← energy φ hφ hg]
      have hh := (sq_lt_sq₀ (dist_nonneg) (Real.sqrt_nonneg ε)).mpr hdist
      rwa [Real.sq_sqrt hε.le] at hh


end SeifertSurfaces.OriginalEndpoints.B1Tangency

namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open ChartMetricProvider.Variational.IsothermalPDELower.NativeDirichlet

theorem halfdisc_native_smooth_h10_export_v468 (R : ℝ)
    (φ : E2 → ℝ) (hs : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (ht : tsupport φ ⊆ halfDisc R) :
    H10On (halfDisc R) φ (planarGradient φ) := halfdisc_native_smooth_h10_v468 R φ hs hc ht

theorem halfdisc_smoothGraph_span_export_v468 (R : ℝ) :
    (Submodule.span ℝ (SmoothGraph (halfDisc R)) : Set (Pair (halfDisc R))) =
      SmoothGraph (halfDisc R) := halfdisc_smoothGraph_span_v468 R

theorem halfdisc_nativeH10_iff_pair_mem_export_v468 (R : ℝ)
    (u : E2 → ℝ) (du : E2 → E2)
    (hu : MemLp u 2 (volume.restrict (halfDisc R)))
    (hdu : MemLp du 2 (volume.restrict (halfDisc R))) :
    H10On (halfDisc R) u du ↔
      pack (halfDisc R) u du hu hdu ∈ space (halfDisc R) := halfdisc_nativeH10_iff_pair_mem_v468 R u du hu hdu

end SeifertSurfaces.OriginalEndpoints.B1Tangency
