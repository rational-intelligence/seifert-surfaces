import B1L1DirectWeakLower
import BoundaryPotentialB00B02
import BoundarySupport
import DifferentialGeometry.Analysis.Elliptic.Euclidean.Regularity.Harmonic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import NativeH10DirichletData
set_option maxHeartbeats 5000000
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak
open SeifertSurfaces.AppendixACoordinates BoundaryPotentialLower BoundarySupport
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.NativeDirichlet
namespace BoundaryContinuation
theorem zero_extension (U : Set E2) (hU : MeasurableSet U) (phi : E2 → ℝ) (dphi : E2 → E2)
    (hphi : H10On U phi dphi) :
    H10On univ (U.indicator phi) (U.indicator dphi) := by
  classical
  have hbridge : ∀ (U : Set E2) (u : E2 → ℝ) (du : E2 → E2)
      (hu : MemLp u 2 (volume.restrict U)) (hdu : MemLp du 2 (volume.restrict U)),
      H10On U u du ↔ pack U u du hu hdu ∈ space U := by
    intro U u du hu hdu
    classical
    have smooth (φ : E2 → ℝ) (hs : ContDiff ℝ ∞ φ)
        (hc : HasCompactSupport φ) (ht : tsupport φ ⊆ U) :
        H10On U φ (planarGradient φ) := by
        classical
        have hgcont : Continuous (planarGradient φ) := continuous_planarGradient hs
        have hgcompact : HasCompactSupport (planarGradient φ) := by
          apply hc.of_isClosed_subset (isClosed_tsupport _)
          apply closure_minimal _ (isClosed_tsupport φ)
          intro x hx
          by_contra h
          exact hx (planarGradient_eq_zero_off_support φ h)
        have huLp : MemLp φ 2 (volume.restrict (U)) :=
          (hs.continuous.memLp_of_hasCompactSupport (μ := volume) hc).restrict _
        have hgLp : MemLp (planarGradient φ) 2 (volume.restrict (U)) :=
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
            have hdsub : tsupport (fun x => fderiv ℝ ψ x (coordinateVector 2 i)) ⊆ U :=
              (tsupport_fderiv_apply_subset ℝ (coordinateVector 2 i)).trans htψ
            rw [show fderiv ℝ ψ x (coordinateVector 2 i) = 0 from
              image_eq_zero_of_notMem_tsupport (f := fun x => fderiv ℝ ψ x (coordinateVector 2 i))
                (fun h => hx (hdsub h)), mul_zero]
        · intro ε hε
          refine ⟨φ, hs, hc, ht, ?_⟩
          simpa using hε
    have span_eq : (Submodule.span ℝ (SmoothGraph U) : Set (Pair U)) = SmoothGraph U := by
      have hzero : (0 : Pair U) ∈ SmoothGraph U := by { have hg : planarGradient (0 : E2 → ℝ) = 0 := by { funext x; simp [planarGradient] }; have hglp : MemLp (planarGradient (0 : E2 → ℝ)) 2 (volume.restrict U) := by { rw [hg]; exact MemLp.zero }; refine ⟨0, MemLp.zero, hglp, contDiff_const, HasCompactSupport.zero, ?_, ?_⟩; { simp }; { unfold pack; simp only [hg, MemLp.toLp_zero]; rfl } }; have hadd : ∀ p q : Pair U, p ∈ SmoothGraph U → q ∈ SmoothGraph U → p + q ∈ SmoothGraph U := by { rintro p q ⟨φ, hφ, hgφ, hsφ, hcφ, htφ, rfl⟩ ⟨ψ, hψ, hgψ, hsψ, hcψ, htψ, rfl⟩; have hg : planarGradient (φ + ψ) = planarGradient φ + planarGradient ψ := by { funext x; unfold planarGradient; rw [fderiv_add (hsφ.differentiable (by simp) x) (hsψ.differentiable (by simp) x)]; simp only [ContinuousLinearMap.add_apply, add_smul, Finset.sum_add_distrib, Pi.add_apply] }; have hglp : MemLp (planarGradient (φ + ψ)) 2 (volume.restrict U) := by { rw [hg]; exact hgφ.add hgψ }; refine ⟨φ + ψ, hφ.add hψ, hglp, hsφ.add hsψ, hcφ.add hcψ, ?_, ?_⟩; { exact (tsupport_add φ ψ).trans (union_subset htφ htψ) }; { unfold pack; simp only [hg]; rfl } }; have hsmul : ∀ (a : ℝ) (p : Pair U), p ∈ SmoothGraph U → a • p ∈ SmoothGraph U := by { rintro a p ⟨φ, hφ, hgφ, hsφ, hcφ, htφ, rfl⟩; have hg : planarGradient (a • φ) = a • planarGradient φ := by { funext x; unfold planarGradient; rw [fderiv_const_smul (hsφ.differentiable (by simp) x)]; simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, Pi.smul_apply, mul_smul, Finset.smul_sum] }; have hglp : MemLp (planarGradient (a • φ)) 2 (volume.restrict U) := by { rw [hg]; exact hgφ.const_smul a }; refine ⟨a • φ, hφ.const_smul a, hglp, contDiff_const.smul hsφ, hcφ.smul_left, ?_, ?_⟩; { exact (tsupport_smul_subset_right (fun _ : E2 => a) φ).trans htφ }; { unfold pack; simp only [hg]; rfl } }; let S : Submodule ℝ (Pair U) := { carrier := SmoothGraph U, zero_mem' := hzero, add_mem' := hadd _ _, smul_mem' := hsmul }; exact congrArg (fun T : Submodule ℝ (Pair U) => (T : Set (Pair U))) (Submodule.span_eq S)
    classical
    let μ := volume.restrict U
    let p : Pair U := pack U u du hu hdu
    have space_eq : (space U : Set (Pair U)) = closure (SmoothGraph U) := by
      rw [Submodule.topologicalClosure_coe, span_eq]
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
      have hφ := (smooth φ hs hc ht).1.2.1
      have hg := (smooth φ hs hc ht).1.2.2
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
          have hw := (smooth φ hφs hφc hφt).1.1.2.2 ψ hs hc ht i
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
  let u := U.indicator phi
  let du := U.indicator dphi
  have hu : MemLp u 2 volume := (memLp_indicator_iff_restrict hU.nullMeasurableSet).mpr hphi.1.2.1
  have hdu : MemLp du 2 volume := (memLp_indicator_iff_restrict hU.nullMeasurableSet).mpr hphi.1.2.2
  have hum : MemLp u 2 (volume.restrict univ) := by simpa only [Measure.restrict_univ] using hu
  have hdum : MemLp du 2 (volume.restrict univ) := by simpa only [Measure.restrict_univ] using hdu
  let p : Pair univ := pack univ u du hum hdum
  have energy (φ : E2 → ℝ) (hφ : MemLp φ 2 (volume.restrict univ))
      (hg : MemLp (planarGradient φ) 2 (volume.restrict univ)) :
      dist p (pack univ φ (planarGradient φ) hφ hg) ^ 2 =
        ∫ x in univ, |u x - φ x| ^ 2 + ‖du x - planarGradient φ x‖ ^ 2 := by
    have scalar_sq : ‖hum.toLp u - hφ.toLp φ‖ ^ 2 = ∫ x, |u x - φ x| ^ 2 ∂(volume.restrict univ) := by
      rw [← MemLp.toLp_sub, ← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [(hum.sub hφ).coeFn_toLp] with x hx
      rw [hx, Real.inner_apply]
      change (u x - φ x) * (u x - φ x) = |u x - φ x| ^ 2
      rw [sq_abs]
      ring
    have vector_sq : ‖hdum.toLp du - hg.toLp (planarGradient φ)‖ ^ 2 =
        ∫ x, ‖du x - planarGradient φ x‖ ^ 2 ∂(volume.restrict univ) := by
      rw [← MemLp.toLp_sub, ← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [(hdum.sub hg).coeFn_toLp] with x hx
      rw [hx, real_inner_self_eq_norm_sq]
      rfl
    rw [dist_eq_norm, WithLp.prod_norm_sq_eq_of_L2]
    change ‖hum.toLp u - hφ.toLp φ‖ ^ 2 + ‖hdum.toLp du - hg.toLp (planarGradient φ)‖ ^ 2 = _
    rw [scalar_sq, vector_sq]
    have hs : Integrable (fun x => |u x - φ x| ^ 2) (volume.restrict univ) := by
      exact ((hum.sub hφ).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).congr
        (Filter.Eventually.of_forall fun x => by simp only [Real.norm_eq_abs, Pi.sub_apply])
    have hv : Integrable (fun x => ‖du x - planarGradient φ x‖ ^ 2) (volume.restrict univ) :=
      (hdum.sub hg).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
    exact (integral_add hs hv).symm
  apply (hbridge _ _ _ hum hdum).mpr
  change p ∈ (space univ : Set (Pair univ))
  rw [Submodule.topologicalClosure_coe]
  apply (closure_mono (show SmoothGraph univ ⊆ (Submodule.span ℝ (SmoothGraph univ) : Set (Pair univ)) from
    Submodule.subset_span))
  apply Metric.mem_closure_iff.mpr
  intro eps heps
  obtain ⟨psi,hs,hc,ht,herr⟩ := hphi.2 (eps ^ 2) (sq_pos_of_pos heps)
  have hgc : HasCompactSupport (planarGradient psi) := by
    apply hc.mono'
    intro y hy
    by_contra hn
    exact hy (planarGradient_eq_zero_off_support _ hn)
  have hp : MemLp psi 2 (volume.restrict univ) := (hs.continuous.memLp_of_hasCompactSupport hc).restrict univ
  have hgp : MemLp (planarGradient psi) 2 (volume.restrict univ) :=
    ((continuous_planarGradient hs).memLp_of_hasCompactSupport hgc).restrict univ
  refine ⟨pack univ _ _ hp hgp,⟨_,hp,hgp,hs,hc,subset_univ _,rfl⟩,?_⟩
  have heq (y : E2) : |u y - psi y| ^ 2 + ‖du y - planarGradient psi y‖ ^ 2 =
      U.indicator (fun y => |phi y - psi y| ^ 2 + ‖dphi y - planarGradient psi y‖ ^ 2) y := by
    by_cases hy : y ∈ U
    · simp only [u,du,indicator_of_mem hy]
    · have hz : psi y = 0 := image_eq_zero_of_notMem_tsupport (fun hn => hy (ht hn))
      have hgz : planarGradient psi y = 0 := planarGradient_eq_zero_off_support psi (fun hn => hy (ht hn))
      simp [u,du,hy,hz,hgz]
  have hsquare : dist p (pack univ _ _ hp hgp) ^ 2 < eps ^ 2 := by
    rw [energy psi hp hgp]
    simp_rw [heq]
    rw [Measure.restrict_univ,integral_indicator hU]
    exact herr
  exact (sq_lt_sq₀ dist_nonneg heps.le).mp hsquare


theorem linear_h1_pullback (U : Set E2) (P : E2 ≃L[ℝ] E2) (u : E2 → ℝ) (du : E2 → E2)
    (hu : H1On U u du) :
    H1On (P ⁻¹' U) (fun y => u (P y))
      (fun y => P.toContinuousLinearMap.adjoint (du (P y))) := by
  have hmap : Measure.map P (volume.restrict (P ⁻¹' U)) =
      ENNReal.ofReal |(LinearMap.det P.toLinearMap)⁻¹| • volume.restrict U := by
    have he : MeasurableEmbedding (P : E2 → E2) := P.toHomeomorph.toMeasurableEquiv.measurableEmbedding
    have hm : Measure.map P volume = ENNReal.ofReal |(LinearMap.det P.toLinearMap)⁻¹| • volume :=
      Measure.map_linearMap_addHaar_eq_smul_addHaar volume P.toLinearEquiv.isUnit_det'.ne_zero
    rw [← he.restrict_map,hm,Measure.restrict_smul]
  have hlp {E : Type} [NormedAddCommGroup E] (f : E2 → E) (hf : MemLp f 2 (volume.restrict U)) :
      MemLp (fun y => f (P y)) 2 (volume.restrict (P ⁻¹' U)) := by
    have hm : MemLp f 2 (Measure.map P (volume.restrict (P ⁻¹' U))) := by
      rw [hmap]
      exact hf.smul_measure ENNReal.ofReal_ne_top
    exact hm.comp_of_map P.continuous.measurable.aemeasurable
  have hint (f : E2 → ℝ) : (∫ y in P ⁻¹' U, f (P y)) =
      |(LinearMap.det P.toLinearMap)⁻¹| * ∫ x in U, f x := by
    have he : MeasurableEmbedding (P : E2 → E2) := P.toHomeomorph.toMeasurableEquiv.measurableEmbedding
    rw [← he.integral_map,hmap,integral_smul_measure,ENNReal.toReal_ofReal (abs_nonneg _)]
    rfl
  have csum (L : E2 →L[ℝ] ℝ) (v : E2) : L v = ∑ i : Fin 2, v i * L (EuclideanSpace.single i 1) := by
    have hv : (∑ i : Fin 2, v i • EuclideanSpace.single i 1) = v := by
      ext j
      fin_cases j <;> simp
    calc
      _ = L (∑ i : Fin 2, v i • EuclideanSpace.single i 1) := congrArg L hv.symm
      _ = _ := by simp
  have hdir (φ : E2 → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
      (hφΩ : tsupport φ ⊆ U) (v : E2) :
      (∫ x in U, u x * fderiv ℝ φ x v) = -∫ x in U, inner ℝ (du x) v * φ x := by
    let Ω := U
    let h := u
    have hw (i : Fin 2) : (∫ x in Ω, h x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        -∫ x in Ω, du x i * φ x := by
      simpa only [coordinateVector] using hu.1.2.2 φ hφ hφc hφΩ i
    have hD (i : Fin 2) : MemLp (fun x => (fderiv ℝ φ x) (EuclideanSpace.single i 1))
        2 (volume.restrict Ω) := by
      have hd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ φ) := hφ.fderiv_right (by simp)
      exact ((hd.clm_apply contDiff_const).continuous.memLp_of_hasCompactSupport
        (hφc.fderiv_apply (𝕜 := ℝ) _)).restrict Ω
    have hp : MemLp φ 2 (volume.restrict Ω) :=
      (hφ.continuous.memLp_of_hasCompactSupport hφc).restrict Ω
    have hL (i : Fin 2) : Integrable (fun x => v i * (h x *
        (fderiv ℝ φ x) (EuclideanSpace.single i 1))) (volume.restrict Ω) :=
      (hu.2.1.integrable_mul (hD i)).const_mul (v i)
    have hG (i : Fin 2) : Integrable (fun x => v i * (du x i * φ x))
        (volume.restrict Ω) := (hu.2.2.eval_piLp i |>.integrable_mul hp).const_mul (v i)
    have hinner (x : E2) : inner ℝ (du x) v = ∑ i : Fin 2, v i * du x i := by
      simp [PiLp.inner_apply]
    have he : (fun x => h x * (fderiv ℝ φ x) v) =
        fun x => ∑ i : Fin 2, v i * (h x * (fderiv ℝ φ x) (EuclideanSpace.single i 1)) := by
      funext x
      rw [csum]
      simp only [Fin.sum_univ_two]
      ring
    rw [he]
    simp_rw [hinner, Finset.sum_mul, mul_assoc]
    rw [integral_finsetSum _ (fun i _ => hL i), integral_finsetSum _ (fun i _ => hG i)]
    simp_rw [integral_const_mul, hw _, mul_neg, Finset.sum_neg_distrib]
  have hval : MemLp (fun y => u (P y)) 2 (volume.restrict (P ⁻¹' U)) := hlp u hu.2.1
  have hgrad : MemLp (fun y => P.toContinuousLinearMap.adjoint (du (P y))) 2
      (volume.restrict (P ⁻¹' U)) := (hlp du hu.2.2).continuousLinearMap_comp P.toContinuousLinearMap.adjoint
  refine ⟨⟨locallyIntegrableOn_of_locallyIntegrable_restrict (hval.locallyIntegrable (by norm_num)),
    locallyIntegrableOn_of_locallyIntegrable_restrict (hgrad.locallyIntegrable (by norm_num)),?_⟩,hval,hgrad⟩
  intro phi hs hc ht i
  let psi : E2 → ℝ := fun x => phi (P.symm x)
  have hps : ContDiff ℝ ∞ psi := hs.comp P.symm.contDiff
  have hpc : HasCompactSupport psi := hc.comp_homeomorph P.symm.toHomeomorph
  have hpt : tsupport psi ⊆ U := by
    rw [show psi = phi ∘ P.symm.toHomeomorph from rfl,tsupport_comp_eq_preimage]
    intro x hx
    have h := ht hx
    simpa using h
  have hdpsi (x : E2) : fderiv ℝ psi x = (fderiv ℝ phi (P.symm x)).comp P.symm.toContinuousLinearMap :=
    ((hs.differentiable (by simp) (P.symm x)).hasFDerivAt.comp x P.symm.hasFDerivAt).fderiv
  have hid (y : E2) : fderiv ℝ phi y (coordinateVector 2 i) =
      fderiv ℝ psi (P y) (P (coordinateVector 2 i)) := by rw [hdpsi]; simp
  have hp (y : E2) : psi (P y) = phi y := by simp [psi]
  have hadj (y : E2) : P.toContinuousLinearMap.adjoint (du (P y)) i =
      inner ℝ (du (P y)) (P (coordinateVector 2 i)) := by
    calc
      _ = inner ℝ (P.toContinuousLinearMap.adjoint (du (P y))) (EuclideanSpace.single i 1) := by
        simp [EuclideanSpace.inner_single_right]
      _ = _ := by rw [ContinuousLinearMap.adjoint_inner_left]; rfl
  simp_rw [hid,hadj,← hp]
  rw [hint (fun x => u x * fderiv ℝ psi x (P (coordinateVector 2 i))),
    hint (fun x => inner ℝ (du x) (P (coordinateVector 2 i)) * psi x),
    hdir psi hps hpc hpt (P (coordinateVector 2 i)),mul_neg]


theorem linear_h10_pullback (U : Set E2) (P : E2 ≃L[ℝ] E2) (u : E2 → ℝ) (du : E2 → E2)
    (hu : H10On U u du) :
    H10On (P ⁻¹' U) (fun y => u (P y))
      (fun y => P.toContinuousLinearMap.adjoint (du (P y))) := by
  have hH1 : H1On (P ⁻¹' U) (fun y => u (P y))
      (fun y => P.toContinuousLinearMap.adjoint (du (P y))) := by
    have hu : H1On U u du := hu.1
    have hmap : Measure.map P (volume.restrict (P ⁻¹' U)) =
        ENNReal.ofReal |(LinearMap.det P.toLinearMap)⁻¹| • volume.restrict U := by
      have he : MeasurableEmbedding (P : E2 → E2) := P.toHomeomorph.toMeasurableEquiv.measurableEmbedding
      have hm : Measure.map P volume = ENNReal.ofReal |(LinearMap.det P.toLinearMap)⁻¹| • volume :=
        Measure.map_linearMap_addHaar_eq_smul_addHaar volume P.toLinearEquiv.isUnit_det'.ne_zero
      rw [← he.restrict_map,hm,Measure.restrict_smul]
    have hlp {E : Type} [NormedAddCommGroup E] (f : E2 → E) (hf : MemLp f 2 (volume.restrict U)) :
        MemLp (fun y => f (P y)) 2 (volume.restrict (P ⁻¹' U)) := by
      have hm : MemLp f 2 (Measure.map P (volume.restrict (P ⁻¹' U))) := by
        rw [hmap]
        exact hf.smul_measure ENNReal.ofReal_ne_top
      exact hm.comp_of_map P.continuous.measurable.aemeasurable
    have hint (f : E2 → ℝ) : (∫ y in P ⁻¹' U, f (P y)) =
        |(LinearMap.det P.toLinearMap)⁻¹| * ∫ x in U, f x := by
      have he : MeasurableEmbedding (P : E2 → E2) := P.toHomeomorph.toMeasurableEquiv.measurableEmbedding
      rw [← he.integral_map,hmap,integral_smul_measure,ENNReal.toReal_ofReal (abs_nonneg _)]
      rfl
    have csum (L : E2 →L[ℝ] ℝ) (v : E2) : L v = ∑ i : Fin 2, v i * L (EuclideanSpace.single i 1) := by
      have hv : (∑ i : Fin 2, v i • EuclideanSpace.single i 1) = v := by
        ext j
        fin_cases j <;> simp
      calc
        _ = L (∑ i : Fin 2, v i • EuclideanSpace.single i 1) := congrArg L hv.symm
        _ = _ := by simp
    have hdir (φ : E2 → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
        (hφΩ : tsupport φ ⊆ U) (v : E2) :
        (∫ x in U, u x * fderiv ℝ φ x v) = -∫ x in U, inner ℝ (du x) v * φ x := by
      let Ω := U
      let h := u
      have hw (i : Fin 2) : (∫ x in Ω, h x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
          -∫ x in Ω, du x i * φ x := by
        simpa only [coordinateVector] using hu.1.2.2 φ hφ hφc hφΩ i
      have hD (i : Fin 2) : MemLp (fun x => (fderiv ℝ φ x) (EuclideanSpace.single i 1))
          2 (volume.restrict Ω) := by
        have hd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ φ) := hφ.fderiv_right (by simp)
        exact ((hd.clm_apply contDiff_const).continuous.memLp_of_hasCompactSupport
          (hφc.fderiv_apply (𝕜 := ℝ) _)).restrict Ω
      have hp : MemLp φ 2 (volume.restrict Ω) :=
        (hφ.continuous.memLp_of_hasCompactSupport hφc).restrict Ω
      have hL (i : Fin 2) : Integrable (fun x => v i * (h x *
          (fderiv ℝ φ x) (EuclideanSpace.single i 1))) (volume.restrict Ω) :=
        (hu.2.1.integrable_mul (hD i)).const_mul (v i)
      have hG (i : Fin 2) : Integrable (fun x => v i * (du x i * φ x))
          (volume.restrict Ω) := (hu.2.2.eval_piLp i |>.integrable_mul hp).const_mul (v i)
      have hinner (x : E2) : inner ℝ (du x) v = ∑ i : Fin 2, v i * du x i := by
        simp [PiLp.inner_apply]
      have he : (fun x => h x * (fderiv ℝ φ x) v) =
          fun x => ∑ i : Fin 2, v i * (h x * (fderiv ℝ φ x) (EuclideanSpace.single i 1)) := by
        funext x
        rw [csum]
        simp only [Fin.sum_univ_two]
        ring
      rw [he]
      simp_rw [hinner, Finset.sum_mul, mul_assoc]
      rw [integral_finsetSum _ (fun i _ => hL i), integral_finsetSum _ (fun i _ => hG i)]
      simp_rw [integral_const_mul, hw _, mul_neg, Finset.sum_neg_distrib]
    have hval : MemLp (fun y => u (P y)) 2 (volume.restrict (P ⁻¹' U)) := hlp u hu.2.1
    have hgrad : MemLp (fun y => P.toContinuousLinearMap.adjoint (du (P y))) 2
        (volume.restrict (P ⁻¹' U)) := (hlp du hu.2.2).continuousLinearMap_comp P.toContinuousLinearMap.adjoint
    refine ⟨⟨locallyIntegrableOn_of_locallyIntegrable_restrict (hval.locallyIntegrable (by norm_num)),
      locallyIntegrableOn_of_locallyIntegrable_restrict (hgrad.locallyIntegrable (by norm_num)),?_⟩,hval,hgrad⟩
    intro phi hs hc ht i
    let psi : E2 → ℝ := fun x => phi (P.symm x)
    have hps : ContDiff ℝ ∞ psi := hs.comp P.symm.contDiff
    have hpc : HasCompactSupport psi := hc.comp_homeomorph P.symm.toHomeomorph
    have hpt : tsupport psi ⊆ U := by
      rw [show psi = phi ∘ P.symm.toHomeomorph from rfl,tsupport_comp_eq_preimage]
      intro x hx
      have h := ht hx
      simpa using h
    have hdpsi (x : E2) : fderiv ℝ psi x = (fderiv ℝ phi (P.symm x)).comp P.symm.toContinuousLinearMap :=
      ((hs.differentiable (by simp) (P.symm x)).hasFDerivAt.comp x P.symm.hasFDerivAt).fderiv
    have hid (y : E2) : fderiv ℝ phi y (coordinateVector 2 i) =
        fderiv ℝ psi (P y) (P (coordinateVector 2 i)) := by rw [hdpsi]; simp
    have hp (y : E2) : psi (P y) = phi y := by simp [psi]
    have hadj (y : E2) : P.toContinuousLinearMap.adjoint (du (P y)) i =
        inner ℝ (du (P y)) (P (coordinateVector 2 i)) := by
      calc
        _ = inner ℝ (P.toContinuousLinearMap.adjoint (du (P y))) (EuclideanSpace.single i 1) := by
          simp [EuclideanSpace.inner_single_right]
        _ = _ := by rw [ContinuousLinearMap.adjoint_inner_left]; rfl
    simp_rw [hid,hadj,← hp]
    rw [hint (fun x => u x * fderiv ℝ psi x (P (coordinateVector 2 i))),
      hint (fun x => inner ℝ (du x) (P (coordinateVector 2 i)) * psi x),
      hdir psi hps hpc hpt (P (coordinateVector 2 i)),mul_neg]
  have hmap : Measure.map P (volume.restrict (P ⁻¹' U)) =
      ENNReal.ofReal |(LinearMap.det P.toLinearMap)⁻¹| • volume.restrict U := by
    have he : MeasurableEmbedding (P : E2 → E2) := P.toHomeomorph.toMeasurableEquiv.measurableEmbedding
    have hm : Measure.map P volume = ENNReal.ofReal |(LinearMap.det P.toLinearMap)⁻¹| • volume :=
      Measure.map_linearMap_addHaar_eq_smul_addHaar volume P.toLinearEquiv.isUnit_det'.ne_zero
    rw [← he.restrict_map,hm,Measure.restrict_smul]
  have hint (f : E2 → ℝ) : (∫ y in P ⁻¹' U, f (P y)) =
      |(LinearMap.det P.toLinearMap)⁻¹| * ∫ x in U, f x := by
    have he : MeasurableEmbedding (P : E2 → E2) := P.toHomeomorph.toMeasurableEquiv.measurableEmbedding
    rw [← he.integral_map,hmap,integral_smul_measure,ENNReal.toReal_ofReal (abs_nonneg _)]
    rfl
  have hlp {E : Type} [NormedAddCommGroup E] (f : E2 → E) (hf : MemLp f 2 (volume.restrict U)) :
      MemLp (fun y => f (P y)) 2 (volume.restrict (P ⁻¹' U)) := by
    have hm : MemLp f 2 (Measure.map P (volume.restrict (P ⁻¹' U))) := by
      rw [hmap]
      exact hf.smul_measure ENNReal.ofReal_ne_top
    exact hm.comp_of_map P.continuous.measurable.aemeasurable
  have pair_grad (psi : E2 → ℝ) (y q : E2) : inner ℝ (planarGradient psi y) q = fderiv ℝ psi y q := by
    have hq : q = q 0 • coordinateVector 2 0 + q 1 • coordinateVector 2 1 := by
      ext i
      fin_cases i <;> simp [coordinateVector]
    conv_rhs => rw [hq]
    rw [map_add,map_smul,map_smul]
    simp only [PiLp.inner_apply,Fin.sum_univ_two,RCLike.inner_apply,conj_trivial]
    have hg (i : Fin 2) : planarGradient psi y i = fderiv ℝ psi y (coordinateVector 2 i) := by
      fin_cases i <;> simp [planarGradient,coordinateVector,Fin.sum_univ_two,EuclideanSpace.single]
    rw [hg,hg]
    simp only [smul_eq_mul]
  have hchain (psi : E2 → ℝ) (hs : ContDiff ℝ ∞ psi) (y : E2) :
      planarGradient (fun x => psi (P x)) y = P.toContinuousLinearMap.adjoint (planarGradient psi (P y)) := by
    apply ext_inner_right ℝ
    intro q
    rw [pair_grad,ContinuousLinearMap.adjoint_inner_left,pair_grad]
    change (fderiv ℝ (psi ∘ P) y) q = (fderiv ℝ psi (P y)) (P q)
    rw [((hs.differentiable (by simp) (P y)).hasFDerivAt.comp y P.hasFDerivAt).fderiv]
    rfl
  let J : ℝ := |(LinearMap.det P.toLinearMap)⁻¹|
  let C : ℝ := ‖P.toContinuousLinearMap.adjoint‖ ^ 2 + 1
  let D : ℝ := (J + 1) * C
  have hJ : 0 ≤ J := abs_nonneg _
  have hC : 0 < C := by dsimp only [C]; positivity
  have hD : 0 < D := mul_pos (by positivity) hC
  refine ⟨hH1,?_⟩
  intro eps heps
  obtain ⟨psi,hs,hc,ht,herr⟩ := hu.2 (eps / D) (div_pos heps hD)
  have hps : ContDiff ℝ ∞ (fun y => psi (P y)) := hs.comp P.contDiff
  have hpc : HasCompactSupport (fun y => psi (P y)) := hc.comp_homeomorph P.toHomeomorph
  have hpt : tsupport (fun y => psi (P y)) ⊆ P ⁻¹' U := by
    rw [show (fun y => psi (P y)) = psi ∘ P.toHomeomorph from rfl,tsupport_comp_eq_preimage]
    exact preimage_mono ht
  refine ⟨fun y => psi (P y),hps,hpc,hpt,?_⟩
  have hgpcompact : HasCompactSupport (planarGradient psi) := by
    apply hc.mono'
    intro y hy
    by_contra hn
    exact hy (planarGradient_eq_zero_off_support _ hn)
  have hgp : MemLp (planarGradient psi) 2 (volume.restrict U) :=
    ((continuous_planarGradient hs).memLp_of_hasCompactSupport hgpcompact).restrict U
  have hpm : MemLp psi 2 (volume.restrict U) := (hs.continuous.memLp_of_hasCompactSupport hc).restrict U
  have hscalar := hlp _ (hu.1.2.1.sub hpm)
  have hvector := hlp _ (hu.1.2.2.sub hgp)
  have hpointgrad (y : E2) :
      P.toContinuousLinearMap.adjoint (du (P y)) - planarGradient (fun x => psi (P x)) y =
      P.toContinuousLinearMap.adjoint (du (P y) - planarGradient psi (P y)) := by
    rw [hchain psi hs,map_sub]
  have hscalarInt : IntegrableOn (fun y => |u (P y) - psi (P y)| ^ 2) (P ⁻¹' U) := by
    simpa only [IntegrableOn,sq_abs,Pi.sub_apply] using hscalar.integrable_sq
  have hleft : IntegrableOn
      (fun y => |u (P y) - psi (P y)| ^ 2 +
        ‖P.toContinuousLinearMap.adjoint (du (P y)) - planarGradient (fun x => psi (P x)) y‖ ^ 2)
      (P ⁻¹' U) := by
    simp_rw [hpointgrad]
    exact hscalarInt.add
      ((hvector.continuousLinearMap_comp P.toContinuousLinearMap.adjoint).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))
  have herrInt : IntegrableOn (fun y => |u y - psi y| ^ 2 + ‖du y - planarGradient psi y‖ ^ 2) U := by
    simp only [sq_abs]
    exact ((hu.1.2.1.sub hpm).integrable_sq).add
      ((hu.1.2.2.sub hgp).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))
  have hrpulled := hlp _ (hu.1.2.1.sub hpm)
  have hright : IntegrableOn (fun y => C * (|u (P y) - psi (P y)| ^ 2 +
      ‖du (P y) - planarGradient psi (P y)‖ ^ 2)) (P ⁻¹' U) := by
    apply Integrable.const_mul
    exact hscalarInt.add
      (hvector.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))
  have hi := integral_mono hleft hright (fun y => by
    rw [hpointgrad]
    have hn := P.toContinuousLinearMap.adjoint.le_opNorm (du (P y) - planarGradient psi (P y))
    have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn
    dsimp only [C]
    nlinarith only [hs,mul_nonneg (sq_nonneg ‖P.toContinuousLinearMap.adjoint‖) (sq_nonneg |u (P y) - psi (P y)|),
      sq_nonneg |u (P y) - psi (P y)|,sq_nonneg ‖du (P y) - planarGradient psi (P y)‖])
  rw [integral_const_mul,hint (fun y => |u y - psi y| ^ 2 + ‖du y - planarGradient psi y‖ ^ 2)] at hi
  have hE : 0 ≤ ∫ y in U, |u y - psi y| ^ 2 + ‖du y - planarGradient psi y‖ ^ 2 :=
    integral_nonneg fun y => add_nonneg (sq_nonneg _) (sq_nonneg _)
  calc
    _ ≤ C * (J * (∫ y in U, |u y - psi y| ^ 2 + ‖du y - planarGradient psi y‖ ^ 2)) := hi
    _ ≤ D * (∫ y in U, |u y - psi y| ^ 2 + ‖du y - planarGradient psi y‖ ^ 2) := by
      dsimp only [D]
      nlinarith only [mul_nonneg hC.le hE]
    _ < eps := by
      have hh := mul_lt_mul_of_pos_left herr hD
      rwa [mul_div_cancel₀ _ hD.ne'] at hh


theorem flat_odd_h1 (r : ℝ) (hr : 0 < r) (v : E2 → ℝ) (dv : E2 → E2)
    (htrace : FlatZeroTrace r v dv) :
    ∃ w : E2 → ℝ, ∃ dw : E2 → E2,
      H1On univ w dw ∧
      (∀ y ∈ halfDisc (r/2), w y = v y ∧ dw y = dv y) ∧
      (∀ y : E2, w (reflect y) = -w y) ∧
      (∀ y : E2, y 1 = 0 → w y = 0) := by
  have zeroExt : ∀ (U : Set E2) (hU : MeasurableSet U) (phi : E2 → ℝ) (dphi : E2 → E2),
      H10On U phi dphi → H10On univ (U.indicator phi) (U.indicator dphi) := by
    intro U hU phi dphi hphi
    classical
    have hbridge : ∀ (U : Set E2) (u : E2 → ℝ) (du : E2 → E2)
        (hu : MemLp u 2 (volume.restrict U)) (hdu : MemLp du 2 (volume.restrict U)),
        H10On U u du ↔ pack U u du hu hdu ∈ space U := by
      intro U u du hu hdu
      classical
      have smooth (φ : E2 → ℝ) (hs : ContDiff ℝ ∞ φ)
          (hc : HasCompactSupport φ) (ht : tsupport φ ⊆ U) :
          H10On U φ (planarGradient φ) := by
          classical
          have hgcont : Continuous (planarGradient φ) := continuous_planarGradient hs
          have hgcompact : HasCompactSupport (planarGradient φ) := by
            apply hc.of_isClosed_subset (isClosed_tsupport _)
            apply closure_minimal _ (isClosed_tsupport φ)
            intro x hx
            by_contra h
            exact hx (planarGradient_eq_zero_off_support φ h)
          have huLp : MemLp φ 2 (volume.restrict (U)) :=
            (hs.continuous.memLp_of_hasCompactSupport (μ := volume) hc).restrict _
          have hgLp : MemLp (planarGradient φ) 2 (volume.restrict (U)) :=
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
              have hdsub : tsupport (fun x => fderiv ℝ ψ x (coordinateVector 2 i)) ⊆ U :=
                (tsupport_fderiv_apply_subset ℝ (coordinateVector 2 i)).trans htψ
              rw [show fderiv ℝ ψ x (coordinateVector 2 i) = 0 from
                image_eq_zero_of_notMem_tsupport (f := fun x => fderiv ℝ ψ x (coordinateVector 2 i))
                  (fun h => hx (hdsub h)), mul_zero]
          · intro ε hε
            refine ⟨φ, hs, hc, ht, ?_⟩
            simpa using hε
      have span_eq : (Submodule.span ℝ (SmoothGraph U) : Set (Pair U)) = SmoothGraph U := by
        have hzero : (0 : Pair U) ∈ SmoothGraph U := by { have hg : planarGradient (0 : E2 → ℝ) = 0 := by { funext x; simp [planarGradient] }; have hglp : MemLp (planarGradient (0 : E2 → ℝ)) 2 (volume.restrict U) := by { rw [hg]; exact MemLp.zero }; refine ⟨0, MemLp.zero, hglp, contDiff_const, HasCompactSupport.zero, ?_, ?_⟩; { simp }; { unfold pack; simp only [hg, MemLp.toLp_zero]; rfl } }; have hadd : ∀ p q : Pair U, p ∈ SmoothGraph U → q ∈ SmoothGraph U → p + q ∈ SmoothGraph U := by { rintro p q ⟨φ, hφ, hgφ, hsφ, hcφ, htφ, rfl⟩ ⟨ψ, hψ, hgψ, hsψ, hcψ, htψ, rfl⟩; have hg : planarGradient (φ + ψ) = planarGradient φ + planarGradient ψ := by { funext x; unfold planarGradient; rw [fderiv_add (hsφ.differentiable (by simp) x) (hsψ.differentiable (by simp) x)]; simp only [ContinuousLinearMap.add_apply, add_smul, Finset.sum_add_distrib, Pi.add_apply] }; have hglp : MemLp (planarGradient (φ + ψ)) 2 (volume.restrict U) := by { rw [hg]; exact hgφ.add hgψ }; refine ⟨φ + ψ, hφ.add hψ, hglp, hsφ.add hsψ, hcφ.add hcψ, ?_, ?_⟩; { exact (tsupport_add φ ψ).trans (union_subset htφ htψ) }; { unfold pack; simp only [hg]; rfl } }; have hsmul : ∀ (a : ℝ) (p : Pair U), p ∈ SmoothGraph U → a • p ∈ SmoothGraph U := by { rintro a p ⟨φ, hφ, hgφ, hsφ, hcφ, htφ, rfl⟩; have hg : planarGradient (a • φ) = a • planarGradient φ := by { funext x; unfold planarGradient; rw [fderiv_const_smul (hsφ.differentiable (by simp) x)]; simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, Pi.smul_apply, mul_smul, Finset.smul_sum] }; have hglp : MemLp (planarGradient (a • φ)) 2 (volume.restrict U) := by { rw [hg]; exact hgφ.const_smul a }; refine ⟨a • φ, hφ.const_smul a, hglp, contDiff_const.smul hsφ, hcφ.smul_left, ?_, ?_⟩; { exact (tsupport_smul_subset_right (fun _ : E2 => a) φ).trans htφ }; { unfold pack; simp only [hg]; rfl } }; let S : Submodule ℝ (Pair U) := { carrier := SmoothGraph U, zero_mem' := hzero, add_mem' := hadd _ _, smul_mem' := hsmul }; exact congrArg (fun T : Submodule ℝ (Pair U) => (T : Set (Pair U))) (Submodule.span_eq S)
      classical
      let μ := volume.restrict U
      let p : Pair U := pack U u du hu hdu
      have space_eq : (space U : Set (Pair U)) = closure (SmoothGraph U) := by
        rw [Submodule.topologicalClosure_coe, span_eq]
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
        have hφ := (smooth φ hs hc ht).1.2.1
        have hg := (smooth φ hs hc ht).1.2.2
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
            have hw := (smooth φ hφs hφc hφt).1.1.2.2 ψ hs hc ht i
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
    let u := U.indicator phi
    let du := U.indicator dphi
    have hu : MemLp u 2 volume := (memLp_indicator_iff_restrict hU.nullMeasurableSet).mpr hphi.1.2.1
    have hdu : MemLp du 2 volume := (memLp_indicator_iff_restrict hU.nullMeasurableSet).mpr hphi.1.2.2
    have hum : MemLp u 2 (volume.restrict univ) := by simpa only [Measure.restrict_univ] using hu
    have hdum : MemLp du 2 (volume.restrict univ) := by simpa only [Measure.restrict_univ] using hdu
    let p : Pair univ := pack univ u du hum hdum
    have energy (φ : E2 → ℝ) (hφ : MemLp φ 2 (volume.restrict univ))
        (hg : MemLp (planarGradient φ) 2 (volume.restrict univ)) :
        dist p (pack univ φ (planarGradient φ) hφ hg) ^ 2 =
          ∫ x in univ, |u x - φ x| ^ 2 + ‖du x - planarGradient φ x‖ ^ 2 := by
      have scalar_sq : ‖hum.toLp u - hφ.toLp φ‖ ^ 2 = ∫ x, |u x - φ x| ^ 2 ∂(volume.restrict univ) := by
        rw [← MemLp.toLp_sub, ← real_inner_self_eq_norm_sq, L2.inner_def]
        apply integral_congr_ae
        filter_upwards [(hum.sub hφ).coeFn_toLp] with x hx
        rw [hx, Real.inner_apply]
        change (u x - φ x) * (u x - φ x) = |u x - φ x| ^ 2
        rw [sq_abs]
        ring
      have vector_sq : ‖hdum.toLp du - hg.toLp (planarGradient φ)‖ ^ 2 =
          ∫ x, ‖du x - planarGradient φ x‖ ^ 2 ∂(volume.restrict univ) := by
        rw [← MemLp.toLp_sub, ← real_inner_self_eq_norm_sq, L2.inner_def]
        apply integral_congr_ae
        filter_upwards [(hdum.sub hg).coeFn_toLp] with x hx
        rw [hx, real_inner_self_eq_norm_sq]
        rfl
      rw [dist_eq_norm, WithLp.prod_norm_sq_eq_of_L2]
      change ‖hum.toLp u - hφ.toLp φ‖ ^ 2 + ‖hdum.toLp du - hg.toLp (planarGradient φ)‖ ^ 2 = _
      rw [scalar_sq, vector_sq]
      have hs : Integrable (fun x => |u x - φ x| ^ 2) (volume.restrict univ) := by
        exact ((hum.sub hφ).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).congr
          (Filter.Eventually.of_forall fun x => by simp only [Real.norm_eq_abs, Pi.sub_apply])
      have hv : Integrable (fun x => ‖du x - planarGradient φ x‖ ^ 2) (volume.restrict univ) :=
        (hdum.sub hg).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
      exact (integral_add hs hv).symm
    apply (hbridge _ _ _ hum hdum).mpr
    change p ∈ (space univ : Set (Pair univ))
    rw [Submodule.topologicalClosure_coe]
    apply (closure_mono (show SmoothGraph univ ⊆ (Submodule.span ℝ (SmoothGraph univ) : Set (Pair univ)) from
      Submodule.subset_span))
    apply Metric.mem_closure_iff.mpr
    intro eps heps
    obtain ⟨psi,hs,hc,ht,herr⟩ := hphi.2 (eps ^ 2) (sq_pos_of_pos heps)
    have hgc : HasCompactSupport (planarGradient psi) := by
      apply hc.mono'
      intro y hy
      by_contra hn
      exact hy (planarGradient_eq_zero_off_support _ hn)
    have hp : MemLp psi 2 (volume.restrict univ) := (hs.continuous.memLp_of_hasCompactSupport hc).restrict univ
    have hgp : MemLp (planarGradient psi) 2 (volume.restrict univ) :=
      ((continuous_planarGradient hs).memLp_of_hasCompactSupport hgc).restrict univ
    refine ⟨pack univ _ _ hp hgp,⟨_,hp,hgp,hs,hc,subset_univ _,rfl⟩,?_⟩
    have heq (y : E2) : |u y - psi y| ^ 2 + ‖du y - planarGradient psi y‖ ^ 2 =
        U.indicator (fun y => |phi y - psi y| ^ 2 + ‖dphi y - planarGradient psi y‖ ^ 2) y := by
      by_cases hy : y ∈ U
      · simp only [u,du,indicator_of_mem hy]
      · have hz : psi y = 0 := image_eq_zero_of_notMem_tsupport (fun hn => hy (ht hn))
        have hgz : planarGradient psi y = 0 := planarGradient_eq_zero_off_support psi (fun hn => hy (ht hn))
        simp [u,du,hy,hz,hgz]
    have hsquare : dist p (pack univ _ _ hp hgp) ^ 2 < eps ^ 2 := by
      rw [energy psi hp hgp]
      simp_rw [heq]
      rw [Measure.restrict_univ,integral_indicator hU]
      exact herr
    exact (sq_lt_sq₀ dist_nonneg heps.le).mp hsquare
  have pull : ∀ (U : Set E2) (P : E2 ≃L[ℝ] E2) (u : E2 → ℝ) (du : E2 → E2),
      H1On U u du → H1On (P ⁻¹' U) (fun y => u (P y))
        (fun y => P.toContinuousLinearMap.adjoint (du (P y))) := by
    intro U P u du hu
    have hmap : Measure.map P (volume.restrict (P ⁻¹' U)) =
        ENNReal.ofReal |(LinearMap.det P.toLinearMap)⁻¹| • volume.restrict U := by
      have he : MeasurableEmbedding (P : E2 → E2) := P.toHomeomorph.toMeasurableEquiv.measurableEmbedding
      have hm : Measure.map P volume = ENNReal.ofReal |(LinearMap.det P.toLinearMap)⁻¹| • volume :=
        Measure.map_linearMap_addHaar_eq_smul_addHaar volume P.toLinearEquiv.isUnit_det'.ne_zero
      rw [← he.restrict_map,hm,Measure.restrict_smul]
    have hlp {E : Type} [NormedAddCommGroup E] (f : E2 → E) (hf : MemLp f 2 (volume.restrict U)) :
        MemLp (fun y => f (P y)) 2 (volume.restrict (P ⁻¹' U)) := by
      have hm : MemLp f 2 (Measure.map P (volume.restrict (P ⁻¹' U))) := by
        rw [hmap]
        exact hf.smul_measure ENNReal.ofReal_ne_top
      exact hm.comp_of_map P.continuous.measurable.aemeasurable
    have hint (f : E2 → ℝ) : (∫ y in P ⁻¹' U, f (P y)) =
        |(LinearMap.det P.toLinearMap)⁻¹| * ∫ x in U, f x := by
      have he : MeasurableEmbedding (P : E2 → E2) := P.toHomeomorph.toMeasurableEquiv.measurableEmbedding
      rw [← he.integral_map,hmap,integral_smul_measure,ENNReal.toReal_ofReal (abs_nonneg _)]
      rfl
    have csum (L : E2 →L[ℝ] ℝ) (v : E2) : L v = ∑ i : Fin 2, v i * L (EuclideanSpace.single i 1) := by
      have hv : (∑ i : Fin 2, v i • EuclideanSpace.single i 1) = v := by
        ext j
        fin_cases j <;> simp
      calc
        _ = L (∑ i : Fin 2, v i • EuclideanSpace.single i 1) := congrArg L hv.symm
        _ = _ := by simp
    have hdir (φ : E2 → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
        (hφΩ : tsupport φ ⊆ U) (v : E2) :
        (∫ x in U, u x * fderiv ℝ φ x v) = -∫ x in U, inner ℝ (du x) v * φ x := by
      let Ω := U
      let h := u
      have hw (i : Fin 2) : (∫ x in Ω, h x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
          -∫ x in Ω, du x i * φ x := by
        simpa only [coordinateVector] using hu.1.2.2 φ hφ hφc hφΩ i
      have hD (i : Fin 2) : MemLp (fun x => (fderiv ℝ φ x) (EuclideanSpace.single i 1))
          2 (volume.restrict Ω) := by
        have hd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ φ) := hφ.fderiv_right (by simp)
        exact ((hd.clm_apply contDiff_const).continuous.memLp_of_hasCompactSupport
          (hφc.fderiv_apply (𝕜 := ℝ) _)).restrict Ω
      have hp : MemLp φ 2 (volume.restrict Ω) :=
        (hφ.continuous.memLp_of_hasCompactSupport hφc).restrict Ω
      have hL (i : Fin 2) : Integrable (fun x => v i * (h x *
          (fderiv ℝ φ x) (EuclideanSpace.single i 1))) (volume.restrict Ω) :=
        (hu.2.1.integrable_mul (hD i)).const_mul (v i)
      have hG (i : Fin 2) : Integrable (fun x => v i * (du x i * φ x))
          (volume.restrict Ω) := (hu.2.2.eval_piLp i |>.integrable_mul hp).const_mul (v i)
      have hinner (x : E2) : inner ℝ (du x) v = ∑ i : Fin 2, v i * du x i := by
        simp [PiLp.inner_apply]
      have he : (fun x => h x * (fderiv ℝ φ x) v) =
          fun x => ∑ i : Fin 2, v i * (h x * (fderiv ℝ φ x) (EuclideanSpace.single i 1)) := by
        funext x
        rw [csum]
        simp only [Fin.sum_univ_two]
        ring
      rw [he]
      simp_rw [hinner, Finset.sum_mul, mul_assoc]
      rw [integral_finsetSum _ (fun i _ => hL i), integral_finsetSum _ (fun i _ => hG i)]
      simp_rw [integral_const_mul, hw _, mul_neg, Finset.sum_neg_distrib]
    have hval : MemLp (fun y => u (P y)) 2 (volume.restrict (P ⁻¹' U)) := hlp u hu.2.1
    have hgrad : MemLp (fun y => P.toContinuousLinearMap.adjoint (du (P y))) 2
        (volume.restrict (P ⁻¹' U)) := (hlp du hu.2.2).continuousLinearMap_comp P.toContinuousLinearMap.adjoint
    refine ⟨⟨locallyIntegrableOn_of_locallyIntegrable_restrict (hval.locallyIntegrable (by norm_num)),
      locallyIntegrableOn_of_locallyIntegrable_restrict (hgrad.locallyIntegrable (by norm_num)),?_⟩,hval,hgrad⟩
    intro phi hs hc ht i
    let psi : E2 → ℝ := fun x => phi (P.symm x)
    have hps : ContDiff ℝ ∞ psi := hs.comp P.symm.contDiff
    have hpc : HasCompactSupport psi := hc.comp_homeomorph P.symm.toHomeomorph
    have hpt : tsupport psi ⊆ U := by
      rw [show psi = phi ∘ P.symm.toHomeomorph from rfl,tsupport_comp_eq_preimage]
      intro x hx
      have h := ht hx
      simpa using h
    have hdpsi (x : E2) : fderiv ℝ psi x = (fderiv ℝ phi (P.symm x)).comp P.symm.toContinuousLinearMap :=
      ((hs.differentiable (by simp) (P.symm x)).hasFDerivAt.comp x P.symm.hasFDerivAt).fderiv
    have hid (y : E2) : fderiv ℝ phi y (coordinateVector 2 i) =
        fderiv ℝ psi (P y) (P (coordinateVector 2 i)) := by rw [hdpsi]; simp
    have hp (y : E2) : psi (P y) = phi y := by simp [psi]
    have hadj (y : E2) : P.toContinuousLinearMap.adjoint (du (P y)) i =
        inner ℝ (du (P y)) (P (coordinateVector 2 i)) := by
      calc
        _ = inner ℝ (P.toContinuousLinearMap.adjoint (du (P y))) (EuclideanSpace.single i 1) := by
          simp [EuclideanSpace.inner_single_right]
        _ = _ := by rw [ContinuousLinearMap.adjoint_inner_left]; rfl
    simp_rw [hid,hadj,← hp]
    rw [hint (fun x => u x * fderiv ℝ psi x (P (coordinateVector 2 i))),
      hint (fun x => inner ℝ (du x) (P (coordinateVector 2 i)) * psi x),
      hdir psi hps hpc hpt (P (coordinateVector 2 i)),mul_neg]
  have sub : ∀ (U : Set E2) (f g : E2 → ℝ) (df dg : E2 → E2),
      H1On U f df → H1On U g dg → H1On U (fun y => f y - g y) (fun y => df y - dg y) := by
    intro U f g df dg hf hg
    refine ⟨⟨hf.1.1.sub hg.1.1,hf.1.2.1.sub hg.1.2.1,?_⟩,hf.2.1.sub hg.2.1,hf.2.2.sub hg.2.2⟩
    intro psi hs hc ht i
    let mu := volume.restrict U
    have hpsi : MemLp psi 2 mu := (hs.continuous.memLp_of_hasCompactSupport hc).restrict U
    have hdpsi : MemLp (fun y => fderiv ℝ psi y (coordinateVector 2 i)) 2 mu :=
      (((hs.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
        (hc.fderiv_apply ℝ (coordinateVector 2 i))).restrict U
    have hfi := hf.2.1.integrable_mul hdpsi
    have hgi := hg.2.1.integrable_mul hdpsi
    have hdfi := (hf.2.2.eval_piLp i).integrable_mul hpsi
    have hdgi := (hg.2.2.eval_piLp i).integrable_mul hpsi
    have hfeq := hf.1.2.2 psi hs hc ht i
    have hgeq := hg.1.2.2 psi hs hc ht i
    simp only [PiLp.sub_apply,sub_mul]
    rw [integral_sub (f := fun y => f y * fderiv ℝ psi y (coordinateVector 2 i))
      (g := fun y => g y * fderiv ℝ psi y (coordinateVector 2 i)) hfi hgi,
      integral_sub (f := fun y => df y i * psi y) (g := fun y => dg y i * psi y) hdfi hdgi]
    linarith only [hfeq,hgeq]
  classical
  let bump : ContDiffBump (0 : E2) := ⟨r/2,3*r/4,by linarith,by linarith⟩
  let chi : E2 → ℝ := bump
  have hcs : ContDiff ℝ ∞ chi := bump.contDiff
  have hcc : HasCompactSupport chi := bump.hasCompactSupport
  have hcone : ∀ y ∈ closedDisc (r/2), chi y = 1 := by
    intro y hy
    exact bump.one_of_mem_closedBall hy
  have hcts : tsupport chi ⊆ disc r := by
    rw [show chi = (bump : E2 → ℝ) from rfl,bump.tsupport_eq]
    exact Metric.closedBall_subset_ball (by dsimp [bump]; linarith)
  have hcu := htrace chi hcs hcc hcts
  have continuous_coord : Continuous (fun y : E2 => y 1) := (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous
  have hUm : MeasurableSet (halfDisc r) := by
    unfold halfDisc disc
    exact (Metric.isOpen_ball.inter (isOpen_lt continuous_const continuous_coord)).measurableSet
  let f : E2 → ℝ := (halfDisc r).indicator (fun y => chi y * v y)
  let df : E2 → E2 := (halfDisc r).indicator (cutoffGradient chi v dv)
  have hf : H1On univ f df := (zeroExt (halfDisc r) hUm _ _ hcu).1
  let R : E2 ≃ₗᵢ[ℝ] E2 := LinearIsometryEquiv.piLpCongrRight 2
    (fun i : Fin 2 => if i = 1 then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)
  have hR (y : E2) : R y = reflect y := by
    ext i
    fin_cases i <;> simp [R,reflect]
  have hR1 (y : E2) : R y 1 = -y 1 := by rw [hR]; simp [reflect]
  have hRR (y : E2) : R (R y) = y := by
    ext i
    fin_cases i <;> simp [R]
  have hRf := pull univ R.toContinuousLinearEquiv f df hf
  have hRf' : H1On univ (fun y => f (R y))
      (fun y => R.toContinuousLinearEquiv.toContinuousLinearMap.adjoint (df (R y))) := by
    change H1On univ (fun y => f (R y))
      (fun y => R.toContinuousLinearEquiv.toContinuousLinearMap.adjoint (df (R y))) at hRf
    exact hRf
  let w : E2 → ℝ := fun y => f y - f (R y)
  let dw : E2 → E2 := fun y => df y - R.toContinuousLinearEquiv.toContinuousLinearMap.adjoint (df (R y))
  refine ⟨w,dw,sub _ _ _ _ _ hf hRf',?_,?_,?_⟩
  · intro y hy
    have hyr : y ∈ halfDisc r := ⟨Metric.mem_ball.mpr ((Metric.mem_ball.mp hy.1).trans (by linarith)),hy.2⟩
    have hn : R y ∉ halfDisc r := by intro h; have h1 := h.2; rw [hR1] at h1; linarith [hy.2]
    have hchi : chi y = 1 := hcone y (Metric.ball_subset_closedBall hy.1)
    have hder : fderiv ℝ chi y = 0 := by
      have hev : chi =ᶠ[𝓝 y] (fun _ => 1) :=
        (show ∀ᶠ z in 𝓝 y, z ∈ Metric.ball 0 (r/2) from Metric.isOpen_ball.mem_nhds hy.1).mono (fun z hz => hcone z (Metric.ball_subset_closedBall hz))
      rw [hev.fderiv_eq,fderiv_const_apply]
    have hgrad : planarGradient chi y = 0 := by simp [planarGradient,hder]
    constructor
    · dsimp only [w,f]
      rw [indicator_of_mem hyr,indicator_of_notMem hn,hchi,one_mul,sub_zero]
    · dsimp only [dw,df]
      rw [indicator_of_mem hyr,indicator_of_notMem hn,map_zero,sub_zero]
      unfold cutoffGradient
      rw [hchi,hgrad,one_smul,smul_zero,add_zero]
  · intro y
    dsimp only [w]
    rw [← hR,hRR]
    ring
  · intro y hy
    have hn : y ∉ halfDisc r := by intro h; linarith [h.2]
    have hnr : R y ∉ halfDisc r := by intro h; have hh := h.2; rw [hR1,hy] at hh; norm_num at hh
    dsimp only [w,f]
    rw [indicator_of_notMem hn,indicator_of_notMem hnr,sub_self]


theorem weak_laplace_regular (U W : Set E2) (hU : IsOpen U) (hW : IsOpen W)
    (hWc : IsCompact (closure W)) (hWU : closure W ⊆ U)
    (u : E2 → ℝ) (du : E2 → E2) (hu : H1On U u du)
    (hweak : ∀ (psi : E2 → ℝ), ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ U →
      (∫ y in U, inner ℝ (du y) (planarGradient psi y)) = 0) :
    ∃ w : E2 → ℝ, ContDiffOn ℝ ∞ w W ∧ w =ᵐ[volume.restrict W] u := by
  let hw : DeGiorgi.MemW1pWitness 2 u U :=
    { memLp := hu.2.1
      weakGrad := du
      weakGrad_component_memLp := fun i => hu.2.2.eval_piLp i
      isWeakGrad := by
        intro i psi hs hc ht
        simpa only [coordinateVector] using hu.1.2.2 psi hs hc ht i }
  have hgrad (psi : E2 → ℝ) : DeGiorgi.smoothGradField psi = planarGradient psi := by
    funext y
    ext i
    fin_cases i <;> simp [DeGiorgi.smoothGradField,planarGradient,coordinateVector,
      Fin.sum_univ_two,EuclideanSpace.single]
  obtain ⟨w,hws,hae⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_contDiffOn_ae_eq_of_integral_inner_weakGrad_smoothGrad_eq_zero
      hU hW hWc hWU hw (by
        intro psi hpsi
        change (∫ y in U, inner ℝ (du y) (DeGiorgi.smoothGradField psi y)) = 0
        rw [hgrad]
        exact hweak psi hpsi.1 hpsi.2.1 hpsi.2.2)
  exact ⟨w,hws,hae.symm⟩


theorem smooth_gradient_identity (Ω : Set E2) (hΩ : IsOpen Ω) (h f : E2 → ℝ) (du : E2 → E2)
    (hu : H1On Ω h du) (hf : ContDiffOn ℝ ∞ f Ω)
    (hfh : f =ᵐ[volume.restrict Ω] h) :
    planarGradient f =ᵐ[volume.restrict Ω] du := by
  have cmul : ∀ (Ω : Set E2), IsOpen Ω → ∀ (f g : E2 → ℝ),
      ContinuousOn f Ω → Continuous g → tsupport g ⊆ Ω →
      Continuous (fun x => f x * g x) := by
    intro Ω hΩ f g hf hg hgΩ
    apply continuous_of_tsupport
    intro x hx
    have hxΩ : x ∈ Ω := hgΩ (tsupport_mul_subset_right hx)
    exact (hf.continuousAt (hΩ.mem_nhds hxΩ)).mul hg.continuousAt
  have partial_test : ∀ (Ω : Set E2), IsOpen Ω → ∀ (f : E2 → ℝ),
      ContDiffOn ℝ ∞ f Ω → ∀ i : Fin 2,
      DeGiorgi.HasWeakPartialDeriv i
        (fun x => (fderiv ℝ f x) (EuclideanSpace.single i 1)) f Ω := by
    intro Ω hΩ f hf i
    intro φ hφ hφc hφΩ
    let v := EuclideanSpace.single i (1 : ℝ)
    have hdΩ : tsupport (fun x => (fderiv ℝ φ x) v) ⊆ Ω :=
      (tsupport_fderiv_apply_subset ℝ v).trans hφΩ
    have hdφ : Continuous (fun x => (fderiv ℝ φ x) v) :=
      (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hdf : ContinuousOn (fun x => (fderiv ℝ f x) v) Ω :=
      (hf.continuousOn_fderiv_of_isOpen hΩ (by simp)).clm_apply continuousOn_const
    have he := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
      ((cmul Ω hΩ _ φ hdf hφ.continuous hφΩ).integrable_of_hasCompactSupport
        hφc.mul_left)
      ((cmul Ω hΩ f _ hf.continuousOn hdφ hdΩ).integrable_of_hasCompactSupport
        (hφc.fderiv_apply (𝕜 := ℝ) v).mul_left)
      ((cmul Ω hΩ f φ hf.continuousOn hφ.continuous hφΩ).integrable_of_hasCompactSupport
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
  have heach (i : Fin 2) :
      (fun x => planarGradient f x i) =ᵐ[volume.restrict Ω] (fun x => du x i) := by
    let g : E2 → ℝ := fun x => (fderiv ℝ f x) (EuclideanSpace.single i 1)
    have hgc : ContinuousOn g Ω :=
      (hf.continuousOn_fderiv_of_isOpen hΩ (by simp)).clm_apply continuousOn_const
    have hgw := partial_test Ω hΩ f hf i
    have hhw : DeGiorgi.HasWeakPartialDeriv i (fun x => du x i) f Ω := by
      apply (show DeGiorgi.HasWeakPartialDeriv i (fun x => du x i) h Ω from
        fun psi hs hc ht => by simpa only [coordinateVector] using hu.1.2.2 psi hs hc ht i).congr_ae
        hfh.symm EventuallyEq.rfl
    suffices hz : ∀ᵐ x ∂volume.restrict Ω, g x - du x i = 0 by
      filter_upwards [hz] with x hx
      have hc : planarGradient f x i = g x := by
        fin_cases i <;> simp [g,planarGradient,Fin.sum_univ_two,coordinateVector,
          EuclideanSpace.single]
      exact hc.trans (sub_eq_zero.mp hx)
    rw [ae_restrict_iff' hΩ.measurableSet]
    apply IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hΩ
    · exact hgc.locallyIntegrableOn hΩ.measurableSet |>.sub
        (locallyIntegrableOn_of_locallyIntegrable_restrict
          ((hu.2.2.eval_piLp i).locallyIntegrable (by norm_num)))
    · intro φ hφ hφc hφΩ
      have heq : (∫ x in Ω, g x * φ x) = ∫ x in Ω, du x i * φ x := by
        have h1 := hgw φ hφ hφc hφΩ
        have h2 := hhw φ hφ hφc hφΩ
        linarith
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ω)
        (fun x hx => show φ x • (g x - du x i) = 0 by
          rw [ image_eq_zero_of_notMem_tsupport (fun ht => hx (hφΩ ht)), zero_smul])]
      simp only [smul_eq_mul, mul_sub]
      rw [integral_sub]
      · simpa only [mul_comm (φ _), heq, sub_self]
      · exact ((cmul Ω hΩ g φ hgc hφ.continuous hφΩ).integrable_of_hasCompactSupport
          hφc.mul_left).restrict (s := Ω) |>.congr (Eventually.of_forall fun x => mul_comm _ _)
      · simpa only [smul_eq_mul] using
          ((hu.2.2.eval_piLp i).locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
            hφ.continuous hφc
  filter_upwards [ae_all_iff.mpr heach] with x hx
  exact PiLp.ext fun i => hx i


theorem normalized_frozen_equation (U : Set E2) (hU : IsOpen U) (M : Mat2) (T : E2 ≃L[ℝ] E2)
    (hnorm : ∀ p : E2, T.symm (matrixAction (symmetricPart M)
      (T.symm.toContinuousLinearMap.adjoint p)) = p)
    (u : E2 → ℝ) (du : E2 → E2) (hu : H1On U u du)
    (hweak : ∀ phi : E2 → ℝ, ∀ dphi : E2 → E2, H10On U phi dphi →
      (∫ y in U, inner ℝ (matrixAction M (du y)) (dphi y)) = 0) :
    H1On (T ⁻¹' U) (fun y => u (T y))
      (fun y => T.toContinuousLinearMap.adjoint (du (T y))) ∧
    ∀ phi : E2 → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ T ⁻¹' U →
      (∫ y in T ⁻¹' U, inner ℝ (T.toContinuousLinearMap.adjoint (du (T y)))
        (planarGradient phi y)) = 0 := by
  have pull : ∀ (U : Set E2) (P : E2 ≃L[ℝ] E2) (u : E2 → ℝ) (du : E2 → E2),
      H1On U u du → H1On (P ⁻¹' U) (fun y => u (P y))
        (fun y => P.toContinuousLinearMap.adjoint (du (P y))) := by
    intro U P u du hu
    have hmap : Measure.map P (volume.restrict (P ⁻¹' U)) =
        ENNReal.ofReal |(LinearMap.det P.toLinearMap)⁻¹| • volume.restrict U := by
      have he : MeasurableEmbedding (P : E2 → E2) := P.toHomeomorph.toMeasurableEquiv.measurableEmbedding
      have hm : Measure.map P volume = ENNReal.ofReal |(LinearMap.det P.toLinearMap)⁻¹| • volume :=
        Measure.map_linearMap_addHaar_eq_smul_addHaar volume P.toLinearEquiv.isUnit_det'.ne_zero
      rw [← he.restrict_map,hm,Measure.restrict_smul]
    have hlp {E : Type} [NormedAddCommGroup E] (f : E2 → E) (hf : MemLp f 2 (volume.restrict U)) :
        MemLp (fun y => f (P y)) 2 (volume.restrict (P ⁻¹' U)) := by
      have hm : MemLp f 2 (Measure.map P (volume.restrict (P ⁻¹' U))) := by
        rw [hmap]
        exact hf.smul_measure ENNReal.ofReal_ne_top
      exact hm.comp_of_map P.continuous.measurable.aemeasurable
    have hint (f : E2 → ℝ) : (∫ y in P ⁻¹' U, f (P y)) =
        |(LinearMap.det P.toLinearMap)⁻¹| * ∫ x in U, f x := by
      have he : MeasurableEmbedding (P : E2 → E2) := P.toHomeomorph.toMeasurableEquiv.measurableEmbedding
      rw [← he.integral_map,hmap,integral_smul_measure,ENNReal.toReal_ofReal (abs_nonneg _)]
      rfl
    have csum (L : E2 →L[ℝ] ℝ) (v : E2) : L v = ∑ i : Fin 2, v i * L (EuclideanSpace.single i 1) := by
      have hv : (∑ i : Fin 2, v i • EuclideanSpace.single i 1) = v := by
        ext j
        fin_cases j <;> simp
      calc
        _ = L (∑ i : Fin 2, v i • EuclideanSpace.single i 1) := congrArg L hv.symm
        _ = _ := by simp
    have hdir (φ : E2 → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
        (hφΩ : tsupport φ ⊆ U) (v : E2) :
        (∫ x in U, u x * fderiv ℝ φ x v) = -∫ x in U, inner ℝ (du x) v * φ x := by
      let Ω := U
      let h := u
      have hw (i : Fin 2) : (∫ x in Ω, h x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
          -∫ x in Ω, du x i * φ x := by
        simpa only [coordinateVector] using hu.1.2.2 φ hφ hφc hφΩ i
      have hD (i : Fin 2) : MemLp (fun x => (fderiv ℝ φ x) (EuclideanSpace.single i 1))
          2 (volume.restrict Ω) := by
        have hd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ φ) := hφ.fderiv_right (by simp)
        exact ((hd.clm_apply contDiff_const).continuous.memLp_of_hasCompactSupport
          (hφc.fderiv_apply (𝕜 := ℝ) _)).restrict Ω
      have hp : MemLp φ 2 (volume.restrict Ω) :=
        (hφ.continuous.memLp_of_hasCompactSupport hφc).restrict Ω
      have hL (i : Fin 2) : Integrable (fun x => v i * (h x *
          (fderiv ℝ φ x) (EuclideanSpace.single i 1))) (volume.restrict Ω) :=
        (hu.2.1.integrable_mul (hD i)).const_mul (v i)
      have hG (i : Fin 2) : Integrable (fun x => v i * (du x i * φ x))
          (volume.restrict Ω) := (hu.2.2.eval_piLp i |>.integrable_mul hp).const_mul (v i)
      have hinner (x : E2) : inner ℝ (du x) v = ∑ i : Fin 2, v i * du x i := by
        simp [PiLp.inner_apply]
      have he : (fun x => h x * (fderiv ℝ φ x) v) =
          fun x => ∑ i : Fin 2, v i * (h x * (fderiv ℝ φ x) (EuclideanSpace.single i 1)) := by
        funext x
        rw [csum]
        simp only [Fin.sum_univ_two]
        ring
      rw [he]
      simp_rw [hinner, Finset.sum_mul, mul_assoc]
      rw [integral_finsetSum _ (fun i _ => hL i), integral_finsetSum _ (fun i _ => hG i)]
      simp_rw [integral_const_mul, hw _, mul_neg, Finset.sum_neg_distrib]
    have hval : MemLp (fun y => u (P y)) 2 (volume.restrict (P ⁻¹' U)) := hlp u hu.2.1
    have hgrad : MemLp (fun y => P.toContinuousLinearMap.adjoint (du (P y))) 2
        (volume.restrict (P ⁻¹' U)) := (hlp du hu.2.2).continuousLinearMap_comp P.toContinuousLinearMap.adjoint
    refine ⟨⟨locallyIntegrableOn_of_locallyIntegrable_restrict (hval.locallyIntegrable (by norm_num)),
      locallyIntegrableOn_of_locallyIntegrable_restrict (hgrad.locallyIntegrable (by norm_num)),?_⟩,hval,hgrad⟩
    intro phi hs hc ht i
    let psi : E2 → ℝ := fun x => phi (P.symm x)
    have hps : ContDiff ℝ ∞ psi := hs.comp P.symm.contDiff
    have hpc : HasCompactSupport psi := hc.comp_homeomorph P.symm.toHomeomorph
    have hpt : tsupport psi ⊆ U := by
      rw [show psi = phi ∘ P.symm.toHomeomorph from rfl,tsupport_comp_eq_preimage]
      intro x hx
      have h := ht hx
      simpa using h
    have hdpsi (x : E2) : fderiv ℝ psi x = (fderiv ℝ phi (P.symm x)).comp P.symm.toContinuousLinearMap :=
      ((hs.differentiable (by simp) (P.symm x)).hasFDerivAt.comp x P.symm.hasFDerivAt).fderiv
    have hid (y : E2) : fderiv ℝ phi y (coordinateVector 2 i) =
        fderiv ℝ psi (P y) (P (coordinateVector 2 i)) := by rw [hdpsi]; simp
    have hp (y : E2) : psi (P y) = phi y := by simp [psi]
    have hadj (y : E2) : P.toContinuousLinearMap.adjoint (du (P y)) i =
        inner ℝ (du (P y)) (P (coordinateVector 2 i)) := by
      calc
        _ = inner ℝ (P.toContinuousLinearMap.adjoint (du (P y))) (EuclideanSpace.single i 1) := by
          simp [EuclideanSpace.inner_single_right]
        _ = _ := by rw [ContinuousLinearMap.adjoint_inner_left]; rfl
    simp_rw [hid,hadj,← hp]
    rw [hint (fun x => u x * fderiv ℝ psi x (P (coordinateVector 2 i))),
      hint (fun x => inner ℝ (du x) (P (coordinateVector 2 i)) * psi x),
      hdir psi hps hpc hpt (P (coordinateVector 2 i)),mul_neg]
  have smooth (φ : E2 → ℝ) (hs : ContDiff ℝ ∞ φ)
      (hc : HasCompactSupport φ) (ht : tsupport φ ⊆ U) :
      H10On U φ (planarGradient φ) := by
      classical
      have hgcont : Continuous (planarGradient φ) := continuous_planarGradient hs
      have hgcompact : HasCompactSupport (planarGradient φ) := by
        apply hc.of_isClosed_subset (isClosed_tsupport _)
        apply closure_minimal _ (isClosed_tsupport φ)
        intro x hx
        by_contra h
        exact hx (planarGradient_eq_zero_off_support φ h)
      have huLp : MemLp φ 2 (volume.restrict (U)) :=
        (hs.continuous.memLp_of_hasCompactSupport (μ := volume) hc).restrict _
      have hgLp : MemLp (planarGradient φ) 2 (volume.restrict (U)) :=
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
          have hdsub : tsupport (fun x => fderiv ℝ ψ x (coordinateVector 2 i)) ⊆ U :=
            (tsupport_fderiv_apply_subset ℝ (coordinateVector 2 i)).trans htψ
          rw [show fderiv ℝ ψ x (coordinateVector 2 i) = 0 from
            image_eq_zero_of_notMem_tsupport (f := fun x => fderiv ℝ ψ x (coordinateVector 2 i))
              (fun h => hx (hdsub h)), mul_zero]
      · intro ε hε
        refine ⟨φ, hs, hc, ht, ?_⟩
        simpa using hε
  refine ⟨pull U T u du hu,?_⟩
  intro phi hs hc ht
  let psi : E2 → ℝ := fun x => phi (T.symm x)
  have hps : ContDiff ℝ ∞ psi := hs.comp T.symm.contDiff
  have hpc : HasCompactSupport psi := hc.comp_homeomorph T.symm.toHomeomorph
  have hpt : tsupport psi ⊆ U := by
    rw [show psi = phi ∘ T.symm.toHomeomorph from rfl,tsupport_comp_eq_preimage]
    intro x hx
    have h := ht hx
    simpa using h
  have hpsi := smooth psi hps hpc hpt
  have hsym := B02_frozen_symmetric_operator M U hU u du psi (planarGradient psi) hu hpsi
  have hzero : (∫ y in U, inner ℝ (matrixAction (symmetricPart M) (du y))
      (planarGradient psi y)) = 0 := hsym.2.2.symm.trans (hweak psi _ hpsi)
  have pair_grad (f : E2 → ℝ) (y q : E2) : inner ℝ (planarGradient f y) q = fderiv ℝ f y q := by
    have hq : q = q 0 • coordinateVector 2 0 + q 1 • coordinateVector 2 1 := by
      ext i
      fin_cases i <;> simp [coordinateVector]
    conv_rhs => rw [hq]
    rw [map_add,map_smul,map_smul]
    simp only [PiLp.inner_apply,Fin.sum_univ_two,RCLike.inner_apply,conj_trivial]
    have hg (i : Fin 2) : planarGradient f y i = fderiv ℝ f y (coordinateVector 2 i) := by
      fin_cases i <;> simp [planarGradient,coordinateVector,Fin.sum_univ_two,EuclideanSpace.single]
    rw [hg,hg]
    simp only [smul_eq_mul]
  have hgrad (y : E2) : planarGradient psi (T y) =
      T.symm.toContinuousLinearMap.adjoint (planarGradient phi y) := by
    apply ext_inner_right ℝ
    intro q
    rw [pair_grad,ContinuousLinearMap.adjoint_inner_left,pair_grad]
    change fderiv ℝ (phi ∘ T.symm) (T y) q = fderiv ℝ phi y (T.symm q)
    rw [((hs.differentiable (by simp) (T.symm (T y))).hasFDerivAt.comp (T y) T.symm.hasFDerivAt).fderiv]
    simp
  have hTI : T.symm.toContinuousLinearMap.adjoint.comp T.toContinuousLinearMap.adjoint =
      ContinuousLinearMap.id ℝ E2 := by
    rw [← ContinuousLinearMap.adjoint_comp]
    have hi : T.toContinuousLinearMap.comp T.symm.toContinuousLinearMap = ContinuousLinearMap.id ℝ E2 := by
      ext1 p
      exact T.apply_symm_apply p
    rw [hi,ContinuousLinearMap.adjoint_id]
  have hTIap (p : E2) : T.symm.toContinuousLinearMap.adjoint
      (T.toContinuousLinearMap.adjoint p) = p := DFunLike.congr_fun hTI p
  have hn (p : E2) : T.symm (matrixAction (symmetricPart M) p) = T.toContinuousLinearMap.adjoint p := by
    simpa only [hTIap] using hnorm (T.toContinuousLinearMap.adjoint p)
  have hp (y : E2) : inner ℝ (matrixAction (symmetricPart M) (du (T y)))
      (planarGradient psi (T y)) =
      inner ℝ (T.toContinuousLinearMap.adjoint (du (T y))) (planarGradient phi y) := by
    rw [hgrad,ContinuousLinearMap.adjoint_inner_right]
    change inner ℝ (T.symm (matrixAction (symmetricPart M) (du (T y)))) (planarGradient phi y) = _
    rw [hn]
  have hmap : Measure.map T (volume.restrict (T ⁻¹' U)) =
      ENNReal.ofReal |(LinearMap.det T.toLinearMap)⁻¹| • volume.restrict U := by
    have he : MeasurableEmbedding (T : E2 → E2) := T.toHomeomorph.toMeasurableEquiv.measurableEmbedding
    have hm : Measure.map T volume = ENNReal.ofReal |(LinearMap.det T.toLinearMap)⁻¹| • volume :=
      Measure.map_linearMap_addHaar_eq_smul_addHaar volume T.toLinearEquiv.isUnit_det'.ne_zero
    rw [← he.restrict_map,hm,Measure.restrict_smul]
  have hint (f : E2 → ℝ) : (∫ y in T ⁻¹' U, f (T y)) =
      |(LinearMap.det T.toLinearMap)⁻¹| * ∫ x in U, f x := by
    have he : MeasurableEmbedding (T : E2 → E2) := T.toHomeomorph.toMeasurableEquiv.measurableEmbedding
    rw [← he.integral_map,hmap,integral_smul_measure,ENNReal.toReal_ofReal (abs_nonneg _)]
    rfl
  simp_rw [← hp]
  rw [hint (fun y => inner ℝ (matrixAction (symmetricPart M) (du y)) (planarGradient psi y)),hzero,mul_zero]

theorem h10_pair_bridge (U : Set E2) (u : E2 → ℝ) (du : E2 → E2)
    (hu : MemLp u 2 (volume.restrict U)) (hdu : MemLp du 2 (volume.restrict U)) :
    H10On U u du ↔ pack U u du hu hdu ∈ space U := by
  classical
  have smooth (φ : E2 → ℝ) (hs : ContDiff ℝ ∞ φ)
      (hc : HasCompactSupport φ) (ht : tsupport φ ⊆ U) :
      H10On U φ (planarGradient φ) := by
      classical
      have hgcont : Continuous (planarGradient φ) := continuous_planarGradient hs
      have hgcompact : HasCompactSupport (planarGradient φ) := by
        apply hc.of_isClosed_subset (isClosed_tsupport _)
        apply closure_minimal _ (isClosed_tsupport φ)
        intro x hx
        by_contra h
        exact hx (planarGradient_eq_zero_off_support φ h)
      have huLp : MemLp φ 2 (volume.restrict (U)) :=
        (hs.continuous.memLp_of_hasCompactSupport (μ := volume) hc).restrict _
      have hgLp : MemLp (planarGradient φ) 2 (volume.restrict (U)) :=
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
          have hdsub : tsupport (fun x => fderiv ℝ ψ x (coordinateVector 2 i)) ⊆ U :=
            (tsupport_fderiv_apply_subset ℝ (coordinateVector 2 i)).trans htψ
          rw [show fderiv ℝ ψ x (coordinateVector 2 i) = 0 from
            image_eq_zero_of_notMem_tsupport (f := fun x => fderiv ℝ ψ x (coordinateVector 2 i))
              (fun h => hx (hdsub h)), mul_zero]
      · intro ε hε
        refine ⟨φ, hs, hc, ht, ?_⟩
        simpa using hε
  have span_eq : (Submodule.span ℝ (SmoothGraph U) : Set (Pair U)) = SmoothGraph U := by
    have hzero : (0 : Pair U) ∈ SmoothGraph U := by { have hg : planarGradient (0 : E2 → ℝ) = 0 := by { funext x; simp [planarGradient] }; have hglp : MemLp (planarGradient (0 : E2 → ℝ)) 2 (volume.restrict U) := by { rw [hg]; exact MemLp.zero }; refine ⟨0, MemLp.zero, hglp, contDiff_const, HasCompactSupport.zero, ?_, ?_⟩; { simp }; { unfold pack; simp only [hg, MemLp.toLp_zero]; rfl } }; have hadd : ∀ p q : Pair U, p ∈ SmoothGraph U → q ∈ SmoothGraph U → p + q ∈ SmoothGraph U := by { rintro p q ⟨φ, hφ, hgφ, hsφ, hcφ, htφ, rfl⟩ ⟨ψ, hψ, hgψ, hsψ, hcψ, htψ, rfl⟩; have hg : planarGradient (φ + ψ) = planarGradient φ + planarGradient ψ := by { funext x; unfold planarGradient; rw [fderiv_add (hsφ.differentiable (by simp) x) (hsψ.differentiable (by simp) x)]; simp only [ContinuousLinearMap.add_apply, add_smul, Finset.sum_add_distrib, Pi.add_apply] }; have hglp : MemLp (planarGradient (φ + ψ)) 2 (volume.restrict U) := by { rw [hg]; exact hgφ.add hgψ }; refine ⟨φ + ψ, hφ.add hψ, hglp, hsφ.add hsψ, hcφ.add hcψ, ?_, ?_⟩; { exact (tsupport_add φ ψ).trans (union_subset htφ htψ) }; { unfold pack; simp only [hg]; rfl } }; have hsmul : ∀ (a : ℝ) (p : Pair U), p ∈ SmoothGraph U → a • p ∈ SmoothGraph U := by { rintro a p ⟨φ, hφ, hgφ, hsφ, hcφ, htφ, rfl⟩; have hg : planarGradient (a • φ) = a • planarGradient φ := by { funext x; unfold planarGradient; rw [fderiv_const_smul (hsφ.differentiable (by simp) x)]; simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, Pi.smul_apply, mul_smul, Finset.smul_sum] }; have hglp : MemLp (planarGradient (a • φ)) 2 (volume.restrict U) := by { rw [hg]; exact hgφ.const_smul a }; refine ⟨a • φ, hφ.const_smul a, hglp, contDiff_const.smul hsφ, hcφ.smul_left, ?_, ?_⟩; { exact (tsupport_smul_subset_right (fun _ : E2 => a) φ).trans htφ }; { unfold pack; simp only [hg]; rfl } }; let S : Submodule ℝ (Pair U) := { carrier := SmoothGraph U, zero_mem' := hzero, add_mem' := hadd _ _, smul_mem' := hsmul }; exact congrArg (fun T : Submodule ℝ (Pair U) => (T : Set (Pair U))) (Submodule.span_eq S)
  classical
  let μ := volume.restrict U
  let p : Pair U := pack U u du hu hdu
  have space_eq : (space U : Set (Pair U)) = closure (SmoothGraph U) := by
    rw [Submodule.topologicalClosure_coe, span_eq]
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
    have hφ := (smooth φ hs hc ht).1.2.1
    have hg := (smooth φ hs hc ht).1.2.2
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
        have hw := (smooth φ hφs hφc hφt).1.1.2.2 ψ hs hc ht i
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

end BoundaryContinuation
end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak
