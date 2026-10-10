import B1L1DirectWeakLower
import NativeH10DirichletData
set_option maxHeartbeats 3000000
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.NativeDirichlet

theorem BoundaryContinuation.h10_cutoff (U : Set E2) (chi : E2 → ℝ) (hs : ContDiff ℝ ∞ chi)
    (hc : HasCompactSupport chi) (phi : E2 → ℝ) (dphi : E2 → E2)
    (hphi : H10On U phi dphi) :
    H10On U (fun y => chi y * phi y) (cutoffGradient chi phi dphi) := by
  classical
  have hbridge : ∀ (u : E2 → ℝ) (du : E2 → E2)
      (hu : MemLp u 2 (volume.restrict U)) (hdu : MemLp du 2 (volume.restrict U)),
      H10On U u du ↔ pack U u du hu hdu ∈ space U := by
    intro u du hu hdu
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
    let mu := volume.restrict U
    let p : Pair U := pack U u du hu hdu
    have space_eq : (space U : Set (Pair U)) = closure (SmoothGraph U) := by
      rw [Submodule.topologicalClosure_coe, span_eq]
    have energy (φ : E2 → ℝ) (hφ : MemLp φ 2 mu)
        (hg : MemLp (planarGradient φ) 2 mu) :
        dist p (pack U φ (planarGradient φ) hφ hg) ^ 2 =
          ∫ x in U, |u x - φ x| ^ 2 + ‖du x - planarGradient φ x‖ ^ 2 := by
      have scalar_sq : ‖hu.toLp u - hφ.toLp φ‖ ^ 2 = ∫ x, |u x - φ x| ^ 2 ∂mu := by
        rw [← MemLp.toLp_sub, ← real_inner_self_eq_norm_sq, L2.inner_def]
        apply integral_congr_ae
        filter_upwards [(hu.sub hφ).coeFn_toLp] with x hx
        rw [hx, Real.inner_apply]
        change (u x - φ x) * (u x - φ x) = |u x - φ x| ^ 2
        rw [sq_abs]
        ring
      have vector_sq : ‖hdu.toLp du - hg.toLp (planarGradient φ)‖ ^ 2 =
          ∫ x, ‖du x - planarGradient φ x‖ ^ 2 ∂mu := by
        rw [← MemLp.toLp_sub, ← real_inner_self_eq_norm_sq, L2.inner_def]
        apply integral_congr_ae
        filter_upwards [(hdu.sub hg).coeFn_toLp] with x hx
        rw [hx, real_inner_self_eq_norm_sq]
        rfl
      rw [dist_eq_norm, WithLp.prod_norm_sq_eq_of_L2]
      change ‖hu.toLp u - hφ.toLp φ‖ ^ 2 + ‖hdu.toLp du - hg.toLp (planarGradient φ)‖ ^ 2 = _
      rw [scalar_sq, vector_sq]
      have hs : Integrable (fun x => |u x - φ x| ^ 2) mu := by
        exact ((hu.sub hφ).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).congr
          (Filter.Eventually.of_forall fun x => by simp only [Real.norm_eq_abs, Pi.sub_apply])
      have hv : Integrable (fun x => ‖du x - planarGradient φ x‖ ^ 2) mu :=
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
        have hψ : MemLp ψ 2 mu := (hs.continuous.memLp_of_hasCompactSupport (μ := volume) hc).restrict U
        have hdψ : MemLp dψ 2 mu :=
          (((hs.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
            (μ := volume) (hc.fderiv_apply ℝ (coordinateVector 2 i))).restrict U
        let project : Lp E2 2 mu →L[ℝ] Lp ℝ 2 mu := (EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 mu
        let F : Pair U → ℝ := fun q =>
          inner ℝ q.fst (hdψ.toLp dψ) + inner ℝ (project q.snd) (hψ.toLp ψ)
        have cf : Continuous (fun q : Pair U => q.fst) := WithLp.continuous_fst 2 (Lp ℝ 2 mu) (Lp E2 2 mu)
        have cs : Continuous (fun q : Pair U => q.snd) := WithLp.continuous_snd 2 (Lp ℝ 2 mu) (Lp E2 2 mu)
        have cF : Continuous F := (cf.inner continuous_const).add
          ((project.continuous.comp cs).inner continuous_const)
        have eqF (v : E2 → ℝ) (dv : E2 → E2) (hv : MemLp v 2 mu) (hdv : MemLp dv 2 mu) :
            F (pack U v dv hv hdv) =
              (∫ x in U, v x * fderiv ℝ ψ x (coordinateVector 2 i)) +
                ∫ x in U, dv x i * ψ x := by
          have first : inner ℝ (hv.toLp v) (hdψ.toLp dψ) = ∫ x, v x * dψ x ∂mu := by
            rw [L2.inner_def]
            apply integral_congr_ae
            filter_upwards [hv.coeFn_toLp, hdψ.coeFn_toLp] with x hx hdx
            rw [hx, hdx, Real.inner_apply]
          have second : inner ℝ (project (hdv.toLp dv)) (hψ.toLp ψ) = ∫ x, dv x i * ψ x ∂mu := by
            rw [L2.inner_def]
            apply integral_congr_ae
            filter_upwards [(EuclideanSpace.proj (𝕜 := ℝ) i).coeFn_compLpL (p := 2) (μ := mu) (hdv.toLp dv),
              hdv.coeFn_toLp, hψ.coeFn_toLp] with x hx hdx hψx
            change inner ℝ (((EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 mu (hdv.toLp dv)) x)
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
  let mu := volume.restrict U
  have hgcont : Continuous (planarGradient chi) := continuous_planarGradient hs
  have hgc : HasCompactSupport (planarGradient chi) := by
    apply hc.mono'
    intro y hy
    by_contra hn
    exact hy (planarGradient_eq_zero_off_support chi hn)
  have hchi : MemLp chi ⊤ mu := hs.continuous.memLp_top_of_hasCompactSupport hc mu
  have hgchi : MemLp (planarGradient chi) ⊤ mu := hgcont.memLp_top_of_hasCompactSupport hgc mu
  let u : E2 → ℝ := fun y => chi y * phi y
  let du := cutoffGradient chi phi dphi
  have hu : MemLp u 2 mu := hchi.mul hphi.1.2.1
  have hdu : MemLp du 2 mu := (hchi.smul hphi.1.2.2).add (hphi.1.2.1.smul hgchi)
  let p : Pair U := pack U u du hu hdu
  have energy (φ : E2 → ℝ) (hφ : MemLp φ 2 mu)
      (hg : MemLp (planarGradient φ) 2 mu) :
      dist p (pack U φ (planarGradient φ) hφ hg) ^ 2 =
        ∫ x in U, |u x - φ x| ^ 2 + ‖du x - planarGradient φ x‖ ^ 2 := by
    have scalar_sq : ‖hu.toLp u - hφ.toLp φ‖ ^ 2 = ∫ x, |u x - φ x| ^ 2 ∂mu := by
      rw [← MemLp.toLp_sub, ← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [(hu.sub hφ).coeFn_toLp] with x hx
      rw [hx, Real.inner_apply]
      change (u x - φ x) * (u x - φ x) = |u x - φ x| ^ 2
      rw [sq_abs]
      ring
    have vector_sq : ‖hdu.toLp du - hg.toLp (planarGradient φ)‖ ^ 2 =
        ∫ x, ‖du x - planarGradient φ x‖ ^ 2 ∂mu := by
      rw [← MemLp.toLp_sub, ← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [(hdu.sub hg).coeFn_toLp] with x hx
      rw [hx, real_inner_self_eq_norm_sq]
      rfl
    rw [dist_eq_norm, WithLp.prod_norm_sq_eq_of_L2]
    change ‖hu.toLp u - hφ.toLp φ‖ ^ 2 + ‖hdu.toLp du - hg.toLp (planarGradient φ)‖ ^ 2 = _
    rw [scalar_sq, vector_sq]
    have hs : Integrable (fun x => |u x - φ x| ^ 2) mu := by
      exact ((hu.sub hφ).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).congr
        (Filter.Eventually.of_forall fun x => by simp only [Real.norm_eq_abs, Pi.sub_apply])
    have hv : Integrable (fun x => ‖du x - planarGradient φ x‖ ^ 2) mu :=
      (hdu.sub hg).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
    exact (integral_add hs hv).symm
  obtain ⟨B0,hB0⟩ := hs.continuous.bounded_above_of_compact_support hc
  obtain ⟨D0,hD0⟩ := hgcont.bounded_above_of_compact_support hgc
  let B : ℝ := max B0 0
  let D : ℝ := max D0 0
  have hB : 0 ≤ B := le_max_right _ _
  have hD : 0 ≤ D := le_max_right _ _
  have hb (y : E2) : |chi y| ≤ B := by
    rw [← Real.norm_eq_abs]
    exact (hB0 y).trans (le_max_left _ _)
  have hd (y : E2) : ‖planarGradient chi y‖ ≤ D := (hD0 y).trans (le_max_left _ _)
  let C : ℝ := 3 * B ^ 2 + 2 * D ^ 2 + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  have hgradprod (psi : E2 → ℝ) (hps : ContDiff ℝ ∞ psi) (y : E2) :
      planarGradient (fun x => chi x * psi x) y =
        chi y • planarGradient psi y + psi y • planarGradient chi y := by
    unfold planarGradient
    rw [fderiv_fun_mul (hs.differentiable (by simp) y) (hps.differentiable (by simp) y)]
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
      smul_eq_mul,add_smul,mul_smul,Finset.sum_add_distrib,Finset.smul_sum]
  apply (hbridge _ _ hu hdu).mpr
  change p ∈ (space U : Set (Pair U))
  rw [Submodule.topologicalClosure_coe]
  apply (closure_mono (show SmoothGraph U ⊆ (Submodule.span ℝ (SmoothGraph U) : Set (Pair U)) from
    Submodule.subset_span))
  apply Metric.mem_closure_iff.mpr
  intro eps heps
  obtain ⟨psi,hps,hpc,hpt,herr⟩ := hphi.2 (eps ^ 2 / C) (div_pos (sq_pos_of_pos heps) hC)
  have hproduct : ContDiff ℝ ∞ (fun y => chi y * psi y) := hs.mul hps
  have hproductc : HasCompactSupport (fun y => chi y * psi y) := hc.mul_right
  have hproductt : tsupport (fun y => chi y * psi y) ⊆ U := tsupport_mul_subset_right.trans hpt
  have hgproductc : HasCompactSupport (planarGradient (fun y => chi y * psi y)) := by
    apply hproductc.mono'
    intro y hy
    by_contra hn
    exact hy (planarGradient_eq_zero_off_support _ hn)
  have hp : MemLp (fun y => chi y * psi y) 2 mu :=
    (hproduct.continuous.memLp_of_hasCompactSupport hproductc).restrict U
  have hgp : MemLp (planarGradient (fun y => chi y * psi y)) 2 mu :=
    ((continuous_planarGradient hproduct).memLp_of_hasCompactSupport hgproductc).restrict U
  refine ⟨pack U _ _ hp hgp,⟨_,hp,hgp,hproduct,hproductc,hproductt,rfl⟩,?_⟩
  have hpoint (y : E2) : |u y - chi y * psi y| ^ 2 +
      ‖du y - planarGradient (fun x => chi x * psi x) y‖ ^ 2 ≤
      C * (|phi y - psi y| ^ 2 + ‖dphi y - planarGradient psi y‖ ^ 2) := by
    have hscalar : u y - chi y * psi y = chi y * (phi y - psi y) := by dsimp only [u]; ring
    have hvector : du y - planarGradient (fun x => chi x * psi x) y =
        chi y • (dphi y - planarGradient psi y) + (phi y - psi y) • planarGradient chi y := by
      rw [hgradprod psi hps y]
      dsimp only [du]
      unfold cutoffGradient
      ext i
      simp only [PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul]
      ring
    have hsbound : |u y - chi y * psi y| ≤ B * |phi y - psi y| := by
      rw [hscalar,abs_mul]
      exact mul_le_mul_of_nonneg_right (hb y) (abs_nonneg _)
    have hdbound : ‖du y - planarGradient (fun x => chi x * psi x) y‖ ≤
        B * ‖dphi y - planarGradient psi y‖ + D * |phi y - psi y| := by
      rw [hvector]
      apply (norm_add_le _ _).trans
      simp only [norm_smul,Real.norm_eq_abs]
      exact add_le_add (mul_le_mul_of_nonneg_right (hb y) (norm_nonneg _))
        (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hd y) (abs_nonneg (phi y - psi y)))
    have hss := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hsbound
    have hds := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hdbound
    dsimp only [C]
    nlinarith only [hss,hds,
      sq_nonneg (B * ‖dphi y - planarGradient psi y‖ - D * |phi y - psi y|),
      mul_nonneg (sq_nonneg B) (sq_nonneg |phi y - psi y|),
      mul_nonneg (sq_nonneg B) (sq_nonneg ‖dphi y - planarGradient psi y‖),
      mul_nonneg (sq_nonneg D) (sq_nonneg ‖dphi y - planarGradient psi y‖),
      sq_nonneg |phi y - psi y|,sq_nonneg ‖dphi y - planarGradient psi y‖]
  have hpsLp : MemLp psi 2 mu := (hps.continuous.memLp_of_hasCompactSupport hpc).restrict U
  have hgscompact : HasCompactSupport (planarGradient psi) := by
    apply hpc.mono'
    intro y hy
    by_contra hn
    exact hy (planarGradient_eq_zero_off_support _ hn)
  have hgsLp : MemLp (planarGradient psi) 2 mu :=
    ((continuous_planarGradient hps).memLp_of_hasCompactSupport hgscompact).restrict U
  have hleft : Integrable (fun y => |u y - chi y * psi y| ^ 2 +
      ‖du y - planarGradient (fun x => chi x * psi x) y‖ ^ 2) mu := by
    simp only [sq_abs]
    exact ((hu.sub hp).integrable_sq).add
      ((hdu.sub hgp).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))
  have hright : Integrable (fun y => |phi y - psi y| ^ 2 +
      ‖dphi y - planarGradient psi y‖ ^ 2) mu := by
    simp only [sq_abs]
    exact ((hphi.1.2.1.sub hpsLp).integrable_sq).add
      ((hphi.1.2.2.sub hgsLp).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))
  have hi := integral_mono hleft (hright.const_mul C) hpoint
  rw [integral_const_mul] at hi
  have hsquare : dist p (pack U _ _ hp hgp) ^ 2 < eps ^ 2 := by
    rw [energy]
    calc
      _ ≤ C * (∫ y in U, |phi y - psi y| ^ 2 + ‖dphi y - planarGradient psi y‖ ^ 2) := hi
      _ < eps ^ 2 := by
        have hh := mul_lt_mul_of_pos_left herr hC
        rwa [mul_div_cancel₀ _ hC.ne'] at hh
  exact (sq_lt_sq₀ dist_nonneg heps.le).mp hsquare

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak
