import B1InteriorCoefficientWindow_v475
import B1HalfDiscInteriorRepresentative_v468
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open DifferentialGeometry.Analysis.Sobolev.Euclidean
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem interior_compact_smooth_scalar_product_v475
    (m : ℕ) (V : Set E2) (hV : IsOpen V) (hVc : IsCompact (closure V))
    (a f : E2 → ℝ) (ha : ContDiff ℝ ∞ a) (hf : MemWkp m 2 f V) :
    MemWkp m 2 (fun x => a x * f x) V := by
  obtain ⟨C,_,hC⟩ := DifferentialGeometry.Analysis.Calculus.exists_uniform_iteratedFDerivWithin_bound_of_contDiffOn
    isOpen_univ ha.contDiffOn hVc (subset_univ _) m
  exact MemWkp.smul_smooth_bounded m (by norm_num) hV ha
    (fun j hj x hx => by simpa only [iteratedFDerivWithin_univ] using hC x (subset_closure hx) j hj) hf

/-- The actual lower-order source inherits the entire finite Sobolev tower from the
literal native gradient; local smooth coefficients are extended only for multiplication. -/
theorem interior_window_lower_source_tower_v475
    (W : InteriorCoefficientWindow_v475) (u : E2 → ℝ) (du : E2 → E2)
    (hu : H1On (halfDisc W.R) u du) (V : Set E2)
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVU : closure V ⊆ halfDisc W.R)
    (m : ℕ) (hm : MemWkp (m+1) 2 u V) :
    MemWkp m 2 (fun x => inner ℝ (W.b x) (du x) + W.c x * u x) V := by
  let U := halfDisc W.R
  let O := W.O
  have hO := W.isOpen_O
  have hWO := W.closed_subset
  have hb := W.smooth_b
  have hc := W.smooth_c
  have hUW : U ⊆ closedHalfDisc W.R := fun x hx =>
    ⟨Metric.ball_subset_closedBall hx.1,hx.2.le⟩
  have hVO : closure V ⊆ O := hVU.trans (hUW.trans hWO)
  obtain ⟨χ,hχ,hχc,hχone,hχO,hχrange⟩ := DifferentialGeometry.Analysis.exists_bump_compact hVc hO hVO
  have hχ1 (x : E2) (hx : x ∈ V) : χ x = 1 := hχone.self_of_nhdsSet (subset_closure hx)
  have hbs (i : Fin 2) : ContDiff ℝ ∞ (fun x => χ x * W.b x i) :=
    DifferentialGeometry.Analysis.contDiff_cutoff_smul hO hχ hχO
      ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp_contDiffOn hb)
  have hcs : ContDiff ℝ ∞ (fun x => χ x * W.c x) :=
    DifferentialGeometry.Analysis.contDiff_cutoff_smul hO hχ hχO hc
  let hw := (native_regular_witness_v468 U u du hu).restrict hV (subset_closure.trans hVU)
  have hdm (i : Fin 2) : MemWkp m 2 (fun x => du x i) V := by
    have he := (chosenWeakPartialOrZero_isWeakPartial_of_mem hm.memW1p i).ae_eq hV (hw.isWeakGrad i)
      ((chosenWeakPartialOrZero_memLp_of_mem hm.memW1p i).locallyIntegrable (by norm_num))
      ((hw.weakGrad_component_memLp i).locallyIntegrable (by norm_num))
    exact (MemWkp_congr_ae (by norm_num) hV he).mp (hm.chosenWeakPartial_mem i)
  have hp (i : Fin 2) : MemWkp m 2 (fun x => W.b x i * du x i) V := by
    have hh := interior_compact_smooth_scalar_product_v475 m V hV hVc _ _ (hbs i) (hdm i)
    apply (MemWkp_congr_ae (by norm_num) hV _).mp hh
    filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
    simp only [hχ1 x hx,one_mul]
  have hcp : MemWkp m 2 (fun x => W.c x * u x) V := by
    have hh := interior_compact_smooth_scalar_product_v475 m V hV hVc _ _ hcs hm.le_succ
    apply (MemWkp_congr_ae (by norm_num) hV _).mp hh
    filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
    simp only [hχ1 x hx,one_mul]
  have hsum := MemWkp.add (by norm_num) hV (MemWkp.add (by norm_num) hV (hp 0) (hp 1)) hcp
  convert hsum using 1
  funext x
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct,Fin.sum_univ_two,Pi.star_apply,star_trivial]
  ring

theorem interior_window_native_tower_v475
    (W : InteriorCoefficientWindow_v475) (u : E2 → ℝ) (du : E2 → E2)
    (hu : H1On (halfDisc W.R) u du)
    (heq : WeakLinearEquationOn (halfDisc W.R) W.a W.b W.c u du) :
    ∀ k : ℕ, ∀ V : Set E2, IsOpen V → IsCompact (closure V) →
      closure V ⊆ halfDisc W.R → MemWkp k 2 u V := by
  let U := halfDisc W.R
  have hU : IsOpen U := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous)
  let hw := native_regular_witness_v468 U u du hu
  obtain ⟨A,hAa⟩ := interior_window_elliptic_coeff_v475 W
  obtain ⟨-, hb, hc, M,B,C,hM,hB,hC,hMa,hBb,hCc⟩ := interior_window_full_form_bounds_v475 W
  have hf := native_lower_source_L2_v468 U u du W.b W.c hu hb hc B C
    (by filter_upwards [ae_restrict_mem hU.measurableSet] with x hx; exact hBb x hx)
    (by filter_upwards [ae_restrict_mem hU.measurableSet] with x hx; exact hCc x hx)
  have hweak := native_linear_principal_weak_v468 U hU W.a W.b W.c u du hu heq A hAa hf
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro V hV hVc hVU
    by_cases hk0 : k = 0
    · subst k
      exact MemWkp.zero_iff_memLp.mpr ((hw.restrict hV (subset_closure.trans hVU)).memLp)
    by_cases hk1 : k = 1
    · subst k
      exact MemWkp.one_iff_memW1p.mpr ((hw.restrict hV (subset_closure.trans hVU)).memW1p)
    have hk2 : 2 ≤ k := by omega
    let m := k-2
    obtain ⟨O,hO,hVO,hOU,hOc⟩ := exists_open_between_and_isCompact_closure hVc hU hVU
    have hOsub : O ⊆ U := subset_closure.trans hOU
    have hprev : MemWkp (m+1) 2 u O := ih (m+1) (by dsimp [m]; omega) O hO hOc hOU
    have hsource := interior_window_lower_source_tower_v475 W u du hu O hO hOc hOU m hprev
    let AO := A.restrict hOsub
    let hwO := hw.restrict hO hOsub
    have hweakO : ∀ v, DeGiorgi.MemH01 v O → ∀ hv : DeGiorgi.MemW1pWitness 2 v O,
        DeGiorgi.bilinFormOfCoeff AO hwO hv =
        ∫ x in O, (inner ℝ (W.b x) (du x) + W.c x * u x) * v x := by
      intro v hv0 hv
      exact DeGiorgi.bilinFormOfCoeff_restrict_eq_integral hU hO hOsub hw hweak hv0 hv
    obtain ⟨F,hFa⟩ := interior_window_smooth_elliptic_extension_v475 W
      (closure O) hOc hOU
    have hcoeff : ∀ x ∈ O, ∀ i j : Fin 2, AO.a x i j = (1 : ℝ) * F.a x i j := by
      intro x hx i j
      change A.a x i j = 1 * F.a x i j
      rw [hAa x (hOsub hx),one_mul]
      exact (congrFun (congrFun (hFa x (subset_closure hx)) i) j).symm
    have hh := DeGiorgi.memWkp_add_two_of_bilinFormOfCoeff_eq_integral m hO hV hVc hVO
      hwO hsource hweakO F one_ne_zero hcoeff
    convert hh using 1
    dsimp [m]
    omega

/-- Each compact interior patch admits an actual smooth a.e. representative of the
native weak solution. -/
theorem interior_window_native_smooth_patch_v475
    (W : InteriorCoefficientWindow_v475) (u : E2 → ℝ) (du : E2 → E2)
    (hu : H1On (halfDisc W.R) u du)
    (heq : WeakLinearEquationOn (halfDisc W.R) W.a W.b W.c u du)
    (V : Set E2) (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hVU : closure V ⊆ halfDisc W.R) :
    ∃ f : E2 → ℝ, ContDiffOn ℝ ∞ f V ∧ u =ᵐ[volume.restrict V] f := by
  apply DifferentialGeometry.Analysis.Sobolev.EuclideanIteratedEmbedding.exists_contDiffOn_ae_eq_of_forall_memWkp_two hV
  intro k
  exact interior_window_native_tower_v475 W u du hu heq k V hV hVc hVU

theorem interior_window_native_smooth_interior_v475
    (W : InteriorCoefficientWindow_v475) (u : E2 → ℝ) (du : E2 → E2)
    (hu : H1On (halfDisc W.R) u du)
    (heq : WeakLinearEquationOn (halfDisc W.R) W.a W.b W.c u du) :
    ∃ f : E2 → ℝ, ContDiffOn ℝ ∞ f (halfDisc W.R) ∧
      u =ᵐ[volume.restrict (halfDisc W.R)] f := by
  let U := halfDisc W.R
  have hU : IsOpen U := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous)
  apply planar_glued_smooth_ae_v468 U u
  intro x
  obtain ⟨rho,hrho,hball⟩ := Metric.isOpen_iff.mp hU x.val x.property
  let r := rho/2
  have hr : 0 < r := half_pos hrho
  have hsub : closure (Metric.ball x.val r) ⊆ U := by
    apply subset_trans (closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall)
    intro y hy
    apply hball
    change dist y x.val < rho
    have hh : dist y x.val ≤ r := hy
    dsimp [r] at hh
    linarith
  have hcompact : IsCompact (closure (Metric.ball x.val r)) :=
    (isCompact_closedBall x.val r).of_isClosed_subset isClosed_closure
      (closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall)
  obtain ⟨f,hf,hae⟩ := interior_window_native_smooth_patch_v475 W u du hu heq
    (Metric.ball x.val r) Metric.isOpen_ball hcompact hsub
  exact ⟨r,hr,subset_closure.trans hsub,f,hf,hae⟩

#print axioms interior_window_native_tower_v475
#print axioms interior_window_native_smooth_interior_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
