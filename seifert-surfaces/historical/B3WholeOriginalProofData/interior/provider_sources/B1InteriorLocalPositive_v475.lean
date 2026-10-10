import B1InteriorTranslation_v475
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Coefficient-only positive normalization around any interior point.  An
artificial translated half-disc is placed after a uniform radius is chosen,
so its flat edge never passes through the working point. -/
theorem native_local_positive_classical_v475
    (O : Set E2) (hO : IsOpen O) (p : E2) (hp : p ∈ O)
    (a : E2 → Mat2) (b : E2 → E2) (c : E2 → ℝ)
    (hEll : SmoothEllipticOn a b c O) :
    ∃ V : Set E2, IsOpen V ∧ p ∈ V ∧ V ⊆ O ∧ ∃ h : E2 → ℝ,
      ContDiffOn ℝ ∞ h V ∧ (∀ x ∈ V, (1/2:ℝ) ≤ h x) ∧
      (∀ x ∈ V, classicalL a b c h x = 0) := by
  classical
  obtain ⟨ha,hb,hc,hsym,ell,Ca,hell,hCa,hbounds⟩ := hEll
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hO p hp
  let δ := ε/2
  have hδ : 0 < δ := half_pos hε
  have hKO : Metric.closedBall p δ ⊆ O := by
    intro x hx
    apply hball
    change dist x p < ε
    exact lt_of_le_of_lt (Metric.mem_closedBall.mp hx) (by dsimp [δ]; linarith)
  have hK : IsCompact (Metric.closedBall p δ) := isCompact_closedBall _ _
  choose A₀ hAb using (fun i j : Fin 2 => hK.exists_bound_of_continuousOn
    (((ha i j).continuousOn_fderiv_of_isOpen hO (by simp)).clm_apply continuousOn_const
      |>.mono hKO : ContinuousOn
        (fun x => fderiv ℝ (fun y => a y i j) x (coordinateVector 2 i)) (Metric.closedBall p δ)))
  obtain ⟨B₀,hBb⟩ := hK.exists_bound_of_continuousOn (hb.continuousOn.mono hKO)
  obtain ⟨C₀,hCb⟩ := hK.exists_bound_of_continuousOn (hc.continuousOn.mono hKO)
  let A := 1+|A₀ 0 0|+|A₀ 0 1|+|A₀ 1 0|+|A₀ 1 1|
  let B := max B₀ 1
  let C := max C₀ 1
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨P,hP,hpoincare⟩ := compact_halfdisc_test_poincare_export_v468
  let Q := B^2/ell+C
  let S := 8*(1+Q)*(1+P)
  let L := 4*A+B
  let M := (C+1)/ell
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hS : 0 < S := by dsimp [S]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  have hM : 0 < M := div_pos (by positivity) hell
  let r := min (δ/2) (min 1 (min (ell/S) (min (ell/(2*L)) (1/(2*M)))))
  have hr : 0 < r := lt_min (half_pos hδ) (lt_min zero_lt_one
    (lt_min (div_pos hell hS) (lt_min (div_pos hell (by positivity))
      (div_pos zero_lt_one (by positivity)))))
  have hrδ : r ≤ δ/2 := min_le_left _ _
  have hr1 : r ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hrS : r ≤ ell/S := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hrL : r ≤ ell/(2*L) := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hrM : r ≤ 1/(2*M) := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  let x₀ : E2 := (r/2) • coordinateVector 2 1
  let q : E2 := p-x₀
  let τ : E2 → E2 := fun x => x+q
  have hx₀norm : ‖x₀‖ = r/2 := by
    have he : ‖coordinateVector 2 1‖ = 1 := by simp [coordinateVector]
    rw [show x₀ = (r/2) • coordinateVector 2 1 from rfl,norm_smul,
      Real.norm_eq_abs,abs_of_pos (half_pos hr),he,mul_one]
  have hτK (x : E2) (hx : x ∈ closedHalfDisc r) : τ x ∈ Metric.closedBall p δ := by
    have hxn : ‖x‖ ≤ r := by simpa only [closedDisc,Metric.mem_closedBall,dist_zero_right] using hx.1
    have he : τ x-p = x-x₀ := by dsimp [τ,q]; abel
    rw [Metric.mem_closedBall,dist_eq_norm,he]
    exact (norm_sub_le _ _).trans (by rw [hx₀norm]; linarith)
  have hτO : closedHalfDisc r ⊆ τ ⁻¹' O := fun x hx => hKO (hτK x hx)
  have hτ : ContDiff ℝ ∞ τ := contDiff_id.add contDiff_const
  let W : InteriorCoefficientWindow_v475 :=
    { R := r
      R_pos := hr
      O := τ ⁻¹' O
      isOpen_O := hO.preimage hτ.continuous
      closed_subset := hτO
      a := fun x => a (τ x)
      b := fun x => b (τ x)
      c := fun x => c (τ x)
      smooth_a := fun i j => (ha i j).comp hτ.contDiffOn (fun _ hx => hx)
      smooth_b := hb.comp hτ.contDiffOn (fun _ hx => hx)
      smooth_c := hc.comp hτ.contDiffOn (fun _ hx => hx)
      symmetric := fun x hx => hsym (τ x) (hτO hx)
      ell := ell
      ell_pos := hell
      coercive := fun x hx v => (hbounds (τ x) (hτO hx) v).1 }
  have hBbound (x : E2) (hx : x ∈ halfDisc r) : ‖W.b x‖ ≤ B :=
    (hBb (τ x) (hτK x ⟨Metric.ball_subset_closedBall hx.1,hx.2.le⟩)).trans (le_max_left _ _)
  have hCbound (x : E2) (hx : x ∈ halfDisc r) : |W.c x| ≤ C := by
    simpa only [Real.norm_eq_abs] using
      (hCb (τ x) (hτK x ⟨Metric.ball_subset_closedBall hx.1,hx.2.le⟩)).trans (le_max_left _ _)
  have hentry (x : E2) (hx : x ∈ halfDisc r) (i j : Fin 2) :
      |fderiv ℝ (fun y => W.a y i j) x (coordinateVector 2 i)| ≤ A := by
    have hxH : x ∈ closedHalfDisc r := ⟨Metric.ball_subset_closedBall hx.1,hx.2.le⟩
    have hd : DifferentiableAt ℝ (fun y => a y i j) (x+q) :=
      (((ha i j) _ (hτO hxH)).contDiffAt (hO.mem_nhds (hτO hxH))).differentiableAt (by simp)
    change |fderiv ℝ (fun y => a (y+q) i j) x (coordinateVector 2 i)| ≤ A
    rw [native_fderiv_translate_v475 _ q x hd]
    have hh := hAb i j (τ x) (hτK x hxH)
    fin_cases i <;> fin_cases j <;>
      calc
        _ ≤ A₀ _ _ := by simpa only [Real.norm_eq_abs] using hh
        _ ≤ |A₀ _ _| := le_abs_self _
        _ ≤ A := by dsimp [A]; linarith [abs_nonneg (A₀ 0 0),abs_nonneg (A₀ 0 1),abs_nonneg (A₀ 1 0),abs_nonneg (A₀ 1 1)]
  have hsmall : Q*P*r^2 ≤ ell/4 := by
    have hmul : r*S ≤ ell := (le_div_iff₀ hS).mp hrS
    have hs : r^2 ≤ r := by nlinarith
    have hQP : 4*(Q*P) ≤ S := by dsimp [S]; nlinarith [mul_nonneg hQ hP.le]
    have ht := mul_le_mul_of_nonneg_left hs (mul_nonneg hQ hP.le)
    have ht2 := mul_le_mul_of_nonneg_left hQP hr.le
    nlinarith
  have hcoer := interior_window_fixed_test_coercivity_v475 W B C P hB.le hC.le hP
    hBbound hCbound hpoincare hsmall
  obtain ⟨v,hv,hvb,hvL⟩ := interior_window_fixed_positive_barrier_v475 W A B C hA hB hC
    hentry hBbound hCbound hr1 hrL hrM
  obtain ⟨u,du,hu,h10,heq,hpos⟩ := interior_window_native_positive_solution_v475 W
    (ell/4) (by positivity) hcoer v hv hvb (fun x hx => (by norm_num : (0:ℝ) ≤ 1).trans (hvL x hx))
  obtain ⟨h,hh,-,-,-,hpos,heq⟩ := interior_window_classical_positive_v475 W u du hu h10 heq hpos
  let V : Set E2 := (fun x => x-q) ⁻¹' halfDisc r
  have hhalf : IsOpen (halfDisc r) := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (1:Fin 2)).continuous)
  have hV : IsOpen V := hhalf.preimage (continuous_id.sub continuous_const)
  have hpV : p ∈ V := by
    have he : p-q = x₀ := by dsimp [q]; abel
    change p-q ∈ halfDisc r
    rw [he]
    constructor
    · simpa only [disc,Metric.mem_ball,dist_zero_right,hx₀norm] using (by linarith : r/2 < r)
    · simp [x₀,coordinateVector,PiLp.single_apply,half_pos hr]
  have hVO : V ⊆ O := by
    intro x hx
    have hh := hτO ⟨Metric.ball_subset_closedBall hx.1,hx.2.le⟩
    change (x-q)+q ∈ O at hh
    simpa using hh
  let H : E2 → ℝ := fun x => h (x-q)
  have hH : ContDiffOn ℝ ∞ H V := hh.comp
    (contDiff_id.sub contDiff_const).contDiffOn (fun _ hx => hx)
  refine ⟨V,hV,hpV,hVO,H,hH,fun x hx => hpos _ hx,?_⟩
  intro x hx
  change x-q ∈ halfDisc r at hx
  have htrans := native_classical_translate_v475 (halfDisc r) hhalf W.a W.b W.c h
    (fun i j => (W.smooth_a i j).mono (fun y hy => hτO
      ⟨Metric.ball_subset_closedBall hy.1,hy.2.le⟩)) hh (-q) x (by simpa only [sub_eq_add_neg] using hx)
  have haeq : (fun y => W.a (y+ -q)) = a := by funext y; change a ((y+ -q)+q) = a y; simp
  have hbeq : (fun y => W.b (y+ -q)) = b := by funext y; change b ((y+ -q)+q) = b y; simp
  have hceq : (fun y => W.c (y+ -q)) = c := by funext y; change c ((y+ -q)+q) = c y; simp
  rw [haeq,hbeq,hceq] at htrans
  change classicalL a b c (fun y => h (y-q)) x = 0
  simpa only [sub_eq_add_neg] using htrans.trans (heq _ hx)

#print axioms native_local_positive_classical_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
