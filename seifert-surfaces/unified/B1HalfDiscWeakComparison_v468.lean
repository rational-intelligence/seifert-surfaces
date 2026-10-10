import B1HalfDiscCompletedBarrier_v468
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open ChartMetricProvider.Variational.IsothermalPDELower.NativeDirichlet
set_option maxHeartbeats 800000
set_option maxRecDepth 100000

private theorem pack_native_pair_v468 (U : Set E2) (p : X U) :
    pack U (val U p) (grad U p) (Lp.memLp (valLp U p)) (Lp.memLp (gradLp U p)) = p.val := by
  have hv : (Lp.memLp (valLp U p)).toLp (val U p) = valLp U p :=
    Lp.toLp_coeFn (valLp U p) (Lp.memLp (valLp U p))
  have hg : (Lp.memLp (gradLp U p)).toLp (grad U p) = gradLp U p :=
    Lp.toLp_coeFn (gradLp U p) (Lp.memLp (gradLp U p))
  unfold pack
  rw [hv,hg]
  rfl

/-- Coercivity and a classical positive barrier imply comparison for the native Dirichlet solution. -/
theorem halfdisc_native_barrier_comparison_v468
    (R δ : ℝ) (hδ : 0 < δ) (O : Set E2) (hO : IsOpen O) (hUO : halfDisc R ⊆ O)
    (a : E2 → Mat2) (b : E2 → E2) (c v : E2 → ℝ)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) O)
    (hb : ContDiffOn ℝ ∞ b O) (hc : ContDiffOn ℝ ∞ c O)
    (hv : ContDiff ℝ ∞ v)
    (hvlp : MemLp v 2 (volume.restrict (halfDisc R)))
    (hdvlp : MemLp (planarGradient v) 2 (volume.restrict (halfDisc R)))
    (hclp : MemLp c 2 (volume.restrict (halfDisc R)))
    (hLlp : MemLp (classicalL a b c v) 2 (volume.restrict (halfDisc R)))
    (hvle : ∀ x ∈ halfDisc R, v x ≤ 1)
    (hLv : ∀ x ∈ halfDisc R, 0 ≤ classicalL a b c v x)
    (F : Pair (halfDisc R) →L[ℝ] Pair (halfDisc R) →L[ℝ] ℝ)
    (hFeq : ∀ p q, F p q =
      ∫ x in halfDisc R, inner ℝ (matrixAction (a x) (p.snd x)) (q.snd x) -
        (inner ℝ (b x) (p.snd x) + c x * p.fst x) * q.fst x)
    (hcoer : ∀ q : X (halfDisc R), δ * ‖q‖ ^ 2 ≤ F q.val q.val)
    (p : X (halfDisc R))
    (hsolve : ∀ q : X (halfDisc R), F p.val q.val =
      ∫ x in halfDisc R, c x * val (halfDisc R) q x) :
    ∀ᵐ x ∂(volume.restrict (halfDisc R)), v x ≤ val (halfDisc R) p x + 1 := by
  classical
  let U := halfDisc R
  let μ := volume.restrict U
  have hU : IsOpen U := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous)
  haveI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr
    (lt_of_le_of_lt (measure_mono (show U ⊆ Metric.ball (0 : E2) R from fun x hx => hx.1))
      measure_ball_lt_top).ne
  have h1lp : MemLp (fun _ : E2 => (1 : ℝ)) 2 μ := memLp_const 1
  have h0lp : MemLp (fun _ : E2 => (0 : E2)) 2 μ := MemLp.zero
  let datum := pack U (fun _ : E2 => (1 : ℝ)) (fun _ : E2 => (0 : E2)) h1lp h0lp
  let V := pack U v (planarGradient v) hvlp hdvlp
  let n : X U := -p
  let w := fun x => v x - 1
  have hw : ContDiff ℝ ∞ w := hv.sub contDiff_const
  have hgradw : planarGradient w = planarGradient v := by
    funext x
    unfold w planarGradient
    rw [fderiv_fun_sub (hv.differentiable (by simp) x) (differentiableAt_const _)]
    simp
  have hwlp : MemLp w 2 μ := hvlp.sub h1lp
  have hdwlp : MemLp (planarGradient w) 2 μ := by rw [hgradw]; exact hdvlp
  have hwn : ∀ x ∈ U, w x ≤ 0 := fun x hx => sub_nonpos.mpr (hvle x hx)
  have hn := halfdisc_pair_native_h10_v468 R n
  have hsum := native_h1_add_smooth_v468 U (val U n) (grad U n) hn.1 w hw hwlp hdwlp
  let t := fun x => val U n x + w x
  let dt := fun x => grad U n x + planarGradient w x
  let z := fun x => max (t x) 0
  let dz := fun x => if 0 < t x then dt x else 0
  have hzt : H10On U z dz := halfdisc_native_offset_positive_h10_v468 R n w hw hwn hwlp hdwlp
  let Q : X U := ⟨pack U z dz hzt.1.2.1 hzt.1.2.2,
    (halfdisc_nativeH10_iff_pair_mem_export_v468 R z dz hzt.1.2.1 hzt.1.2.2).mp hzt⟩
  let T := pack U t dt hsum.2.1 hsum.2.2
  have hT : T = n.val + V - datum := by
    have hnp := pack_native_pair_v468 U n
    have hwpack : pack U w (planarGradient w) hwlp hdwlp = V - datum := by
      apply (WithLp.equiv 2 (Lp ℝ 2 μ × Lp E2 2 μ)).injective
      apply Prod.ext
      · change hwlp.toLp w = hvlp.toLp v - h1lp.toLp (fun _ : E2 => (1 : ℝ))
        exact MemLp.toLp_sub hvlp h1lp
      · change hdwlp.toLp (planarGradient w) = hdvlp.toLp (planarGradient v) - h0lp.toLp (fun _ : E2 => (0 : E2))
        apply Lp.ext
        filter_upwards [hdwlp.coeFn_toLp,hdvlp.coeFn_toLp,h0lp.coeFn_toLp,
          Lp.coeFn_sub (hdvlp.toLp (planarGradient v)) (h0lp.toLp (fun _ : E2 => (0 : E2)))] with x hx hvx h0x hsubx
        rw [hx,hsubx]
        change planarGradient w x = (hdvlp.toLp (planarGradient v)) x - (h0lp.toLp (fun _ : E2 => (0 : E2))) x
        rw [hvx,h0x,sub_zero]
        exact congrFun hgradw x
    calc
      T = pack U (val U n) (grad U n) hn.1.2.1 hn.1.2.2 +
        pack U w (planarGradient w) hwlp hdwlp := by rfl
      _ = n.val + V - datum := by rw [hnp,hwpack]; abel
  have hQV : F Q.val Q.val = F T Q.val := by
    rw [hFeq,hFeq]
    apply integral_congr_ae
    filter_upwards [hzt.1.2.1.coeFn_toLp,hzt.1.2.2.coeFn_toLp,
      hsum.2.1.coeFn_toLp,hsum.2.2.coeFn_toLp] with x hz hdz ht hdt
    change inner ℝ (matrixAction (a x) ((hzt.1.2.2.toLp _) x)) ((hzt.1.2.2.toLp _) x) -
      (inner ℝ (b x) ((hzt.1.2.2.toLp _) x) + c x * (hzt.1.2.1.toLp _) x) * (hzt.1.2.1.toLp _) x =
      inner ℝ (matrixAction (a x) ((hsum.2.2.toLp _) x)) ((hzt.1.2.2.toLp _) x) -
      (inner ℝ (b x) ((hsum.2.2.toLp _) x) + c x * (hsum.2.1.toLp _) x) * (hzt.1.2.1.toLp _) x
    rw [hz,hdz,ht,hdt]
    by_cases hx : 0 < t x
    · simp only [z,dz,hx,ite_true,max_eq_left hx.le]
      rfl
    · simp only [z,dz,hx,if_false,max_eq_right (le_of_not_gt hx)]
      simp
  have hdatum : F datum Q.val = -(∫ x in U, c x * val U Q x) := by
    rw [hFeq]
    have hload : IntegrableOn (fun x => c x * val U Q x) U :=
      hclp.integrable_mul (Lp.memLp (valLp U Q))
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [h1lp.coeFn_toLp,h0lp.coeFn_toLp] with x h1 h0
    change inner ℝ (matrixAction (a x) ((h0lp.toLp (fun _ => (0:E2))) x)) (grad U Q x) -
      (inner ℝ (b x) ((h0lp.toLp (fun _ => (0:E2))) x) + c x * (h1lp.toLp _) x) * val U Q x = _
    have ha0 : matrixAction (a x) (0 : E2) = 0 := by
      ext i
      simp [matrixAction]
    rw [h1,h0,ha0]
    simp
  have hV := halfdisc_classical_form_completed_identity_v468 R O hO hUO a b c v ha hb hc hv
    hvlp hdvlp hLlp F hFeq Q
  have hVnonpos : F V Q.val ≤ 0 := by
    rw [hV]
    have hnonneg : 0 ≤ ∫ x in U, classicalL a b c v x * val U Q x := by
      apply integral_nonneg_of_ae
      filter_upwards [ae_restrict_mem hU.measurableSet,hzt.1.2.1.coeFn_toLp] with x hx hz
      have hq : val U Q x = z x := hz
      rw [hq]
      exact mul_nonneg (hLv x hx) (le_max_right _ _)
    linarith
  have henergy : F Q.val Q.val ≤ 0 := by
    rw [hQV,hT]
    simp only [map_sub,map_add,add_apply,sub_apply]
    change F n Q.val + F V Q.val - F datum Q.val ≤ 0
    rw [show n.val = -p.val from rfl]
    simp only [map_neg,neg_apply]
    rw [hsolve Q,hdatum]
    linarith
  have hnorm : ‖Q‖ = 0 := by
    have hi := hcoer Q
    have hn : 0 ≤ δ * ‖Q‖ ^ 2 := mul_nonneg hδ.le (sq_nonneg _)
    have he : δ * ‖Q‖ ^ 2 = 0 := le_antisymm (hi.trans henergy) hn
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp he).resolve_left hδ.ne')
  have hQzero : Q = 0 := norm_eq_zero.mp hnorm
  have hz0 : z =ᵐ[μ] (fun _ => (0 : ℝ)) := by
    have hclass : hzt.1.2.1.toLp z = 0 := by
      have h := congrArg (fun q : X U => valLp U q) hQzero
      exact h
    have heq := hzt.1.2.1.coeFn_toLp
    rw [hclass] at heq
    exact heq.symm.trans (Lp.coeFn_zero ℝ 2 μ)
  have hnneg : val U n =ᵐ[μ] fun x => -val U p x := Lp.coeFn_neg (valLp U p)
  filter_upwards [hz0,hnneg] with x hz hnx
  have htx : t x ≤ 0 := by
    have hle : t x ≤ z x := le_max_left _ _
    rw [hz] at hle
    exact hle
  dsimp [t,w] at htx
  rw [hnx] at htx
  linarith

end SeifertSurfaces.OriginalEndpoints.B1Tangency
