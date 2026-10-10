import VM03ExactCaller_v464
import B1CollarMetricExtensions
noncomputable section
open Set Topology Function MeasureTheory
open scoped Manifold ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
universe v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}
set_option maxHeartbeats 0
theorem actual_collar_window (D : B1OriginalData g J) (s : Circle) :
    Nonempty (CollarWindow D s) := by
  let R := min D.r0 (D.leafLength / 4) / 2
  have hm : 0 < min D.r0 (D.leafLength / 4) := lt_min D.r0_pos (div_pos D.leafLength_pos (by norm_num))
  have hR : 0 < R := by dsimp [R]; positivity
  have hr : R < D.r0 := by dsimp [R]; linarith [min_le_left D.r0 (D.leafLength / 4)]
  have hl : 4 * R < D.leafLength := by dsimp [R]; linarith [min_le_right D.r0 (D.leafLength / 4)]
  let P : E2 → Circle × ℝ := fun x => (localCircle D s (x 0), x 1)
  have hP : ContMDiff 𝓘(ℝ, E2) ((𝓡 1).prod 𝓘(ℝ)) ∞ P := by
    have ha : ContDiff ℝ ∞ (fun x : E2 => 2 * Real.pi * x 0 / D.leafLength) := by fun_prop
    have hb : ContMDiff 𝓘(ℝ, E2) (𝓡 1) ∞ (fun x : E2 => localCircle D s (x 0)) :=
      contMDiff_const.mul (contMDiff_circleExp.comp ha.contMDiff)
    exact hb.prodMk (by apply ContDiff.contMDiff; fun_prop)
  let U := P ⁻¹' D.extendedDomain
  have hU : IsOpen U := D.extendedDomain_open.preimage hP.continuous
  have hcontains : closedHalfDisc R ⊆ U := by
    intro x hx
    apply D.extendedDomain_contains
    change x 1 ∈ Icc (0 : ℝ) D.r0
    have hn : ‖x‖ ≤ R := by
      have hxball : x ∈ Metric.closedBall (0 : E2) R := hx.1
      have hd : dist x 0 ≤ R := Metric.mem_closedBall.mp hxball
      rwa [dist_zero_right] at hd
    exact ⟨hx.2, (le_trans (le_trans (le_abs_self _)
      (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x 1)) hn).trans hr.le⟩
  have hsmooth : ContDiffOn ℝ ∞ (localHeight D s) U :=
    (D.f_smooth.comp hP.contMDiffOn (fun _ h => h)).contDiffOn
  have metricExtension : ∃ (V : Set E3) (hV : IsOpen V) (G : CoordinateMetric V),
      (∀ x ∈ closedHalfDisc R, ∀ t ∈ Icc (0 : ℝ) 1,
        jetPoint (x, t * localHeight D s x, t • planarGradient (localHeight D s) x) ∈ V) ∧
      (∀ y ∈ V ∩ collarDomain D R, ∀ i j : Fin 3,
        G.tensor y i j =
          g.inner (localCollar D s y)
            (mfderivWithin 𝓘(ℝ, E3) (𝓡∂ 3) (localCollar D s) (collarDomain D R) y
              ((NormedSpace.fromTangentSpace y).symm (coordinateVector 3 i)))
            (mfderivWithin 𝓘(ℝ, E3) (𝓡∂ 3) (localCollar D s) (collarDomain D R) y
              ((NormedSpace.fromTangentSpace y).symm (coordinateVector 3 j)))) := by
    classical
    let H := closedHalfDisc R
    let Q := H ×ˢ Icc (0 : ℝ) 1
    let F : E2 × ℝ → E3 := fun p => jetPoint
      (p.1, p.2 * localHeight D s p.1, p.2 • planarGradient (localHeight D s) p.1)
    have hHcompact : IsCompact H :=
      (isCompact_closedBall (0 : E2) R).inter_right
        (isClosed_le continuous_const (EuclideanSpace.proj (1 : Fin 2)).continuous)
    have hQcompact : IsCompact Q := hHcompact.prod isCompact_Icc
    have hF : ContinuousOn F Q := by
      apply (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous.comp_continuousOn
      apply continuousOn_pi.mpr
      intro i
      fin_cases i
      · exact (EuclideanSpace.proj (0 : Fin 2)).continuous.continuousOn.comp
          continuousOn_fst (fun p hp => hp.1)
      · exact (EuclideanSpace.proj (1 : Fin 2)).continuous.continuousOn.comp
          continuousOn_fst (fun p hp => hp.1)
      · exact continuousOn_snd.mul
          ((hsmooth.continuousOn.mono hcontains).comp continuousOn_fst (fun p hp => hp.1))
    let K0 := F '' Q
    have hKcompact : IsCompact K0 := hQcompact.image_of_continuousOn hF
    have hcoord (x : E2) (hx : x ∈ H) (i : Fin 2) : |x i| ≤ R := by
      have hxi : |x i| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i
      exact hxi.trans
        (by simpa [dist_zero_right] using Metric.mem_closedBall.mp hx.1)
    have hKdomain : K0 ⊆ collarDomain D R := by
      rintro y ⟨⟨x,t⟩, ⟨hx,ht⟩, rfl⟩
      change |x 0| < 2 * R ∧ x 1 ∈ Icc (0 : ℝ) D.r0 ∧
        |t * localHeight D s x| < D.eta
      have hrx : x 1 ∈ Icc (0 : ℝ) D.r0 :=
        ⟨hx.2, (le_abs_self _).trans ((hcoord x hx 1).trans hr.le)⟩
      refine ⟨lt_of_le_of_lt (hcoord x hx 0) (by linarith), hrx, ?_⟩
      have hf := D.graph_inside (localCircle D s (x 0)) (x 1) hrx
      rw [abs_mul, abs_of_nonneg ht.1]
      exact (mul_le_of_le_one_left (abs_nonneg _) ht.2).trans_lt hf
    have hKradial : ∀ y ∈ K0, y 1 < D.r0 := by
      rintro y ⟨⟨x,t⟩, ⟨hx,ht⟩, rfl⟩
      exact ((le_abs_self (x 1)).trans (hcoord x hx 1)).trans_lt hr
    have hlocal := CollarMetricExtensions.actual_collar_local_positive_coefficient_extension
      D s R hR hr hl K0 hKcompact hKdomain hKradial
    have hindexed (y : K0) : ∃ O : Set E3, IsOpen O ∧ y.val ∈ O ∧
        ∃ M : CoordinateMetric O, ∀ z ∈ O ∩ collarDomain D R,
          M.tensor z = CollarMetricExtensions.actualCollarCoefficients D s R z :=
      hlocal y.val y.property
    choose O hO hy M hM using hindexed
    have hcover : K0 ⊆ ⋃ y : K0, O y := by
      intro y hyK
      exact mem_iUnion.mpr ⟨⟨y,hyK⟩, hy ⟨y,hyK⟩⟩
    obtain ⟨n,selected,V,hV,hKV,hcl,ρ,hρ,G,hG,hactual⟩ :=
      CollarMetricExtensions.finite_positive_coefficient_gluing K0 (collarDomain D R)
        hKcompact hKdomain (CollarMetricExtensions.actualCollarCoefficients D s R)
        O hO M hcover hM
    refine ⟨V,hV,G,?_,?_⟩
    · intro x hx t ht
      exact hKV ⟨(x,t),⟨hx,ht⟩,rfl⟩
    · intro y hy i j
      exact congrFun (congrFun (hactual y hy) i) j
  obtain ⟨V, hV, G, hjets, hactual⟩ := metricExtension
  exact ⟨⟨R, hR, hr, hl, U, hU, hcontains, hsmooth, V, hV, G, hjets, hactual⟩⟩

end SeifertSurfaces.OriginalEndpoints.B1Tangency
