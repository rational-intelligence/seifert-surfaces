import DiagramExtensionRemaining
import QuotientPolarHelpers
import A5SectorLocalInverse
import A5RectangleLocalExtension
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.LongitudeProducers
open SeifertSurfaces.LongitudeProducers.QuotientChartHelpers
open SeifertSurfaces.LongitudeProducers.DiagramRemainingHelpers

theorem planar_sector_pi_upper_halfplane :
    planarSector Real.pi = {z : Euc 2 | 0 ≤ z 1} := by
  ext x
  constructor
  · rintro ⟨r, hr, t, ht, rfl⟩
    exact mul_nonneg hr (Real.sin_nonneg_of_nonneg_of_le_pi ht.1 ht.2)
  · intro hx
    let z : ℂ := ⟨x 0, x 1⟩
    refine ⟨‖z‖, norm_nonneg z, Complex.arg z,
      ⟨Complex.arg_nonneg_iff.mpr hx, Complex.arg_le_pi z⟩, ?_⟩
    ext i
    fin_cases i
    · exact (Complex.norm_mul_cos_arg z).symm
    · exact (Complex.norm_mul_sin_arg z).symm

/-- A straight native sector also has a local C1 extension at its polar
origin, preserving its actual closed-domain derivative. -/
theorem C1_straight_sector_extension_at_origin
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (R : ℝ) (hR : 0 < R) (G : Euc 2 → V)
    (hG : ContDiffWithinAt ℝ 1 G (Metric.ball 0 R ∩ planarSector Real.pi) 0) :
    ∃ g : Euc 2 → V, ContDiffAt ℝ 1 g 0 ∧
      g =ᶠ[𝓝[Metric.ball 0 R ∩ planarSector Real.pi] 0] G ∧
      fderiv ℝ g 0 = fderivWithin ℝ G (Metric.ball 0 R ∩ planarSector Real.pi) 0 := by
  let δ := R / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let a : Euc 2 := !₂[-δ, 0]
  let b : Euc 2 := !₂[δ, δ]
  let T := euclideanRectangle a b
  have hab : ∀ i, a i < b i := by
    intro i
    fin_cases i
    · change -δ < δ; linarith
    · exact hδ
  have hzT : (0 : Euc 2) ∈ T := by
    intro i
    fin_cases i
    · exact ⟨by change -δ ≤ 0; linarith, hδ.le⟩
    · exact ⟨le_rfl, hδ.le⟩
  have hsub : T ⊆ Metric.ball 0 R ∩ planarSector Real.pi := by
    intro z hz
    have hz0 : -δ ≤ z 0 ∧ z 0 ≤ δ := hz 0
    have hz1 : 0 ≤ z 1 ∧ z 1 ≤ δ := hz 1
    refine ⟨?_, ?_⟩
    · have hs : ‖z‖ ^ 2 = (z 0) ^ 2 + (z 1) ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq]
        simp only [Fin.sum_univ_two]
      have hb0 := sq_le_sq₀ (abs_nonneg (z 0)) hδ.le |>.mpr (abs_le.mpr hz0)
      have hb1 := sq_le_sq₀ hz1.1 hδ.le |>.mpr hz1.2
      rw [sq_abs] at hb0
      rw [Metric.mem_ball, dist_zero_right]
      dsimp [δ] at hb0 hb1
      nlinarith [norm_nonneg z]
    · rw [planar_sector_pi_upper_halfplane]
      exact hz1.1
  obtain ⟨g, hg, heqT, _⟩ := C1_rectangle_local_extension a b hab G 0 hzT (hG.mono hsub)
  have hnear : ∀ᶠ z in 𝓝[Metric.ball 0 R ∩ planarSector Real.pi] (0 : Euc 2), z ∈ T := by
    filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : Euc 2) hδ),
      self_mem_nhdsWithin] with z hz hzS
    have hn : ‖z‖ < δ := by simpa only [Metric.mem_ball, dist_zero_right] using hz
    have hb (i : Fin 2) : |z i| < δ := (PiLp.norm_apply_le z i).trans_lt hn
    rw [planar_sector_pi_upper_halfplane] at hzS
    intro i
    fin_cases i
    · exact ⟨(abs_lt.mp (hb 0)).1.le, (abs_lt.mp (hb 0)).2.le⟩
    · exact ⟨hzS.2, (abs_lt.mp (hb 1)).2.le⟩
  have htend : Tendsto id (𝓝[Metric.ball 0 R ∩ planarSector Real.pi] (0 : Euc 2)) (𝓝[T] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨nhdsWithin_le_nhds, hnear⟩
  have heq : g =ᶠ[𝓝[Metric.ball 0 R ∩ planarSector Real.pi] 0] G := htend.eventually heqT
  have hzS : (0 : Euc 2) ∈ Metric.ball 0 R ∩ planarSector Real.pi := hsub hzT
  have hu : UniqueDiffWithinAt ℝ (Metric.ball 0 R ∩ planarSector Real.pi) 0 := by
    simpa only [inter_comm] using
      (planarSector_uniqueDiffWithinAt_zero Real.pi_pos (by linarith [Real.pi_pos])).inter
        (Metric.isOpen_ball.mem_nhds hzS.1)
  exact ⟨g, hg, heq, ((hg.differentiableAt (by norm_num)).fderivWithin hu).symm.trans
    (heq.fderivWithin_eq (heq.self_of_nhdsWithin hzS))⟩

/-- Away from the polar origin the actual closed-sector C1 map has a local
C1 extension to the ambient plane. Reflex openings are retained, using a
centered polar branch and the certified finite rectangle extension. -/
theorem C1_sector_extension_away_origin
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (θ R : ℝ) (hθ : 0 < θ) (hθπ : θ < 2 * Real.pi)
    (G : Euc 2 → V)
    (x : Euc 2) (hx : x ∈ Metric.ball 0 R ∩ planarSector θ) (hx0 : x ≠ 0)
    (hG : ContDiffWithinAt ℝ 1 G (Metric.ball 0 R ∩ planarSector θ) x) :
    ∃ g : Euc 2 → V, ContDiffAt ℝ 1 g x ∧
      g =ᶠ[𝓝[Metric.ball 0 R ∩ planarSector θ] x] G ∧
      fderiv ℝ g x = fderivWithin ℝ G (Metric.ball 0 R ∩ planarSector θ) x := by
  have hpoly (z : Euc 2) (hz : z ∈ planarSector θ) : z ∈ polygonSector θ := by
    obtain ⟨r, hr, t, ht, he⟩ := hz
    refine ⟨r, t, hr, ht, ?_⟩
    rw [he]
    ext i
    fin_cases i <;> rfl
  have harg := centered_sector_argument θ ⟨hθ, hθπ⟩ ⟨x, hpoly x hx.2⟩ hx0
  let a : Euc 2 := !₂[‖x‖ / 2, 0]
  let b : Euc 2 := !₂[(‖x‖ + R) / 2, θ]
  let T := euclideanRectangle a b
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hxR : ‖x‖ < R := by simpa only [Metric.mem_ball, dist_zero_right] using hx.1
  have hab : ∀ i, a i < b i := by
    intro i
    fin_cases i
    · change ‖x‖ / 2 < (‖x‖ + R) / 2
      linarith
    · exact hθ
  let Φ : Euc 2 → Euc 2 := fun z => polarPoint (z 0) (z 1)
  have hΦ : ContDiff ℝ 1 Φ := by
    apply (contDiff_piLp (p := 2)).mpr
    intro i
    fin_cases i <;> dsimp [Φ, polarPoint] <;> fun_prop
  have hΦmaps : MapsTo Φ T (Metric.ball 0 R ∩ planarSector θ) := by
    intro z hz
    have hz0 : ‖x‖ / 2 ≤ z 0 ∧ z 0 ≤ (‖x‖ + R) / 2 := hz 0
    have hz1 : z 1 ∈ Icc (0 : ℝ) θ := hz 1
    have hr : 0 ≤ z 0 := by linarith
    refine ⟨?_, z 0, hr, z 1, hz1, ?_⟩
    · change dist (polarPoint (z 0) (z 1)) 0 < R
      rw [dist_zero_right, polar_radius _ _ hr]
      linarith
    · ext i
      fin_cases i <;> rfl
  let ψ : Euc 2 → Euc 2 := fun z => !₂[‖z‖, centeredSectorAngle θ z]
  have hψ : ContDiffAt ℝ 1 ψ x := by
    apply (contDiffAt_piLp (p := 2)).mpr
    intro i
    fin_cases i
    · exact contDiffAt_norm ℝ hx0
    · change ContDiffAt ℝ 1 (fun z => Complex.arg (centeredSectorComplex θ z) + θ / 2) x
      have hc : ContDiff ℝ 1 (centeredSectorComplex θ) :=
        (complexCoordinatesEquiv.contDiff (n := 1)).mul contDiff_const
      have hl := ((Complex.contDiffAt_log (n := 1) harg.1).restrict_scalars ℝ).comp x hc.contDiffAt
      have hi := Complex.imCLM.contDiff.contDiffAt.comp x hl
      simpa only [Function.comp_def, Complex.imCLM_apply, Complex.log_im] using
        hi.add (contDiffAt_const (c := θ / 2))
  have hψx : ψ x ∈ T := by
    intro i
    fin_cases i
    · change ‖x‖ / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ (‖x‖ + R) / 2
      constructor <;> linarith
    · exact harg.2.1
  have hΦψ : Φ (ψ x) = x := harg.2.2.symm
  have hGF : ContDiffWithinAt ℝ 1 (G ∘ Φ) T (ψ x) :=
    (hΦψ.symm ▸ hG).comp (ψ x) hΦ.contDiffAt.contDiffWithinAt hΦmaps
  obtain ⟨e, he, heqT, _⟩ := C1_rectangle_local_extension a b hab (G ∘ Φ) (ψ x) hψx hGF
  let g := e ∘ ψ
  have hg : ContDiffAt ℝ 1 g x := he.comp x hψ
  have hnear : ∀ᶠ z in 𝓝 x, ‖x‖ / 2 < ‖z‖ ∧ ‖z‖ < (‖x‖ + R) / 2 :=
    continuous_norm.continuousAt.eventually
      (Ioo_mem_nhds (by linarith) (by linarith))
  have hψmaps : ∀ᶠ z in 𝓝[Metric.ball 0 R ∩ planarSector θ] x, ψ z ∈ T ∧ Φ (ψ z) = z := by
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hzS
    have hz0 : z ≠ 0 := by
      intro he
      rw [he, norm_zero] at hz
      linarith [hz.1]
    have har := centered_sector_argument θ ⟨hθ, hθπ⟩ ⟨z, hpoly z hzS.2⟩ hz0
    have hzT : ψ z ∈ T := by
      intro i
      fin_cases i
      · exact ⟨hz.1.le, hz.2.le⟩
      · exact har.2.1
    exact ⟨hzT, har.2.2.symm⟩
  have htend : Tendsto ψ (𝓝[Metric.ball 0 R ∩ planarSector θ] x) (𝓝[T] (ψ x)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hψ.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,
      hψmaps.mono (fun _ hz => hz.1)⟩
  have heq : g =ᶠ[𝓝[Metric.ball 0 R ∩ planarSector θ] x] G := by
    filter_upwards [htend.eventually heqT, hψmaps] with z hz hzmap
    exact hz.trans (congrArg G hzmap.2)
  refine ⟨g, hg, heq, ?_⟩
  have hu : UniqueDiffWithinAt ℝ (Metric.ball 0 R ∩ planarSector θ) x := by
    simpa only [inter_comm] using (planarSector_uniqueDiffOn hθ hθπ x hx.2).inter
      (Metric.isOpen_ball.mem_nhds hx.1)
  exact ((hg.differentiableAt (by norm_num)).fderivWithin hu).symm.trans
    (heq.fderivWithin_eq (heq.self_of_nhdsWithin hx))

/-- Every noncorner native sector point has an ambient C1 extension with its
literal within derivative. Interior charts are included. -/
theorem C1_sector_model_extension
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (A : SectorModel) (G : Euc 2 → V) (x : Euc 2) (hx : x ∈ A.domain)
    (hregular : x ≠ 0 ∨ A.angle = Real.pi)
    (hG : ContDiffWithinAt ℝ 1 G A.domain x) :
    ∃ g : Euc 2 → V, ContDiffAt ℝ 1 g x ∧
      g =ᶠ[𝓝[A.domain] x] G ∧ fderiv ℝ g x = fderivWithin ℝ G A.domain x := by
  cases h : A.interiorChart
  · have hdom : A.domain = Metric.ball 0 A.radius ∩ planarSector A.angle := by
      simp [SectorModel.domain, h]
    rw [hdom] at hx hG ⊢
    rcases hregular with hn | ha
    · exact C1_sector_extension_away_origin A.angle A.radius A.angle_positive A.angle_lt_two_pi G x hx hn hG
    · by_cases hn : x = 0
      · subst x
        rw [ha] at hG ⊢
        exact C1_straight_sector_extension_at_origin A.radius A.radius_positive G hG
      · exact C1_sector_extension_away_origin A.angle A.radius A.angle_positive A.angle_lt_two_pi G x hx hn hG
  · have hdom : A.domain = Metric.ball 0 A.radius := by simp [SectorModel.domain, h]
    have hn : A.domain ∈ 𝓝 x := by rw [hdom] at hx ⊢; exact Metric.isOpen_ball.mem_nhds hx
    have hg := hG.contDiffAt hn
    exact ⟨G, hg, Filter.EventuallyEq.rfl, ((hg.differentiableAt (by norm_num)).fderivWithin
      (A.uniqueDiffOn_domain x hx)).symm⟩

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
