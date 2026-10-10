import A5SectorC1Extension
import A5RegularSectorBoundary

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.LongitudeProducers
open SeifertSurfaces.LongitudeProducers.QuotientChartHelpers

private theorem polar_complex (r t : ℝ) :
    complexCoordinates (polarPoint r t) = (r : ℂ) * Complex.exp ((t : ℂ) * Complex.I) := by
  rw [Complex.exp_mul_I]
  apply Complex.ext <;> simp [complexCoordinates, polarPoint]

/-- The centered polar branch reconstructs every point, independently of
whether that point belongs to the sector. -/
theorem centered_polar_reconstruction (θ : ℝ) (x : Euc 2) :
    polarPoint ‖x‖ (centeredSectorAngle θ x) = x := by
  apply complexCoordinatesEquiv.injective
  change complexCoordinates _ = complexCoordinates x
  rw [polar_complex]
  have hn : ‖centeredSectorComplex θ x‖ = ‖x‖ := by
    simp [centeredSectorComplex, Complex.norm_exp, complex_coordinates_norm]
  have hsplit : ((centeredSectorAngle θ x : ℝ) : ℂ) * Complex.I =
      ((Complex.arg (centeredSectorComplex θ x) : ℝ) : ℂ) * Complex.I +
        Complex.I * (θ : ℂ) / 2 := by
    simp only [centeredSectorAngle, Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_ofNat]
    ring
  rw [hsplit, Complex.exp_add, ← mul_assoc, ← hn, Complex.norm_mul_exp_arg_mul_I]
  dsimp only [centeredSectorComplex]
  rw [mul_assoc, ← Complex.exp_add]
  have he : -(Complex.I * (θ : ℂ)) / 2 + Complex.I * (θ : ℂ) / 2 = 0 := by ring
  rw [show -Complex.I * (θ : ℂ) / 2 = -(Complex.I * (θ : ℂ)) / 2 by ring, he,
    Complex.exp_zero, mul_one]

theorem planar_sector_iff_centered_angle
    (θ : ℝ) (hθ : 0 < θ) (hθπ : θ < 2 * Real.pi)
    (x : Euc 2) (hx0 : x ≠ 0) :
    x ∈ planarSector θ ↔ centeredSectorAngle θ x ∈ Icc (0 : ℝ) θ := by
  constructor
  · intro hx
    have hp : x ∈ polygonSector θ := by
      obtain ⟨r, hr, t, ht, he⟩ := hx
      refine ⟨r, t, hr, ht, ?_⟩
      rw [he]
      ext i
      fin_cases i <;> rfl
    exact (centered_sector_argument θ ⟨hθ, hθπ⟩ ⟨x, hp⟩ hx0).2.1
  · intro hx
    refine ⟨‖x‖, norm_nonneg x, centeredSectorAngle θ x, hx, ?_⟩
    have he := centered_polar_reconstruction θ x
    convert he.symm using 1
    ext i
    fin_cases i <;> rfl

theorem centered_angle_smooth_on_sector_nonzero
    (θ : ℝ) (hθ : 0 < θ) (hθπ : θ < 2 * Real.pi)
    (x : Euc 2) (hx : x ∈ planarSector θ) (hx0 : x ≠ 0) :
    ContDiffAt ℝ ∞ (centeredSectorAngle θ) x := by
  have hp : x ∈ polygonSector θ := by
    obtain ⟨r, hr, t, ht, he⟩ := hx
    refine ⟨r, t, hr, ht, ?_⟩
    rw [he]
    ext i
    fin_cases i <;> rfl
  have hs := (centered_sector_argument θ ⟨hθ, hθπ⟩ ⟨x, hp⟩ hx0).1
  have hc : ContDiff ℝ ∞ (centeredSectorComplex θ) :=
    (complexCoordinatesEquiv.contDiff (n := ∞)).mul contDiff_const
  have hl := ((Complex.contDiffAt_log (n := ∞) hs).restrict_scalars ℝ).comp x hc.contDiffAt
  have hi := Complex.imCLM.contDiff.contDiffAt.comp x hl
  change ContDiffAt ℝ ∞ (fun z => Complex.arg (centeredSectorComplex θ z) + θ / 2) x
  simpa only [Function.comp_def, Complex.imCLM_apply, Complex.log_im] using
    hi.add (contDiffAt_const (c := θ / 2))

/-- Near a nonzero point of either radial boundary, the native domain is
exactly one side of a smooth centered angular defining function. -/
theorem centered_angle_derivative_surjective
    (θ : ℝ) (hθ : 0 < θ) (hθπ : θ < 2 * Real.pi)
    (x : Euc 2) (hx : x ∈ planarSector θ) (hx0 : x ≠ 0) :
    Function.Surjective (fderiv ℝ (centeredSectorAngle θ) x) := by
  let t := centeredSectorAngle θ x
  have ht : t ∈ Icc (0 : ℝ) θ := (planar_sector_iff_centered_angle θ hθ hθπ x hx0).mp hx
  let p : ℝ → Euc 2 := fun s => polarPoint ‖x‖ s
  have hp : ContDiff ℝ ∞ p := by
    apply (contDiff_piLp (p := 2)).mpr
    intro i
    fin_cases i <;> dsimp [p, polarPoint] <;> fun_prop
  have hpx : p t = x := centered_polar_reconstruction θ x
  have hc := (centered_angle_smooth_on_sector_nonzero θ hθ hθπ x hx hx0).differentiableAt (by simp)
  have hdx : HasFDerivAt (centeredSectorAngle θ) (fderiv ℝ (centeredSectorAngle θ) x) (p t) :=
    hpx.symm ▸ hc.hasFDerivAt
  have hcomp := hdx.comp_hasDerivAt t ((hp.differentiable (by simp)) t).hasDerivAt
  have heq : EqOn (centeredSectorAngle θ ∘ p) id (Icc (0 : ℝ) θ) := by
    intro s hs
    exact centered_angle_polar θ ‖x‖ s ⟨hθ, hθπ⟩ (norm_pos_iff.mpr hx0) hs
  have hd := hcomp.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hθ t ht)
  have hv : (fderiv ℝ (centeredSectorAngle θ) x) (deriv p t) = 1 := by
    rw [derivWithin_congr heq (heq ht), derivWithin_id t (Icc 0 θ) (uniqueDiffOn_Icc hθ t ht)] at hd
    exact hd.symm
  intro y
  refine ⟨y • deriv p t, ?_⟩
  rw [map_smul, hv, smul_eq_mul, mul_one]

/-- Near a nonzero point of either radial boundary, the native domain is
exactly one side of a smooth regular defining function. -/
theorem nonzero_sector_boundary_defining_function
    (A : SectorModel) (x : Euc 2)
    (hx : x ∈ A.domain ∩ frontier A.domain) (hx0 : x ≠ 0) :
    ∃ s : Euc 2 → ℝ, ContDiffAt ℝ ∞ s x ∧ s x = 0 ∧
      Function.Surjective (fderiv ℝ s x) ∧
      (∀ᶠ z in 𝓝 x, z ∈ A.domain ↔ 0 ≤ s z) := by
  have hxb : x ∈ A.boundary := by
    by_contra hn
    exact hx.2.2 (by rw [AreaCertificates.sector_model_interior]; exact ⟨hx.1, hn⟩)
  have hfalse : A.interiorChart = false := by
    cases h : A.interiorChart
    · rfl
    · simp [SectorModel.boundary, h] at hxb
  have hdom : A.domain = Metric.ball 0 A.radius ∩ planarSector A.angle := by
    simp [SectorModel.domain, hfalse]
  have hxD := hx.1
  rw [hdom] at hxD
  have hxc := centered_angle_smooth_on_sector_nonzero A.angle A.angle_positive A.angle_lt_two_pi x hxD.2 hx0
  have hsurj := centered_angle_derivative_surjective A.angle A.angle_positive A.angle_lt_two_pi x hxD.2 hx0
  have hbd : x ∈ sectorBoundary A.angle := by
    simpa [SectorModel.boundary, hfalse] using hxb.2
  obtain ⟨r, hr, he | he⟩ := hbd
  all_goals
    have hrp : 0 < r := by
      apply lt_of_le_of_ne hr
      intro hz
      apply hx0
      rw [he, ← hz, zero_smul]
  · have hang : centeredSectorAngle A.angle x = 0 := by
      rw [he]
      exact centered_angle_polar A.angle r 0 ⟨A.angle_positive, A.angle_lt_two_pi⟩ hrp
        ⟨le_rfl, A.angle_positive.le⟩
    refine ⟨centeredSectorAngle A.angle, hxc, hang, hsurj, ?_⟩
    have hlt : ∀ᶠ z in 𝓝 x, centeredSectorAngle A.angle z < A.angle :=
      hxc.continuousAt.eventually_lt_const (by rw [hang]; exact A.angle_positive)
    filter_upwards [Metric.isOpen_ball.mem_nhds hxD.1, hlt,
      isOpen_compl_singleton.mem_nhds hx0] with z hzB hzA hz0
    rw [hdom, mem_inter_iff, and_iff_right hzB,
      planar_sector_iff_centered_angle A.angle A.angle_positive A.angle_lt_two_pi z hz0]
    exact and_iff_left hzA.le
  · have hang : centeredSectorAngle A.angle x = A.angle := by
      rw [he]
      exact centered_angle_polar A.angle r A.angle ⟨A.angle_positive, A.angle_lt_two_pi⟩ hrp
        ⟨A.angle_positive.le, le_rfl⟩
    refine ⟨fun z => A.angle - centeredSectorAngle A.angle z,
      contDiffAt_const.sub hxc, by dsimp only; rw [hang, sub_self], ?_, ?_⟩
    · intro y
      obtain ⟨v, hv⟩ := hsurj (-y)
      refine ⟨v, ?_⟩
      rw [((hxc.differentiableAt (by simp)).hasFDerivAt.const_sub A.angle).fderiv]
      simp [hv]
    have hlt : ∀ᶠ z in 𝓝 x, 0 < centeredSectorAngle A.angle z :=
      hxc.continuousAt.eventually_const_lt (by rw [hang]; exact A.angle_positive)
    filter_upwards [Metric.isOpen_ball.mem_nhds hxD.1, hlt,
      isOpen_compl_singleton.mem_nhds hx0] with z hzB hzA hz0
    rw [hdom, mem_inter_iff, and_iff_right hzB,
      planar_sector_iff_centered_angle A.angle A.angle_positive A.angle_lt_two_pi z hz0]
    exact (and_iff_right hzA.le).trans (sub_nonneg.symm)

/-- At every regular native sector boundary point, including a straight
polar origin, the literal domain has a smooth regular local defining function. -/
theorem regular_sector_boundary_defining_function
    (A : SectorModel) (x : Euc 2) (hx : x ∈ A.domain ∩ frontier A.domain)
    (hregular : x ≠ 0 ∨ A.angle = Real.pi) :
    ∃ s : Euc 2 → ℝ, ContDiffAt ℝ ∞ s x ∧ s x = 0 ∧
      Function.Surjective (fderiv ℝ s x) ∧
      (∀ᶠ z in 𝓝 x, z ∈ A.domain ↔ 0 ≤ s z) := by
  by_cases hn : x = 0
  · subst x
    have ha : A.angle = Real.pi := hregular.resolve_left (by simp)
    have hb : A.interiorChart = false := by
      cases h : A.interiorChart
      · rfl
      · have hi : IsOpen A.domain := by simp [SectorModel.domain, h]
        exact False.elim (hx.2.2 (by rw [hi.interior_eq]; exact hx.1))
    let L := EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)
    refine ⟨L, L.contDiff.contDiffAt, map_zero _, ?_, ?_⟩
    · rw [L.fderiv]
      intro y
      exact ⟨!₂[0, y], rfl⟩
    · filter_upwards [Metric.ball_mem_nhds (0 : Euc 2) A.radius_positive] with z hz
      simp only [SectorModel.domain, hb, Bool.false_eq_true, ↓reduceIte, ha,
        planar_sector_pi_upper_halfplane, mem_inter_iff, mem_ofPred_eq, and_iff_right hz]
      rfl
  · exact nonzero_sector_boundary_defining_function A x hx hn

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
