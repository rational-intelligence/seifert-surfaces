import DiskBandQuotientCharts
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

set_option autoImplicit false
set_option maxSynthPendingDepth 3
open Set Topology
namespace SeifertSurfaces.LongitudeProducers.QuotientChartHelpers
open Foundations MetricFoundations
noncomputable section
attribute [local instance] Classical.propDecidable

/-- P1. The norm is the Euclidean norm inherited from Euc 2. -/
theorem polar_radius (r θ : ℝ) (hr : 0 ≤ r) : ‖polarPoint r θ‖ = r := by
  have h := EuclideanSpace.real_norm_sq_eq (polarPoint r θ)
  simp only [Fin.sum_univ_two, polarPoint] at h
  simp at h
  apply (sq_eq_sq₀ (norm_nonneg _) hr).mp
  change ‖!₂[r * Real.cos θ, r * Real.sin θ]‖ ^ 2 = r ^ 2
  rw [h]
  calc
    (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 =
        r ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by ring
    _ = r ^ 2 := by rw [Real.cos_sq_add_sin_sq, mul_one]

theorem polar_positive_unique (a r s θ φ : ℝ)
    (ha : 0 < a ∧ a < 2 * Real.pi) (hr : 0 < r) (hs : 0 < s)
    (hθ : θ ∈ Icc (0 : ℝ) a) (hφ : φ ∈ Icc (0 : ℝ) a)
    (heq : polarPoint r θ = polarPoint s φ) : r = s ∧ θ = φ := by
  have hrs : r = s := by
    have h := congrArg norm heq
    simpa only [polar_radius r θ hr.le, polar_radius s φ hs.le] using h
  refine ⟨hrs, ?_⟩
  have hc : Real.cos θ = Real.cos φ := by
    have h := congrArg (fun x : Euc 2 => x 0) heq
    simp only [polarPoint] at h
    simp at h
    rw [← hrs] at h
    exact mul_left_cancel₀ hr.ne' h
  have hs' : Real.sin θ = Real.sin φ := by
    have h := congrArg (fun x : Euc 2 => x 1) heq
    simp only [polarPoint] at h
    simp at h
    rw [← hrs] at h
    exact mul_left_cancel₀ hr.ne' h
  have he : (θ : Real.Angle) = (φ : Real.Angle) := Real.Angle.cos_sin_inj hc hs'
  letI : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico
    (show θ ∈ Ico (0 : ℝ) (0 + 2 * Real.pi) from ⟨hθ.1, by linarith [hθ.2, ha.2]⟩)
    (show φ ∈ Ico (0 : ℝ) (0 + 2 * Real.pi) from ⟨hφ.1, by linarith [hφ.2, ha.2]⟩)).mp he

theorem polar_vertex (θ : ℝ) : polarPoint 0 θ = 0 := by
  ext i
  fin_cases i <;> simp [polarPoint]

/-- P2. Centering the branch cut permits reflex sectors. -/
def complexCoordinates (x : Euc 2) : ℂ := (x 0 : ℂ) + Complex.I * (x 1 : ℂ)

def complexCoordinatesInverse (z : ℂ) : Euc 2 := !₂[z.re, z.im]

def complexCoordinatesEquiv : Euc 2 ≃L[ℝ] ℂ where
  toFun := complexCoordinates
  invFun := complexCoordinatesInverse
  left_inv := by
    intro x
    ext i
    fin_cases i <;> simp [complexCoordinates, complexCoordinatesInverse]
  right_inv := by
    intro z
    apply Complex.ext <;> simp [complexCoordinates, complexCoordinatesInverse]
  map_add' := by
    intro x y
    apply Complex.ext <;> simp [complexCoordinates] <;> ring
  map_smul' := by
    intro r x
    apply Complex.ext <;> simp [complexCoordinates] <;> ring
  continuous_toFun := by
    unfold complexCoordinates
    fun_prop
  continuous_invFun := by
    unfold complexCoordinatesInverse
    fun_prop

def centeredSectorComplex (a : ℝ) (x : Euc 2) : ℂ :=
  complexCoordinates x * Complex.exp (-Complex.I * (a : ℂ) / 2)

def centeredSectorAngle (a : ℝ) (x : Euc 2) : ℝ :=
  Complex.arg (centeredSectorComplex a x) + a / 2

theorem complex_coordinates_norm (x : Euc 2) : ‖complexCoordinates x‖ = ‖x‖ := by
  have hx := EuclideanSpace.real_norm_sq_eq x
  have hz := Complex.sq_norm (complexCoordinates x)
  simp [Fin.sum_univ_two] at hx
  simp [complexCoordinates, Complex.normSq_apply] at hz
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change ‖↑(x 0) + Complex.I * ↑(x 1)‖ ^ 2 = ‖x‖ ^ 2
  rw [hz, hx]
  ring

theorem centered_sector_argument (a : ℝ) (ha : 0 < a ∧ a < 2 * Real.pi)
    (x : ↥(polygonSector a)) (hx : (x : Euc 2) ≠ 0) :
    centeredSectorComplex a x ∈ Complex.slitPlane ∧
    centeredSectorAngle a x ∈ Icc (0 : ℝ) a ∧
    (x : Euc 2) = polarPoint ‖(x : Euc 2)‖ (centeredSectorAngle a x) := by
  rcases x.property with ⟨r, θ, hr, hθ, heq⟩
  have hrpos : 0 < r := by
    by_contra h
    have hz : r = 0 := le_antisymm (le_of_not_gt h) hr
    exact hx (heq.trans (hz ▸ polar_vertex θ))
  have hrot : centeredSectorComplex a (polarPoint r θ) =
      (r : ℂ) * (Real.cos (θ - a / 2) + Real.sin (θ - a / 2) * Complex.I) := by
    have he : Complex.exp (-Complex.I * (a : ℂ) / 2) =
        Complex.exp ((-(a / 2) : ℝ) * Complex.I) := by
      congr 1
      push_cast
      ring
    unfold centeredSectorComplex
    rw [he, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    apply Complex.ext <;>
      simp only [complexCoordinates, polarPoint, Complex.add_re, Complex.add_im,
        Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_fin_one, Real.cos_sub, Real.sin_sub,
        Real.cos_neg, Real.sin_neg] <;> ring
  have hbounds : θ - a / 2 ∈ Ioc (-Real.pi) Real.pi := by
    constructor <;> linarith [ha.1, ha.2, hθ.1, hθ.2]
  have harg : Complex.arg (centeredSectorComplex a x) = θ - a / 2 := by
    rw [heq, hrot]
    simpa only [Complex.ofReal_cos, Complex.ofReal_sin] using
      Complex.arg_mul_cos_add_sin_mul_I hrpos hbounds
  have hangle : centeredSectorAngle a x = θ := by
    unfold centeredSectorAngle
    rw [harg]
    ring
  refine ⟨?_, ?_, ?_⟩
  · apply Complex.mem_slitPlane_iff_arg.mpr
    refine ⟨?_, ?_⟩
    · rw [harg]
      linarith [hθ.2, ha.2]
    · have hnorm : ‖centeredSectorComplex a x‖ = ‖(x : Euc 2)‖ := by
        simp [centeredSectorComplex, norm_mul, Complex.norm_exp, complex_coordinates_norm]
      intro hz
      have hn := norm_pos_iff.mpr hx
      rw [hz, norm_zero] at hnorm
      linarith
  · rw [hangle]
    exact hθ
  · rw [hangle, heq, polar_radius r θ hr]


theorem centered_angle_polar (a r θ : ℝ) (ha : 0 < a ∧ a < 2 * Real.pi)
    (hr : 0 < r) (hθ : θ ∈ Icc (0 : ℝ) a) :
    centeredSectorAngle a (polarPoint r θ) = θ := by
  have hm : polarPoint r θ ∈ polygonSector a := ⟨r, θ, hr.le, hθ, rfl⟩
  have hn : polarPoint r θ ≠ 0 := by
    intro h
    have he := polar_radius r θ hr.le
    rw [h, norm_zero] at he
    linarith
  have h := centered_sector_argument a ha ⟨polarPoint r θ, hm⟩ hn
  have he : polarPoint r θ = polarPoint r (centeredSectorAngle a (polarPoint r θ)) := by
    simpa only [polar_radius r θ hr.le] using h.2.2
  exact (polar_positive_unique a r r θ (centeredSectorAngle a (polarPoint r θ))
    ha hr hr hθ h.2.1 he).2.symm

/-- P3. Both maps explicitly assign zero at the vertex. -/
def sectorHalfspaceForward (a : ℝ) (x : Euc 2) : Euc 2 :=
  if x = 0 then 0 else
    !₂[‖x‖ * Real.sin (Real.pi * centeredSectorAngle a x / a),
       ‖x‖ * Real.cos (Real.pi * centeredSectorAngle a x / a)]

def halfspacePolarAngle (u : EuclideanHalfSpace 2) : ℝ :=
  Real.pi / 2 - Complex.arg (complexCoordinates u.val)

def sectorHalfspaceInverse (a : ℝ) (u : EuclideanHalfSpace 2) : Euc 2 :=
  if u.val = 0 then 0 else
    polarPoint ‖u.val‖ (a * halfspacePolarAngle u / Real.pi)

theorem sector_forward_nonnegative (a : ℝ) (ha : 0 < a ∧ a < 2 * Real.pi)
    (x : ↥(polygonSector a)) : 0 ≤ sectorHalfspaceForward a x 0 := by
  unfold sectorHalfspaceForward
  split_ifs with hx
  · simp
  · have hθ := (centered_sector_argument a ha x hx).2.1
    have ht : Real.pi * centeredSectorAngle a x / a ∈ Icc (0 : ℝ) Real.pi := by
      constructor
      · exact div_nonneg (mul_nonneg Real.pi_pos.le hθ.1) ha.1.le
      · apply (div_le_iff₀ ha.1).mpr
        nlinarith [Real.pi_pos, hθ.2]
    simpa using mul_nonneg (norm_nonneg (x : Euc 2)) (Real.sin_nonneg_of_mem_Icc ht)

theorem halfspace_polar_angle_bounds (u : EuclideanHalfSpace 2) (hu : u.val ≠ 0) :
    halfspacePolarAngle u ∈ Icc (0 : ℝ) Real.pi := by
  have hre : 0 ≤ (complexCoordinates u.val).re := by
    simpa [complexCoordinates] using u.property
  have h := Complex.abs_arg_le_pi_div_two_iff.mpr hre
  rw [abs_le] at h
  unfold halfspacePolarAngle
  constructor <;> linarith [h.1, h.2]

theorem sector_inverse_mem (a : ℝ) (ha : 0 < a ∧ a < 2 * Real.pi)
    (u : EuclideanHalfSpace 2) : sectorHalfspaceInverse a u ∈ polygonSector a := by
  unfold sectorHalfspaceInverse
  split_ifs with hu
  · exact ⟨0, 0, le_rfl, ⟨le_rfl, ha.1.le⟩, (polar_vertex 0).symm⟩
  · have ht := halfspace_polar_angle_bounds u hu
    refine ⟨‖u.val‖, a * halfspacePolarAngle u / Real.pi, norm_nonneg _, ?_, rfl⟩
    constructor
    · exact div_nonneg (mul_nonneg ha.1.le ht.1) Real.pi_pos.le
    · apply (div_le_iff₀ Real.pi_pos).mpr
      nlinarith [ha.1, ht.2]

def sectorForwardPoint (a : ℝ) (ha : 0 < a ∧ a < 2 * Real.pi)
    (x : ↥(polygonSector a)) : EuclideanHalfSpace 2 :=
  ⟨sectorHalfspaceForward a x, by exact sector_forward_nonnegative a ha x⟩

def sectorInversePoint (a : ℝ) (ha : 0 < a ∧ a < 2 * Real.pi)
    (u : EuclideanHalfSpace 2) : ↥(polygonSector a) :=
  ⟨sectorHalfspaceInverse a u, by exact sector_inverse_mem a ha u⟩

theorem sector_inverse_forward (a : ℝ) (ha : 0 < a ∧ a < 2 * Real.pi)
    (x : ↥(polygonSector a)) :
    sectorInversePoint a ha (sectorForwardPoint a ha x) = x := by
  apply Subtype.ext
  change sectorHalfspaceInverse a (sectorForwardPoint a ha x) = (x : Euc 2)
  by_cases hx : (x : Euc 2) = 0
  · simp [sectorHalfspaceInverse, sectorForwardPoint, sectorHalfspaceForward, hx]
  · let θ := centeredSectorAngle a x
    let t := Real.pi * θ / a
    let r := ‖(x : Euc 2)‖
    have hr : 0 < r := norm_pos_iff.mpr hx
    have hθ := (centered_sector_argument a ha x hx).2.1
    have ht : t ∈ Icc (0 : ℝ) Real.pi := by
      constructor
      · exact div_nonneg (mul_nonneg Real.pi_pos.le hθ.1) ha.1.le
      · apply (div_le_iff₀ ha.1).mpr
        nlinarith [Real.pi_pos, hθ.2]
    have hv : (sectorForwardPoint a ha x).val = polarPoint r (Real.pi / 2 - t) := by
      change sectorHalfspaceForward a x = _
      rw [sectorHalfspaceForward, if_neg hx]
      ext i
      fin_cases i <;> simp [polarPoint, r, t, θ, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
    have hn : ‖(sectorForwardPoint a ha x).val‖ = r := by
      rw [hv, polar_radius r _ hr.le]
    have hvne : (sectorForwardPoint a ha x).val ≠ 0 := by
      intro h
      rw [h, norm_zero] at hn
      linarith
    have hc : complexCoordinates (sectorForwardPoint a ha x).val =
        (r : ℂ) * ((Real.cos (Real.pi / 2 - t) : ℂ) +
          (Real.sin (Real.pi / 2 - t) : ℂ) * Complex.I) := by
      rw [hv]
      apply Complex.ext <;>
        simp only [complexCoordinates, polarPoint, Complex.add_re, Complex.add_im,
          Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, Matrix.cons_val_zero, Matrix.cons_val_one] <;> ring
    have harg : Complex.arg (complexCoordinates (sectorForwardPoint a ha x).val) =
        Real.pi / 2 - t := by
      rw [hc]
      have hb : Real.pi / 2 - t ∈ Ioc (-Real.pi) Real.pi := by
        constructor <;> linarith [ht.1, ht.2, Real.pi_pos]
      simpa only [Complex.ofReal_cos, Complex.ofReal_sin] using
        Complex.arg_mul_cos_add_sin_mul_I hr hb
    have hang : halfspacePolarAngle (sectorForwardPoint a ha x) = t := by
      unfold halfspacePolarAngle
      rw [harg]
      ring
    rw [sectorHalfspaceInverse, if_neg hvne, hn, hang]
    have halg : a * t / Real.pi = θ := by
      dsimp [t]
      field_simp [ha.1.ne', Real.pi_pos.ne']
    rw [halg]
    exact (centered_sector_argument a ha x hx).2.2.symm

theorem sector_forward_inverse (a : ℝ) (ha : 0 < a ∧ a < 2 * Real.pi)
    (u : EuclideanHalfSpace 2) :
    sectorForwardPoint a ha (sectorInversePoint a ha u) = u := by
  apply Subtype.ext
  change sectorHalfspaceForward a (sectorHalfspaceInverse a u) = u.val
  by_cases hu : u.val = 0
  · simp [sectorHalfspaceInverse, sectorHalfspaceForward, hu]
  · let θ := a * halfspacePolarAngle u / Real.pi
    have hr : 0 < ‖u.val‖ := norm_pos_iff.mpr hu
    have ht := halfspace_polar_angle_bounds u hu
    have hθ : θ ∈ Icc (0 : ℝ) a := by
      constructor
      · exact div_nonneg (mul_nonneg ha.1.le ht.1) Real.pi_pos.le
      · apply (div_le_iff₀ Real.pi_pos).mpr
        nlinarith [ha.1, ht.2]
    have hv : polarPoint ‖u.val‖ θ ≠ 0 := by
      intro h
      have hn := polar_radius ‖u.val‖ θ hr.le
      rw [h, norm_zero] at hn
      linarith
    rw [sectorHalfspaceInverse, if_neg hu]
    change sectorHalfspaceForward a (polarPoint ‖u.val‖ θ) = u.val
    rw [sectorHalfspaceForward, if_neg hv, polar_radius _ _ hr.le,
      centered_angle_polar a _ θ ha hr hθ]
    have halg : Real.pi * θ / a = halfspacePolarAngle u := by
      dsimp [θ]
      field_simp [ha.1.ne', Real.pi_pos.ne']
    rw [halg]
    have hc := Complex.norm_mul_cos_arg (complexCoordinates u.val)
    have hs := Complex.norm_mul_sin_arg (complexCoordinates u.val)
    rw [complex_coordinates_norm] at hc hs
    simp only [complexCoordinates, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, zero_mul, one_mul, mul_zero, add_zero, zero_add,
      sub_zero] at hc hs
    ext i
    fin_cases i <;> simp [halfspacePolarAngle, complexCoordinates, Real.sin_pi_div_two_sub,
      Real.cos_pi_div_two_sub, hc, hs]

theorem sector_forward_norm (a : ℝ) (ha : 0 < a ∧ a < 2 * Real.pi)
    (x : ↥(polygonSector a)) : ‖sectorHalfspaceForward a x‖ = ‖(x : Euc 2)‖ := by
  unfold sectorHalfspaceForward
  split_ifs with hx
  · simp [hx]
  · have he :
        !₂[‖(x : Euc 2)‖ * Real.sin (Real.pi * centeredSectorAngle a x / a),
          ‖(x : Euc 2)‖ * Real.cos (Real.pi * centeredSectorAngle a x / a)] =
        polarPoint ‖(x : Euc 2)‖ (Real.pi / 2 - Real.pi * centeredSectorAngle a x / a) := by
      ext i
      fin_cases i <;> simp [polarPoint, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
    rw [he]
    exact polar_radius _ _ (norm_nonneg _)

theorem sector_inverse_norm (a : ℝ) (ha : 0 < a ∧ a < 2 * Real.pi)
    (u : EuclideanHalfSpace 2) : ‖sectorHalfspaceInverse a u‖ = ‖u.val‖ := by
  unfold sectorHalfspaceInverse
  split_ifs with hu
  · simp [hu]
  · exact polar_radius _ _ (norm_nonneg _)

theorem sector_forward_ray (a r θ : ℝ) (ha : 0 < a ∧ a < 2 * Real.pi)
    (hr : 0 ≤ r) (hθ : θ ∈ Icc (0 : ℝ) a) :
    sectorHalfspaceForward a (polarPoint r θ) =
      !₂[r * Real.sin (Real.pi * θ / a), r * Real.cos (Real.pi * θ / a)] := by
  by_cases hz : r = 0
  · subst r
    ext i
    fin_cases i <;> simp [polar_vertex, sectorHalfspaceForward]
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hz)
    have hp : polarPoint r θ ≠ 0 := by
      intro h
      have hn := polar_radius r θ hr
      rw [h, norm_zero] at hn
      exact hz hn.symm
    simp only [sectorHalfspaceForward, dif_neg hp, if_neg hp,
      polar_radius r θ hr, centered_angle_polar a r θ ha hrpos hθ]

/-- P4. No continuity of an angle at the vertex is asserted. -/
theorem sector_forward_continuous (a : ℝ) (ha : 0 < a ∧ a < 2 * Real.pi) :
    Continuous (sectorForwardPoint a ha) := by
  apply Continuous.subtype_mk
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : (x : Euc 2) = 0
  · change Filter.Tendsto (fun y : ↥(polygonSector a) => sectorHalfspaceForward a y)
      (𝓝 x) (𝓝 (sectorHalfspaceForward a x))
    rw [show sectorHalfspaceForward a x = 0 by simp [sectorHalfspaceForward, hx]]
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hn : (fun y : ↥(polygonSector a) => ‖sectorHalfspaceForward a y‖) =
        (fun y : ↥(polygonSector a) => ‖(y : Euc 2)‖) := by
      funext y
      exact sector_forward_norm a ha y
    rw [hn]
    have hc : Continuous (fun y : ↥(polygonSector a) => ‖(y : Euc 2)‖) := by fun_prop
    simpa only [hx, norm_zero] using (hc.continuousAt (x := x)).tendsto
  · have hC : ContinuousAt (fun y : ↥(polygonSector a) => centeredSectorComplex a y) x := by
      unfold centeredSectorComplex complexCoordinates
      fun_prop
    have harg : ContinuousAt (fun y : ↥(polygonSector a) =>
        Complex.arg (centeredSectorComplex a y)) x :=
      (Complex.continuousAt_arg (centered_sector_argument a ha x hx).1).comp
        (f := fun y : ↥(polygonSector a) => centeredSectorComplex a y) hC
    have hangle : ContinuousAt (fun y : ↥(polygonSector a) => centeredSectorAngle a y) x :=
      harg.add continuousAt_const
    have hf : ContinuousAt (fun y : ↥(polygonSector a) =>
        !₂[‖(y : Euc 2)‖ * Real.sin (Real.pi * centeredSectorAngle a y / a),
           ‖(y : Euc 2)‖ * Real.cos (Real.pi * centeredSectorAngle a y / a)]) x := by
      fun_prop
    apply hf.congr_of_eventuallyEq
    have hne : ∀ᶠ y : ↥(polygonSector a) in 𝓝 x, (y : Euc 2) ≠ 0 :=
      continuous_subtype_val.continuousAt.tendsto.eventually (eventually_ne_nhds hx)
    filter_upwards [hne] with y hy
    simp only [sectorHalfspaceForward, if_neg hy]

theorem sector_inverse_continuous (a : ℝ) (ha : 0 < a ∧ a < 2 * Real.pi) :
    Continuous (sectorInversePoint a ha) := by
  apply Continuous.subtype_mk
  apply continuous_iff_continuousAt.mpr
  intro u
  by_cases hu : u.val = 0
  · change Filter.Tendsto (sectorHalfspaceInverse a) (𝓝 u) (𝓝 (sectorHalfspaceInverse a u))
    rw [show sectorHalfspaceInverse a u = 0 by simp [sectorHalfspaceInverse, hu]]
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hn : (fun v : EuclideanHalfSpace 2 => ‖sectorHalfspaceInverse a v‖) =
        (fun v : EuclideanHalfSpace 2 => ‖v.val‖) := by
      funext v
      exact sector_inverse_norm a ha v
    rw [hn]
    have hc : Continuous (fun v : EuclideanHalfSpace 2 => ‖v.val‖) := by fun_prop
    simpa only [hu, norm_zero] using (hc.continuousAt (x := u)).tendsto
  · have hz : complexCoordinates u.val ∈ Complex.slitPlane := by
      apply Complex.mem_slitPlane_iff_arg.mpr
      have ht := halfspace_polar_angle_bounds u hu
      refine ⟨?_, ?_⟩
      · unfold halfspacePolarAngle at ht
        linarith [ht.1, Real.pi_pos]
      · intro h
        have hn := complex_coordinates_norm u.val
        rw [h, norm_zero] at hn
        exact hu (norm_eq_zero.mp hn.symm)
    have hC : ContinuousAt (fun v : EuclideanHalfSpace 2 => complexCoordinates v.val) u := by
      unfold complexCoordinates
      fun_prop
    have harg : ContinuousAt (fun v : EuclideanHalfSpace 2 =>
        Complex.arg (complexCoordinates v.val)) u := (Complex.continuousAt_arg hz).comp
          (f := fun v : EuclideanHalfSpace 2 => complexCoordinates v.val) hC
    have hangle : ContinuousAt halfspacePolarAngle u := continuousAt_const.sub harg
    have hf : ContinuousAt (fun v : EuclideanHalfSpace 2 =>
        polarPoint ‖v.val‖ (a * halfspacePolarAngle v / Real.pi)) u := by
      unfold polarPoint
      fun_prop
    apply hf.congr_of_eventuallyEq
    have hne : ∀ᶠ v : EuclideanHalfSpace 2 in 𝓝 u, v.val ≠ 0 :=
      continuous_subtype_val.continuousAt.tendsto.eventually (eventually_ne_nhds hu)
    filter_upwards [hne] with v hv
    simp only [sectorHalfspaceInverse, if_neg hv]

/-- P5. The bundled map has the literal forward and inverse formulas. -/
def sectorHalfspaceHomeomorph (a : ℝ) (ha : 0 < a ∧ a < 2 * Real.pi) :
    ↥(polygonSector a) ≃ₜ EuclideanHalfSpace 2 where
  toFun := sectorForwardPoint a ha
  invFun := sectorInversePoint a ha
  left_inv := by exact sector_inverse_forward a ha
  right_inv := by exact sector_forward_inverse a ha
  continuous_toFun := by exact sector_forward_continuous a ha
  continuous_invFun := by exact sector_inverse_continuous a ha

def sectorHalfspaceModel (a : ℝ) (ha : 0 < a ∧ a < 2 * Real.pi) :
    PolygonSectorHalfspace a where
  homeomorph := sectorHalfspaceHomeomorph a ha
  angular_formula := by
    intro r θ hr hθ hpoint
    exact sector_forward_ray a r θ ha hr hθ

theorem sector_boundary_rays (a r : ℝ) (ha : 0 < a ∧ a < 2 * Real.pi)
    (hr : 0 ≤ r) : sectorHalfspaceForward a (polarPoint r 0) = !₂[0, r] ∧
    sectorHalfspaceForward a (polarPoint r a) = !₂[0, -r] := by
  constructor
  · rw [sector_forward_ray a r 0 ha hr ⟨le_rfl,ha.1.le⟩]
    simp
  · rw [sector_forward_ray a r a ha hr ⟨ha.1.le,le_rfl⟩]
    simp [ha.1.ne',mul_div_cancel_right₀]

/-- P6. Function order is x ↦ h_b.symm (h_a x). -/
def sectorRescalingHomeomorph (a b : ℝ)
    (ha : 0 < a ∧ a < 2 * Real.pi) (hb : 0 < b ∧ b < 2 * Real.pi) :
    ↥(polygonSector a) ≃ₜ ↥(polygonSector b) :=
  (sectorHalfspaceHomeomorph a ha).trans (sectorHalfspaceHomeomorph b hb).symm

def sectorRescalingModel (a b : ℝ)
    (ha : 0 < a ∧ a < 2 * Real.pi) (hb : 0 < b ∧ b < 2 * Real.pi) :
    SectorAngularRescaling a b where
  homeomorph := sectorRescalingHomeomorph a b ha hb
  formula := by
    intro r θ hr hθ hpoint
    have hθ' : b * θ / a ∈ Icc (0 : ℝ) b := by
      constructor
      · exact div_nonneg (mul_nonneg hb.1.le hθ.1) ha.1.le
      · apply (div_le_iff₀ ha.1).mpr
        nlinarith [hb.1, hθ.2]
    have hm : polarPoint r (b * θ / a) ∈ polygonSector b :=
      ⟨r, b * θ / a, hr, hθ', rfl⟩
    have he : sectorRescalingHomeomorph a b ha hb ⟨polarPoint r θ, hpoint⟩ =
        ⟨polarPoint r (b * θ / a), hm⟩ := by
      change (sectorHalfspaceHomeomorph b hb).symm
        (sectorHalfspaceHomeomorph a ha ⟨polarPoint r θ, hpoint⟩) = _
      apply (sectorHalfspaceHomeomorph b hb).injective
      rw [Homeomorph.apply_symm_apply]
      apply Subtype.ext
      change sectorHalfspaceForward a (polarPoint r θ) =
        sectorHalfspaceForward b (polarPoint r (b * θ / a))
      rw [sector_forward_ray a r θ ha hr hθ,
        sector_forward_ray b r (b * θ / a) hb hr hθ']
      have halg : Real.pi * (b * θ / a) / b = Real.pi * θ / a := by
        field_simp [ha.1.ne', hb.1.ne']
      rw [halg]
    exact congrArg Subtype.val he

theorem sector_rescaling_radius (a b : ℝ)
    (ha : 0 < a ∧ a < 2 * Real.pi) (hb : 0 < b ∧ b < 2 * Real.pi)
    (x : ↥(polygonSector a)) :
    ‖(sectorRescalingHomeomorph a b ha hb x : Euc 2)‖ = ‖(x : Euc 2)‖ := by
  change ‖sectorHalfspaceInverse b (sectorForwardPoint a ha x)‖ = ‖(x : Euc 2)‖
  rw [sector_inverse_norm b hb]
  exact sector_forward_norm a ha x

theorem sector_rescaling_clipped (a b ρ : ℝ)
    (ha : 0 < a ∧ a < 2 * Real.pi) (hb : 0 < b ∧ b < 2 * Real.pi) (hρ : 0 < ρ) :
    (fun x : ↥(polygonSector a) => (sectorRescalingHomeomorph a b ha hb x : Euc 2)) ''
      {x : ↥(polygonSector a) | (x : Euc 2) ∈ clippedPolygonSector a ρ} =
        clippedPolygonSector b ρ := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(sectorRescalingHomeomorph a b ha hb x).property, ?_⟩
    rw [Metric.mem_ball, dist_zero_right, sector_rescaling_radius a b ha hb]
    simpa only [Metric.mem_ball, dist_zero_right] using hx.2
  · intro hy
    let z : ↥(polygonSector b) := ⟨y, hy.1⟩
    let x := (sectorRescalingHomeomorph a b ha hb).symm z
    have he : sectorRescalingHomeomorph a b ha hb x = z :=
      Homeomorph.apply_symm_apply _ z
    refine ⟨x, ⟨x.property, ?_⟩, congrArg Subtype.val he⟩
    have hn := sector_rescaling_radius a b ha hb x
    rw [he] at hn
    rw [Metric.mem_ball, dist_zero_right, ← hn]
    simpa only [Metric.mem_ball, dist_zero_right] using hy.2


end
end SeifertSurfaces.LongitudeProducers.QuotientChartHelpers
