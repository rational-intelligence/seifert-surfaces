import StageBoundaryVelocity
import DifferentialGeometry.Analysis.Calculus.Inverse.VectorParameterizedInverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue

open Set Filter Topology
open scoped ContDiff Manifold

namespace SeifertSurfaces.Foundations.AmbientNeatTransport
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A smooth family which preserves the boundary hyperplane and has positive
normal derivative has the correct sign on a whole product neighbourhood. The
parameter is only required to lie in the prescribed closed time set. -/
theorem exists_local_normal_sign
    {h : ℝ × (ℝ × E) → ℝ × E} (hh : ContDiff ℝ ∞ h)
    {J : Set ℝ} {U : Set (ℝ × (ℝ × E))} (hU : IsOpen U)
    {t : ℝ} {z : E} (hqU : (t, (0, z)) ∈ U)
    (hpositive : 0 < (fderiv ℝ h (t, (0, z)) (0, (1, 0))).1)
    (hzero : ∀ r ∈ U, r.1 ∈ J → r.2.1 = 0 → (h r).1 = 0) :
    ∃ W : Set (ℝ × (ℝ × E)), IsOpen W ∧ (t, (0, z)) ∈ W ∧ W ⊆ U ∧
      ∀ r ∈ W, r.1 ∈ J →
        ((0 ≤ (h r).1 ↔ 0 ≤ r.2.1) ∧ ((h r).1 = 0 ↔ r.2.1 = 0)) := by
  let v : ℝ × (ℝ × E) := (0, (1, 0))
  have hc : Continuous (fun r => (fderiv ℝ h r v).1) :=
    ((hh.continuous_fderiv (by simp)).clm_apply continuous_const).fst
  let D : Set (ℝ × (ℝ × E)) := U ∩ {r | 0 < (fderiv ℝ h r v).1}
  have hD : IsOpen D := hU.inter (isOpen_lt continuous_const hc)
  have hqD : (t, (0, z)) ∈ D := ⟨hqU, hpositive⟩
  obtain ⟨T,B,hTo,htT,hBo,hqB,hTB⟩ := mem_nhds_prod_iff'.mp (hD.mem_nhds hqD)
  obtain ⟨N,Z,hNo,h0N,hZo,hzZ,hNZ⟩ := mem_nhds_prod_iff'.mp (hBo.mem_nhds hqB)
  obtain ⟨ε,hε,hεN⟩ := Metric.mem_nhds_iff.mp (hNo.mem_nhds h0N)
  have hNN : Ioo (-ε) ε ⊆ N := by
    intro a ha
    apply hεN
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_lt, Set.mem_Ioo] using ha
  let W : Set (ℝ × (ℝ × E)) := T ×ˢ (Ioo (-ε) ε ×ˢ Z)
  have hWD (r : ℝ × (ℝ × E)) (hr : r ∈ W) : r ∈ D := hTB ⟨hr.1, hNZ ⟨hNN hr.2.1, hr.2.2⟩⟩
  refine ⟨W,hTo.prod (isOpen_Ioo.prod hZo),⟨htT,⟨neg_lt_zero.mpr hε,hε⟩,hzZ⟩,
    fun r hr => (hWD r hr).1,?_⟩
  intro r hr htime
  let φ : ℝ → ℝ := fun a => (h (r.1, (a, r.2.2))).1
  have hder (a : ℝ) : HasDerivAt φ (fderiv ℝ h (r.1, (a, r.2.2)) v).1 a := by
    have hl : HasDerivAt (fun b : ℝ => (r.1, (b, r.2.2))) v a :=
      (hasDerivAt_const a r.1).prodMk ((hasDerivAt_id a).prodMk (hasDerivAt_const a r.2.2))
    exact (((hh.differentiable (by simp)).differentiableAt.hasFDerivAt).comp_hasDerivAt a hl).fst
  have hmono : StrictMonoOn φ (Ioo (-ε) ε) :=
    strictMonoOn_of_deriv_pos (convex_Ioo _ _)
      (fun a _ => (hder a).continuousAt.continuousWithinAt) (by
        intro a ha
        rw [(hder a).deriv]
        exact (hWD (r.1, (a, r.2.2)) ⟨hr.1,interior_subset ha,hr.2.2⟩).2)
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_lt_zero.mpr hε,hε⟩
  have hφ0 : φ 0 = 0 := hzero (r.1, (0, r.2.2))
    (hWD (r.1, (0, r.2.2)) ⟨hr.1,h0,hr.2.2⟩).1 htime rfl
  have hn := hr.2.1
  have hsign : 0 ≤ φ r.2.1 ↔ 0 ≤ r.2.1 := by
    simpa only [hφ0] using hmono.le_iff_le h0 hn
  have heq : φ r.2.1 = 0 ↔ r.2.1 = 0 := by
    simpa only [hφ0] using hmono.injOn.eq_iff hn h0
  exact ⟨hsign,heq⟩

/-- The genuine Euclidean parameter inverse restricts to a boundary-compatible
local inverse throughout the closed set of times. No boundaryless manifold
assumption is introduced. -/
theorem exists_local_inverse_preserving_halfspace_parameter
    [CompleteSpace E]
    {h : ℝ × (ℝ × E) → ℝ × E} (hh : ContDiff ℝ ∞ h)
    {J : Set ℝ} {U : Set (ℝ × (ℝ × E))} (hU : IsOpen U)
    {t : ℝ} {z : E} (hqU : (t, (0, z)) ∈ U)
    (A : (ℝ × E) ≃L[ℝ] (ℝ × E))
    (hvertical : ∀ w, fderiv ℝ h (t, (0, z)) (0, w) = A w)
    (hnormal : ∀ w, (A w).1 = w.1)
    (hzero : ∀ r ∈ U, r.1 ∈ J → r.2.1 = 0 → (h r).1 = 0) :
    ∃ e : OpenPartialHomeomorph (ℝ × (ℝ × E)) (ℝ × (ℝ × E)),
      (t, (0, z)) ∈ e.source ∧ e.source ⊆ U ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ r, e r = (r.1, h r)) ∧
      (∀ r ∈ e.target, (e.symm r).1 = r.1 ∧ h (e.symm r) = r.2) ∧
      ∀ r ∈ e.target, r.1 ∈ J →
        ((0 ≤ (e.symm r).2.1 ↔ 0 ≤ r.2.1) ∧
         ((e.symm r).2.1 = 0 ↔ r.2.1 = 0)) := by
  have hp : 0 < (fderiv ℝ h (t, (0, z)) (0, (1, 0))).1 := by
    rw [hvertical, hnormal]
    exact zero_lt_one
  obtain ⟨W,hW,hqW,hWU,hWsign⟩ := exists_local_normal_sign hh hU hqU hp hzero
  obtain ⟨e,hqe,heW,he,hei,hemap,heinv⟩ :=
    DifferentialGeometry.Analysis.exists_localInverse_preserving_vector_parameter
      hh.contDiffOn hW hqW A hvertical
  refine ⟨e,hqe,heW.trans hWU,he,hei,hemap,heinv,?_⟩
  intro r hr ht
  have hparam := heinv r hr
  have hs := hWsign (e.symm r) (heW (e.map_target hr)) (hparam.1 ▸ ht)
  rw [hparam.2] at hs
  exact ⟨hs.1.symm,hs.2.symm⟩

end
end SeifertSurfaces.Foundations.AmbientNeatTransport
