import SectorFlatSideProbe
import A5OutwardDefiningSign
import NativeClockC1Probe

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set Topology Filter
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal

theorem seamFrame_reconstruction (e m v : Euc 2)
    (he : ‖e‖ = 1) (hm : ‖m‖ = 1) (hem : inner ℝ e m = 0) :
    v = (inner ℝ e v) • e + (inner ℝ m v) • m := by
  obtain ⟨z, hz⟩ := (seamFrameMap_bijective e m he hm hem).2 v
  have hme : inner ℝ m e = 0 := by rw [real_inner_comm, hem]
  have h1 := congrArg (fun v => inner ℝ e v) hz
  have h2 := congrArg (fun v => inner ℝ m v) hz
  simp only [seamFrameMap_apply, inner_add_right, inner_smul_right,
    real_inner_self_eq_norm_sq, he, hm, hem, hme, one_pow, mul_one,
    mul_zero, add_zero, zero_add] at h1 h2
  rw [← h1, ← h2, ← seamFrameMap_apply, hz]

/-- A regular exact boundary lift has an actual straight-sector scalar
clock near its centre. The clock, frame, C1 regularity and nonzero derivative
are produced from the native sector domain. -/
theorem regular_sector_boundary_straight_clock
    (A : SectorModel) (q : ℝ → Euc 2) (U : Set ℝ) (hU : IsOpen U) (h0 : 0 ∈ U)
    (hq : MapsTo q U (A.domain ∩ frontier A.domain))
    (hqc : ContDiffOn ℝ 1 q U) (hqr : ∀ t ∈ U, deriv q t ≠ 0)
    (hregular : q 0 ≠ 0 ∨ A.angle = Real.pi) :
    ∃ e m : Euc 2, ‖e‖ = 1 ∧ ‖m‖ = 1 ∧ inner ℝ e m = 0 ∧
      inner ℝ m (q 0) = 0 ∧ (∀ᶠ z in 𝓝 (q 0), z ∈ A.domain ↔ 0 ≤ inner ℝ m z) ∧
      ∃ V : Set ℝ, IsOpen V ∧ V ⊆ U ∧ 0 ∈ V ∧ ∃ clock : ℝ → ℝ,
        clock 0 = 0 ∧ ContDiffOn ℝ 1 clock V ∧
        (∀ t ∈ V, deriv clock t ≠ 0) ∧
        ∀ t ∈ V, q t = q 0 + clock t • e := by
  obtain ⟨e, m, he, hm, hem, hmx, hside⟩ :=
    native_sector_orthonormal_boundary_frame A (q 0) (hq h0) hregular
  let L : Euc 2 →L[ℝ] ℝ := innerSL ℝ m
  have hzero := defining_function_zero_on_frontier A.domain L (q 0)
    L.contDiff.contDiffAt hside
  have hq0c := (hqc 0 h0).contDiffAt (hU.mem_nhds h0)
  have hzclock : ∀ᶠ t in 𝓝 (0 : ℝ), inner ℝ m (q t) = 0 := by
    filter_upwards [hq0c.continuousAt.tendsto.eventually hzero, hU.mem_nhds h0] with t ht htU
    exact ht (hq htU)
  obtain ⟨V₀, hV₀sub, hV₀open, h0V₀⟩ := mem_nhds_iff.mp hzclock
  let V := U ∩ V₀
  have hV : IsOpen V := hU.inter hV₀open
  have h0V : (0 : ℝ) ∈ V := ⟨h0, h0V₀⟩
  let clock : ℝ → ℝ := fun t => inner ℝ e (q t - q 0)
  have hc : ContDiffOn ℝ 1 clock V :=
    (innerSL ℝ e).contDiff.contDiffOn.comp
      ((hqc.mono inter_subset_left).sub contDiffOn_const) (mapsTo_univ _ _)
  have hline (t : ℝ) (ht : t ∈ V) : q t = q 0 + clock t • e := by
    have hmq : inner ℝ m (q t - q 0) = 0 := by
      rw [inner_sub_right, hV₀sub ht.2, hmx, sub_self]
    have hr := seamFrame_reconstruction e m (q t - q 0) he hm hem
    rw [hmq, zero_smul, add_zero] at hr
    exact (sub_eq_iff_eq_add.mp hr).trans (add_comm _ _)
  have hcreg (t : ℝ) (ht : t ∈ V) : deriv clock t ≠ 0 := by
    have hct := (hc t ht).contDiffAt (hV.mem_nhds ht)
    have hd := ((hct.differentiableAt (by norm_num)).hasDerivAt.smul_const e).const_add (q 0)
    have heq : q =ᶠ[𝓝 t] (fun t => q 0 + clock t • e) := by
      filter_upwards [hV.mem_nhds ht] with z hz
      exact hline z hz
    have hdq : deriv q t = deriv clock t • e := heq.deriv_eq.trans hd.deriv
    intro hz
    apply hqr t ht.1
    rw [hdq, hz, zero_smul]
  exact ⟨e, m, he, hm, hem, hmx, hside, V, hV, inter_subset_left, h0V,
    clock, by simp [clock], hc, hcreg, hline⟩

theorem scalar_clock_embedding_of_straight_lift
    (U : Set ℝ) (o e : Euc 2) (clock : ℝ → ℝ) (q : ℝ → Euc 2)
    (hc : ContinuousOn clock U) (hq : IsEmbedding (fun t : U => q t))
    (heq : ∀ t ∈ U, q t = o + clock t • e) :
    IsEmbedding (fun t : U => clock t) := by
  have hcomp : IsEmbedding ((fun r : ℝ => o + r • e) ∘ (fun t : U => clock t)) := by
    have heq' : ((fun r : ℝ => o + r • e) ∘ (fun t : U => clock t)) = (fun t : U => q t) := by
      funext t
      exact (heq t t.property).symm
    rwa [heq']
  exact IsEmbedding.of_comp hc.domRestrict (by fun_prop) hcomp

universe u
variable {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)

/-- An exact original embedded source clock induces an embedded coordinate
lift in its actual selected native sector chart. -/
theorem native_exact_source_clock_coordinate_embedding
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count)
    (U : Set ℝ) (β : ℝ → S) (q : ℝ → Euc 2)
    (hβ : IsEmbedding (fun t : U => β t))
    (hqm : MapsTo q U ((F.domain i).chart j).map.target)
    (heq : ∀ t ∈ U, F.parametrization i (((F.domain i).chart j).map.symm (q t)) = β t) :
    IsEmbedding (fun t : U => q t) := by
  let A := ((F.domain i).chart j).map.target
  have hqc : ContinuousOn q U := continuous_coordinate_lift_of_embedded_image
    ((F.domain i).chart j).map (F.parametrization i) (F.parametrization_embedding i)
    U β q (continuousOn_iff_continuous_domRestrict.mpr hβ.continuous) hqm heq
  let q' : U → A := fun t => ⟨q t, hqm t.property⟩
  let f : A → S := fun y => F.parametrization i (((F.domain i).chart j).map.symm y)
  have hfemb : IsEmbedding f := (F.parametrization_embedding i).comp
    ((F.domain i).chart j).map.symm.isEmbedding_restrict
  have hq'c : Continuous q' := hqc.domRestrict.subtype_mk _
  have hcomp : IsEmbedding (f ∘ q') := by
    have heq' : f ∘ q' = (fun t : U => β t) := funext (fun t => heq t t.property)
    rwa [heq']
  exact IsEmbedding.subtypeVal.comp (IsEmbedding.of_comp hq'c hfemb.continuous hcomp)

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
