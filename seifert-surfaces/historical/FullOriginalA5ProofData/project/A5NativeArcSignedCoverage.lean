import A5NativeSeamIsolation
import A5NativeProjectedArcGeometry

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC CurvedDivergence
universe u

/-- Exact native arc incidence and the literal affine local parameter
supply the zero-set coverage needed by curved seam removal. The source
neighborhood is constructed and all other arcs, circles and boundary are excluded. -/
theorem native_arc_projected_signed_zero_near
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (a : Fin F.seam.arcCount) (s₀ : Time) (hs0 : 0 < s₀) (hs1 : s₀ < 1)
    (scale : ℝ) (hscale : 0 < scale) (parameter : Ioo (-1 : ℝ) 1 → Time)
    (hparameter : ∀ t, (parameter t : ℝ) = (s₀ : ℝ) + scale * (t : ℝ))
    (γ : ℝ → ThreeSphere)
    (hγ : ∀ t : Ioo (-1 : ℝ) 1, γ t = E.toSphere (F.map (F.seam.arc a (parameter t))))
    (c : SmoothAmbientChart ThreeSphere) (P : E3 →L[ℝ] E2)
    (ρ : ℝ) (s : E2 → ℝ) (left right : ℝ) (hl : left < 0) (hr : 0 < right)
    (hgeom : SignedArcGeometry (Metric.ball 0 ρ) s
      (fun t => P (c.chart (γ t)) - P (c.chart (γ 0))) left right) :
    ∃ U : Set S, IsOpen U ∧ F.seam.arc a s₀ ∈ U ∧ U ⊆ S.boundaryᶜ ∧
      ∀ z ∈ U, z ∈ F.seam.carrier →
        P (c.chart (E.toSphere (F.map z))) -
          P (c.chart (E.toSphere (F.map (F.seam.arc a s₀)))) ∈ Metric.ball 0 ρ →
        s (P (c.chart (E.toSphere (F.map z))) -
          P (c.chart (E.toSphere (F.map (F.seam.arc a s₀))))) = 0 := by
  let l := max (-1 : ℝ) left
  let r := min (1 : ℝ) right
  have hl0 : l < 0 := max_lt (by norm_num) hl
  have hr0 : 0 < r := lt_min (by norm_num) hr
  let V : Set Time := {t | (s₀ : ℝ) + scale * l < (t : ℝ) ∧ (t : ℝ) < (s₀ : ℝ) + scale * r}
  have hV : IsOpen V := isOpen_Ioo.preimage continuous_subtype_val
  have hsV : s₀ ∈ V := by
    constructor
    · nlinarith [mul_neg_of_pos_of_neg hscale hl0]
    · nlinarith [mul_pos hscale hr0]
  obtain ⟨U, hU, hxU, hboundary, hseam⟩ := native_regular_arc_seam_isolation F.seam a s₀ hs0 hs1 V hV hsV
  let zero : Ioo (-1 : ℝ) 1 := ⟨0, by norm_num, by norm_num⟩
  have hparam0 : parameter zero = s₀ := Subtype.ext (by simpa only [zero, mul_zero, add_zero] using hparameter zero)
  have hcenter : γ 0 = E.toSphere (F.map (F.seam.arc a s₀)) := by
    simpa only [zero, hparam0] using hγ zero
  refine ⟨U, hU, hxU, hboundary, ?_⟩
  intro z hz hzG hzball
  have hm : z ∈ (F.seam.arc a '' V) ∩ U := hseam ▸ And.intro hzG hz
  obtain ⟨v, hv, hvz⟩ := hm.1
  let t : ℝ := ((v : ℝ) - (s₀ : ℝ)) / scale
  have ht : t ∈ Ioo l r := by
    constructor
    · apply (lt_div_iff₀ hscale).mpr
      have hv' := hv.1
      change (s₀ : ℝ) + scale * l < (v : ℝ) at hv'
      nlinarith
    · apply (div_lt_iff₀ hscale).mpr
      have hv' := hv.2
      change (v : ℝ) < (s₀ : ℝ) + scale * r at hv'
      nlinarith
  have htlocal : t ∈ Ioo (-1 : ℝ) 1 :=
    ⟨(le_max_left _ _).trans_lt ht.1, ht.2.trans_le (min_le_left _ _)⟩
  have htarc : t ∈ Ioo left right :=
    ⟨(le_max_right _ _).trans_lt ht.1, ht.2.trans_le (min_le_right _ _)⟩
  have hparam : parameter ⟨t, htlocal⟩ = v := by
    apply Subtype.ext
    rw [hparameter]
    dsimp [t]
    field_simp
    ring
  have hpoint : γ t = E.toSphere (F.map z) := by
    have hh := hγ ⟨t, htlocal⟩
    rw [hparam, hvz] at hh
    exact hh
  have hzero : P (c.chart (E.toSphere (F.map z))) -
      P (c.chart (E.toSphere (F.map (F.seam.arc a s₀)))) ∈
      {y ∈ Metric.ball 0 ρ | s y = 0} := by
    rw [hgeom.zero_set_exact]
    refine ⟨⟨t, htarc, ?_⟩, hzball⟩
    dsimp only
    rw [hpoint, hcenter]
  exact hzero.2

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
