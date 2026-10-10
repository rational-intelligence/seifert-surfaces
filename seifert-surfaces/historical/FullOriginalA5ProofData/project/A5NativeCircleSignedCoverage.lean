import A5NativeArcSignedCoverage

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC CurvedDivergence
universe u

/-- The original open embedded circle parameter supplies exact signed
zero-set coverage near the native circle seam point. -/
theorem native_circle_projected_signed_zero_near
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (a : Fin F.seam.circleCount) (s₀ : Circle)
    (parameter : Ioo (-1 : ℝ) 1 → Circle) (hp : IsEmbedding parameter)
    (hpopen : IsOpen (range parameter))
    (hpzero : parameter ⟨0, by norm_num, by norm_num⟩ = s₀)
    (γ : ℝ → ThreeSphere)
    (hγ : ∀ t : Ioo (-1 : ℝ) 1, γ t = E.toSphere (F.map (F.seam.circle a (parameter t))))
    (c : SmoothAmbientChart ThreeSphere) (P : E3 →L[ℝ] E2)
    (ρ : ℝ) (s : E2 → ℝ) (left right : ℝ) (hl : left < 0) (hr : 0 < right)
    (hgeom : SignedArcGeometry (Metric.ball 0 ρ) s
      (fun t => P (c.chart (γ t)) - P (c.chart (γ 0))) left right) :
    ∃ U : Set S, IsOpen U ∧ F.seam.circle a s₀ ∈ U ∧ U ⊆ S.boundaryᶜ ∧
      ∀ z ∈ U, z ∈ F.seam.carrier →
        P (c.chart (E.toSphere (F.map z))) -
          P (c.chart (E.toSphere (F.map (F.seam.circle a s₀)))) ∈ Metric.ball 0 ρ →
        s (P (c.chart (E.toSphere (F.map z))) -
          P (c.chart (E.toSphere (F.map (F.seam.circle a s₀))))) = 0 := by
  let V := parameter '' {t : Ioo (-1 : ℝ) 1 | (t : ℝ) ∈ Ioo left right}
  have hV : IsOpen V :=
    (show IsOpenEmbedding parameter from ⟨hp, hpopen⟩).isOpenMap _
      (isOpen_Ioo.preimage continuous_subtype_val)
  have hsV : s₀ ∈ V := ⟨⟨0, by norm_num, by norm_num⟩, ⟨hl, hr⟩, hpzero⟩
  obtain ⟨U, hU, hxU, hboundary, hseam⟩ := native_circle_seam_isolation F.seam a s₀ V hV hsV
  have hcenter : γ 0 = E.toSphere (F.map (F.seam.circle a s₀)) := by
    simpa only [hpzero] using hγ ⟨0, by norm_num, by norm_num⟩
  refine ⟨U, hU, hxU, hboundary, ?_⟩
  intro z hz hzG hzball
  have hm : z ∈ (F.seam.circle a '' V) ∩ U := hseam ▸ And.intro hzG hz
  obtain ⟨v, ⟨t, ht, htv⟩, hvz⟩ := hm.1
  have hpoint : γ t = E.toSphere (F.map z) := by
    rw [hγ t, htv, hvz]
  have hzero : P (c.chart (E.toSphere (F.map z))) -
      P (c.chart (E.toSphere (F.map (F.seam.circle a s₀)))) ∈
      {y ∈ Metric.ball 0 ρ | s y = 0} := by
    rw [hgeom.zero_set_exact]
    refine ⟨⟨t, ht, ?_⟩, hzball⟩
    dsimp only
    rw [hpoint, hcenter]
  exact hzero.2

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
