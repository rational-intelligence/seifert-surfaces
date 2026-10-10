import A5SectorProjectedInverse

set_option autoImplicit false
open scoped ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations

/-- On one regular closed-sector sheet, a transverse C1 projection is
injective in an actual coordinate ball. -/
theorem regular_sector_projection_injective_near
    (A : SectorModel) (G : Euc 2 → Euc 3) (x : Euc 2)
    (hx : x ∈ A.domain) (hregular : x ≠ 0 ∨ A.angle = Real.pi)
    (hG : ContDiffWithinAt ℝ 1 G A.domain x)
    (P : Euc 3 →L[ℝ] Euc 2)
    (hP : Function.Bijective (P.comp (fderivWithin ℝ G A.domain x))) :
    ∃ r : ℝ, 0 < r ∧ InjOn (P ∘ G) (Metric.ball x r ∩ A.domain) := by
  obtain ⟨e, hex, _, heq, _, _, _, _⟩ :=
    C1_sector_projected_local_diffeomorphism A G x hx hregular hG P hP
  have hgood : ∀ᶠ y in 𝓝[A.domain] x, y ∈ e.source ∧ e y = P (G y) := by
    filter_upwards [heq, nhdsWithin_le_nhds (e.open_source.mem_nhds hex)] with y he hy
    exact ⟨hy, he⟩
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhdsWithin_iff.mp hgood
  refine ⟨r, hr, ?_⟩
  intro y hy z hz he
  apply e.injOn (hsub hy).1 (hsub hz).1
  rw [(hsub hy).2, (hsub hz).2]
  exact he

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
