import B1ActualGraphMembership_v474
import DifferentialGeometry.Topology.InvarianceOfDomainManifold

noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
universe v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- The literal local circle parameter is injective on the supplied collar
window; the strict length bound prevents a wrap around the circle. -/
theorem actual_localCircle_injective_v475
    (D : B1OriginalData g J) (s : Circle) (W : CollarWindow D s) :
    InjOn (localCircle D s) {t : ℝ | |t| < 2 * W.R} := by
  have hangle : ∀ t : ℝ, |t| < 2 * W.R →
      2 * Real.pi * t / D.leafLength ∈ Ico (-Real.pi) Real.pi := by
    intro t ht
    have ht' : |t| < D.leafLength / 2 := by linarith [W.R_circle]
    have hmul := mul_lt_mul_of_pos_left ht' (by positivity : 0 < 2 * Real.pi)
    have habs : |2 * Real.pi * t / D.leafLength| < Real.pi := by
      rw [abs_div, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi),
        abs_of_pos D.leafLength_pos, div_lt_iff₀ D.leafLength_pos]
      nlinarith
    exact ⟨(abs_lt.mp habs).1.le,(abs_lt.mp habs).2⟩
  intro a ha b hb hab
  have he : Circle.exp (2 * Real.pi * a / D.leafLength) =
      Circle.exp (2 * Real.pi * b / D.leafLength) := mul_left_cancel hab
  have hangleeq := Circle.exp_injOn_Ico (a := -Real.pi) (b := Real.pi)
    (by linarith) (hangle a ha) (hangle b hb) he
  have hh : 2 * Real.pi * a = 2 * Real.pi * b := by
    exact (div_left_inj' D.leafLength_pos.ne').mp hangleeq
  exact (mul_right_injective₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0)) hh

/-- Smoothness of the original local collar on its actual half-domain. -/
theorem actual_localCollar_smooth_v475
    (D : B1OriginalData g J) (s : Circle) (R : ℝ) :
    ContMDiffOn 𝓘(ℝ,E3) (𝓡∂ 3) ∞ (localCollar D s) (collarDomain D R) := by
  have h0 : ContDiff ℝ ∞ (fun y : E3 => y 0) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).contDiff
  have h1 : ContDiff ℝ ∞ (fun y : E3 => y 1) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)).contDiff
  have h2 : ContDiff ℝ ∞ (fun y : E3 => y 2) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).contDiff
  have hpre : ContMDiff 𝓘(ℝ,E3) ((𝓡 1).prod (𝓘(ℝ).prod 𝓘(ℝ))) ∞
      (fun y : E3 => (localCircle D s (y 0),y 1,y 2)) :=
    (contMDiff_const.mul (contMDiff_circleExp.comp
      (((contDiff_const.mul h0).div_const D.leafLength).contMDiff))).prodMk
      (h1.contMDiff.prodMk h2.contMDiff)
  exact D.collar_smooth.comp hpre.contMDiffOn (fun y hy => ⟨hy.2.1,hy.2.2⟩)

/-- The original embedding and local circle bound give injectivity in all
three collar coordinates. -/
theorem actual_localCollar_injective_v475
    (D : B1OriginalData g J) (s : Circle) (W : CollarWindow D s) :
    InjOn (localCollar D s) (collarDomain D W.R) := by
  intro y hy z hz he
  have hpre : (localCircle D s (y 0),y 1,y 2) =
      (localCircle D s (z 0),z 1,z 2) := by
    have hsub := D.collar_embedding.injective
      (a₁ := ⟨(localCircle D s (y 0),y 1,y 2),⟨hy.2.1,hy.2.2⟩⟩)
      (a₂ := ⟨(localCircle D s (z 0),z 1,z 2),⟨hz.2.1,hz.2.2⟩⟩) he
    exact congrArg Subtype.val hsub
  have h0 := actual_localCircle_injective_v475 D s W hy.1 hz.1 (congrArg Prod.fst hpre)
  have h1 := congrArg (fun p : Circle × (ℝ × ℝ) => p.2.1) hpre
  have h2 := congrArg (fun p : Circle × (ℝ × ℝ) => p.2.2) hpre
  ext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- Every open subpatch of the actual three-dimensional collar domain has
open image in the actual exterior. This is invariance of domain, with all
continuity and injectivity premises supplied by the original collar. -/
theorem actual_localCollar_open_image_v475
    (D : B1OriginalData g J) (s : Circle) (W : CollarWindow D s)
    (O : Set E3) (hO : IsOpen O) (hOC : O ⊆ collarDomain D W.R) :
    IsOpen (localCollar D s '' O) := by
  let f : O → E.Carrier := fun y => localCollar D s y
  have hf : Continuous f :=
    ((actual_localCollar_smooth_v475 D s W.R).continuousOn.mono hOC).domRestrict
  have hinj : Injective f := by
    intro y z he
    exact Subtype.ext (actual_localCollar_injective_v475 D s W (hOC y.property)
      (hOC z.property) he)
  have ho := DifferentialGeometry.Topology.isOpen_range_of_isOpen_of_continuous_injective_real
    (𝓡∂ 3) hO f hf hinj
  have heq : range f = localCollar D s '' O := by
    ext p
    constructor
    · rintro ⟨y,rfl⟩
      exact ⟨y,y.property,rfl⟩
    · rintro ⟨y,hy,rfl⟩
      exact ⟨⟨y,hy⟩,rfl⟩
  rwa [heq] at ho

#print axioms actual_localCircle_injective_v475
#print axioms actual_localCollar_smooth_v475
#print axioms actual_localCollar_injective_v475
#print axioms actual_localCollar_open_image_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
