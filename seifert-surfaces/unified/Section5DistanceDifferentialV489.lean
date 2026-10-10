import A7NativeBoundaryCovectorV464
import Section5GlobalDistanceV489
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
open SeifertSurfaces.OriginalEndpoints.A7Support
noncomputable section
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}

theorem inward_distance_mfderiv_ne_zero (g : SmoothMetric E.Carrier)
    {U : Set E.Carrier} (hU : IsOpen U) {r : E.Carrier → ℝ}
    (hr : IsInwardDistanceCoordinate g U r) {p : E.Carrier} (hp : p ∈ U) :
    mfderiv (𝓡∂ 3) 𝓘(ℝ) r p ≠ 0 := by
  obtain ⟨n,hn,hpair⟩ := hr.2.2.2 p hp
  have hnn := hpair n
  change g.inner p n n = mfderivWithin (𝓡∂ 3) 𝓘(ℝ) r U p n at hnn
  rw [mfderivWithin_eq_mfderiv (hU.uniqueMDiffWithinAt hp)
    (((hr.1 p hp).contMDiffAt (hU.mem_nhds hp)).mdifferentiableAt (by simp))] at hnn
  intro hz
  rw [hz,zero_apply,hn] at hnn
  exact one_ne_zero hnn

theorem inward_distance_differential_positive (g : SmoothMetric E.Carrier)
    {U : Set E.Carrier} (hU : IsOpen U) {r : E.Carrier → ℝ}
    (hr : IsInwardDistanceCoordinate g U r) {p : E.Carrier} (hp : p ∈ U)
    (hpb : p ∈ (𝓡∂ 3).boundary E.Carrier)
    (w : TangentSpace (𝓡∂ 3) p) (hw : 0 < inwardCoordinate p w) :
    0 < (show ℝ from mfderiv (𝓡∂ 3) 𝓘(ℝ) r p w) := by
  have hd : MDifferentiableAt (𝓡∂ 3) 𝓘(ℝ) r p :=
    ((hr.1 p hp).contMDiffAt (hU.mem_nhds hp)).mdifferentiableAt (by simp)
  have hzero : r p = 0 := (hr.2.2.1 p hp).mp hpb
  have hnonneg : ∀ᶠ q in 𝓝 p, 0 ≤ r q := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact hr.2.1 q hq
  have hcoord : 0 < (show E3 from w) 0 := by
    rwa [inwardCoordinate_eq_coordinate] at hw
  have hge := boundary_minimum_covector_nonneg hd hpb hzero hnonneg w hcoord.le
  apply lt_of_le_of_ne hge
  intro he
  have he' : mfderiv (𝓡∂ 3) 𝓘(ℝ) r p w = 0 := he.symm
  apply inward_distance_mfderiv_ne_zero g hU hr hp
  ext v
  let z : TangentSpace (𝓡∂ 3) p :=
    v - (((show E3 from v) 0) / ((show E3 from w) 0)) • w
  have hz : inwardCoordinate p z = 0 := by
    rw [inwardCoordinate_eq_coordinate]
    change (show E3 from v) 0 - ((show E3 from v) 0 / (show E3 from w) 0) * (show E3 from w) 0 = 0
    rw [div_mul_cancel₀ _ hcoord.ne',sub_self]
  have hv := boundary_minimum_covector hd hpb hzero hnonneg z hz
  dsimp only [z] at hv
  rw [map_sub,map_smul] at hv
  simpa only [he',smul_zero,sub_zero,zero_apply] using! hv

#print axioms inward_distance_differential_positive
end
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
