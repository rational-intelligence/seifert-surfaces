import ChartFlowTangentEquation
import LocalSpatialVelocity
import Mathlib.Analysis.ODE.ExistUnique

open scoped Manifold ContDiff
open Set Filter Topology
namespace SeifertSurfaces.Foundations.AmbientNeatTransport
noncomputable section
universe v
variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M] [T2Space M]

/-- Coordinate uniqueness uses the differential of the chart, including at
spatial boundary points. Both curves solve the same intrinsic field. -/
theorem spatial_chart_unique_Icc_right
    (Y : (q : Time × M) → TangentSpace (𝓡∂ 3) q.2)
    (d : OpenPartialHomeomorph M (EuclideanHalfSpace 3))
    (hd : d ∈ IsManifold.maximalAtlas (𝓡∂ 3) ∞ M)
    {U : Set (Time × M)} (hUd : U ⊆ univ ×ˢ d.source)
    {V : ℝ × Euc 3 → Euc 3} (hV : ContDiff ℝ ∞ V) (hs : HasCompactSupport V)
    (hVU : ∀ q ∈ U, V ((q.1 : ℝ),d.extend (𝓡∂ 3) q.2) = spatialChartVelocity Y d q)
    {a b : ℝ} (hab : Icc a b ⊆ Icc (0 : ℝ) 1)
    {γ η : ℝ → M}
    (hγ : ContinuousOn γ (Icc a b)) (hη : ContinuousOn η (Icc a b))
    (hγU : ∀ t ∈ Icc a b, (projIcc 0 1 (by norm_num) t,γ t) ∈ U)
    (hηU : ∀ t ∈ Icc a b, (projIcc 0 1 (by norm_num) t,η t) ∈ U)
    (hγd : ∀ t ∈ Ico a b, HasMFDerivWithinAt 𝓘(ℝ,ℝ) (𝓡∂ 3) γ (Ici t) t
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (Y (projIcc 0 1 (by norm_num) t,γ t))))
    (hηd : ∀ t ∈ Ico a b, HasMFDerivWithinAt 𝓘(ℝ,ℝ) (𝓡∂ 3) η (Ici t) t
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (Y (projIcc 0 1 (by norm_num) t,η t))))
    (heq : γ a = η a) : EqOn γ η (Icc a b) := by
  let e := d.extend (𝓡∂ 3)
  have hγs : MapsTo γ (Icc a b) d.source := fun t ht => (hUd (hγU t ht)).2
  have hηs : MapsTo η (Icc a b) d.source := fun t ht => (hUd (hηU t ht)).2
  have hγc : ContinuousOn (e ∘ γ) (Icc a b) :=
    (d.contMDiffOn_extend hd).continuousOn.comp hγ hγs
  have hηc : ContinuousOn (e ∘ η) (Icc a b) :=
    (d.contMDiffOn_extend hd).continuousOn.comp hη hηs
  obtain ⟨K,hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs hV (by simp)
  have hlip (t : ℝ) : LipschitzOnWith K (fun z => V (t,z)) univ :=
    by simpa only [mul_one,Function.comp_def] using
      (hK.comp (LipschitzWith.prodMk_left t)).lipschitzOnWith (s := univ)
  have hcoord {c : ℝ → M} (hcU : ∀ t ∈ Icc a b,
      (projIcc 0 1 (by norm_num) t,c t) ∈ U)
      (hcd : ∀ t ∈ Ico a b, HasMFDerivWithinAt 𝓘(ℝ,ℝ) (𝓡∂ 3) c (Ici t) t
        ((ContinuousLinearMap.id ℝ ℝ).smulRight (Y (projIcc 0 1 (by norm_num) t,c t)))) :
      ∀ t ∈ Ico a b, HasDerivWithinAt (e ∘ c) (V (t,e (c t))) (Ici t) t := by
    intro t ht
    have ht' := Ico_subset_Icc_self ht
    have hh := chart_coordinate_hasDerivWithinAt d hd (hUd (hcU t ht')).2
      (Y (projIcc 0 1 (by norm_num) t,c t)) (hcd t ht)
    have hv := hVU (projIcc 0 1 (by norm_num) t,c t) (hcU t ht')
    have hp : (projIcc 0 1 (by norm_num) t : ℝ) = t := congrArg Subtype.val (projIcc_of_mem (by norm_num) (hab ht'))
    rw [hp] at hv
    exact hh.congr_deriv hv.symm
  have hc := ODE_solution_unique_of_mem_Icc_right (fun t _ => hlip t)
    hγc (hcoord hγU hγd) (fun _ _ => mem_univ _)
    hηc (hcoord hηU hηd) (fun _ _ => mem_univ _) (congrArg e heq)
  intro t ht
  have hh := congrArg e.symm (hc ht)
  change e.symm (e (γ t)) = e.symm (e (η t)) at hh
  rw [e.left_inv (by simpa only [e,d.extend_source] using hγs ht),
    e.left_inv (by simpa only [e,d.extend_source] using hηs ht)] at hh
  exact hh

/-- Coordinate uniqueness uses the differential of the chart, including at
spatial boundary points. Both curves solve the same intrinsic field. -/
theorem spatial_chart_unique_Icc_left
    (Y : (q : Time × M) → TangentSpace (𝓡∂ 3) q.2)
    (d : OpenPartialHomeomorph M (EuclideanHalfSpace 3))
    (hd : d ∈ IsManifold.maximalAtlas (𝓡∂ 3) ∞ M)
    {U : Set (Time × M)} (hUd : U ⊆ univ ×ˢ d.source)
    {V : ℝ × Euc 3 → Euc 3} (hV : ContDiff ℝ ∞ V) (hs : HasCompactSupport V)
    (hVU : ∀ q ∈ U, V ((q.1 : ℝ),d.extend (𝓡∂ 3) q.2) = spatialChartVelocity Y d q)
    {a b : ℝ} (hab : Icc a b ⊆ Icc (0 : ℝ) 1)
    {γ η : ℝ → M}
    (hγ : ContinuousOn γ (Icc a b)) (hη : ContinuousOn η (Icc a b))
    (hγU : ∀ t ∈ Icc a b, (projIcc 0 1 (by norm_num) t,γ t) ∈ U)
    (hηU : ∀ t ∈ Icc a b, (projIcc 0 1 (by norm_num) t,η t) ∈ U)
    (hγd : ∀ t ∈ Ioc a b, HasMFDerivWithinAt 𝓘(ℝ,ℝ) (𝓡∂ 3) γ (Iic t) t
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (Y (projIcc 0 1 (by norm_num) t,γ t))))
    (hηd : ∀ t ∈ Ioc a b, HasMFDerivWithinAt 𝓘(ℝ,ℝ) (𝓡∂ 3) η (Iic t) t
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (Y (projIcc 0 1 (by norm_num) t,η t))))
    (heq : γ b = η b) : EqOn γ η (Icc a b) := by
  let e := d.extend (𝓡∂ 3)
  have hγs : MapsTo γ (Icc a b) d.source := fun t ht => (hUd (hγU t ht)).2
  have hηs : MapsTo η (Icc a b) d.source := fun t ht => (hUd (hηU t ht)).2
  have hγc : ContinuousOn (e ∘ γ) (Icc a b) :=
    (d.contMDiffOn_extend hd).continuousOn.comp hγ hγs
  have hηc : ContinuousOn (e ∘ η) (Icc a b) :=
    (d.contMDiffOn_extend hd).continuousOn.comp hη hηs
  obtain ⟨K,hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs hV (by simp)
  have hlip (t : ℝ) : LipschitzOnWith K (fun z => V (t,z)) univ :=
    by simpa only [mul_one,Function.comp_def] using
      (hK.comp (LipschitzWith.prodMk_left t)).lipschitzOnWith (s := univ)
  have hcoord {c : ℝ → M} (hcU : ∀ t ∈ Icc a b,
      (projIcc 0 1 (by norm_num) t,c t) ∈ U)
      (hcd : ∀ t ∈ Ioc a b, HasMFDerivWithinAt 𝓘(ℝ,ℝ) (𝓡∂ 3) c (Iic t) t
        ((ContinuousLinearMap.id ℝ ℝ).smulRight (Y (projIcc 0 1 (by norm_num) t,c t)))) :
      ∀ t ∈ Ioc a b, HasDerivWithinAt (e ∘ c) (V (t,e (c t))) (Iic t) t := by
    intro t ht
    have ht' := Ioc_subset_Icc_self ht
    have hh := chart_coordinate_hasDerivWithinAt d hd (hUd (hcU t ht')).2
      (Y (projIcc 0 1 (by norm_num) t,c t)) (hcd t ht)
    have hv := hVU (projIcc 0 1 (by norm_num) t,c t) (hcU t ht')
    have hp : (projIcc 0 1 (by norm_num) t : ℝ) = t := congrArg Subtype.val (projIcc_of_mem (by norm_num) (hab ht'))
    rw [hp] at hv
    exact hh.congr_deriv hv.symm
  have hc := ODE_solution_unique_of_mem_Icc_left (fun t _ => hlip t)
    hγc (hcoord hγU hγd) (fun _ _ => mem_univ _)
    hηc (hcoord hηU hηd) (fun _ _ => mem_univ _) (congrArg e heq)
  intro t ht
  have hh := congrArg e.symm (hc ht)
  change e.symm (e (γ t)) = e.symm (e (η t)) at hh
  rw [e.left_inv (by simpa only [e,d.extend_source] using hγs ht),
    e.left_inv (by simpa only [e,d.extend_source] using hηs ht)] at hh
  exact hh

end
end SeifertSurfaces.Foundations.AmbientNeatTransport
