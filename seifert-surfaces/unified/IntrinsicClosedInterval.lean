import IntrinsicChartUniqueness
import Mathlib.Topology.Connected.Clopen

open scoped Manifold ContDiff
open Set Filter Topology
namespace SeifertSurfaces.Foundations.AmbientNeatTransport
noncomputable section
universe v
variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M] [T2Space M]

omit [IsManifold (𝓡∂ 3) ∞ M] [T2Space M] in
theorem mfderivWithin_on_Ici_of_Icc {c : ℝ → M} {a b t : ℝ}
    {L : TangentSpace 𝓘(ℝ,ℝ) t →L[ℝ] TangentSpace (𝓡∂ 3) (c t)}
    (h : HasMFDerivWithinAt 𝓘(ℝ,ℝ) (𝓡∂ 3) c (Icc a b) t L)
    (ht : t ∈ Ico a b) : HasMFDerivWithinAt 𝓘(ℝ,ℝ) (𝓡∂ 3) c (Ici t) t L := by
  apply h.mono_of_mem_nhdsWithin
  rw [mem_nhdsWithin]
  refine ⟨Iio b,isOpen_Iio,ht.2,?_⟩
  intro r hr
  exact ⟨ht.1.trans hr.2,hr.1.le⟩

omit [IsManifold (𝓡∂ 3) ∞ M] [T2Space M] in
theorem mfderivWithin_on_Iic_of_Icc {c : ℝ → M} {a b t : ℝ}
    {L : TangentSpace 𝓘(ℝ,ℝ) t →L[ℝ] TangentSpace (𝓡∂ 3) (c t)}
    (h : HasMFDerivWithinAt 𝓘(ℝ,ℝ) (𝓡∂ 3) c (Icc a b) t L)
    (ht : t ∈ Ioc a b) : HasMFDerivWithinAt 𝓘(ℝ,ℝ) (𝓡∂ 3) c (Iic t) t L := by
  apply h.mono_of_mem_nhdsWithin
  rw [mem_nhdsWithin]
  refine ⟨Ioi a,isOpen_Ioi,ht.1,?_⟩
  intro r hr
  exact ⟨hr.1.le,hr.2.trans ht.2⟩

/-- Relative local uniqueness includes the endpoints of the closed time interval. -/
theorem spatial_solution_eventuallyEq_Icc
    (Y : (q : Time × M) → TangentSpace (𝓡∂ 3) q.2)
    (hY : ContMDiff ((𝓡∂ 1).prod (𝓡∂ 3)) (𝓡∂ 3).tangent ∞
      (fun q => (⟨q.2,Y q⟩ : TangentBundle (𝓡∂ 3) M)))
    (hYb : ∀ q, q.2 ∈ (𝓡∂ 3).boundary M → inwardCoordinate q.2 (Y q) = 0)
    {a b : ℝ} (hab : Icc a b ⊆ Icc (0 : ℝ) 1) {γ η : ℝ → M}
    (hγ : ContinuousOn γ (Icc a b)) (hη : ContinuousOn η (Icc a b))
    (hγd : ∀ t ∈ Icc a b, HasMFDerivWithinAt 𝓘(ℝ,ℝ) (𝓡∂ 3) γ (Icc a b) t
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (Y (projIcc 0 1 (by norm_num) t,γ t))))
    (hηd : ∀ t ∈ Icc a b, HasMFDerivWithinAt 𝓘(ℝ,ℝ) (𝓡∂ 3) η (Icc a b) t
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (Y (projIcc 0 1 (by norm_num) t,η t))))
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b) (heq : γ t₀ = η t₀) :
    γ =ᶠ[𝓝[Icc a b] t₀] η := by
  obtain ⟨d,hd,U,hU,hpU,hUd,V,hV,hVs,hVb,hlocal,hVU⟩ :=
    exists_local_compact_spatial_chart_velocity Y hY hYb (projIcc 0 1 (by norm_num) t₀,γ t₀)
  have hcγ : ContinuousWithinAt (fun r => (projIcc 0 1 (by norm_num) r,γ r)) (Icc a b) t₀ :=
    continuous_projIcc.continuousWithinAt.prodMk (hγ t₀ ht₀)
  have hcη : ContinuousWithinAt (fun r => (projIcc 0 1 (by norm_num) r,η r)) (Icc a b) t₀ :=
    continuous_projIcc.continuousWithinAt.prodMk (hη t₀ ht₀)
  have hmem : {r | (projIcc 0 1 (by norm_num) r,γ r) ∈ U ∧
      (projIcc 0 1 (by norm_num) r,η r) ∈ U} ∈ 𝓝[Icc a b] t₀ :=
    inter_mem (hcγ (hU.mem_nhds hpU))
      (hcη (hU.mem_nhds (by dsimp only; rw [← heq]; exact hpU)))
  obtain ⟨ε,hε,hεU⟩ := Metric.mem_nhdsWithin_iff.mp hmem
  apply Filter.eventuallyEq_iff_exists_mem.mpr
  refine ⟨Metric.ball t₀ ε ∩ Icc a b,
    inter_mem (nhdsWithin_le_nhds (Metric.ball_mem_nhds _ hε)) self_mem_nhdsWithin,?_⟩
  intro u hu
  have hball₀ : t₀ ∈ Metric.ball t₀ ε := Metric.mem_ball_self hε
  have hseg : Icc (min t₀ u) (max t₀ u) ⊆ Metric.ball t₀ ε ∩ Icc a b := by
    intro r hr
    refine ⟨?_,?_,?_⟩
    · rw [Real.ball_eq_Ioo] at hu hball₀ ⊢
      exact ⟨lt_of_lt_of_le (lt_min hball₀.1 hu.1.1) hr.1,
        lt_of_le_of_lt hr.2 (max_lt hball₀.2 hu.1.2)⟩
    · exact (le_min ht₀.1 hu.2.1).trans hr.1
    · exact hr.2.trans (max_le ht₀.2 hu.2.2)
  have hsegA : Icc (min t₀ u) (max t₀ u) ⊆ Icc a b :=
    hseg.trans inter_subset_right
  have hγU' : ∀ r ∈ Icc (min t₀ u) (max t₀ u),
      (projIcc 0 1 (by norm_num) r,γ r) ∈ U := fun r hr => (hεU (hseg hr)).1
  have hηU' : ∀ r ∈ Icc (min t₀ u) (max t₀ u),
      (projIcc 0 1 (by norm_num) r,η r) ∈ U := fun r hr => (hεU (hseg hr)).2
  have hγd' (r) (hr : r ∈ Icc (min t₀ u) (max t₀ u)) :=
    (hγd r (hsegA hr)).mono hsegA
  have hηd' (r) (hr : r ∈ Icc (min t₀ u) (max t₀ u)) :=
    (hηd r (hsegA hr)).mono hsegA
  rcases le_total t₀ u with hle | hle
  · have hmin : min t₀ u = t₀ := min_eq_left hle
    have hmax : max t₀ u = u := max_eq_right hle
    have hh := spatial_chart_unique_Icc_right Y d hd hUd hV hVs hVU (hsegA.trans hab)
      (hγ.mono hsegA) (hη.mono hsegA) hγU' hηU'
      (fun r hr => mfderivWithin_on_Ici_of_Icc (hγd' r (Ico_subset_Icc_self hr)) hr)
      (fun r hr => mfderivWithin_on_Ici_of_Icc (hηd' r (Ico_subset_Icc_self hr)) hr)
      (by simpa only [hmin] using heq)
    exact hh (by simp only [hmin,hmax,mem_Icc]; exact ⟨hle,le_rfl⟩)
  · have hmin : min t₀ u = u := min_eq_right hle
    have hmax : max t₀ u = t₀ := max_eq_left hle
    have hh := spatial_chart_unique_Icc_left Y d hd hUd hV hVs hVU (hsegA.trans hab)
      (hγ.mono hsegA) (hη.mono hsegA) hγU' hηU'
      (fun r hr => mfderivWithin_on_Iic_of_Icc (hγd' r (Ioc_subset_Icc_self hr)) hr)
      (fun r hr => mfderivWithin_on_Iic_of_Icc (hηd' r (Ioc_subset_Icc_self hr)) hr)
      (by simpa only [hmax] using heq)
    exact hh (by simp only [hmin,hmax,mem_Icc]; exact ⟨le_rfl,hle⟩)

/-- Intrinsic solutions of a smooth boundary-tangent field are unique across
all chart changes on a closed interval. No interior-point premise is used. -/
theorem spatial_solution_unique_Icc
    (Y : (q : Time × M) → TangentSpace (𝓡∂ 3) q.2)
    (hY : ContMDiff ((𝓡∂ 1).prod (𝓡∂ 3)) (𝓡∂ 3).tangent ∞
      (fun q => (⟨q.2,Y q⟩ : TangentBundle (𝓡∂ 3) M)))
    (hYb : ∀ q, q.2 ∈ (𝓡∂ 3).boundary M → inwardCoordinate q.2 (Y q) = 0)
    {a b : ℝ} (hab : Icc a b ⊆ Icc (0 : ℝ) 1) {γ η : ℝ → M}
    (hγ : ContinuousOn γ (Icc a b)) (hη : ContinuousOn η (Icc a b))
    (hγd : ∀ t ∈ Icc a b, HasMFDerivWithinAt 𝓘(ℝ,ℝ) (𝓡∂ 3) γ (Icc a b) t
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (Y (projIcc 0 1 (by norm_num) t,γ t))))
    (hηd : ∀ t ∈ Icc a b, HasMFDerivWithinAt 𝓘(ℝ,ℝ) (𝓡∂ 3) η (Icc a b) t
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (Y (projIcc 0 1 (by norm_num) t,η t))))
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b) (heq : γ t₀ = η t₀) : EqOn γ η (Icc a b) := by
  let E : Set (Icc a b) := {r | γ r = η r}
  have hc : IsClosed E := isClosed_eq hγ.domRestrict hη.domRestrict
  have ho : IsOpen E := by
    rw [isOpen_iff_mem_nhds]
    intro r hr
    have hh := spatial_solution_eventuallyEq_Icc Y hY hYb hab hγ hη hγd hηd r.property hr
    rw [nhds_subtype_eq_comap_nhdsWithin]
    exact hh.comap Subtype.val
  letI : PreconnectedSpace (Icc a b) := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  have hE : E = univ := (IsClopen.eq_univ ⟨hc,ho⟩ ⟨⟨t₀,ht₀⟩,heq⟩)
  intro t ht
  have hh : (⟨t,ht⟩ : Icc a b) ∈ E := hE.symm ▸ mem_univ _
  exact hh

end
end SeifertSurfaces.Foundations.AmbientNeatTransport
