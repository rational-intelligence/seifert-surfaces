import A5NativeBoundaryClockCoverage

set_option autoImplicit false
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal

/-- A native embedded boundary clock covers every sufficiently near
boundary point by arbitrarily small clock parameters. This uses only the
literal topological image equality, without differentiating source maps. -/
theorem embedded_boundary_clock_arbitrarily_small_coverage
    {X : Type*} [TopologicalSpace X] (B : Set X) (b : ℝ → X)
    (hbi : IsEmbedding (fun t : Ioo (-1 : ℝ) 1 => b t))
    (U : Set X) (hU : IsOpen U) (hbU : b 0 ∈ U)
    (hcover : range (fun t : Ioo (-1 : ℝ) 1 => b t) = U ∩ B)
    (J : Set ℝ) (hJ : J ∈ 𝓝 (0 : ℝ)) :
    ∀ᶠ x in 𝓝[B] (b 0), ∃ t ∈ J, b t = x := by
  let z : Ioo (-1 : ℝ) 1 := ⟨0,by constructor <;> norm_num⟩
  have hJ' : (Subtype.val ⁻¹' J : Set (Ioo (-1 : ℝ) 1)) ∈ 𝓝 z :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds hJ
  have hh := hbi.isInducing.image_mem_nhdsWithin hJ'
  change (fun t : Ioo (-1 : ℝ) 1 => b t) '' (Subtype.val ⁻¹' J) ∈
    𝓝[range (fun t : Ioo (-1 : ℝ) 1 => b t)] (b 0) at hh
  rw [hcover,nhdsWithin_inter_of_mem (nhdsWithin_le_nhds (hU.mem_nhds hbU))] at hh
  filter_upwards [hh] with x hx
  obtain ⟨t,ht,hbt⟩ := hx
  exact ⟨t,ht,hbt⟩

/-- Continuous source lifts pull actual boundary-clock coverage back to
the closed half-disc, retaining arbitrarily small clock parameters. -/
theorem boundary_clock_coverage_under_continuous_lift
    {X : Type*} [TopologicalSpace X] (B : Set X) (b : ℝ → X)
    (hbi : IsEmbedding (fun t : Ioo (-1 : ℝ) 1 => b t))
    (U : Set X) (hU : IsOpen U) (hbU : b 0 ∈ U)
    (hcover : range (fun t : Ioo (-1 : ℝ) 1 => b t) = U ∩ B)
    {Y : Type*} [TopologicalSpace Y] (A : Set Y) (y : Y) (q : Y → X)
    (hq : ContinuousWithinAt q A y) (hq0 : q y = b 0)
    (Z : Set Y) (hqB : ∀ z ∈ A, z ∈ Z → q z ∈ B) :
    ∀ J ∈ 𝓝 (0 : ℝ), ∀ᶠ z in 𝓝[A] y,
      z ∈ Z → ∃ t ∈ J, q z = b t := by
  intro J hJ
  have hh := embedded_boundary_clock_arbitrarily_small_coverage B b hbi U hU hbU hcover J hJ
  obtain ⟨V,hV,hVsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hh
  have hVq : ∀ᶠ z in 𝓝[A] y, q z ∈ V :=
    hq.preimage_mem_nhdsWithin (hq0.symm ▸ hV)
  filter_upwards [hVq,self_mem_nhdsWithin] with z hzV hzA
  intro hzZ
  obtain ⟨t,ht,hbt⟩ := hVsub ⟨hzV,hqB z hzA hzZ⟩
  exact ⟨t,ht,hbt.symm⟩

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
