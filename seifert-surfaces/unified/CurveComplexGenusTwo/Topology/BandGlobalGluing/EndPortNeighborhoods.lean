import CurveComplexGenusTwo.Topology.FrontierCircle.SurfaceInvarianceProbe
import CurveComplexGenusTwo.Topology.FrontierCircle.GlobalBandScaffold

open Set Topology unitInterval
namespace CurveComplex

/-- An interior point of an embedded endpoint rectangle is an ambient interior
point of its range. -/
theorem endRectangle_center_interior
    {S : Type*} [TopologicalSpace S] [ChartedSpace Schoenflies.Plane S]
    (E : EndRectangle → S) (hE : IsEmbedding E) :
    E (⟨0, by norm_num⟩, ⟨0, by norm_num⟩) ∈ interior (Set.range E) := by
  let f : Schoenflies.Plane → S := fun z =>
    E (projIcc (-1) 1 (by norm_num) (z 0),
       projIcc (-1) 1 (by norm_num) (z 1))
  let U : Set Schoenflies.Plane :=
    {z | z 0 ∈ Ioo (-1) 1 ∧ z 1 ∈ Ioo (-1) 1}
  have hU : IsOpen U := (isOpen_Ioo.preimage (by fun_prop)).inter
    (isOpen_Ioo.preimage (by fun_prop))
  have hf : Continuous f := hE.continuous.comp
    ((continuous_projIcc.comp (by fun_prop)).prodMk
      (continuous_projIcc.comp (by fun_prop)))
  have hi : InjOn f U := by
    intro z hz w hw he
    have hh := hE.injective he
    have h0 := congrArg (fun q : EndRectangle => (q.1 : ℝ)) hh
    have h1 := congrArg (fun q : EndRectangle => (q.2 : ℝ)) hh
    simp only [projIcc_of_mem (show (-1:ℝ) ≤ 1 by norm_num)
      ⟨hz.1.1.le,hz.1.2.le⟩,
      projIcc_of_mem (show (-1:ℝ) ≤ 1 by norm_num)
      ⟨hw.1.1.le,hw.1.2.le⟩] at h0
    simp only [projIcc_of_mem (show (-1:ℝ) ≤ 1 by norm_num)
      ⟨hz.2.1.le,hz.2.2.le⟩,
      projIcc_of_mem (show (-1:ℝ) ≤ 1 by norm_num)
      ⟨hw.2.1.le,hw.2.2.le⟩] at h1
    ext i
    fin_cases i
    · exact h0
    · exact h1
  have hopen : IsOpen (f '' U) :=
    surface_invariance_of_domain_probe f U hU hf.continuousOn hi
  have hsub : f '' U ⊆ Set.range E := by
    rintro z ⟨w,hw,rfl⟩
    exact Set.mem_range_self _
  apply (hopen.subset_interior_iff.mpr hsub)
  refine ⟨Schoenflies.Plane.mk 0 0, ⟨by norm_num, by norm_num⟩, ?_⟩
  simp [f, projIcc_of_mem (show (-1:ℝ) ≤ 1 by norm_num)
    (show (0:ℝ) ∈ Icc (-1) 1 by norm_num)]

/-- Both prescribed first-arc endpoint rectangles capture actual parameter
tails of the outside arc. -/
theorem OneCrossingBandBase.first_endpoint_rectangles_cover_tails
    {S : Type} [TopologicalSpace S] [ChartedSpace Schoenflies.Plane S]
    {a b : Curve S} (D : OneCrossingBandBase a b) :
    ∃ η₀ η₁ : ℝ, 0 < η₀ ∧ 0 < η₁ ∧
      (∀ t : I, (t : ℝ) < η₀ → D.firstArc t ∈ Set.range (D.ends 2)) ∧
      (∀ t : I, 1 - η₁ < (t : ℝ) → D.firstArc t ∈ Set.range (D.ends 0)) := by
  have hstart : D.firstArc (0 : I) ∈ interior (Set.range (D.ends 2)) := by
    rw [D.firstArc.source, ← D.ends_seam]
    exact endRectangle_center_interior (D.ends 2) (D.ends_embedded 2)
  have hend : D.firstArc (1 : I) ∈ interior (Set.range (D.ends 0)) := by
    rw [D.firstArc.target, ← D.ends_seam]
    exact endRectangle_center_interior (D.ends 0) (D.ends_embedded 0)
  have hpre0 : D.firstArc ⁻¹' interior (Set.range (D.ends 2)) ∈ 𝓝 (0 : I) :=
    D.firstArc.continuous.continuousAt.preimage_mem_nhds
      (isOpen_interior.mem_nhds hstart)
  have hpre1 : D.firstArc ⁻¹' interior (Set.range (D.ends 0)) ∈ 𝓝 (1 : I) :=
    D.firstArc.continuous.continuousAt.preimage_mem_nhds
      (isOpen_interior.mem_nhds hend)
  obtain ⟨η₀,hη₀,hball0⟩ := Metric.mem_nhds_iff.mp hpre0
  obtain ⟨η₁,hη₁,hball1⟩ := Metric.mem_nhds_iff.mp hpre1
  refine ⟨η₀,η₁,hη₀,hη₁,?_,?_⟩
  · intro t ht
    apply interior_subset
    apply hball0
    simpa [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq,
      abs_of_nonneg t.property.1] using ht
  · intro t ht
    apply interior_subset
    apply hball1
    have hle : (t : ℝ) ≤ 1 := t.property.2
    have habs : |(t : ℝ) - 1| = 1 - (t : ℝ) :=
      by simpa only [neg_sub] using abs_of_nonpos (sub_nonpos.mpr hle)
    simpa [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq, habs] using
      (show 1 - (t : ℝ) < η₁ by linarith)

/-- The prescribed second-arc endpoint rectangles also capture actual
parameter tails. -/
theorem OneCrossingBandBase.second_endpoint_rectangles_cover_tails
    {S : Type} [TopologicalSpace S] [ChartedSpace Schoenflies.Plane S]
    {a b : Curve S} (D : OneCrossingBandBase a b) :
    ∃ η₀ η₁ : ℝ, 0 < η₀ ∧ 0 < η₁ ∧
      (∀ t : I, (t : ℝ) < η₀ → D.secondArc t ∈ Set.range (D.ends 3)) ∧
      (∀ t : I, 1 - η₁ < (t : ℝ) → D.secondArc t ∈ Set.range (D.ends 1)) := by
  have hstart : D.secondArc (0 : I) ∈ interior (Set.range (D.ends 3)) := by
    rw [D.secondArc.source, ← D.ends_seam]
    exact endRectangle_center_interior (D.ends 3) (D.ends_embedded 3)
  have hend : D.secondArc (1 : I) ∈ interior (Set.range (D.ends 1)) := by
    rw [D.secondArc.target, ← D.ends_seam]
    exact endRectangle_center_interior (D.ends 1) (D.ends_embedded 1)
  have hpre0 : D.secondArc ⁻¹' interior (Set.range (D.ends 3)) ∈ 𝓝 (0 : I) :=
    D.secondArc.continuous.continuousAt.preimage_mem_nhds
      (isOpen_interior.mem_nhds hstart)
  have hpre1 : D.secondArc ⁻¹' interior (Set.range (D.ends 1)) ∈ 𝓝 (1 : I) :=
    D.secondArc.continuous.continuousAt.preimage_mem_nhds
      (isOpen_interior.mem_nhds hend)
  obtain ⟨η₀,hη₀,hball0⟩ := Metric.mem_nhds_iff.mp hpre0
  obtain ⟨η₁,hη₁,hball1⟩ := Metric.mem_nhds_iff.mp hpre1
  refine ⟨η₀,η₁,hη₀,hη₁,?_,?_⟩
  · intro t ht
    apply interior_subset
    apply hball0
    simpa [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq,
      abs_of_nonneg t.property.1] using ht
  · intro t ht
    apply interior_subset
    apply hball1
    have hle : (t : ℝ) ≤ 1 := t.property.2
    have habs : |(t : ℝ) - 1| = 1 - (t : ℝ) :=
      by simpa only [neg_sub] using abs_of_nonpos (sub_nonpos.mpr hle)
    simpa [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq, habs] using
      (show 1 - (t : ℝ) < η₁ by linarith)

#print axioms endRectangle_center_interior
#print axioms OneCrossingBandBase.first_endpoint_rectangles_cover_tails
#print axioms OneCrossingBandBase.second_endpoint_rectangles_cover_tails
end CurveComplex
