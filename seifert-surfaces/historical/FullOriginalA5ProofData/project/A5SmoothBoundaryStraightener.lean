import A5AmbientProjectedBoundaryCoordinates

set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC

/-- A smooth regular boundary curve is straightened by an actual smooth
local coordinate change. Its inverse retains the exact transverse strip
formula; the sign of the transverse vector remains available to the
one-sided graph construction. -/
theorem smooth_boundary_straightener_with_transverse_vector
    (γ : ℝ → E2) (I : Set ℝ) (hI : IsOpen I) (hzero : (0 : ℝ) ∈ I)
    (hγ : ContDiffOn ℝ ∞ γ I) (v w : E2) (hdγ : HasDerivAt γ v 0)
    (hframe : Function.Bijective
      ((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).smulRight v +
        (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).smulRight w)) :
    ∃ d : OpenPartialHomeomorph E2 E2,
      γ 0 ∈ d.source ∧ d (γ 0) = 0 ∧
      (∀ z, d.symm z = γ (z 1) + z 0 • w) ∧
      (∀ z ∈ d.target, z 1 ∈ I) ∧
      ContDiffOn ℝ ∞ d d.source ∧ ContDiffOn ℝ ∞ d.symm d.target ∧
      (∀ z ∈ d.source, Function.Bijective (fderiv ℝ d z)) ∧
      (∀ z ∈ d.target, Function.Bijective (fderiv ℝ d.symm z)) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Ioo (-ε) ε,
        γ t ∈ d.source ∧ d (γ t) = t • coordinateVector 2 1 := by
  let π₀ := EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)
  let π₁ := EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)
  let Φ : E2 → E2 := fun z => γ (z 1) + z 0 • w
  let U : Set E2 := π₁ ⁻¹' I
  have hU : IsOpen U := hI.preimage π₁.continuous
  have hzU : (0 : E2) ∈ U := by simpa [U,π₁] using hzero
  have hΦ : ContDiffOn ℝ ∞ Φ U :=
    (hγ.comp π₁.contDiff.contDiffOn (fun _ hz => hz)).add
      (π₀.contDiff.contDiffOn.smul contDiffOn_const)
  let D : E2 →L[ℝ] E2 := π₁.smulRight v + π₀.smulRight w
  have hΦd : HasFDerivAt Φ D 0 := by
    have hd : HasFDerivAt (γ ∘ π₁) (π₁.smulRight v) (0 : E2) := by
      have hh := hdγ.hasFDerivAt.comp (0 : E2) π₁.hasFDerivAt
      have he : (ContinuousLinearMap.toSpanSingleton ℝ v).comp π₁ = π₁.smulRight v := by
        ext z
        rfl
      rwa [he] at hh
    exact hd.add (π₀.hasFDerivAt.smul_const w)
  obtain ⟨e,heq,he0,heU,he,hi,her,hir⟩ :=
    smooth_local_diffeomorphism_of_regular_map Φ U hU hΦ 0 hzU
      (by rw [hΦd.fderiv]; exact hframe)
  have heγ (t : ℝ) : e (t • coordinateVector 2 1) = γ t := by
    rw [heq]
    simp [Φ,coordinateVector,EuclideanSpace.single]
  have hezero : e 0 = γ 0 := by simpa only [zero_smul] using heγ 0
  refine ⟨e.symm,hezero ▸ e.map_source he0,?_,?_,?_,hi,he,hir,her,?_⟩
  · rw [← hezero,e.left_inv he0]
  · intro z
    change e z = _
    rw [heq]
  · intro z hz
    exact heU hz
  · let line : ℝ →L[ℝ] E2 := ContinuousLinearMap.toSpanSingleton ℝ (coordinateVector 2 1)
    have hline0 : line ⁻¹' e.source ∈ 𝓝 (0 : ℝ) :=
      line.continuous.continuousAt.preimage_mem_nhds (by simpa using e.open_source.mem_nhds he0)
    obtain ⟨ε,hε,hεline⟩ := Metric.mem_nhds_iff.mp hline0
    refine ⟨ε,hε,?_⟩
    intro t ht
    have htline : t • coordinateVector 2 1 ∈ e.source := by
      apply hεline
      simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using abs_lt.mpr ht
    refine ⟨(heγ t) ▸ e.map_source htline,?_⟩
    rw [← heγ t,e.left_inv htline]

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
