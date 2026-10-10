import A5SmoothLocalDiffeomorphism
import A5SignedArcFromCoordinates

set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC CurvedDivergence

/-- A smooth regular curve and one transverse vector construct a genuine
smooth signed defining function on a ball. Exact zero-set coverage, embedded
arc regularity and compact test-parameter control are all conclusions. -/
theorem signed_arc_geometry_near_regular_curve
    (γ : ℝ → E2) (I : Set ℝ) (hI : IsOpen I) (hzero : (0 : ℝ) ∈ I)
    (hγ : ContDiffOn ℝ ∞ γ I) (v w : E2) (hdγ : HasDerivAt γ v 0)
    (hframe : Function.Bijective
      ((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).smulRight v +
        (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).smulRight w)) :
    ∃ r : ℝ, 0 < r ∧ ∃ left right : ℝ, left < 0 ∧ 0 < right ∧
      ∃ s : E2 → ℝ, SignedArcGeometry (Metric.ball (γ 0) r) s γ left right := by
  let π₀ := EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)
  let π₁ := EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)
  let Φ : E2 → E2 := fun z => γ (z 1) + z 0 • w
  let U : Set E2 := π₁ ⁻¹' I
  have hU : IsOpen U := hI.preimage π₁.continuous
  have hzU : (0 : E2) ∈ U := by simpa [U, π₁] using hzero
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
  have hΦrank : Function.Bijective (fderiv ℝ Φ 0) := by
    rw [hΦd.fderiv]
    exact hframe
  obtain ⟨e, heq, he0, _, he, hi, her, hir⟩ :=
    smooth_local_diffeomorphism_of_regular_map Φ U hU hΦ 0 hzU hΦrank
  have heγ (t : ℝ) : e (t • coordinateVector 2 1) = γ t := by
    rw [heq]
    simp [Φ, coordinateVector, EuclideanSpace.single]
  have hp : e 0 = γ 0 := by simpa only [zero_smul] using heγ 0
  let line : ℝ →L[ℝ] E2 := ContinuousLinearMap.toSpanSingleton ℝ (coordinateVector 2 1)
  have hline0 : line ⁻¹' e.source ∈ 𝓝 (0 : ℝ) :=
    line.continuous.continuousAt.preimage_mem_nhds (by simpa using e.open_source.mem_nhds he0)
  obtain ⟨ε, hε, hεline⟩ := Metric.mem_nhds_iff.mp hline0
  have hline (t : ℝ) (ht : t ∈ Ioo (-ε) ε) : t • coordinateVector 2 1 ∈ e.source := by
    apply hεline
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using abs_lt.mpr ht
  let V := e.target ∩ e.symm ⁻¹' (π₁ ⁻¹' Ioo (-ε) ε)
  have hV : IsOpen V := e.symm.continuousOn.isOpen_inter_preimage e.open_target
    (isOpen_Ioo.preimage π₁.continuous)
  have hpV : γ 0 ∈ V := by
    rw [← hp]
    refine ⟨e.map_source he0, ?_⟩
    change π₁ (e.symm (e 0)) ∈ Ioo (-ε) ε
    rw [e.left_inv he0, map_zero]
    exact ⟨neg_neg_of_pos hε, hε⟩
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hpV)
  refine ⟨r, hr, -ε, ε, neg_neg_of_pos hε, hε, (fun z => e.symm z 0), ?_⟩
  have hg := signed_arc_geometry_of_smooth_coordinates e he hi her hir
    (Metric.ball (γ 0) r) Metric.isOpen_ball (fun z hz => (hrV hz).1)
    (-ε) ε hline (fun z hz => (hrV hz).2)
  have hfun : (fun t => e (t • coordinateVector 2 1)) = γ := funext heγ
  rwa [hfun] at hg

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
