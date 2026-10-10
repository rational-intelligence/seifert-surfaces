import A7EuclideanStraighteningV464
import A7NativeExtensionV464
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Function Filter
open scoped Manifold ContDiff Topology
namespace SeifertSurfaces.OriginalEndpoints.A7Support
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC

universe u v
variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 2) M]
  [IsManifold (𝓡∂ 2) ∞ M]
  {N : Type v} [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold 𝓘(ℝ,E3) ∞ N]

/-- The native tangent frame parametrizes its actual range. -/
def rangeFrame {F : M → N} (x : M)
    (hinj : Function.Injective (mfderiv (𝓡∂ 2) 𝓘(ℝ,E3) F x)) :
    E2 ≃L[ℝ] LinearMap.range (mfderiv (𝓡∂ 2) 𝓘(ℝ,E3) F x).toLinearMap :=
  ((tangentSpaceCastModel (𝓡∂ 2) x).symm.trans
    (LinearEquiv.ofInjective (mfderiv (𝓡∂ 2) 𝓘(ℝ,E3) F x).toLinearMap hinj).toContinuousLinearEquiv)

theorem ambient_chart_straightening {F : M → N}
    (hF : ContMDiff (𝓡∂ 2) 𝓘(ℝ,E3) ∞ F) (x : M)
    (hinj : Function.Injective (mfderiv (𝓡∂ 2) 𝓘(ℝ,E3) F x))
    (h : AmbientMetric N) :
    ∃ n : TangentSpace 𝓘(ℝ,E3) (F x), n ≠ 0 ∧
      (∀ v ∈ LinearMap.range (mfderiv (𝓡∂ 2) 𝓘(ℝ,E3) F x).toLinearMap,
        h.inner (F x) v n = 0) ∧
    ∃ c : SmoothAmbientChart N, F x ∈ c.chart.source ∧
      ∀ᶠ z : E2 in 𝓝[range (𝓡∂ 2)] (extChartAt (𝓡∂ 2) x x),
        F ((extChartAt (𝓡∂ 2) x).symm z) ∈ c.chart.source ∧
        c.chart (F ((extChartAt (𝓡∂ 2) x).symm z)) =
          c.chart (F x) + (chartDifferential c (F x))
            (mfderiv (𝓡∂ 2) 𝓘(ℝ,E3) F x
              ((tangentSpaceCastModel (𝓡∂ 2) x).symm
                (z - extChartAt (𝓡∂ 2) x x))) := by
  let p := F x
  let d := extChartAtPartialDiffeomorph 𝓘(ℝ,E3) ∞ p
  let a := extChartAt (𝓡∂ 2) x x
  let D : E2 →L[ℝ] TangentSpace 𝓘(ℝ,E3) p :=
    (mfderiv (𝓡∂ 2) 𝓘(ℝ,E3) F x).comp
      (tangentSpaceCastModel (𝓡∂ 2) x).symm.toContinuousLinearMap
  have hD : Function.Injective D := hinj.comp (tangentSpaceCastModel (𝓡∂ 2) x).symm.injective
  obtain ⟨n,hn,hort,A,hA⟩ := normal_completion D hD (h.inner p) (h.pos p)
  have hnr : n ≠ (0 : TangentSpace 𝓘(ℝ,E3) p) := hn
  have hort' : ∀ v ∈ LinearMap.range (mfderiv (𝓡∂ 2) 𝓘(ℝ,E3) F x).toLinearMap,
      h.inner p v n = 0 := by
    rintro v ⟨w,rfl⟩
    have hv := hort ((tangentSpaceCastModel (𝓡∂ 2) x) w)
    change h.inner p
      (mfderiv (𝓡∂ 2) 𝓘(ℝ,E3) F x
        ((tangentSpaceCastModel (𝓡∂ 2) x).symm ((tangentSpaceCastModel (𝓡∂ 2) x) w))) n = 0 at hv
    rw [ContinuousLinearEquiv.symm_apply_apply] at hv
    exact hv
  obtain ⟨g,hg,hge,hgd⟩ := native_coordinate_extension hF x
  let L : E2 →L[ℝ] E3 := (tangentSpaceCastModel 𝓘(ℝ,E3) p).toContinuousLinearMap.comp D
  let Ac : (E2 × ℝ) ≃L[ℝ] E3 := A.trans (tangentSpaceCastModel 𝓘(ℝ,E3) p)
  let nc := (tangentSpaceCastModel 𝓘(ℝ,E3) p) n
  have hAc (q) : Ac q = L q.1 + q.2 • nc := by
    simp only [Ac,ContinuousLinearEquiv.trans_apply,hA,map_add,map_smul,L,nc,
      ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe]
    rfl
  obtain ⟨β,hβp,hβ,hβi,hβfix,hβD,hβstraight⟩ :=
    euclidean_straightening hg a hgd nc Ac hAc
  have haR : a ∈ range (𝓡∂ 2) := mem_range_self _
  have hgp : g a = d p := by
    have he := hge.eq_of_nhdsWithin haR
    change g a = extChartAt 𝓘(ℝ,E3) p p
    simpa only [writtenInExtChartAt,Function.comp_apply,
      (extChartAt (𝓡∂ 2) x).left_inv (mem_extChartAt_source x)] using he
  have hdp : p ∈ d.source := mem_extChartAt_source p
  let c : SmoothAmbientChart N := {
    chart := d.toOpenPartialHomeomorph.trans β
    smooth := hβ.contMDiffOn.comp (d.contMDiffOn.mono inter_subset_left)
      (fun _ hz => hz.2)
    inverse_smooth := d.symm.contMDiffOn.comp (hβi.contMDiffOn.mono inter_subset_left)
      (fun _ hz => hz.2) }
  have hpc : p ∈ c.chart.source := by
    refine ⟨hdp,?_⟩
    change d p ∈ β.source
    rw [←hgp]
    exact hβp
  have hchartD : chartDifferential c p = (tangentSpaceCastModel 𝓘(ℝ,E3) p) := by
    have hbMD : MDifferentiableAt 𝓘(ℝ,E3) 𝓘(ℝ,E3) β (d p) := by
      rw [←hgp]
      exact hβD.differentiableAt.mdifferentiableAt
    have heD : mfderiv 𝓘(ℝ,E3) 𝓘(ℝ,E3) d p = ContinuousLinearMap.id ℝ E3 :=
      mfderiv_extChartAt_self
    have hbD : mfderiv 𝓘(ℝ,E3) 𝓘(ℝ,E3) β (d p) = ContinuousLinearMap.id ℝ E3 := by
      rw [mfderiv_eq_fderiv]
      rw [←hgp,hβD.fderiv]
      rfl
    unfold chartDifferential
    change (NormedSpace.fromTangentSpace (c.chart p)).toContinuousLinearMap.comp
      (mfderiv 𝓘(ℝ,E3) 𝓘(ℝ,E3) (β ∘ d) p) = _
    rw [mfderiv_comp p hbMD (d.mdifferentiableAt (by simp) hdp),heD,hbD]
    rfl
  refine ⟨n,hnr,hort',c,hpc,?_⟩
  have hzshift : Tendsto (fun z : E2 => z-a) (𝓝[range (𝓡∂ 2)] a) (𝓝 0) := by
    have ht := ((continuous_id : Continuous (fun z : E2 => z)).sub (continuous_const (y := a))).continuousAt
      (x := a)
    have ht' : Tendsto (fun z : E2 => z-a) (𝓝 a) (𝓝 0) := by
      convert ht.tendsto using 1 <;> first | rfl | simp only [Pi.sub_apply,id_eq,sub_self]
    exact ht'.mono_left nhdsWithin_le_nhds
  have hsource : ∀ᶠ z : E2 in 𝓝[range (𝓡∂ 2)] a,
      F ((extChartAt (𝓡∂ 2) x).symm z) ∈ d.source := by
    have ht := hF.continuous.continuousAt.comp_continuousWithinAt
      ((contMDiffWithinAt_extChartAt_symm_range (I := 𝓡∂ 2) (n := ∞) x
        (mem_extChartAt_target x)).continuousWithinAt)
    have hp0 : F ((extChartAt (𝓡∂ 2) x).symm a) = p := by
      rw [(extChartAt (𝓡∂ 2) x).left_inv (mem_extChartAt_source x)]
    have hn : d.source ∈ 𝓝 (F ((extChartAt (𝓡∂ 2) x).symm a)) := by
      rw [hp0]
      exact d.open_source.mem_nhds hdp
    exact ht.tendsto.eventually hn
  filter_upwards [hge,hzshift.eventually hβstraight,hsource] with z hz hb hs
  have hez : g z = d (F ((extChartAt (𝓡∂ 2) x).symm z)) := hz
  have hcancel : a+(z-a) = z := by abel
  have hbmem : d (F ((extChartAt (𝓡∂ 2) x).symm z)) ∈ β.source := by
    rw [←hez]
    simpa only [hcancel] using hb.1
  refine ⟨⟨hs,hbmem⟩,?_⟩
  change β (d (F ((extChartAt (𝓡∂ 2) x).symm z))) =
    β (d p) + chartDifferential c p (D (z-a))
  rw [hchartD,←hgp,hβfix]
  have hbb : β (g z) = g a + L (z-a) := by
    simpa only [hcancel,L,D] using hb.2
  rw [hez] at hbb
  exact hbb

end SeifertSurfaces.OriginalEndpoints.A7Support
