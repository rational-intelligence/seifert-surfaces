import B1BoundaryClosureRadius_v474
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.HalfSpace
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.Closed
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
set_option maxHeartbeats 500000
set_option maxRecDepth 1500
set_option backward.isDefEq.respectTransparency false

theorem native_halfdisc_ambient_extension_v474 (R q : ℝ) (hqR : q<R)
    (u : E2 → ℝ) (hu : ContDiffOn ℝ ∞ u (closedHalfDisc R)) :
    ∃ G : E2 → ℝ, ContDiff ℝ ∞ G ∧ EqOn G u (closedHalfDisc q) := by
  let k : ℝ × ℝ → E2 := fun z => z.2 • coordinateVector 2 0+z.1 • coordinateVector 2 1
  let j : E2 → ℝ × ℝ := fun x => (x 1,x 0)
  have hk : ContDiff ℝ ∞ k :=
    (contDiff_snd.smul contDiff_const).add (contDiff_fst.smul contDiff_const)
  have hj : ContDiff ℝ ∞ j :=
    (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).contDiff.prodMk
      (EuclideanSpace.proj (𝕜:=ℝ) (0:Fin 2)).contDiff
  have hkj (x : E2) : k (j x)=x := by
    ext i
    fin_cases i <;> simp [k,j,coordinateVector]
  have hk1 (z : ℝ × ℝ) : k z 1=z.1 := by simp [k,coordinateVector]
  let H : Set E2 := {x : E2 | 0≤x 1}
  let V : Set (ℝ × ℝ) := k ⁻¹' Metric.ball 0 R
  have hV : IsOpen V := Metric.isOpen_ball.preimage hk.continuous
  have hread : ContDiffOn ℝ ∞ (u ∘ k) ((Ici 0 ×ˢ univ) ∩ V) := by
    apply hu.comp hk.contDiffOn
    intro z hz
    exact ⟨Metric.ball_subset_closedBall hz.2,by simpa only [hk1] using (mem_Ici.mp hz.1.1)⟩
  have hlocal (x : E2) (hx : x∈closedHalfDisc q) :
      ∃ U ∈ 𝓝 x, ∃ G : E2 → ℝ, ContDiffOn ℝ ∞ G U ∧
        ∀ y ∈ closedHalfDisc q, y∈U → G y=u y := by
    have hxV : j x∈V := by
      change k (j x)∈Metric.ball 0 R
      rw [hkj]
      exact Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hx.1) hqR)
    obtain ⟨F,hF,hFeq⟩ := hread.exists_contDiff_extension_Ici_prod_nhdsWithin hV hxV
    have ht : Tendsto j (𝓝[H] x) (𝓝[Ici (0:ℝ) ×ˢ (univ:Set ℝ)] (j x)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨hj.continuous.continuousAt.mono_left nhdsWithin_le_nhds,?_⟩
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact ⟨hy,mem_univ _⟩
    have he : (F ∘ j) =ᶠ[𝓝[H] x] u := by
      filter_upwards [hFeq.comp_tendsto ht] with y hy
      simpa only [Function.comp_apply,hkj] using hy
    obtain ⟨U,hU,hUeq⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp he
    refine ⟨U,hU,F ∘ j,(hF.comp hj).contDiffOn,?_⟩
    intro y hy hyU
    exact hUeq ⟨hyU,hy.2⟩
  have hclosed : IsClosed (closedHalfDisc q) := Metric.isClosed_closedBall.inter
    (isClosed_le continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)
  obtain ⟨G,hG,hGeq⟩ := DifferentialGeometry.Analysis.exists_contDiff_extension_of_local
    (f:=id) (g:=u) (K:=closedHalfDisc q) (by simpa only [image_id] using hclosed) hlocal
  exact ⟨G,hG,hGeq⟩

end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.native_halfdisc_ambient_extension_v474
