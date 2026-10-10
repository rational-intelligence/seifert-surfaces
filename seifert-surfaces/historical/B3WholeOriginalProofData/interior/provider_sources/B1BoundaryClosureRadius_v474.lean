import B1BoundaryClosureJets_v474
import B1BoundaryMorreyRadius_v474
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open DifferentialGeometry.Analysis.Sobolev.Euclidean
set_option maxHeartbeats 500000
set_option maxRecDepth 1500
set_option backward.isDefEq.respectTransparency false
private def coordinateJet_radius_v474 : List (Fin 2) → (E2 → ℝ) → E2 → ℝ
  | [], u => u
  | i::l, u => fun x => planarGradient (coordinateJet_radius_v474 l u) x i

private theorem coordinateJet_smooth_radius_v474 (R : ℝ) (u : E2 → ℝ)
    (hs : ContDiffOn ℝ ∞ u (halfDisc R)) (l : List (Fin 2)) :
    ContDiffOn ℝ ∞ (coordinateJet_radius_v474 l u) (halfDisc R) := by
  have hU : IsOpen (halfDisc R) := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)
  induction l with
  | nil => exact hs
  | cons i l ih =>
      have he : coordinateJet_radius_v474 (i::l) u =
          fun x => fderiv ℝ (coordinateJet_radius_v474 l u) x (coordinateVector 2 i) := by
        funext x
        exact QuasilinearLocalization.Helpers.gradient_apply _ x i
      rw [he]
      exact (ih.fderiv_of_isOpen hU (m:=∞) (by simp)).clm_apply contDiffOn_const

private theorem coordinateJet_Wkp_radius_v474 (R : ℝ) (u : E2 → ℝ)
    (hs : ContDiffOn ℝ ∞ u (halfDisc R)) (l : List (Fin 2)) (m : ℕ)
    (hu : MemWkp (m+l.length) 2 u (halfDisc R)) :
    MemWkp m 2 (coordinateJet_radius_v474 l u) (halfDisc R) := by
  have hU : IsOpen (halfDisc R) := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)
  induction l generalizing m with
  | nil => simpa only [coordinateJet_radius_v474,List.length_nil,Nat.add_zero] using hu
  | cons i l ih =>
      have horder : m+(i::l).length = (m+1)+l.length := by simp; omega
      have hh := ih (m+1) (horder ▸ hu)
      exact native_smooth_partial_memWkp_v468 _ hU _ (coordinateJet_smooth_radius_v474 R u hs l) m hh i

/-- All native Sobolev orders on one half-disc give literal smoothness on
a fixed closed smaller half-disc. Every boundary jet is constructed by
Morrey; no boundary regularity is supplied as a premise. -/
theorem native_halfdisc_smooth_closure_radius_v474 (R q : ℝ) (hq : 0<q) (hqR : q<R) (u : E2 → ℝ)
    (hs : ContDiffOn ℝ ∞ u (halfDisc R))
    (hc : ContinuousOn u (closedHalfDisc R))
    (hu : ∀ m : ℕ, MemWkp m 2 u (halfDisc R)) :
    ContDiffOn ℝ ∞ u (closedHalfDisc q) := by
  have hR : 0<R := hq.trans hqR
  have hsub : halfDisc q ⊆ halfDisc R :=
    fun x hx => ⟨Metric.ball_subset_ball hqR.le hx.1,hx.2⟩
  have hclosedsub : closedHalfDisc q ⊆ closedHalfDisc R :=
    fun x hx => ⟨Metric.closedBall_subset_closedBall hqR.le hx.1,hx.2⟩
  have hU : IsOpen (halfDisc q) := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)
  have hex (l : List (Fin 2)) : ∃ G : E2 → ℝ, Continuous G ∧
      EqOn G (coordinateJet_radius_v474 l u) (halfDisc q) :=
    native_halfdisc_H2_continuous_radius_v474 R q hq hqR _ (coordinateJet_smooth_radius_v474 R u hs l)
      (coordinateJet_Wkp_radius_v474 R u hs l 2 (hu _))
  choose G hG heq using hex
  have hGs (l : List (Fin 2)) : ContDiffOn ℝ ∞ (G l) (halfDisc q) :=
    ((coordinateJet_smooth_radius_v474 R u hs l).mono hsub).congr (fun x hx => heq l hx)
  have hgradient (l : List (Fin 2)) (i : Fin 2) :
      EqOn (G (i::l)) (fun x => planarGradient (G l) x i) (halfDisc q) := by
    intro x hx
    rw [heq (i::l) hx]
    change planarGradient (coordinateJet_radius_v474 l u) x i=planarGradient (G l) x i
    simp only [QuasilinearLocalization.Helpers.gradient_apply]
    have hh : fderiv ℝ (G l) x = fderiv ℝ (coordinateJet_radius_v474 l u) x :=
      ((heq l).eventuallyEq_of_mem (hU.mem_nhds hx)).fderiv_eq
    rw [hh]
  have hderiv (l : List (Fin 2)) (x : E2) : HasFDerivWithinAt (G l)
      (G (0::l) x • (EuclideanSpace.proj (𝕜:=ℝ) (0:Fin 2))+
        G (1::l) x • (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2))) (closedHalfDisc q) x :=
    native_halfdisc_derivative_closure_v474 q hq (G l) (hGs l) (hG l).continuousOn
      (fun i => G (i::l)) (fun i => hG (i::l)) (hgradient l) x
  have huniq := native_halfdisc_uniqueDiff_v474 q hq
  have htower : ∀ n : ℕ, ∀ l : List (Fin 2), ContDiffOn ℝ n (G l) (closedHalfDisc q) := by
    intro n
    induction n with
    | zero => exact fun l => contDiffOn_zero.mpr (hG l).continuousOn
    | succ n ih =>
      intro l
      rw [show ((n+1:ℕ):ℕ∞ω)=(n:ℕ∞ω)+1 by simp,
        contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn huniq]
      refine ⟨by simp, (fun x => G (0::l) x • (EuclideanSpace.proj (𝕜:=ℝ) (0:Fin 2))+
        G (1::l) x • (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2))), ?_,fun x hx => hderiv l x⟩
      exact ((ih (0::l)).smul contDiffOn_const).add ((ih (1::l)).smul contDiffOn_const)
  have hG0 := contDiffOn_infty.mpr (fun n => htower n [])
  have heqClosed : EqOn (G []) u (closedHalfDisc q) := by
    rw [←native_halfdisc_closure_v474 q hq]
    apply (heq []).of_subset_closure
    · exact (hG []).continuousOn
    · rw [native_halfdisc_closure_v474 q hq]
      exact hc.mono hclosedsub
    · exact subset_closure
    · exact Subset.rfl
  exact hG0.congr (fun x hx => (heqClosed hx).symm)


end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.native_halfdisc_smooth_closure_radius_v474
