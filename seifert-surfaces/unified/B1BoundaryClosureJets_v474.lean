import B1ActualBoundaryC1Closure_v474
import B1ActualBoundaryTower_v474
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open DifferentialGeometry.Analysis.Sobolev.Euclidean
set_option maxHeartbeats 200000
set_option maxRecDepth 1500
set_option backward.isDefEq.respectTransparency false
theorem native_halfdisc_closure_v474 (R : ℝ) (hR : 0<R) :
    closure (halfDisc R) = closedHalfDisc R := by
  letI : IsBoundedSMul ℝ E2 := NormedSpace.toIsBoundedSMul
  letI : ContinuousSMul ℝ E2 := IsBoundedSMul.continuousSMul
  have hc : Convex ℝ (closedHalfDisc R) :=
    (convex_closedBall (0:E2) R).inter
      (convex_halfSpace_ge (f := fun x : E2 => x 1) ⟨by intros; rfl,by intros; rfl⟩ 0)
  have hint : interior (closedHalfDisc R) = halfDisc R := by
    change interior (Metric.closedBall (0:E2) R ∩ {x : E2 | 0≤x 1}) = _
    rw [interior_inter,interior_closedBall _ hR.ne',interior_halfSpace]
    rfl
  have hne : (interior (closedHalfDisc R)).Nonempty := by
    change (interior (closedHalfDisc R)).Nonempty
    rw [hint]
    refine ⟨(R/2) • coordinateVector 2 1,?_,?_⟩
    · apply Metric.mem_ball.mpr
      rw [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (half_pos hR)]
      have hn : ‖coordinateVector 2 (1:Fin 2)‖ = 1 := by simp [coordinateVector]
      rw [hn,mul_one]
      linarith
    · simpa [coordinateVector] using half_pos hR
  have hclosed : IsClosed (closedHalfDisc R) := Metric.isClosed_closedBall.inter
    (isClosed_le continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)
  rw [←hint,hc.closure_interior_eq_closure_of_nonempty_interior hne,hclosed.closure_eq]

theorem native_halfdisc_uniqueDiff_v474 (R : ℝ) (hR : 0<R) :
  UniqueDiffOn ℝ (closedHalfDisc R) := by
  apply uniqueDiffOn_convex
    ((convex_closedBall (0:E2) R).inter
      (convex_halfSpace_ge (f:=fun x : E2 => x 1) ⟨by intros; rfl,by intros; rfl⟩ 0))
  have hint : interior (closedHalfDisc R)=halfDisc R := by
    change interior (Metric.closedBall (0:E2) R ∩ {x : E2 | 0≤x 1}) = _
    rw [interior_inter,interior_closedBall _ hR.ne',interior_halfSpace]
    rfl
  change (interior (closedHalfDisc R)).Nonempty
  rw [hint]
  refine ⟨(R/2) • coordinateVector 2 1,?_,?_⟩
  · apply Metric.mem_ball.mpr
    rw [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (half_pos hR)]
    have hn : ‖coordinateVector 2 (1:Fin 2)‖=1 := by simp [coordinateVector]
    rw [hn,mul_one]
    linarith
  · simpa [coordinateVector] using half_pos hR

theorem native_halfdisc_derivative_closure_v474 (R : ℝ) (hR : 0<R) (u : E2 → ℝ)
    (hs : ContDiffOn ℝ ∞ u (halfDisc R))
    (hc : ContinuousOn u (closedHalfDisc R))
    (G : Fin 2 → E2 → ℝ) (hG : ∀ i, Continuous (G i))
    (heq : ∀ i, EqOn (G i) (fun x => planarGradient u x i) (halfDisc R)) :
    ∀ x, HasFDerivWithinAt u
      (G 0 x • (EuclideanSpace.proj (𝕜:=ℝ) (0:Fin 2)) +
        G 1 x • (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2))) (closedHalfDisc R) x := by
  let L : E2 → (E2 →L[ℝ] ℝ) := fun x =>
    G 0 x • (EuclideanSpace.proj (𝕜:=ℝ) (0:Fin 2)) +
      G 1 x • (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2))
  have hL : Continuous L := ((hG 0).smul continuous_const).add
    ((hG 1).smul continuous_const)
  have hL_apply (x : E2) (i : Fin 2) : L x (coordinateVector 2 i)=G i x := by
    fin_cases i <;> simp [L,coordinateVector]
  have hd (x : E2) (hx : x∈halfDisc R) (i : Fin 2) :
      fderiv ℝ u x (coordinateVector 2 i)=G i x :=
    (QuasilinearLocalization.Helpers.gradient_apply u x i).symm.trans (heq i hx).symm
  have hdeq (x : E2) (hx : x∈halfDisc R) : fderiv ℝ u x=L x := by
    apply ContinuousLinearMap.ext
    intro v
    have hv : v=v 0 • coordinateVector 2 0+v 1 • coordinateVector 2 1 := by
      ext i
      fin_cases i <;> simp [coordinateVector]
    rw [hv,map_add,map_smul,map_smul,map_add,map_smul,map_smul,
      hd x hx 0,hd x hx 1,hL_apply,hL_apply]
  have hU : IsOpen (halfDisc R) := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)
  have hconv : Convex ℝ (halfDisc R) := (convex_ball (0:E2) R).inter
    (convex_halfSpace_gt (f:=fun x : E2 => x 1) ⟨by intros; rfl,by intros; rfl⟩ 0)
  have hclosure := native_halfdisc_closure_v474 R hR
  have hcont : ∀ y ∈ closure (halfDisc R), ContinuousWithinAt u (halfDisc R) y := by
    intro y hy
    apply (hc y (hclosure ▸ hy)).mono
    intro z hz
    exact ⟨Metric.ball_subset_closedBall hz.1,hz.2.le⟩
  have hderiv (x : E2) : HasFDerivWithinAt u (L x) (closedHalfDisc R) x := by
    rw [←hclosure]
    apply hasFDerivWithinAt_closure_of_tendsto_fderiv
      (hs.differentiableOn (by simp)) hconv hU hcont
    have hev : (fun y => fderiv ℝ u y)=ᶠ[𝓝[halfDisc R] x] L := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact hdeq y hy
    exact hL.continuousAt.continuousWithinAt.congr' hev.symm
  exact hderiv

private def coordinateJet_v474 : List (Fin 2) → (E2 → ℝ) → E2 → ℝ
  | [], u => u
  | i::l, u => fun x => planarGradient (coordinateJet_v474 l u) x i

private theorem coordinateJet_smooth_v474 (R : ℝ) (u : E2 → ℝ)
    (hs : ContDiffOn ℝ ∞ u (halfDisc R)) (l : List (Fin 2)) :
    ContDiffOn ℝ ∞ (coordinateJet_v474 l u) (halfDisc R) := by
  have hU : IsOpen (halfDisc R) := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)
  induction l with
  | nil => exact hs
  | cons i l ih =>
      have he : coordinateJet_v474 (i::l) u =
          fun x => fderiv ℝ (coordinateJet_v474 l u) x (coordinateVector 2 i) := by
        funext x
        exact QuasilinearLocalization.Helpers.gradient_apply _ x i
      rw [he]
      exact (ih.fderiv_of_isOpen hU (m:=∞) (by simp)).clm_apply contDiffOn_const

private theorem coordinateJet_Wkp_v474 (R : ℝ) (u : E2 → ℝ)
    (hs : ContDiffOn ℝ ∞ u (halfDisc R)) (l : List (Fin 2)) (m : ℕ)
    (hu : MemWkp (m+l.length) 2 u (halfDisc R)) :
    MemWkp m 2 (coordinateJet_v474 l u) (halfDisc R) := by
  have hU : IsOpen (halfDisc R) := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)
  induction l generalizing m with
  | nil => simpa only [coordinateJet_v474,List.length_nil,Nat.add_zero] using hu
  | cons i l ih =>
      have horder : m+(i::l).length = (m+1)+l.length := by simp; omega
      have hh := ih (m+1) (horder ▸ hu)
      exact native_smooth_partial_memWkp_v468 _ hU _ (coordinateJet_smooth_v474 R u hs l) m hh i

/-- All native Sobolev orders on one half-disc give literal smoothness on
a fixed closed smaller half-disc. Every boundary jet is constructed by
Morrey; no boundary regularity is supplied as a premise. -/
theorem native_halfdisc_smooth_closure_v474 (R : ℝ) (hR : 0<R) (u : E2 → ℝ)
    (hs : ContDiffOn ℝ ∞ u (halfDisc R))
    (hc : ContinuousOn u (closedHalfDisc R))
    (hu : ∀ m : ℕ, MemWkp m 2 u (halfDisc R)) :
    ContDiffOn ℝ ∞ u (closedHalfDisc (R/4)) := by
  have hq : 0<R/4 := by positivity
  have hsub : halfDisc (R/4) ⊆ halfDisc R :=
    fun x hx => ⟨Metric.ball_subset_ball (by linarith : R/4≤R) hx.1,hx.2⟩
  have hclosedsub : closedHalfDisc (R/4) ⊆ closedHalfDisc R :=
    fun x hx => ⟨Metric.closedBall_subset_closedBall (by linarith : R/4≤R) hx.1,hx.2⟩
  have hU : IsOpen (halfDisc (R/4)) := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)
  have hex (l : List (Fin 2)) : ∃ G : E2 → ℝ, Continuous G ∧
      EqOn G (coordinateJet_v474 l u) (halfDisc (R/4)) :=
    native_halfdisc_H2_continuous_extension_v468 R hR _ (coordinateJet_smooth_v474 R u hs l)
      (coordinateJet_Wkp_v474 R u hs l 2 (hu _))
  choose G hG heq using hex
  have hGs (l : List (Fin 2)) : ContDiffOn ℝ ∞ (G l) (halfDisc (R/4)) :=
    ((coordinateJet_smooth_v474 R u hs l).mono hsub).congr (fun x hx => heq l hx)
  have hgradient (l : List (Fin 2)) (i : Fin 2) :
      EqOn (G (i::l)) (fun x => planarGradient (G l) x i) (halfDisc (R/4)) := by
    intro x hx
    rw [heq (i::l) hx]
    change planarGradient (coordinateJet_v474 l u) x i=planarGradient (G l) x i
    simp only [QuasilinearLocalization.Helpers.gradient_apply]
    have hh : fderiv ℝ (G l) x = fderiv ℝ (coordinateJet_v474 l u) x :=
      ((heq l).eventuallyEq_of_mem (hU.mem_nhds hx)).fderiv_eq
    rw [hh]
  have hderiv (l : List (Fin 2)) (x : E2) : HasFDerivWithinAt (G l)
      (G (0::l) x • (EuclideanSpace.proj (𝕜:=ℝ) (0:Fin 2))+
        G (1::l) x • (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2))) (closedHalfDisc (R/4)) x :=
    native_halfdisc_derivative_closure_v474 (R/4) hq (G l) (hGs l) (hG l).continuousOn
      (fun i => G (i::l)) (fun i => hG (i::l)) (hgradient l) x
  have huniq := native_halfdisc_uniqueDiff_v474 (R/4) hq
  have htower : ∀ n : ℕ, ∀ l : List (Fin 2), ContDiffOn ℝ n (G l) (closedHalfDisc (R/4)) := by
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
  have heqClosed : EqOn (G []) u (closedHalfDisc (R/4)) := by
    rw [←native_halfdisc_closure_v474 (R/4) hq]
    apply (heq []).of_subset_closure
    · exact (hG []).continuousOn
    · rw [native_halfdisc_closure_v474 (R/4) hq]
      exact hc.mono hclosedsub
    · exact subset_closure
    · exact Subset.rfl
  exact hG0.congr (fun x hx => (heqClosed hx).symm)

end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.native_halfdisc_smooth_closure_v474
