import B1ActualBoundaryH2FullRadius_v474
import NativeH10CutoffLocalization
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Density
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open ChartMetricProvider.Variational.DirectWeak.BoundaryContinuation
set_option maxHeartbeats 1000000
set_option maxRecDepth 1500
set_option backward.isDefEq.respectTransparency false

/-- The same positive classical Dirichlet solution constructed from the
original D,s,W data has all finite Sobolev orders on each fixed smaller
half-disc. The boundary trace, positivity and native equation are retained. -/
theorem actual_positive_boundary_sobolev_full_radius_v474
    (D : B1OriginalData (g:=g) J) (s : Circle) (W : CollarWindow D s) :
    ∃ R : ℝ, 0<R ∧ R<W.R ∧ ∃ h : E2 → ℝ,
      ContinuousOn h (closedHalfDisc R) ∧
      (∀ x ∈ frontier (halfDisc R), h x=1) ∧
      (∀ x ∈ closedHalfDisc R, (1/2 : ℝ)≤h x) ∧
      ContDiffOn ℝ ∞ h (halfDisc R) ∧
      H1On (halfDisc R) h (planarGradient h) ∧
      H10On (halfDisc R) (fun x => h x-1) (planarGradient h) ∧
      WeakLinearEquationOn (halfDisc R) W.a W.b W.c h (planarGradient h) ∧
      (∀ x ∈ halfDisc R, classicalL W.a W.b W.c h x=0) ∧
      ∀ m : ℕ, ∀ q : ℝ, 0<q → q<R → MemWkp m 2 h (halfDisc q) := by
  obtain ⟨R,hR,hRW,h,hhc,hfront,hpos,hs,h1,h0,heq,hcl,hH2⟩ :=
    actual_positive_boundary_H2_full_radius_v474 D s W
  have hP : IsCompact (closedHalfDisc R) := (isCompact_closedBall (0:E2) R).inter_right
    (isClosed_le continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)
  obtain ⟨B,hBa⟩ := actual_closed_halfdisc_smooth_elliptic_extension_v468 D s W
    (closedHalfDisc R) hP (fun x hx => ⟨Metric.closedBall_subset_closedBall hRW.le hx.1,hx.2⟩)
  have htower : ∀ m : ℕ, ∀ q : ℝ, 0<q → q<R → MemWkp (m+2) 2 h (halfDisc q) := by
    intro m
    induction m with
    | zero => exact fun q hq hqR => hH2 q hq hqR
    | succ m ih =>
      intro q hq hqR
      let r : ℝ := (q+R)/2
      have hr : 0<r := by dsimp [r]; linarith
      have hqr : q<r := by dsimp [r]; linarith
      have hrR4 : r<R := by dsimp [r]; linarith
      have hrR : r<R := by linarith
      have hsub : halfDisc r ⊆ halfDisc R :=
        fun x hx => ⟨Metric.ball_subset_ball hrR.le hx.1,hx.2⟩
      have hqsub : halfDisc q ⊆ halfDisc r :=
        fun x hx => ⟨Metric.ball_subset_ball hqr.le hx.1,hx.2⟩
      have hU : IsOpen (halfDisc r) := Metric.isOpen_ball.inter
        (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)
      have hQ : IsOpen (halfDisc q) := Metric.isOpen_ball.inter
        (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)
      have hUc : IsCompact (closure (halfDisc r)) := (isCompact_closedBall (0:E2) r).of_isClosed_subset
        isClosed_closure (closure_minimal (fun x hx => Metric.ball_subset_closedBall hx.1)
          Metric.isClosed_closedBall)
      have hUW : closure (halfDisc r) ⊆ closedHalfDisc W.R := by
        apply closure_minimal
        · intro x hx
          exact ⟨Metric.ball_subset_closedBall (Metric.ball_subset_ball (hrR.trans hRW).le hx.1),hx.2.le⟩
        · exact Metric.isClosed_closedBall.inter
            (isClosed_le continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)
      have hhigh := ih r hr hrR4
      let S : E2 → ℝ := fun x => inner ℝ (W.b x) (planarGradient h x)+W.c x*h x
      have hS := actual_halfdisc_boundary_lower_source_tower_v468 D s W R hRW h _ h1
        (halfDisc r) hU hUc hsub hUW (m+1) hhigh
      have hrEq := native_full_linear_restrict_v468 _ _ hsub W.a W.b W.c h _ h1 heq
      have hweak : ∀ phi : E2 → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
          tsupport phi ⊆ halfDisc r →
          (∫ x in halfDisc r, inner ℝ (matrixAction (B.a x) (planarGradient h x))
            (planarGradient phi x)-S x*phi x)=0 := by
        intro phi hp hc ht
        have hh := (hrEq.2 phi hp hc ht).2
        convert hh using 1
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
        rw [hBa x ⟨Metric.ball_subset_closedBall (hsub hx).1,(hsub hx).2.le⟩]
      have hsource := native_boundary_classical_source_Wkp_v474 r (m+1) h (hs.mono hsub) B S hS hweak
      let u : E2 → ℝ := fun x => h x-1
      have hus : ContDiffOn ℝ ∞ u (halfDisc r) := (hs.mono hsub).sub contDiffOn_const
      have huHigh : MemWkp (m+2) 2 u (halfDisc r) :=
        MemWkp.sub (by norm_num) hU hhigh (native_halfdisc_constant_Wkp_v474 r (m+2) 1)
      have hdsub : planarGradient u=planarGradient h := by
        ext x i
        simp only [u,QuasilinearLocalization.Helpers.gradient_apply,fderiv_sub_const]
      have hsourceu : MemWkp (m+1) 2 (fun x => -(∑ i : Fin 2, fderiv ℝ
          (fun y => matrixAction (B.a y) (planarGradient u y) i) x (coordinateVector 2 i)))
          (halfDisc r) := by rw [hdsub]; exact hsource
      have hcutball : Metric.closedBall (0:E2) q ⊆ Metric.ball 0 r := by
        intro x hx
        exact Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hx) hqr)
      obtain ⟨chi,hchi,hchic,hchione,hchisub,hchirange⟩ :=
        DifferentialGeometry.Analysis.exists_bump_compact (isCompact_closedBall (0:E2) q)
          Metric.isOpen_ball hcutball
      let v : E2 → ℝ := fun x => chi x*u x
      have hvS : ContDiffOn ℝ ∞ v (halfDisc r) := hchi.contDiffOn.mul hus
      have hv0a := h10_cutoff_localization (halfDisc R) (halfDisc r) hsub chi hchi hchic
        (fun x hx => ⟨hchisub hx.1,hx.2.2⟩) u (planarGradient h) h0
      have hvgrad := native_smooth_gradient_ae_v468 _ hU v v _ hv0a.1 hvS EventuallyEq.rfl
      have hv0 : H10On (halfDisc r) v (planarGradient v) :=
        native_h10_congr_ae_v468 _ v v _ _ hv0a EventuallyEq.rfl hvgrad
      have hcutSource := native_boundary_cutoff_source_Wkp_v474 r (m+1) u hus huHigh B hsourceu chi hchi
      obtain ⟨A,hAa⟩ := actual_halfdisc_elliptic_coeff_v468 D s W r (hrR.trans hRW)
      have hAB : ∀ x∈halfDisc r, A.a x=B.a x := by
        intro x hx
        exact (hAa x hx).trans (hBa x
          ⟨Metric.ball_subset_closedBall (hsub hx).1,(hsub hx).2.le⟩).symm
      have hvm := native_boundary_Wkp_radius_v474 (m+1) r q hq hqr v hvS hv0 B _ hcutSource A hAB
        (fun phi hp hc ht => native_classical_principal_weak_v468 r v hvS B phi hp hc ht)
      have huq : MemWkp (m+3) 2 u (halfDisc q) := by
        apply (MemWkp_congr_ae (by norm_num) hQ _).mp hvm
        filter_upwards [ae_restrict_mem hQ.measurableSet] with x hx
        dsimp [v]
        rw [hchione.self_of_nhdsSet (Metric.ball_subset_closedBall hx.1)]
        simp
      have hh := MemWkp.add (by norm_num) hQ huq (native_halfdisc_constant_Wkp_v474 q (m+3) 1)
      convert hh using 1
      funext x
      dsimp [u]
      ring
  refine ⟨R,hR,hRW,h,hhc,hfront,hpos,hs,h1,h0,heq,hcl,?_⟩
  intro m q hq hqR
  exact (htower m q hq hqR).le_of_le (by omega)

end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.actual_positive_boundary_sobolev_full_radius_v474
