import B1BoundaryH2RadiusIteration_v474
import B1BoundaryHkStep_v474
import B1BoundaryDifferentiatedSourceWkp_v474
import B1BoundaryCutoffSourceWkp_v474
import B1PrincipalCompletedWeak_v474
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

/-- Arbitrary finite boundary regularity, with a fixed target radius strictly
inside the original radius. Tangential traces are constructed at each step. -/
theorem native_boundary_Wkp_radius_v474
    (m : ℕ) (R q : ℝ) (hq : 0<q) (hqR : q<R) (u : E2 → ℝ)
    (hs : ContDiffOn ℝ ∞ u (halfDisc R))
    (h0 : H10On (halfDisc R) u (planarGradient u))
    (B : SmoothEllipticBilinearForm 2 univ) (S : E2 → ℝ)
    (hS : MemWkp m 2 S (halfDisc R))
    (A : DeGiorgi.EllipticCoeff 2 (halfDisc R))
    (hAB : ∀ x∈halfDisc R, A.a x=B.a x)
    (hweak : ∀ phi : E2 → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ halfDisc R →
      (∫ x in halfDisc R, inner ℝ (matrixAction (B.a x) (planarGradient u x))
        (planarGradient phi x)-S x*phi x)=0) :
    MemWkp (m+2) 2 u (halfDisc q) := by
  induction m generalizing R q u S with
  | zero =>
      exact (native_boundary_H2_radius_v474 R q hq hqR u hs h0 B S
        (native_compact_principal_flux_L2_v468 R B _ h0.1.2.2) hS.memLp hweak).2.1
  | succ m ih =>
      let r : ℝ := (q+R)/2
      have hr : 0<r := by dsimp [r]; linarith
      have hqr : q<r := by dsimp [r]; linarith
      have hrR : r<R := by dsimp [r]; linarith
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
      have huHigh := ih R r hr hrR u hs h0 S hS.le_succ A hAB hweak
      let Ar := A.restrict hsub
      have hABr : ∀ x∈halfDisc r, Ar.a x=B.a x := fun x hx => hAB x (hsub hx)
      have hSr : MemWkp (m+1) 2 S (halfDisc r) := hS.mono_set (by norm_num) hU hsub
      have hur := h1_restrict_subset _ _ hsub u (planarGradient u) h0.1
      have hweaker : ∀ phi : E2 → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
          tsupport phi ⊆ halfDisc r →
          (∫ x in halfDisc r, inner ℝ (matrixAction (B.a x) (planarGradient u x))
            (planarGradient phi x)-S x*phi x)=0 := by
        intro phi hp hc ht
        have hh := hweak phi hp hc (ht.trans hsub)
        have hz : ∀ x, x∉halfDisc r → inner ℝ
            (matrixAction (B.a x) (planarGradient u x)) (planarGradient phi x)-S x*phi x=0 := by
          intro x hx
          have hx' : x∉tsupport phi := fun hh => hx (ht hh)
          rw [QuasilinearLocalization.Helpers.gradient_zero_off_tsupport phi hx',
            image_eq_zero_of_notMem_tsupport hx']
          simp
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz]
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun x hx => hz x (fun hv => hx (hsub hv)))] at hh
        exact hh
      obtain ⟨f,hfm,hgrad,hfd⟩ := native_boundary_differentiated_source_Wkp_v474 r m
        (halfDisc r) hU hUc u _ hur (hs.mono hsub) (fun x hx => rfl) S Ar B hABr huHigh hSr
        (native_principal_completed_weak_v474 _ hU B.a S u _ hur hweaker Ar hABr hSr.memLp) 0
      have hgs : ContDiffOn ℝ ∞ (fun x => planarGradient u x 0) (halfDisc r) := by
        have he : (fun x => planarGradient u x 0)=fun x => fderiv ℝ u x (coordinateVector 2 0) := by
          funext x
          exact QuasilinearLocalization.Helpers.gradient_apply u x 0
        rw [he]
        exact ((hs.mono hsub).fderiv_of_isOpen hU (m:=∞) (by simp)).clm_apply contDiffOn_const
      have hcutball : Metric.closedBall (0:E2) q ⊆ Metric.ball 0 r := by
        intro x hx
        exact Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hx) hqr)
      obtain ⟨chi,hchi,hchic,hchione,hchisub,hchirange⟩ :=
        DifferentialGeometry.Analysis.exists_bump_compact (isCompact_closedBall (0:E2) q)
          Metric.isOpen_ball hcutball
      obtain ⟨df,hdf⟩ := (native_boundary_H2_radius_v474 R r hr hrR u hs h0 B S
        (native_compact_principal_flux_L2_v468 R B _ h0.1.2.2) hS.memLp hweak).1
      have htrace := native_tangent_local_zero_trace_v468 R r hr hrR u hs df hdf
        chi hchi hchic hchisub
      let v : E2 → ℝ := fun x => chi x*planarGradient u x 0
      have hvs : ContDiffOn ℝ ∞ v (halfDisc r) := hchi.contDiffOn.mul hgs
      have hactualgrad := native_smooth_gradient_ae_v468 _ hU v v _ htrace.1 hvs EventuallyEq.rfl
      have hv0 : H10On (halfDisc r) v (planarGradient v) :=
        native_h10_congr_ae_v468 _ v v _ _ htrace EventuallyEq.rfl hactualgrad
      have htm := native_smooth_partial_memWkp_v468 _ hU u (hs.mono hsub) (m+1) huHigh 0
      have hsource := native_boundary_classical_source_Wkp_v474 r m _ hgs B f hfm
        (fun phi hp hc ht => (hfd phi hp hc ht).2)
      have hcutSource := native_boundary_cutoff_source_Wkp_v474 r m _ hgs htm B hsource chi hchi
      have hvm := ih r q hq hqr v hvs hv0 _ hcutSource Ar hABr
        (fun phi hp hc ht => native_classical_principal_weak_v468 r v hvs B phi hp hc ht)
      have ht : MemWkp (m+2) 2 (fun x => planarGradient u x 0) (halfDisc q) := by
        apply (MemWkp_congr_ae (by norm_num) hQ _).mp hvm
        filter_upwards [ae_restrict_mem hQ.measurableSet] with x hx
        dsimp [v]
        rw [hchione.self_of_nhdsSet (Metric.ball_subset_closedBall hx.1)]
        simp
      have hhq := huHigh.mono_set (by norm_num) hQ hqsub
      have hclassSource := native_boundary_classical_source_Wkp_v474 R (m+1) u hs B S hS hweak
      have hsourceq := hclassSource.mono_set (by norm_num) hQ (hqsub.trans hsub)
      exact native_boundary_full_Hk_step_v474 q (m+1) u (hs.mono (hqsub.trans hsub)) hhq ht B _
        hsourceq (fun x hx => add_neg_cancel _)

end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.native_boundary_Wkp_radius_v474
