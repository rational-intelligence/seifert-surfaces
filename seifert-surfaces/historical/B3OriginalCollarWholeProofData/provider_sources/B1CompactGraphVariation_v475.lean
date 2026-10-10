import B1ActualGraphCalculus_v475

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped Manifold ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
universe v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Differentiation under the integral on a compact graph patch, with all
regularity and domination confined to an actual open time-space tube. -/
theorem native_compact_integral_variation_v475
    (A O : Set E2) (hA : IsCompact A) (hO : IsOpen O) (hAO : A ⊆ O)
    (Q : Set ℝ) (hQ : IsOpen Q) (h0 : (0 : ℝ) ∈ Q)
    (F : ℝ × E2 → ℝ) (hF : ContDiffOn ℝ 1 F (Q ×ˢ O)) :
    IntegrableOn (fun x => fderiv ℝ F (0,x) (1,0)) A ∧
    HasDerivAt (fun t => ∫ x in A, F (t,x))
      (∫ x in A, fderiv ℝ F (0,x) (1,0)) 0 := by
  let D := fun p : ℝ × E2 => fderiv ℝ F p (1,0)
  have hD : ContinuousOn D (Q ×ˢ O) :=
    (hF.continuousOn_fderiv_of_isOpen (hQ.prod hO) (by simp)).clm_apply continuousOn_const
  obtain ⟨r,hr,hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hQ.mem_nhds h0)
  have hcomp : IsCompact (Metric.closedBall (0 : ℝ) r ×ˢ A) :=
    (isCompact_closedBall (0 : ℝ) r).prod hA
  have hsub : Metric.closedBall (0 : ℝ) r ×ˢ A ⊆ Q ×ˢ O := prod_mono hball hAO
  obtain ⟨C,hC⟩ := hcomp.exists_bound_of_continuousOn (hD.mono hsub)
  have hmeas : ∀ᶠ t in 𝓝 (0 : ℝ),
      AEStronglyMeasurable (fun x => F (t,x)) (volume.restrict A) := by
    filter_upwards [hQ.mem_nhds h0] with t ht
    exact (hF.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun x hx => ⟨ht,hAO hx⟩)).aestronglyMeasurable hA.measurableSet
  have hint : IntegrableOn (fun x => F (0,x)) A :=
    (hF.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun x hx => ⟨h0,hAO hx⟩)).integrableOn_compact hA
  have hdm : AEStronglyMeasurable (fun x => D (0,x)) (volume.restrict A) :=
    (hD.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun x hx => ⟨h0,hAO hx⟩)).aestronglyMeasurable hA.measurableSet
  have hbound : ∀ᵐ x ∂volume.restrict A, ∀ t ∈ Metric.closedBall (0 : ℝ) r,
      ‖D (t,x)‖ ≤ C := by
    filter_upwards [ae_restrict_mem hA.measurableSet] with x hx t ht
    exact hC (t,x) ⟨ht,hx⟩
  have hboundint : IntegrableOn (fun _ : E2 => C) A :=
    continuousOn_const.integrableOn_compact hA
  have hdiff : ∀ᵐ x ∂volume.restrict A, ∀ t ∈ Metric.closedBall (0 : ℝ) r,
      HasDerivAt (fun τ => F (τ,x)) (D (t,x)) t := by
    filter_upwards [ae_restrict_mem hA.measurableSet] with x hx t ht
    have hf : DifferentiableAt ℝ F (t,x) :=
      (hF.contDiffAt ((hQ.prod hO).mem_nhds ⟨hball ht,hAO hx⟩)).differentiableAt (by simp)
    exact hf.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t x => F (t,x)) (F' := fun t x => D (t,x))
    (μ := volume.restrict A) (bound := fun _ => C)
    (Metric.closedBall_mem_nhds (0 : ℝ) hr) hmeas hint hdm hbound hboundint hdiff

/-- The exact graph-density integral has the exact source first variation on
any compact patch whose entire varied jet tube lies in the supplied metric. -/
theorem actual_compact_graph_density_variation_v475
    (D : B1OriginalData g J) (s : Circle) (W : CollarWindow D s)
    (A O : Set E2) (hA : IsCompact A) (hO : IsOpen O) (hAO : A ⊆ O)
    (Q : Set ℝ) (hQ : IsOpen Q) (h0 : (0 : ℝ) ∈ Q)
    (u φ : E2 → ℝ) (hu : ContDiffOn ℝ ∞ u O) (hφ : ContDiff ℝ ∞ φ)
    (hjets : ∀ t ∈ Q, ∀ x ∈ O,
      jetPoint (x,u x+t*φ x,planarGradient u x+t • planarGradient φ x) ∈ W.V) :
    IntegrableOn (fun x => inner ℝ (W.flux (x,u x,planarGradient u x)) (planarGradient φ x) -
      W.lower (x,u x,planarGradient u x) * φ x) A ∧
    HasDerivAt (fun t => ∫ x in A,
      W.density (x,u x+t*φ x,planarGradient u x+t • planarGradient φ x))
      (∫ x in A, inner ℝ (W.flux (x,u x,planarGradient u x)) (planarGradient φ x) -
        W.lower (x,u x,planarGradient u x) * φ x) 0 := by
  let F := fun p : ℝ × E2 =>
    W.density (p.2,u p.2+p.1*φ p.2,planarGradient u p.2+p.1 • planarGradient φ p.2)
  have hgrad : ContDiffOn ℝ ∞ (planarGradient u) O := by
    unfold planarGradient
    exact ContDiffOn.sum (fun i _ =>
      ((hu.fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const).smul_const _)
  have hgradφ : ContDiff ℝ ∞ (planarGradient φ) := by
    unfold planarGradient
    exact ContDiff.sum (fun i _ => (hφ.fderiv_right (by simp)).clm_apply contDiff_const |>.smul_const _)
  have huv : ContDiffOn ℝ ∞ (fun p : ℝ × E2 => u p.2) (Q ×ˢ O) :=
    hu.comp contDiffOn_snd (fun p hp => hp.2)
  have hgv : ContDiffOn ℝ ∞ (fun p : ℝ × E2 => planarGradient u p.2) (Q ×ˢ O) :=
    hgrad.comp contDiffOn_snd (fun p hp => hp.2)
  have hjet : ContDiffOn ℝ ∞ (fun p : ℝ × E2 =>
      (p.2,u p.2+p.1*φ p.2,planarGradient u p.2+p.1 • planarGradient φ p.2)) (Q ×ˢ O) :=
    contDiffOn_snd.prodMk
      ((huv.add (contDiffOn_fst.mul (hφ.comp contDiff_snd).contDiffOn)).prodMk
        (hgv.add (contDiffOn_fst.smul (hgradφ.comp contDiff_snd).contDiffOn)))
  have hF : ContDiffOn ℝ 1 F (Q ×ˢ O) :=
    ((actual_graph_jet_calculus_v475 D s W).1.comp hjet
      (fun p hp => hjets p.1 hp.1 p.2 hp.2)).of_le (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp)
  have heq (x : E2) (hx : x ∈ A) :
      fderiv ℝ F (0,x) (1,0) =
        inner ℝ (W.flux (x,u x,planarGradient u x)) (planarGradient φ x) -
          W.lower (x,u x,planarGradient u x) * φ x := by
    have hf : DifferentiableAt ℝ F (0,x) :=
      (hF.contDiffAt ((hQ.prod hO).mem_nhds ⟨h0,hAO hx⟩)).differentiableAt (by simp)
    have hd := hf.hasFDerivAt.comp_hasDerivAt 0
      ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const 0 x))
    have hv := actual_graph_density_variation_v475 D s W (x,u x,planarGradient u x)
      (by simpa using hjets 0 h0 x (hAO hx)) (φ x) (planarGradient φ x)
    exact hd.unique hv
  obtain ⟨hint,hd⟩ := native_compact_integral_variation_v475 A O hA hO hAO Q hQ h0 F hF
  have hae : (fun x => fderiv ℝ F (0,x) (1,0)) =ᵐ[volume.restrict A]
      (fun x => inner ℝ (W.flux (x,u x,planarGradient u x)) (planarGradient φ x) -
        W.lower (x,u x,planarGradient u x) * φ x) := by
    filter_upwards [ae_restrict_mem hA.measurableSet] with x hx
    exact heq x hx
  exact ⟨hint.congr hae,hd.congr_deriv (integral_congr_ae hae)⟩

#print axioms native_compact_integral_variation_v475
#print axioms actual_compact_graph_density_variation_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
