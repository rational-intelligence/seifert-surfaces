import B1InteriorGraphCalculus_v475
import B1CompactGraphVariation_v475
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped Manifold ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
/-- The exact graph-density integral has the exact source first variation on
any compact patch whose entire varied jet tube lies in the supplied metric. -/
theorem native_interior_compact_graph_density_variation_v475
    (V : Set E3) (hV : IsOpen V) (H : CoordinateMetric V)
    (A O : Set E2) (hA : IsCompact A) (hO : IsOpen O) (hAO : A ⊆ O)
    (Q : Set ℝ) (hQ : IsOpen Q) (h0 : (0 : ℝ) ∈ Q)
    (u φ : E2 → ℝ) (hu : ContDiffOn ℝ ∞ u O) (hφ : ContDiff ℝ ∞ φ)
    (hjets : ∀ t ∈ Q, ∀ x ∈ O,
      jetPoint (x,u x+t*φ x,planarGradient u x+t • planarGradient φ x) ∈ V) :
    IntegrableOn (fun x => inner ℝ ((native_interior_graph_flux_v475 H) (x,u x,planarGradient u x)) (planarGradient φ x) -
      (native_interior_graph_lower_v475 H) (x,u x,planarGradient u x) * φ x) A ∧
    HasDerivAt (fun t => ∫ x in A,
      (native_interior_graph_density_v475 H) (x,u x+t*φ x,planarGradient u x+t • planarGradient φ x))
      (∫ x in A, inner ℝ ((native_interior_graph_flux_v475 H) (x,u x,planarGradient u x)) (planarGradient φ x) -
        (native_interior_graph_lower_v475 H) (x,u x,planarGradient u x) * φ x) 0 := by
  let F := fun p : ℝ × E2 =>
    (native_interior_graph_density_v475 H) (p.2,u p.2+p.1*φ p.2,planarGradient u p.2+p.1 • planarGradient φ p.2)
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
    ((native_interior_graph_jet_calculus_v475 V hV H).1.comp hjet
      (fun p hp => hjets p.1 hp.1 p.2 hp.2)).of_le (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp)
  have heq (x : E2) (hx : x ∈ A) :
      fderiv ℝ F (0,x) (1,0) =
        inner ℝ ((native_interior_graph_flux_v475 H) (x,u x,planarGradient u x)) (planarGradient φ x) -
          (native_interior_graph_lower_v475 H) (x,u x,planarGradient u x) * φ x := by
    have hf : DifferentiableAt ℝ F (0,x) :=
      (hF.contDiffAt ((hQ.prod hO).mem_nhds ⟨h0,hAO hx⟩)).differentiableAt (by simp)
    have hd := hf.hasFDerivAt.comp_hasDerivAt 0
      ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const 0 x))
    have hv := native_interior_graph_density_variation_v475 V hV H (x,u x,planarGradient u x)
      (by simpa using hjets 0 h0 x (hAO hx)) (φ x) (planarGradient φ x)
    exact hd.unique hv
  obtain ⟨hint,hd⟩ := native_compact_integral_variation_v475 A O hA hO hAO Q hQ h0 F hF
  have hae : (fun x => fderiv ℝ F (0,x) (1,0)) =ᵐ[volume.restrict A]
      (fun x => inner ℝ ((native_interior_graph_flux_v475 H) (x,u x,planarGradient u x)) (planarGradient φ x) -
        (native_interior_graph_lower_v475 H) (x,u x,planarGradient u x) * φ x) := by
    filter_upwards [ae_restrict_mem hA.measurableSet] with x hx
    exact heq x hx
  exact ⟨hint.congr hae,hd.congr_deriv (integral_congr_ae hae)⟩

#print axioms native_interior_compact_graph_density_variation_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
