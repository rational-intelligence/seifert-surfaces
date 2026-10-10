import CurvedSignedDivergenceFinal
import AppendixAInteriorRegularity
import Mathlib.MeasureTheory.Measure.Hausdorff

set_option autoImplicit false
open scoped Manifold ContDiff BigOperators
open Set Topology Function MeasureTheory
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
open CurvedDivergence

/-- Continuous flux with the same trace on a smooth curved interface satisfies
the whole-domain weak identity. Derivatives are needed only in the two open
sides. The paid curved Green theorem supplies both literal boundary terms. -/
theorem weak_divergence_extends_over_curved_arc
    (Ω : Set E2) (s : E2 → ℝ) (γ : ℝ → E2) (left right : ℝ)
    (G : SignedArcGeometry Ω s γ left right)
    (A : E2 → E2) (B : E2 → ℝ) (hA : ContinuousOn A Ω) (hB : ContinuousOn B Ω)
    (hside : ∀ p : Bool, ContDiffOn ℝ 1 A (signedDomain Ω s p))
    (hdiv : ∀ p : Bool, ∀ x ∈ signedDomain Ω s p, planarDivergence A x = -B x) :
    ∀ φ : E2 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      weakFluxIdentity Ω A B φ := by
  intro φ hφ hc hs
  have hopen (p : Bool) : IsOpen (signedDomain Ω s p) := by
    cases p
    · exact G.signed_smooth.continuousOn.isOpen_inter_preimage G.disc_open isOpen_Iio
    · exact G.signed_smooth.continuousOn.isOpen_inter_preimage G.disc_open isOpen_Ioi
  have hBφ : IntegrableOn (fun x => B x * φ x) Ω := by
    apply (((hB.mono hs).mul hφ.continuous.continuousOn).integrableOn_compact hc).of_forall_sdiff_eq_zero
      G.disc_open.measurableSet
    intro x hx
    change B x * φ x = 0
    rw [image_eq_zero_of_notMem_tsupport hx.2, mul_zero]
  have hdivφ (p : Bool) : IntegrableOn (fun x => planarDivergence A x * φ x)
      (signedDomain Ω s p) := by
    apply (hBφ.neg.mono_set (fun _ hx => hx.1)).congr_fun
    · intro x hx
      dsimp only [Pi.neg_apply]
      rw [hdiv p x hx]
      ring
    · exact (hopen p).measurableSet
  have hgreen := signed_curved_integration_by_parts Ω s γ left right G A hA hside φ hφ hc hs hdivφ
  have hsideEq (p : Bool) :
      (∫ x in signedDomain Ω s p, inner ℝ (A x) (planarGradient φ x) - B x * φ x) =
      ∫ t in arcParameters Ω γ left right,
        inner ℝ (A (γ t)) (signedNormal s p (γ t)) * φ (γ t) * ‖fderiv ℝ γ t 1‖ := by
    rw [← (hgreen p).2.2]
    apply setIntegral_congr_fun (hopen p).measurableSet
    intro x hx
    dsimp only
    rw [hdiv p x hx]
    ring
  have hsource : (μH[2] : Measure ℝ) = 0 := Real.hausdorffMeasure_of_finrank_lt (by simp)
  have himage : μH[2] (γ '' Ioo left right) = 0 :=
    (G.arc_smooth.differentiableOn (by simp)).hausdorffMeasure_image_eq_zero
      (by norm_num) (by rw [hsource]; simp)
  have harc : volume (γ '' Ioo left right) = 0 := by
    rw [← EuclideanSpace.euclideanHausdorffMeasure_eq_volume 2,
      Measure.euclideanHausdorffMeasure_def, Measure.smul_apply]
    simp only [Nat.cast_ofNat, himage, smul_zero]
  have hnull : volume {x ∈ Ω | s x = 0} = 0 := by
    rw [G.zero_set_exact]
    exact measure_mono_null inter_subset_left harc
  have hdiff : Ω \ (signedDomain Ω s false ∪ signedDomain Ω s true) ⊆ {x ∈ Ω | s x = 0} := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    by_contra hn
    rcases lt_or_gt_of_ne hn with hn | hp
    · exact hx.2 (Or.inl ⟨hx.1, hn⟩)
    · exact hx.2 (Or.inr ⟨hx.1, hp⟩)
  have hae : Ω =ᵐ[volume] signedDomain Ω s false ∪ signedDomain Ω s true := by
    apply ae_eq_set.mpr
    constructor
    · exact measure_mono_null hdiff hnull
    · have he : (signedDomain Ω s false ∪ signedDomain Ω s true) \ Ω = ∅ :=
        sdiff_eq_empty.mpr (union_subset (fun _ hx => hx.1) (fun _ hx => hx.1))
      rw [he]
      exact measure_empty
  have hd : Disjoint (signedDomain Ω s false) (signedDomain Ω s true) := by
    apply disjoint_left.mpr
    intro x hx hy
    exact lt_asymm hx.2 hy.2
  have hi := (flux_integrand_integrable Ω A B φ hA hB hφ hc hs).integrableOn (s := Ω)
  unfold weakFluxIdentity
  rw [setIntegral_congr_set hae, setIntegral_union hd (hopen true).measurableSet
    (hi.mono_set (fun _ hx => hx.1)) (hi.mono_set (fun _ hx => hx.1)),
    hsideEq false, hsideEq true]
  have he : (fun t => inner ℝ (A (γ t)) (signedNormal s true (γ t)) * φ (γ t) * ‖fderiv ℝ γ t 1‖) =
      fun t => -(inner ℝ (A (γ t)) (signedNormal s false (γ t)) * φ (γ t) * ‖fderiv ℝ γ t 1‖) := by
    funext t
    simp only [signedNormal, Bool.false_eq_true, ↓reduceIte, inner_neg_right, neg_mul]
  rw [he, integral_neg]
  exact add_neg_cancel _

/-- The nonlinear interior bootstrap removes a curved seam from a C1 graph
whose actual smooth operator equation holds on the two open sides. Smoothness
up to either closed side is a conclusion of this step, not a premise. -/
theorem smooth_C1_graph_across_curved_arc
    (Ω : Set E2) (s : E2 → ℝ) (γ : ℝ → E2) (left right : ℝ)
    (G : SignedArcGeometry Ω s γ left right)
    (J : Set Jet) (hJ : IsOpen J) (Q : SmoothQuasilinearOperator J)
    (helliptic : UniformlyEllipticOn J Q.flux)
    (u : E2 → ℝ) (hC1 : ContDiffOn ℝ 1 u Ω)
    (hjets : ∀ x ∈ Ω, (x, u x, planarGradient u x) ∈ J)
    (hsmooth : ∀ p : Bool, ContDiffOn ℝ ∞ u (signedDomain Ω s p))
    (heq : ∀ p : Bool, ∀ x ∈ signedDomain Ω s p,
      planarDivergence (fun y => Q.flux (y, u y, planarGradient u y)) x =
        -Q.lowerOrder (x, u x, planarGradient u x)) :
    ContDiffOn ℝ ∞ u Ω := by
  have hgrad : ContinuousOn (planarGradient u) Ω := by
    unfold planarGradient
    apply continuousOn_finsetSum
    intro i hi
    exact ((hC1.continuousOn_fderiv_of_isOpen G.disc_open (by simp)).clm_apply
      continuousOn_const).smul continuousOn_const
  have hj : ContinuousOn (fun x => (x, u x, planarGradient u x)) Ω :=
    continuousOn_id.prodMk (hC1.continuousOn.prodMk hgrad)
  have hA := Q.flux_smooth.continuousOn.comp hj hjets
  have hB := Q.lowerOrder_smooth.continuousOn.comp hj hjets
  have hside (p : Bool) : ContDiffOn ℝ 1
      (fun y => Q.flux (y, u y, planarGradient u y)) (signedDomain Ω s p) := by
    have hopen : IsOpen (signedDomain Ω s p) := by
      cases p
      · exact G.signed_smooth.continuousOn.isOpen_inter_preimage G.disc_open isOpen_Iio
      · exact G.signed_smooth.continuousOn.isOpen_inter_preimage G.disc_open isOpen_Ioi
    have hg : ContDiffOn ℝ ∞ (planarGradient u) (signedDomain Ω s p) := by
      unfold planarGradient
      apply ContDiffOn.sum
      intro i hi
      exact (((hsmooth p).fderiv_of_isOpen hopen (by simp)).clm_apply
        contDiffOn_const).smul contDiffOn_const
    exact (Q.flux_smooth.comp (contDiffOn_id.prodMk ((hsmooth p).prodMk hg))
      (fun x hx => hjets x hx.1)).of_le (by simp)
  apply smooth_of_C1_weak_uniformlyElliptic Ω G.disc_open J hJ Q helliptic u hC1 hjets
  exact weak_divergence_extends_over_curved_arc Ω s γ left right G _ _ hA hB hside heq

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
