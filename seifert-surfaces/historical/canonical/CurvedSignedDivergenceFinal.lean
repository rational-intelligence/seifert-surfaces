import CurvedGaussGreenHelpers
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

noncomputable section
open Set Topology Function MeasureTheory
open scoped Manifold ContDiff BigOperators
namespace SeifertSurfaces.OriginalEndpoints.CurvedDivergence
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC GaussGreen

/-- Both signs use the same trace and literal Euclidean arc-length density.
The integrable divergence near the curved boundary is explicit analytic debt. -/
theorem signed_curved_integration_by_parts (disc : Set E2) (s : E2 → ℝ)
    (γ : ℝ → E2) (left right : ℝ) (G : SignedArcGeometry disc s γ left right)
    (F : E2 → E2) (hF : ContinuousOn F disc)
    (hside : ∀ positive : Bool, ContDiffOn ℝ 1 F (signedDomain disc s positive))
    (φ : E2 → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ disc)
    (hdiv : ∀ positive : Bool,
      IntegrableOn (fun x => planarDivergence F x * φ x) (signedDomain disc s positive)) :
    ∀ positive : Bool,
      IntegrableOn (fun x => inner ℝ (F x) (planarGradient φ x) +
        planarDivergence F x * φ x) (signedDomain disc s positive) ∧
      IntegrableOn (fun t => inner ℝ (F (γ t)) (signedNormal s positive (γ t)) *
        φ (γ t) * ‖fderiv ℝ γ t 1‖) (arcParameters disc γ left right) ∧
      (∫ x in signedDomain disc s positive,
        inner ℝ (F x) (planarGradient φ x) + planarDivergence F x * φ x) =
      (∫ t in arcParameters disc γ left right,
        inner ℝ (F (γ t)) (signedNormal s positive (γ t)) *
          φ (γ t) * ‖fderiv ℝ γ t 1‖) :=  by
  classical
  have hopen (p : Bool) : IsOpen (signedDomain disc s p) := by
    cases p
    · change IsOpen (disc ∩ s ⁻¹' Iio 0)
      exact G.signed_smooth.continuousOn.isOpen_inter_preimage G.disc_open isOpen_Iio
    · change IsOpen (disc ∩ s ⁻¹' Ioi 0)
      exact G.signed_smooth.continuousOn.isOpen_inter_preimage G.disc_open isOpen_Ioi
  have hboundary (chi : E2 → ℝ) (hchi : ContDiff ℝ ∞ chi)
      (hbound : ∀ x, |chi x| ≤ 1)
      (C : SignedGraphChart disc s γ left right)
      (hsupport : tsupport (fun x => chi x * φ x) ⊆ C.window)
      (a b h : ℝ) (ha : C.a0 < a) (hab : a < b) (hb : b < C.b0)
      (hh : 0 < h) (hheight : h < C.h0)
      (hmargin : (shear C.Q C.sigma C.f ⁻¹' tsupport (fun x => chi x * φ x)) ⊆
        Ioo a b ×ˢ Ioo (-h) h) (p : Bool) :
      (∫ x in signedDomain disc s p,
        inner ℝ (F x) (planarGradient (fun y => chi y * φ y) x) +
          planarDivergence F x * (chi x * φ x)) =
      (∫ t in arcParameters disc γ left right,
        inner ℝ (F (γ t)) (signedNormal s p (γ t)) *
          (chi (γ t) * φ (γ t)) * ‖fderiv ℝ γ t 1‖) := by
    let theta : E2 → ℝ := fun x => chi x * φ x
    let W : E2 → E2 := fun x => theta x • F x
    let T := shear C.Q C.sigma C.f
    let A := openHalfBox p a b h
    let d : E2 → ℝ := fun x => inner ℝ (F x) (planarGradient theta x) +
      planarDivergence F x * theta x
    let Z := transformedFlux C.Q C.sigma C.f W
    obtain ⟨htheta, hctheta, hsub, hdisc, hW, hWside, hprod, hi, hzero⟩ :=
      weighted_support_and_divergence disc s γ left right G F hF hside φ hφ hc hs
        hdiv chi hchi hbound
    have hsmall (q : Bool) : openHalfBox q a b h ⊆ openHalfBox q C.a0 C.b0 C.h0 := by
      intro z hz
      cases q <;> change z.1 ∈ Ioo a b ∧ _ at hz <;>
        change z.1 ∈ Ioo C.a0 C.b0 ∧ _ <;>
        constructor
      all_goals first | exact ⟨ha.trans hz.1.1, hz.1.2.trans hb⟩ | exact ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩
    have himageSide (q : Bool) : T '' openHalfBox q a b h ⊆ signedDomain disc s q := by
      have hh : T '' openHalfBox q a b h ⊆ T '' openHalfBox q C.a0 C.b0 C.h0 :=
        image_mono (hsmall q)
      have heq : T '' openHalfBox q C.a0 C.b0 C.h0 =
          signedDomain disc s q ∩
            (shear C.Q C.sigma C.f '' (Ioo C.a0 C.b0 ×ˢ Ioo (-C.h0) C.h0)) :=
        (C.strict_side_image q).symm
      rw [heq] at hh
      exact hh.trans inter_subset_left
    have hAd : T '' A ⊆ signedDomain disc s p := himageSide p
    have hstrip : A ⊆ Ioo C.a0 C.b0 ×ˢ (univ : Set ℝ) := by
      intro z hz
      have hx : a < z.1 ∧ z.1 < b := by cases p <;> exact hz.1
      exact ⟨⟨ha.trans hx.1, hx.2.trans hb⟩, mem_univ _⟩
    have hAm : MeasurableSet A := by
      cases p <;> exact (isOpen_Ioo.prod isOpen_Ioo).measurableSet
    have hzeroD (x : E2) (hx : x ∉ tsupport theta) : d x = 0 := by
      obtain ⟨hz, hg, hw⟩ := hzero x hx
      change theta x = 0 at hz
      change planarGradient theta x = 0 at hg
      change inner ℝ (F x) (planarGradient theta x) + planarDivergence F x * theta x = 0
      rw [hg, hz, inner_zero_right, mul_zero, add_zero]
    have hsuppImage (x : E2) (hx : x ∈ signedDomain disc s p)
        (hxt : x ∈ tsupport theta) : x ∈ T '' A := by
      let z := unshear C.Q C.sigma C.f x
      have hTx : T z = x := C.inverse_right x
      have hzsmall : z ∈ Ioo a b ×ˢ Ioo (-h) h := hmargin (by change T z ∈ tsupport theta; rwa [hTx])
      have hzbig : z ∈ Ioo C.a0 C.b0 ×ˢ Ioo (-C.h0) C.h0 :=
        ⟨⟨ha.trans hzsmall.1.1, hzsmall.1.2.trans hb⟩,
          by linarith [hzsmall.2.1], by linarith [hzsmall.2.2]⟩
      have hsign := C.strict_signs z hzbig
      refine ⟨z, ?_, hTx⟩
      cases p
      · have hsx : s x < 0 := hx.2
        exact ⟨hzsmall.1, hzsmall.2.1, hsign.1.mp (show s (T z) < 0 by rwa [hTx])⟩
      · have hsx : 0 < s x := hx.2
        exact ⟨hzsmall.1, hsign.2.mp (show 0 < s (T z) by rwa [hTx]), hzsmall.2.2⟩
    have hrestrict : (∫ x in signedDomain disc s p, d x) = ∫ x in T '' A, d x :=
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hopen p).measurableSet hAd (by
        intro x hx
        exact hzeroD x (fun ht => hx.2 (hsuppImage x hx.1 ht)))
    obtain ⟨hm, hinj, hdf, hint, htransport⟩ := exact_shear_volume_transport
      C.Q C.frame C.sigma C.sigma_choice C.f C.a0 C.b0 C.graph_smooth
        A hAm hstrip d
    have hiA : IntegrableOn (fun z => d (T z)) A :=
      hint.mp ((hi p).mono_set hAd)
    have hZ := transformed_flux_divergence C.Q C.frame C.sigma C.sigma_choice
      C.f C.a0 C.b0 a b h C.graph_smooth ha hab hb hh W hW
        (fun q => (hWside q).mono (himageSide q))
    have hsum : ∀ z ∈ A,
        fderiv ℝ (fun z => (Z z).1) z (1, 0) +
          fderiv ℝ (fun z => (Z z).2) z (0, 1) = d (T z) := by
      intro z hz
      exact ((hZ.2 p z hz).2.2).trans (hprod p (T z) (hAd (mem_image_of_mem _ hz)))
    have hnull := null_faces_and_summed_divergence_transfer a b h hab hh p
      (fderiv ℝ (fun z => (Z z).1)) (fderiv ℝ (fun z => (Z z).2))
        (fun z => d (T z)) hiA hsum
    have hZzero (z : ℝ × ℝ) (hz : z ∉ Ioo a b ×ˢ Ioo (-h) h) : Z z = (0, 0) := by
      have hthetaZero : theta (T z) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun ht => hz (hmargin ht))
      have hWzero : W (T z) = 0 := by change theta (T z) • F (T z) = 0; rw [hthetaZero, zero_smul]
      change ((C.Q (W (T z))) 0,
        C.sigma * ((C.Q (W (T z))) 1 - deriv C.f z.1 * (C.Q (W (T z))) 0)) = (0, 0)
      simp only [hWzero, map_zero, PiLp.zero_apply, mul_zero, sub_zero]
    have hfaces : ∀ v ∈ (if p then Icc 0 h else Icc (-h) 0),
        (Z (a, v)).1 = 0 ∧ (Z (b, v)).1 = 0 := by
      intro v hv
      constructor
      · rw [hZzero (a, v) (fun hz => lt_irrefl a hz.1.1)]
      · rw [hZzero (b, v) (fun hz => lt_irrefl b hz.1.2)]
    have houter : ∀ u ∈ Icc a b, (Z (u, if p then h else -h)).2 = 0 := by
      intro u hu
      rw [hZzero _ (by cases p <;> intro hz <;> simp only [Bool.false_eq_true, ↓reduceIte] at hz <;> linarith [hz.2.1, hz.2.2])]
    have hbox := lower_upper_half_box_adapter (fun z => (Z z).1) (fun z => (Z z).2)
      (fderiv ℝ (fun z => (Z z).1)) (fderiv ℝ (fun z => (Z z).2))
        a b h hab hh p (hZ.1 p).1 (hZ.1 p).2
          (fun z hz => (hZ.2 p z hz).1) (fun z hz => (hZ.2 p z hz).2.1)
            hnull.2.2.1 hfaces houter
    have harc := original_restricted_arc_integral_transport disc s γ left right G C F hF
      theta htheta hctheta hsupport a b h ha hab hb hh hheight hmargin p
    exact hrestrict.trans (htransport.trans (hnull.2.2.2.symm.trans (hbox.trans harc.2.2)))
  have hinterior (chi : E2 → ℝ) (hchi : ContDiff ℝ ∞ chi)
      (hbound : ∀ x, |chi x| ≤ 1) (q : Bool)
      (hsupport : tsupport (fun x => chi x * φ x) ⊆ signedDomain disc s q) (p : Bool) :
      (∫ x in signedDomain disc s p,
        inner ℝ (F x) (planarGradient (fun y => chi y * φ y) x) +
          planarDivergence F x * (chi x * φ x)) =
      (∫ t in arcParameters disc γ left right,
        inner ℝ (F (γ t)) (signedNormal s p (γ t)) *
          (chi (γ t) * φ (γ t)) * ‖fderiv ℝ γ t 1‖) := by
    let theta : E2 → ℝ := fun x => chi x * φ x
    let W : E2 → E2 := fun x => theta x • F x
    let d : E2 → ℝ := fun x => inner ℝ (F x) (planarGradient theta x) +
      planarDivergence F x * theta x
    obtain ⟨htheta, hctheta, hsub, hdisc, hW, hWside, hprod, hi, hzero⟩ :=
      weighted_support_and_divergence disc s γ left right G F hF hside φ hφ hc hs
        hdiv chi hchi hbound
    have hzeroD (x : E2) (hx : x ∉ tsupport theta) : d x = 0 := by
      obtain ⟨hz, hg, hw⟩ := hzero x hx
      change theta x = 0 at hz
      change planarGradient theta x = 0 at hg
      change inner ℝ (F x) (planarGradient theta x) + planarDivergence F x * theta x = 0
      rw [hg, hz, inner_zero_right, mul_zero, add_zero]
    have hzeroDiv (x : E2) (hx : x ∉ tsupport theta) : planarDivergence W x = 0 := by
      have hlocal : W =ᶠ[𝓝 x] fun _ => 0 := (hzero x hx).2.2
      apply Finset.sum_eq_zero
      intro i hi
      have hiEq : (fun y => W y i) =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
        hlocal.fun_comp (fun v : E2 => v i)
      rw [hiEq.fderiv_eq (𝕜 := ℝ), fderiv_const_apply, ContinuousLinearMap.zero_apply]
    have hglob : ContDiff ℝ 1 W := by
      rw [contDiff_iff_contDiffAt]
      intro x
      by_cases hx : x ∈ tsupport theta
      · exact (hWside q).contDiffAt ((hopen q).mem_nhds (hsupport hx))
      · exact contDiffAt_const.congr_of_eventuallyEq (hzero x hx).2.2
    have hcW : HasCompactSupport W := hctheta.smul_right
    have hcomp (i : Fin 2) : ContDiff ℝ 1 (fun x => W x i) :=
      (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) i).contDiff.comp hglob
    have hccomp (i : Fin 2) : HasCompactSupport (fun x => W x i) :=
      hcW.comp_left (g := fun v : E2 => v i) rfl
    have hiDerivative (i : Fin 2) :
        Integrable (fun x => fderiv ℝ (fun y => W y i) x (coordinateVector 2 i)) := by
      apply Continuous.integrable_of_hasCompactSupport
      · exact ((hcomp i).continuous_fderiv one_ne_zero).clm_apply continuous_const
      · exact (hccomp i).fderiv_apply (𝕜 := ℝ) (coordinateVector 2 i)
    have hDerivativeIntegral (i : Fin 2) :
        (∫ x, fderiv ℝ (fun y => W y i) x (coordinateVector 2 i)) = 0 := by
      have hb := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        (μ := (volume : Measure E2)) (f := fun _ : E2 => (1 : ℝ))
        (g := fun x => W x i) (v := coordinateVector 2 i)
          (by simpa only [fderiv_const_apply, ContinuousLinearMap.zero_apply, zero_mul] using!
            (integrable_zero E2 ℝ (volume : Measure E2)))
          (by simpa only [one_mul] using hiDerivative i)
          (by simpa only [one_mul] using (hcomp i).continuous.integrable_of_hasCompactSupport (hccomp i))
          (fun _ _ => differentiableAt_const _) (fun x _ => (hcomp i).differentiable (by simp) x)
      simpa only [one_mul, fderiv_const_apply, ContinuousLinearMap.zero_apply,
        zero_mul, integral_zero, neg_zero] using hb
    have hglobalIntegral : (∫ x, planarDivergence W x) = 0 := by
      change (∫ x, ∑ i : Fin 2, fderiv ℝ (fun y => W y i) x (coordinateVector 2 i)) = 0
      rw [integral_finset_sum _ (fun i _ => hiDerivative i)]
      exact Finset.sum_eq_zero (fun i _ => hDerivativeIntegral i)
    have hdeq (x : E2) : d x = planarDivergence W x := by
      by_cases hx : x ∈ tsupport theta
      · exact (hprod q x (hsupport hx)).symm
      · rw [hzeroD x hx, hzeroDiv x hx]
    have hvolume : (∫ x in signedDomain disc s p, d x) = 0 := by
      by_cases hpq : p = q
      · subst p
        calc
          (∫ x in signedDomain disc s q, d x) = ∫ x, d x :=
            setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx =>
              hzeroD x (fun ht => hx (hsupport ht)))
          _ = ∫ x, planarDivergence W x := integral_congr_ae (Filter.Eventually.of_forall hdeq)
          _ = 0 := hglobalIntegral
      · apply setIntegral_eq_zero_of_forall_eq_zero
        intro x hx
        apply hzeroD x
        intro ht
        have hxq := hsupport ht
        cases p <;> cases q
        · exact (hpq rfl).elim
        · have hn : s x < 0 := hx.2
          have hp : 0 < s x := hxq.2
          linarith
        · have hp : 0 < s x := hx.2
          have hn : s x < 0 := hxq.2
          linarith
        · exact (hpq rfl).elim
    have harc : (∫ t in arcParameters disc γ left right,
        inner ℝ (F (γ t)) (signedNormal s p (γ t)) * theta (γ t) * ‖fderiv ℝ γ t 1‖) = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro t ht
      have hsz : s (γ t) = 0 := by
        have hmem : γ t ∈ {x ∈ disc | s x = 0} := by
          rw [G.zero_set_exact]
          exact ⟨mem_image_of_mem _ ht.1, ht.2⟩
        exact hmem.2
      have hz : theta (γ t) = 0 := image_eq_zero_of_notMem_tsupport (by
        intro hm
        have hq := (hsupport hm).2
        cases q <;> simp only [Bool.false_eq_true, ↓reduceIte, hsz] at hq <;> exact lt_irrefl _ hq)
      rw [hz, mul_zero, zero_mul]
    exact hvolume.trans harc.symm
  obtain ⟨L⟩ := finite_localization_from_original_support disc s γ left right G φ hφ hc hs
  let theta : Fin L.n → E2 → ℝ := fun j x => L.chi j x * φ x
  have hbound (j : Fin L.n) (x : E2) : |L.chi j x| ≤ 1 :=
    abs_le.mpr ⟨by linarith [(L.chi_bounds j x).1], (L.chi_bounds j x).2⟩
  have hweighted (j : Fin L.n) := weighted_support_and_divergence disc s γ left right G
    F hF hside φ hφ hc hs hdiv (L.chi j) (L.chi_smooth j) (hbound j)
  have htheta (j : Fin L.n) : ContDiff ℝ ∞ (theta j) := (hweighted j).1
  have hsumtheta (x : E2) : ∑ j : Fin L.n, theta j x = φ x := by
    change (∑ j : Fin L.n, L.chi j x * φ x) = φ x
    rw [← Finset.sum_mul]
    by_cases hx : x ∈ L.N
    · rw [L.partition x hx, one_mul]
    · have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hx (L.N_contains ht))
      rw [hz, mul_zero]
  have hsumgradient (x : E2) : ∑ j : Fin L.n, planarGradient (theta j) x = planarGradient φ x := by
    have heq : (fun y => ∑ j : Fin L.n, theta j y) = φ := funext hsumtheta
    have hd : ∀ j ∈ (Finset.univ : Finset (Fin L.n)), DifferentiableAt ℝ (theta j) x :=
      fun j _ => (htheta j).differentiable (by simp) x
    have hderiv : (∑ j : Fin L.n, fderiv ℝ (theta j) x) = fderiv ℝ φ x := by
      rw [← fderiv_fun_sum hd, heq]
    change (∑ j : Fin L.n, ∑ i : Fin 2,
      fderiv ℝ (theta j) x (coordinateVector 2 i) • coordinateVector 2 i) =
        ∑ i : Fin 2, fderiv ℝ φ x (coordinateVector 2 i) • coordinateVector 2 i
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_smul]
    congr 1
    have he := congrArg (fun A : E2 →L[ℝ] ℝ => A (coordinateVector 2 i)) hderiv
    simpa only [ContinuousLinearMap.sum_apply] using he
  let d : Fin L.n → E2 → ℝ := fun j x =>
    inner ℝ (F x) (planarGradient (theta j) x) + planarDivergence F x * theta j x
  let b : Bool → Fin L.n → ℝ → ℝ := fun p j t =>
    inner ℝ (F (γ t)) (signedNormal s p (γ t)) * theta j (γ t) * ‖fderiv ℝ γ t 1‖
  have hid (j : Fin L.n) (p : Bool) : IntegrableOn (d j) (signedDomain disc s p) :=
    (hweighted j).2.2.2.2.2.2.2.1 p
  have hib (j : Fin L.n) (p : Bool) : IntegrableOn (b p j) (arcParameters disc γ left right) :=
    compact_arc_test_integrability disc s γ left right G F hF (theta j)
      (htheta j) (hweighted j).2.1 (hweighted j).2.2.2.1 p
  have hlocal (j : Fin L.n) (p : Bool) :
      (∫ x in signedDomain disc s p, d j x) = ∫ t in arcParameters disc γ left right, b p j t := by
    have hsChi : tsupport (theta j) ⊆ closure (L.U j) :=
      ((hweighted j).2.2.1.trans inter_subset_right).trans ((L.chi_support j).trans subset_closure)
    cases hp : L.patch j with
    | inl C =>
      obtain ⟨ha, hab, hb, hh, hheight, hmargin⟩ := L.boundary_support_margin j C hp
      exact hboundary (L.chi j) (L.chi_smooth j) (hbound j) C
        (hsChi.trans (L.boundary_window j C hp)) (L.a j) (L.b j) (L.h j)
          ha hab hb hh hheight hmargin p
    | inr q =>
      exact hinterior (L.chi j) (L.chi_smooth j) (hbound j) q
        (hsChi.trans (L.interior_window j q hp)) p
  have hsumd (x : E2) : (∑ j : Fin L.n, d j x) =
      inner ℝ (F x) (planarGradient φ x) + planarDivergence F x * φ x := by
    change (∑ j : Fin L.n,
      (inner ℝ (F x) (planarGradient (theta j) x) + planarDivergence F x * theta j x)) = _
    rw [Finset.sum_add_distrib, ← inner_sum, ← Finset.mul_sum, hsumgradient, hsumtheta]
  have hsumb (p : Bool) (t : ℝ) : (∑ j : Fin L.n, b p j t) =
      inner ℝ (F (γ t)) (signedNormal s p (γ t)) * φ (γ t) * ‖fderiv ℝ γ t 1‖ := by
    change (∑ j : Fin L.n,
      inner ℝ (F (γ t)) (signedNormal s p (γ t)) * theta j (γ t) * ‖fderiv ℝ γ t 1‖) = _
    rw [← Finset.sum_mul, ← Finset.mul_sum, hsumtheta]
  intro p
  have hw1 := weighted_support_and_divergence disc s γ left right G F hF hside φ hφ hc hs
    hdiv (fun _ => 1) contDiff_const (by intro x; simp)
  refine ⟨?_, compact_arc_test_integrability disc s γ left right G F hF φ hφ hc hs p, ?_⟩
  · simpa only [one_mul] using hw1.2.2.2.2.2.2.2.1 p
  · calc
      (∫ x in signedDomain disc s p, inner ℝ (F x) (planarGradient φ x) +
          planarDivergence F x * φ x) = ∫ x in signedDomain disc s p, ∑ j : Fin L.n, d j x :=
        integral_congr_ae (Filter.Eventually.of_forall (fun x => (hsumd x).symm))
      _ = ∑ j : Fin L.n, ∫ x in signedDomain disc s p, d j x :=
        integral_finset_sum _ (fun j _ => hid j p)
      _ = ∑ j : Fin L.n, ∫ t in arcParameters disc γ left right, b p j t :=
        Finset.sum_congr rfl (fun j _ => hlocal j p)
      _ = ∫ t in arcParameters disc γ left right, ∑ j : Fin L.n, b p j t :=
        (integral_finset_sum _ (fun j _ => hib j p)).symm
      _ = ∫ t in arcParameters disc γ left right,
          inner ℝ (F (γ t)) (signedNormal s p (γ t)) * φ (γ t) * ‖fderiv ℝ γ t 1‖ :=
        integral_congr_ae (Filter.Eventually.of_forall (hsumb p))

end SeifertSurfaces.OriginalEndpoints.CurvedDivergence
