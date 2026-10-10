import QuasilinearLocalization

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology BigOperators ContDiff

namespace SeifertSurfaces.QuasilinearLocalization
open SeifertSurfaces.AppendixACoordinates

namespace QuotientHelpers
section PartialContinuity
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma x_partial_continuousOn (J : Set Jet) (hJ : IsOpen J)
    (f : Jet → F) (hf : ContDiffOn ℝ ∞ f J) :
    ContinuousOn (fun j : Jet => fderiv ℝ (fun x : E2 => f (x, j.2.1, j.2.2)) j.1) J := by
  have hc := (hf.continuousOn_fderiv_of_isOpen hJ (by simp)).clm_comp
    (continuousOn_const (c := ContinuousLinearMap.inl ℝ E2 (ℝ × E2)))
  apply hc.congr
  intro j hj
  exact Helpers.fderiv_x_slice f j
    ((hf.contDiffAt (hJ.mem_nhds hj)).differentiableAt (by simp))

lemma z_partial_continuousOn (J : Set Jet) (hJ : IsOpen J)
    (f : Jet → F) (hf : ContDiffOn ℝ ∞ f J) :
    ContinuousOn (fun j : Jet => fderiv ℝ (fun z : ℝ => f (j.1, z, j.2.2)) j.2.1 1) J := by
  have hc := ((hf.continuousOn_fderiv_of_isOpen hJ (by simp)).clm_comp
    (continuousOn_const (c := (ContinuousLinearMap.inr ℝ E2 (ℝ × E2)).comp
      (ContinuousLinearMap.inl ℝ ℝ E2)))).clm_apply (continuousOn_const (c := (1 : ℝ)))
  apply hc.congr
  intro j hj
  dsimp only
  rw [Helpers.fderiv_z_slice f j
    ((hf.contDiffAt (hJ.mem_nhds hj)).differentiableAt (by simp))]

lemma p_partial_continuousOn (J : Set Jet) (hJ : IsOpen J)
    (f : Jet → F) (hf : ContDiffOn ℝ ∞ f J) :
    ContinuousOn (fun j : Jet => fderiv ℝ (fun p : E2 => f (j.1, j.2.1, p)) j.2.2) J := by
  have hc := (hf.continuousOn_fderiv_of_isOpen hJ (by simp)).clm_comp
    (continuousOn_const (c := (ContinuousLinearMap.inr ℝ E2 (ℝ × E2)).comp
      (ContinuousLinearMap.inr ℝ ℝ E2)))
  apply hc.congr
  intro j hj
  exact Helpers.fderiv_p_slice f j
    ((hf.contDiffAt (hJ.mem_nhds hj)).differentiableAt (by simp))
end PartialContinuity

lemma jetSegment_continuous (u : E2 → ℝ) (k : Fin 2) (h : ℝ) (x : E2) :
    Continuous (jetSegment u k h x) := by
  unfold jetSegment
  fun_prop

section SegmentFTC
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

lemma fderiv_split (f : Jet → F) (j d : Jet) (hf : DifferentiableAt ℝ f j) :
    fderiv ℝ f j d =
      fderiv ℝ (fun p : E2 => f (j.1, j.2.1, p)) j.2.2 d.2.2 +
      d.2.1 • fderiv ℝ (fun z : ℝ => f (j.1, z, j.2.2)) j.2.1 1 +
      fderiv ℝ (fun x : E2 => f (x, j.2.1, j.2.2)) j.1 d.1 := by
  rw [Helpers.fderiv_p_slice f j hf, Helpers.fderiv_z_slice f j hf,
    Helpers.fderiv_x_slice f j hf]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.inr_apply, ← map_smul]
  change fderiv ℝ f j d =
    fderiv ℝ f j (0, (0, d.2.2)) +
      fderiv ℝ f j (d.2.1 • (0, (1, 0))) + fderiv ℝ f j (d.1, 0)
  rw [← map_add, ← map_add]
  congr 1
  ext <;> simp

lemma segment_FTC (J : Set Jet) (hJ : IsOpen J) (f : Jet → F)
    (hf : ContDiffOn ℝ ∞ f J) (j₀ j₁ : Jet)
    (hs : ∀ t ∈ Icc (0 : ℝ) 1, (1 - t) • j₀ + t • j₁ ∈ J) :
    f j₁ - f j₀ =
      (∫ t in Icc (0 : ℝ) 1,
        fderiv ℝ f ((1 - t) • j₀ + t • j₁) (j₁ - j₀)) := by
  let s : ℝ → Jet := fun t => (1 - t) • j₀ + t • j₁
  have hc : Continuous s := by dsimp [s]; fun_prop
  have hd : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun t => f (s t)) (fderiv ℝ f (s t) (j₁ - j₀)) t := by
    intro t ht
    have hst : HasDerivAt s (j₁ - j₀) t := by
      have hh := (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).smul_const j₀).add
        ((hasDerivAt_id t).smul_const j₁)
      convert hh using 1
      · rfl
      · simp [sub_eq_add_neg, add_comm]
    exact ((hf.contDiffAt (hJ.mem_nhds (hs t (by simpa using ht)))).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt t hst
  have hi : IntervalIntegrable (fun t => fderiv ℝ f (s t) (j₁ - j₀)) volume 0 1 := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mpr
    exact (((hf.continuousOn_fderiv_of_isOpen hJ (by simp)).comp hc.continuousOn hs).clm_apply
      continuousOn_const).integrableOn_compact isCompact_Icc
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc] at heq
  simpa [s] using heq.symm

end SegmentFTC

section CoordinateFTC
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

lemma segment_coordinate_FTC (J : Set Jet) (hJ : IsOpen J) (f : Jet → F)
    (hf : ContDiffOn ℝ ∞ f J) (u : E2 → ℝ) (k : Fin 2) (h : ℝ) (x : E2)
    (hs : ∀ t ∈ Icc (0 : ℝ) 1, jetSegment u k h x t ∈ J) :
    f (firstJet u (shift k h x)) - f (firstJet u x) =
      (∫ t in Icc (0 : ℝ) 1, fderiv ℝ
        (fun p : E2 => f ((jetSegment u k h x t).1, (jetSegment u k h x t).2.1, p))
        (jetSegment u k h x t).2.2) (planarGradient u (shift k h x) - planarGradient u x) +
      (u (shift k h x) - u x) • (∫ t in Icc (0 : ℝ) 1, fderiv ℝ
        (fun z : ℝ => f ((jetSegment u k h x t).1, z, (jetSegment u k h x t).2.2))
        (jetSegment u k h x t).2.1 1) +
      h • (∫ t in Icc (0 : ℝ) 1, fderiv ℝ
        (fun y : E2 => f (y, (jetSegment u k h x t).2.1, (jetSegment u k h x t).2.2))
        (jetSegment u k h x t).1 (coordinateVector 2 k)) := by
  let s := jetSegment u k h x
  let p := fun t => fderiv ℝ (fun p : E2 => f ((s t).1, (s t).2.1, p)) (s t).2.2
  let z := fun t => fderiv ℝ (fun z : ℝ => f ((s t).1, z, (s t).2.2)) (s t).2.1 1
  let a := fun t => fderiv ℝ (fun y : E2 => f (y, (s t).2.1, (s t).2.2)) (s t).1
    (coordinateVector 2 k)
  let dp := planarGradient u (shift k h x) - planarGradient u x
  let dz := u (shift k h x) - u x
  have hc : ContinuousOn s (Icc (0 : ℝ) 1) := (jetSegment_continuous u k h x).continuousOn
  have hp : IntegrableOn p (Icc (0 : ℝ) 1) :=
    ((p_partial_continuousOn J hJ f hf).comp hc hs).integrableOn_compact isCompact_Icc
  have hz : IntegrableOn z (Icc (0 : ℝ) 1) :=
    ((z_partial_continuousOn J hJ f hf).comp hc hs).integrableOn_compact isCompact_Icc
  have ha : IntegrableOn a (Icc (0 : ℝ) 1) :=
    (((x_partial_continuousOn J hJ f hf).comp hc hs).clm_apply
      continuousOn_const).integrableOn_compact isCompact_Icc
  have hdp : IntegrableOn (fun t => p t dp) (Icc (0 : ℝ) 1) :=
    (ContinuousLinearMap.apply ℝ F dp).integrable_comp hp
  have hdz : IntegrableOn (fun t => dz • z t) (Icc (0 : ℝ) 1) := hz.smul dz
  have hda : IntegrableOn (fun t => h • a t) (Icc (0 : ℝ) 1) := ha.smul h
  have hadd : IntegrableOn (fun t => p t dp + dz • z t) (Icc (0 : ℝ) 1) := hdp.add hdz
  rw [segment_FTC J hJ f hf (firstJet u x) (firstJet u (shift k h x)) hs]
  have heq : (∫ t in Icc (0 : ℝ) 1, fderiv ℝ f (s t)
      (firstJet u (shift k h x) - firstJet u x)) =
      ∫ t in Icc (0 : ℝ) 1, p t dp + dz • z t + h • a t := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    dsimp only
    rw [fderiv_split f (s t) _
      ((hf.contDiffAt (hJ.mem_nhds (hs t ht))).differentiableAt (by simp))]
    simp [firstJet, shift, p, z, a, dp, dz, map_smul]
  change (∫ t in Icc (0 : ℝ) 1, fderiv ℝ f (s t)
      (firstJet u (shift k h x) - firstJet u x)) = _
  rw [heq, integral_add hadd hda,
    integral_add hdp hdz, integral_smul, integral_smul,
    ← ContinuousLinearMap.integral_apply hp dp]

end CoordinateFTC

end QuotientHelpers

theorem R2_segment_derivatives_integrable
    (J : Set Jet) (hJ : IsOpen J) (Q : SmoothQuasilinearOperator J)
    (u : E2 → ℝ) (k : Fin 2) (h : ℝ) (x : E2)
    (hsegments : ∀ t ∈ Icc (0 : ℝ) 1, jetSegment u k h x t ∈ J) :
    IntegrableOn (fun t => fluxDp Q (jetSegment u k h x t)) (Icc (0 : ℝ) 1) ∧
    IntegrableOn (fun t => fluxDz Q (jetSegment u k h x t)) (Icc (0 : ℝ) 1) ∧
    IntegrableOn (fun t => fluxDx Q (jetSegment u k h x t) (coordinateVector 2 k))
      (Icc (0 : ℝ) 1) ∧
    IntegrableOn (fun t => lowerDp Q (jetSegment u k h x t)) (Icc (0 : ℝ) 1) ∧
    IntegrableOn (fun t => lowerDz Q (jetSegment u k h x t)) (Icc (0 : ℝ) 1) ∧
    IntegrableOn (fun t => lowerDx Q (jetSegment u k h x t) (coordinateVector 2 k))
      (Icc (0 : ℝ) 1) := by
  have hs : ContinuousOn (jetSegment u k h x) (Icc (0 : ℝ) 1) :=
    (QuotientHelpers.jetSegment_continuous u k h x).continuousOn
  have hpA := (QuotientHelpers.p_partial_continuousOn J hJ Q.flux Q.flux_smooth).comp hs hsegments
  have hzA := (QuotientHelpers.z_partial_continuousOn J hJ Q.flux Q.flux_smooth).comp hs hsegments
  have hxA := ((QuotientHelpers.x_partial_continuousOn J hJ Q.flux Q.flux_smooth).comp hs hsegments).clm_apply
    (continuousOn_const (c := coordinateVector 2 k))
  have hpB := (QuotientHelpers.p_partial_continuousOn J hJ Q.lowerOrder Q.lowerOrder_smooth).comp hs hsegments
  have hzB := (QuotientHelpers.z_partial_continuousOn J hJ Q.lowerOrder Q.lowerOrder_smooth).comp hs hsegments
  have hxB := ((QuotientHelpers.x_partial_continuousOn J hJ Q.lowerOrder Q.lowerOrder_smooth).comp hs hsegments).clm_apply
    (continuousOn_const (c := coordinateVector 2 k))
  exact ⟨hpA.integrableOn_compact isCompact_Icc, hzA.integrableOn_compact isCompact_Icc,
    hxA.integrableOn_compact isCompact_Icc, hpB.integrableOn_compact isCompact_Icc,
    hzB.integrableOn_compact isCompact_Icc, hxB.integrableOn_compact isCompact_Icc⟩

theorem R2_segment_flux_and_source_identity
    (J : Set Jet) (hJ : IsOpen J) (Q : SmoothQuasilinearOperator J)
    (u : E2 → ℝ) (k : Fin 2) (h : ℝ) (hh : h ≠ 0) (x : E2)
    (hsegments : ∀ t ∈ Icc (0 : ℝ) 1, jetSegment u k h x t ∈ J) :
    let C := averagedCoefficients Q u k h
    let G := h⁻¹ • (planarGradient u (shift k h x) - planarGradient u x)
    h⁻¹ • (Q.flux (firstJet u (shift k h x)) - Q.flux (firstJet u x)) =
      linearizedFlux C (differenceQuotient u k h) (fun _ => G) x ∧
    (Q.lowerOrder (firstJet u (shift k h x)) - Q.lowerOrder (firstJet u x)) / h =
      linearizedSource C (differenceQuotient u k h) (fun _ => G) x := by
  dsimp only
  constructor
  · rw [QuotientHelpers.segment_coordinate_FTC J hJ Q.flux Q.flux_smooth u k h x hsegments]
    simp [linearizedFlux, averagedCoefficients, fluxDp, fluxDz, fluxDx,
      differenceQuotient, smul_add, smul_smul, hh, div_eq_mul_inv, mul_comm]
  · rw [QuotientHelpers.segment_coordinate_FTC J hJ Q.lowerOrder Q.lowerOrder_smooth u k h x hsegments]
    simp [linearizedSource, averagedCoefficients, lowerDp, lowerDz, lowerDx,
      differenceQuotient, smul_eq_mul, div_eq_mul_inv, add_mul, hh, map_smul, map_sub]
    field_simp [hh]
    <;> ring

end SeifertSurfaces.QuasilinearLocalization
