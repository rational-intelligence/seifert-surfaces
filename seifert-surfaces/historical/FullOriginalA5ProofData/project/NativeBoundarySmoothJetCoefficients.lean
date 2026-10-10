import NativeBoundaryFullGradientHolder

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization QuasilinearBootstrap

section
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem native_jet_x_partial_smooth (J : Set Jet) (hJ : IsOpen J)
    (f : Jet → F) (hf : ContDiffOn ℝ ∞ f J) :
    ContDiffOn ℝ ∞ (fun j : Jet => fderiv ℝ (fun x : E2 => f (x, j.2.1, j.2.2)) j.1) J := by
  have hd : ContDiffOn ℝ ∞ (fderiv ℝ f) J := hf.fderiv_of_isOpen hJ (by simp)
  apply (hd.clm_comp (contDiffOn_const (c := ContinuousLinearMap.inl ℝ E2 (ℝ × E2)))).congr
  intro j hj
  exact Helpers.fderiv_x_slice f j ((hf.contDiffAt (hJ.mem_nhds hj)).differentiableAt (by simp))

theorem native_jet_p_partial_smooth (J : Set Jet) (hJ : IsOpen J)
    (f : Jet → F) (hf : ContDiffOn ℝ ∞ f J) :
    ContDiffOn ℝ ∞ (fun j : Jet => fderiv ℝ (fun p : E2 => f (j.1, j.2.1, p)) j.2.2) J := by
  have hd : ContDiffOn ℝ ∞ (fderiv ℝ f) J := hf.fderiv_of_isOpen hJ (by simp)
  apply (hd.clm_comp (contDiffOn_const (c := (ContinuousLinearMap.inr ℝ E2 (ℝ × E2)).comp
      (ContinuousLinearMap.inr ℝ ℝ E2)))).congr
  intro j hj
  exact Helpers.fderiv_p_slice f j ((hf.contDiffAt (hJ.mem_nhds hj)).differentiableAt (by simp))

theorem native_jet_z_partial_smooth (J : Set Jet) (hJ : IsOpen J)
    (f : Jet → F) (hf : ContDiffOn ℝ ∞ f J) :
    ContDiffOn ℝ ∞ (fun j : Jet => fderiv ℝ (fun z : ℝ => f (j.1, z, j.2.2)) j.2.1 1) J := by
  have hd : ContDiffOn ℝ ∞ (fderiv ℝ f) J := hf.fderiv_of_isOpen hJ (by simp)
  have hz := hd.clm_comp (contDiffOn_const (c := (ContinuousLinearMap.inr ℝ E2 (ℝ × E2)).comp
      (ContinuousLinearMap.inl ℝ ℝ E2)))
  apply (hz.clm_apply (contDiffOn_const (c := (1 : ℝ)))).congr
  intro j hj
  rw [Helpers.fderiv_z_slice f j ((hf.contDiffAt (hJ.mem_nhds hj)).differentiableAt (by simp))]

end

/-- The actual classical source, as a smooth function of the original jet. -/
def nativeClassicalSourceJet {J : Set Jet} (Q : SmoothQuasilinearOperator J) (j : Jet) : ℝ :=
  -Q.lowerOrder j - ∑ i : Fin 2,
    (fluxDx Q j (coordinateVector 2 i) i + fluxDz Q j i * j.2.2 i)

def nativeClassicalSourceWithin (ρ : ℝ) {J : Set Jet} (Q : SmoothQuasilinearOperator J)
    (u : E2 → ℝ) (x : E2) : ℝ := nativeClassicalSourceJet Q (firstJetWithin ρ u x)

theorem native_classical_source_jet_smooth (J : Set Jet) (hJ : IsOpen J)
    (Q : SmoothQuasilinearOperator J) : ContDiffOn ℝ ∞ (nativeClassicalSourceJet Q) J := by
  have hx : ContDiffOn ℝ ∞ (fluxDx Q) J := native_jet_x_partial_smooth J hJ Q.flux Q.flux_smooth
  have hz : ContDiffOn ℝ ∞ (fluxDz Q) J := native_jet_z_partial_smooth J hJ Q.flux Q.flux_smooth
  have hxi (i : Fin 2) : ContDiffOn ℝ ∞ (fun j : Jet => fluxDx Q j (coordinateVector 2 i) i) J := by
    simpa only [Function.comp_def, EuclideanSpace.proj, PiLp.proj_apply] using
      (EuclideanSpace.proj i).contDiff.comp_contDiffOn (hx.clm_apply contDiffOn_const)
  have hzi (i : Fin 2) : ContDiffOn ℝ ∞ (fun j : Jet => fluxDz Q j i) J := by
    simpa only [Function.comp_def, EuclideanSpace.proj, PiLp.proj_apply] using
      (EuclideanSpace.proj i).contDiff.comp_contDiffOn hz
  have hpi (i : Fin 2) : ContDiffOn ℝ ∞ (fun j : Jet => j.2.2 i) J := by
    have hp : ContDiffOn ℝ ∞ (fun j : Jet => j.2.2) J := by fun_prop
    simpa only [Function.comp_def, EuclideanSpace.proj, PiLp.proj_apply] using
      (EuclideanSpace.proj i).contDiff.comp_contDiffOn hp
  exact Q.lowerOrder_smooth.neg.sub
    (ContDiffOn.sum (fun i _ => (hxi i).add ((hzi i).mul (hpi i))))

theorem native_principal_source_jet_smooth (J : Set Jet) (hJ : IsOpen J)
    (Q : SmoothQuasilinearOperator J) :
    ContDiffOn ℝ ∞ (fun j : Jet => (fluxDp Q j, nativeClassicalSourceJet Q j)) J :=
  (native_jet_p_partial_smooth J hJ Q.flux Q.flux_smooth).prodMk
    (native_classical_source_jet_smooth J hJ Q)

theorem native_classicalSourceWithin_eq {ρ : ℝ} {J : Set Jet}
    (Q : SmoothQuasilinearOperator J) (u : E2 → ℝ) {x : E2} (hx : x ∈ openHalfDisc ρ) :
    nativeClassicalSourceWithin ρ Q u x = classicalSource Q u x := by
  simp only [nativeClassicalSourceWithin, nativeClassicalSourceJet, classicalSource,
    firstJetWithin_eq_firstJet u hx, firstJet, planarGradientWithin_closedHalfDisc_eq u hx]

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
