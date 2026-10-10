import InitialCapTestJetResidual_v458

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
set_option maxHeartbeats 600000
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates L1Independent

local macro "paid_all_tests" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialSeparableTestAE_v457 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.ae_simultaneous_continuous_tests_v457)⟩

local macro "original_test_jet" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialClosedDiscTestJets_v457 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.original_closed_disc_test_jet_v457)⟩

local macro "original_residual" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialCapTestJetResidual_v458 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.original_cap_test_jet_residual_v458)⟩

local macro "paid_residual_cont" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialCapTestJetResidual_v458 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.original_cap_test_jet_residual_continuous_v458)⟩

local macro "paid_residual_native" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialCapTestJetResidual_v458 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.original_cap_test_jet_residual_native_v458)⟩

local macro "paid_fixed_green" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialLocalCapGreen_v457 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.original_local_cap_green_fixed_test_ae_v457)⟩

private theorem original_local_cap_green_all_tests_ae_v460
    (f : E2 → E2) (d : Fin 2 → E2 → E2) (b : ℝ → E2)
    (H1 : ∀ i,H1On (disc 1) (fun x=>f x i) (d i))
    (green : HasGreenBoundaryTrace f d b) (hb : Continuous b)
    (p : E2) (a z : ℝ) (ha : 0 < a) (haz : a < z) (hz : z < 1) :
    ∀ᵐ q ∂volume.restrict (Ioo a z),
      ∀ psi : E2 → ℝ, ContDiff ℝ ∞ psi → ∀ i j : Fin 2,
      (∫ x in planarCap p q,f x i*fderiv ℝ psi x (coordinateVector 2 j)+d i x j*psi x)=
        (q*∫ t in Ioo (-Real.pi) Real.pi,
          (disc 1).indicator (fun x=>f x i*psi x) (p+q•unitCircleParameter t)*unitCircleParameter t j)+
        ∫ t in circlePatch p q,b t i*psi (unitCircleParameter t)*unitCircleParameter t j := by
  classical
  let : CompactSpace (closedDisc 1) := isCompact_iff_compactSpace.mp (isCompact_closedBall (0:E2) 1)
  let J := C(closedDisc 1,ℝ) × (Fin 2 → C(closedDisc 1,ℝ))
  let S : Set J := {u | ∃ psi:E2→ℝ,∃ hpsi:ContDiff ℝ ∞ psi,u=original_test_jet psi hpsi}
  let L (i : Fin 2) : ℝ →L[ℝ] E2 :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight (coordinateVector 2 i)
  have hF : MemLp f 2 (volume.restrict (disc 1)) := by
    have h0 := ((H1 0).2.1).continuousLinearMap_comp (L 0)
    have h1 := ((H1 1).2.1).continuousLinearMap_comp (L 1)
    have he : (fun x=>L 0 (f x 0)+L 1 (f x 1))=f := by
      funext x
      ext i
      fin_cases i <;> simp [L,coordinateVector,EuclideanSpace.single]
    exact he ▸ h0.add h1
  have hpolar := CourantAnalyticB.native_translated_polar_rows (fun _=>f)
    (fun _=>hF.aestronglyMeasurable) (fun _=>hF) p a z ha haz hz
  dsimp only at hpolar
  have hFs : ∀ᵐ q ∂volume.restrict (Ioo a z),
      MemLp (fun t=>(disc 1).indicator f (p+q•unitCircleParameter t)) 2
        (volume.restrict (Ioo (-Real.pi) Real.pi)) := by
    filter_upwards [hpolar.2.2.1] with q hq
    exact (hq.1 0).2.1
  have hpair (i j : Fin 2) : ∀ᵐ q ∂volume.restrict (Ioo a z),
      ∀ u∈S,original_residual f d b p q i j u=0 := by
    apply paid_all_tests (volume.restrict (Ioo a z)) S
      (fun q u=>original_residual f d b p q i j u)
    · filter_upwards [hFs] with q hq
      exact paid_residual_cont f d b H1 hb p q hq i j
    · intro u hu
      obtain ⟨psi,hpsi,rfl⟩ := hu
      filter_upwards [paid_fixed_green f d b H1 green p a z ha haz hz psi hpsi i j] with q hq
      rw [paid_residual_native f d b H1 p q i j psi hpsi]
      linarith
  have hall : ∀ᵐ q ∂volume.restrict (Ioo a z),∀ i j : Fin 2,
      ∀ u∈S,original_residual f d b p q i j u=0 := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    exact hpair i
  filter_upwards [hall] with q hq
  intro psi hpsi i j
  have hz0 := hq i j (original_test_jet psi hpsi) ⟨psi,hpsi,rfl⟩
  rw [paid_residual_native f d b H1 p q i j psi hpsi] at hz0
  linarith

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
