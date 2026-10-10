import B1LocalFluxClassical_v475
import B1CollarWindow_v468

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped Manifold ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
universe v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Smooth calculus for the literal supplied collar density on its actual open
jet tube, including both slope and height variations. -/
theorem actual_graph_jet_calculus_v475 (D : B1OriginalData g J) (s : Circle)
    (W : CollarWindow D s) :
    ContDiffOn ℝ ∞ W.density (jetPoint ⁻¹' W.V) ∧
    ContDiffOn ℝ ∞ W.flux (jetPoint ⁻¹' W.V) ∧
    ContDiffOn ℝ ∞ W.lower (jetPoint ⁻¹' W.V) := by
  have hd : ContDiffOn ℝ ∞ W.density (jetPoint ⁻¹' W.V) := by
    let A : Set Jet := jetPoint ⁻¹' W.V
    have hpoint : ContDiff ℝ ∞ jetPoint := by
      unfold jetPoint
      apply (EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff.comp
      apply contDiff_pi.mpr
      intro i
      fin_cases i
      · exact (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff.comp contDiff_fst
      · exact (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff.comp contDiff_fst
      · exact contDiff_fst.comp contDiff_snd
    have htangent (i : Fin 2) : ContDiff ℝ ∞ (fun j : Jet => jetTangent j.2.2 i) := by
      delta jetTangent
      exact contDiff_const.add
        (((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp (contDiff_snd.comp contDiff_snd)).smul contDiff_const)
    have htensor (a b : Fin 3) : ContDiffOn ℝ ∞ (fun j : Jet => W.metric.tensor (jetPoint j) a b) A :=
      (W.metric.smooth a b).comp hpoint.contDiffOn (fun _ h => h)
    have hgram (i k : Fin 2) : ContDiffOn ℝ ∞ (fun j : Jet => W.gram j i k) A := by
      delta CollarWindow.gram coordinateInner
      apply ContDiffOn.sum
      intro a ha
      apply ContDiffOn.sum
      intro b hb
      exact ((htensor a b).mul
        ((EuclideanSpace.proj (𝕜 := ℝ) a).contDiff.comp_contDiffOn (htangent i).contDiffOn)).mul
        ((EuclideanSpace.proj (𝕜 := ℝ) b).contDiff.comp_contDiffOn (htangent k).contDiffOn)
    have hdet : ContDiffOn ℝ ∞ (fun j : Jet => Matrix.det (W.gram j)) A := by
      simp only [Matrix.det_fin_two]
      exact ((hgram 0 0).mul (hgram 1 1)).sub ((hgram 0 1).mul (hgram 1 0))
    apply hdet.sqrt
    intro j hj
    have hpos : (W.gram j).PosDef := by
      apply Matrix.posDef_iff_dotProduct_mulVec.mpr
      constructor
      · rw [Matrix.isHermitian_iff_isSymm]
        ext i k
        change coordinateInner W.metric.tensor (jetPoint j) (jetTangent j.2.2 k) (jetTangent j.2.2 i) =
          coordinateInner W.metric.tensor (jetPoint j) (jetTangent j.2.2 i) (jetTangent j.2.2 k)
        unfold coordinateInner
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        rw [W.metric.symmetric _ hj b a]
        ring
      · intro p hp
        let v : E3 := (EuclideanSpace.equiv (Fin 3) ℝ).symm
          ![p 0, p 1, j.2.2 0 * p 0 + j.2.2 1 * p 1]
        have hv : v ≠ 0 := by
          intro hv
          apply hp
          funext i
          fin_cases i
          · have := congrArg (fun v : E3 => v 0) hv
            simpa [v] using this
          · have := congrArg (fun v : E3 => v 1) hv
            simpa [v] using this
        have hpos := W.metric.positive _ hj v hv
        have heq : p ⬝ᵥ (W.gram j).mulVec p = coordinateInner W.metric.tensor (jetPoint j) v v := by
          delta CollarWindow.gram jetTangent
          simp [dotProduct, Matrix.mulVec, coordinateInner,
            coordinateVector, v, Fin.sum_univ_two, Fin.sum_univ_three]
          <;> ring
        simpa only [star_trivial, heq] using hpos
    exact ne_of_gt hpos.det_pos
  have hfl : ContDiffOn ℝ ∞ W.flux (jetPoint ⁻¹' W.V) ∧
      ContDiffOn ℝ ∞ W.lower (jetPoint ⁻¹' W.V) := by
    have hpoint : ContDiff ℝ ∞ jetPoint := by
      unfold jetPoint
      apply (EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff.comp
      apply contDiff_pi.mpr
      intro i
      fin_cases i
      · exact (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff.comp contDiff_fst
      · exact (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff.comp contDiff_fst
      · exact contDiff_fst.comp contDiff_snd
    have hA : IsOpen (jetPoint ⁻¹' W.V) := W.V_open.preimage hpoint.continuous
    constructor
    · intro j hj
      apply ContDiffAt.contDiffWithinAt
      have hD := hd.contDiffAt (hA.mem_nhds hj)
      have hpair : ContDiffAt ℝ ∞
          (fun p : Jet × E2 => (p.1.1, p.1.2.1, p.2)) (j,j.2.2) :=
        contDiffAt_fst.fst.prodMk (contDiffAt_fst.snd.fst.prodMk contDiffAt_snd)
      have hpartial : ContDiffAt ℝ ∞
          (fun j : Jet => fderiv ℝ (fun p : E2 => W.density (j.1,j.2.1,p)) j.2.2) j :=
        (hD.comp (j,j.2.2) hpair).fderiv contDiffAt_snd.snd (by simp)
      unfold CollarWindow.flux planarGradient
      exact ContDiffAt.sum (fun i _ => (hpartial.clm_apply contDiffAt_const).smul_const _)
    · intro j hj
      apply ContDiffAt.contDiffWithinAt
      have hD := hd.contDiffAt (hA.mem_nhds hj)
      have hpair : ContDiffAt ℝ ∞
          (fun p : Jet × ℝ => (p.1.1, p.2, p.1.2.2)) (j,j.2.1) :=
        contDiffAt_fst.fst.prodMk (contDiffAt_snd.prodMk contDiffAt_fst.snd.snd)
      have hpartial : ContDiffAt ℝ ∞
          (fun j : Jet => fderiv ℝ (fun z : ℝ => W.density (j.1,z,j.2.2)) j.2.1) j :=
        (hD.comp (j,j.2.1) hpair).fderiv contDiffAt_snd.fst (by simp)
      change ContDiffAt ℝ ∞ (fun j : Jet => -deriv (fun z : ℝ => W.density (j.1, z, j.2.2)) j.2.1) j
      exact (hpartial.clm_apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Jet => (1 : ℝ)) j)).neg
  exact ⟨hd,hfl⟩

/-- The supplied graph residual follows from compactly supported variations of
that very density.  This analytic adapter introduces no alternate coefficients. -/
theorem actual_graph_residual_of_tests_v475 (D : B1OriginalData g J) (s : Circle)
    (W : CollarWindow D s) (O : Set E2) (hO : IsOpen O) (u : E2 → ℝ)
    (hu : ContDiffOn ℝ ∞ u O)
    (hjets : ∀ x ∈ O, jetPoint (x,u x,planarGradient u x) ∈ W.V)
    (hweak : ∀ φ : E2 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ O →
      (∫ x in O, inner ℝ (W.flux (x,u x,planarGradient u x)) (planarGradient φ x) -
        W.lower (x,u x,planarGradient u x) * φ x) = 0) :
    ∀ x ∈ O, W.residual u x = 0 := by
  obtain ⟨hd,hflux,hlower⟩ := actual_graph_jet_calculus_v475 D s W
  have hgrad : ContDiffOn ℝ ∞ (planarGradient u) O := by
    unfold planarGradient
    exact ContDiffOn.sum (fun i _ =>
      ((hu.fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const).smul_const _)
  have hjet : ContDiffOn ℝ ∞ (fun x => (x,u x,planarGradient u x)) O :=
    contDiffOn_id.prodMk (hu.prodMk hgrad)
  have hP : ContDiffOn ℝ ∞ (fun x => W.flux (x,u x,planarGradient u x)) O :=
    hflux.comp hjet hjets
  have hQ : ContinuousOn (fun x => W.lower (x,u x,planarGradient u x)) O :=
    (hlower.comp hjet hjets).continuousOn
  exact native_local_flux_classical_of_tests_v475 O hO _ _
    (fun i => ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp_contDiffOn hP).of_le (by simp))
    hQ hweak

private theorem native_jet_slope_slice_v475 (F : Jet → ℝ) (j : Jet)
    (hf : DifferentiableAt ℝ F j) (p : E2) :
    fderiv ℝ (fun q : E2 => F (j.1,j.2.1,q)) j.2.2 p =
      fderiv ℝ F j (0,0,p) := by
  have hs := (hasFDerivAt_const (𝕜 := ℝ) j.1 j.2.2).prodMk
    ((hasFDerivAt_const (𝕜 := ℝ) j.2.1 j.2.2).prodMk (hasFDerivAt_id (𝕜 := ℝ) j.2.2))
  exact congrArg (fun L : E2 →L[ℝ] ℝ => L p) (hf.hasFDerivAt.comp j.2.2 hs).fderiv

private theorem native_jet_height_slice_v475 (F : Jet → ℝ) (j : Jet)
    (hf : DifferentiableAt ℝ F j) :
    deriv (fun z : ℝ => F (j.1,z,j.2.2)) j.2.1 =
      fderiv ℝ F j (0,1,0) := by
  have hs := (hasFDerivAt_const (𝕜 := ℝ) j.1 j.2.1).prodMk
    ((hasFDerivAt_id (𝕜 := ℝ) j.2.1).prodMk (hasFDerivAt_const (𝕜 := ℝ) j.2.2 j.2.1))
  exact congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) (hf.hasFDerivAt.comp j.2.1 hs).fderiv

/-- A graph test varies height and slope together.  The derivative uses the
source's flux and negative height derivative with their literal signs. -/
theorem actual_graph_density_variation_v475 (D : B1OriginalData g J) (s : Circle)
    (W : CollarWindow D s) (j : Jet)
    (hj : jetPoint j ∈ W.V) (z : ℝ) (p : E2) :
    HasDerivAt (fun t : ℝ => W.density (j.1,j.2.1+t*z,j.2.2+t • p))
      (inner ℝ (W.flux j) p - W.lower j * z) 0 := by
  have hpoint : ContDiff ℝ ∞ jetPoint := by
    unfold jetPoint
    apply (EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff.comp
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff.comp contDiff_fst
    · exact (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff.comp contDiff_fst
    · exact contDiff_fst.comp contDiff_snd
  have hd := (actual_graph_jet_calculus_v475 D s W).1
  have hdiff : DifferentiableAt ℝ W.density j :=
    (hd.contDiffAt ((W.V_open.preimage hpoint.continuous).mem_nhds hj)).differentiableAt (by simp)
  have hcurve : HasDerivAt (fun t : ℝ => (j.1,j.2.1+t*z,j.2.2+t • p))
      (0,z,p) 0 := by
    convert (hasDerivAt_const 0 j.1).prodMk
      (((hasDerivAt_const 0 j.2.1).add ((hasDerivAt_id 0).mul_const z)).prodMk
        ((hasDerivAt_const 0 j.2.2).add ((hasDerivAt_id 0).smul_const p))) using 1 <;> simp
  have hdcurve : HasFDerivAt W.density (fderiv ℝ W.density j)
      (j.1,j.2.1+0*z,j.2.2+(0 : ℝ) • p) := by
    simpa using hdiff.hasFDerivAt
  have hh := hdcurve.comp_hasDerivAt 0 hcurve
  apply hh.congr_deriv
  rw [show ((0,z,p) : Jet) = (0,0,p) + z • (0,1,0) by ext <;> simp]
  rw [map_add,map_smul,← native_jet_slope_slice_v475 W.density j hdiff p,
    ← native_jet_height_slice_v475 W.density j hdiff]
  have hp : p = p 0 • coordinateVector 2 0 + p 1 • coordinateVector 2 1 := by
    ext i
    fin_cases i <;> simp [coordinateVector,EuclideanSpace.single]
  rw [hp,map_add,map_smul,map_smul]
  simp [CollarWindow.flux,CollarWindow.lower,planarGradient,coordinateVector,
    EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_two]
  ring

#print axioms actual_graph_jet_calculus_v475
#print axioms actual_graph_residual_of_tests_v475
#print axioms actual_graph_density_variation_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
