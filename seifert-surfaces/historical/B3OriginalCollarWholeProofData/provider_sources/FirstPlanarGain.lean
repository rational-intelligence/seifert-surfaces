import HolderQuotients
import DifferentiatedWeakEquation
import HomogeneousBall
import WeakDivergenceData
import WeakSchauderGain
import Mathlib.Analysis.Matrix.Normed

attribute [-instance] DifferentialGeometry.Tensor0SBundle.instNormedAddCommGroupTensor0SModel

/-! Appendix A.3: actual planar recovery after the separate R4 weak gain.+New theorem bodies are statement obligations only. -/
noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 2000000
open Set MeasureTheory Filter
open scoped Topology BigOperators ContDiff

namespace SeifertSurfaces.QuasilinearBootstrap
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.QuasilinearLocalization
open SeifertSurfaces.QuasilinearProviderBridge

/-- Bounded actual finite derivative jet on an open domain, with one common
Hölder constant for all orders up to m. This includes classical differentiability. -/
def PlanarHolderJetBound (m : ℕ) (u : E2 → ℝ) (B : Set E2)
    (α K : NNReal) : Prop :=
  ContDiffOn ℝ m u B ∧ ∀ q : ℕ, q ≤ m →
    (∀ x ∈ B, ‖iteratedFDeriv ℝ q u x‖ ≤ (K : ℝ)) ∧
    HolderOnWith K α (iteratedFDeriv ℝ q u) B

/-- Produce precisely the raw lifted coefficient field and the same actual
Sobolev witnesses to be consumed by R4. No classical derivative of D_k u is
an input. The lifting constant is the existing liftD, not new abstract data. -/
theorem R4_differentiated_lift_schauder_data
    (Ω : Set E2) (hΩ : IsOpen Ω) (J : Set Jet) (hJ : IsOpen J)
    (Q : SmoothQuasilinearOperator J) (u : E2 → ℝ) (hC1 : ContDiffOn ℝ 1 u Ω)
    (hjets : ∀ x ∈ Ω, firstJet u x ∈ J)
    (hweak : IsWeakDivergenceSolutionOn Ω Q.flux Q.lowerOrder u)
    (x₀ : E2) (r κ M : ℝ) (hr : 0 < r) (T : Set Jet)
    (hball : Metric.closedBall x₀ (4 * r) ⊆ Ω)
    (hT : Convex ℝ T) (hTJ : closure T ⊆ J)
    (hjetsT : ∀ x ∈ Metric.closedBall x₀ (4 * r), firstJet u x ∈ T)
    (hbound : JetTubeBounds Q u x₀ r κ M T)
    (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ r) (K α : NNReal)
    (hα : 0 < α) (hαone : α < 1)
    (hholder : ∀ k : Fin 2,
      HolderOnWith K α (fun x => planarGradient u x k) (Metric.ball x₀ ρ)) :
    ∃ s : ℝ, ∃ H : NNReal, 0 < s ∧ s ≤ ρ / 2 ∧ s ≤ 1 / 2 ∧
      ∀ k : Fin 2,
      ∃ (hw : DeGiorgi.MemW1pWitness 2 (fun x => planarGradient u x k)
          (Metric.ball x₀ ρ))
        (hV : SeifertSurfaces.WeakSchauder.H1Witness
          (liftFunction (fun x => planarGradient u x k))
          (Metric.ball (liftedPoint x₀ 0) s)),
        hV.weakGrad =ᵐ[volume.restrict (Metric.ball (liftedPoint x₀ 0) s)]
          liftGradient hw.weakGrad ∧
        SeifertSurfaces.WeakSchauder.CoefficientBounds
          (liftMatrix (differentiatedCoefficients Q u k)
            (fun x => planarGradient u x k) (liftD κ M M))
          (Metric.ball (liftedPoint x₀ 0) s)
          (min (κ / 2) 1) (3 * liftEntryBound κ M M) ∧
        SeifertSurfaces.WeakSchauder.CoefficientHolder
          (liftMatrix (differentiatedCoefficients Q u k)
            (fun x => planarGradient u x k) (liftD κ M M))
          (Metric.ball (liftedPoint x₀ 0) s) H α ∧
        SeifertSurfaces.WeakSchauder.WeakEquation
          (liftMatrix (differentiatedCoefficients Q u k)
            (fun x => planarGradient u x k) (liftD κ M M)) hV ∧
        ContinuousOn (liftFunction (fun x => planarGradient u x k))
          (Metric.ball (liftedPoint x₀ 0) s) := by
  classical
  let s := min (ρ / 2) (1 / 2)
  have hs : 0 < s := lt_min (by positivity) (by norm_num)
  have hsρ : s ≤ ρ / 2 := min_le_left _ _
  have hs1 : s ≤ 1 / 2 := min_le_right _ _
  have hclosed : Metric.closedBall x₀ (4 * ρ) ⊆ Metric.closedBall x₀ (4 * r) :=
    Metric.closedBall_subset_closedBall (by gcongr)
  have hboundρ : JetTubeBounds Q u x₀ ρ κ M T :=
    ⟨hbound.1, hbound.2.1, fun x hx => hbound.2.2.1 x (hclosed hx), hbound.2.2.2⟩
  have hballρ : Metric.closedBall x₀ (4 * ρ) ⊆ Ω := hclosed.trans hball
  have hjTρ : ∀ x ∈ Metric.closedBall x₀ (4 * ρ), firstJet u x ∈ T :=
    fun x hx => hjetsT x (hclosed hx)
  have hcy : Metric.ball (liftedPoint x₀ 0) s ⊆ cylinder (Metric.ball x₀ ρ) := by
    convert HolderAssembly.ball_in_cylinder x₀ (r := ρ / 2) (R := s)
      (by positivity) hsρ hs1 using 1
    congr 2
    ring
  have hM0 : 0 ≤ M := by linarith [hbound.2.1]
  have hvbound (k : Fin 2) (x : E2) (hx : x ∈ Metric.ball x₀ ρ) :
      |planarGradient u x k| ≤ M := by
    have hk : |planarGradient u x k| ≤ ‖planarGradient u x‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (planarGradient u x) k
    exact hk.trans
        (hboundρ.2.2.1 x ((Metric.ball_subset_closedBall.trans
          (Metric.closedBall_subset_closedBall (by linarith))) hx)).2
  have hcoeffHolder : ∃ H : NNReal, ∀ k : Fin 2,
      SeifertSurfaces.WeakSchauder.CoefficientHolder
        (liftMatrix (differentiatedCoefficients Q u k)
          (fun x => planarGradient u x k) (liftD κ M M))
        (Metric.ball (liftedPoint x₀ 0) s) H α := by
    let B := Metric.closedBall x₀ (ρ / 2)
    have hBρ : B ⊆ Metric.ball x₀ ρ := Metric.closedBall_subset_ball (by linarith)
    have hBΩ : B ⊆ Ω := hBρ.trans
      ((Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))).trans hballρ)
    obtain ⟨Lu, hLu⟩ := (hC1.mono hBΩ).exists_lipschitzOnWith one_ne_zero
      (convex_closedBall _ _) (isCompact_closedBall _ _)
    let Db : NNReal := (Metric.ediam B).toNNReal
    have hDb : ∀ x ∈ B, ∀ y ∈ B, edist x y ≤ (Db : ENNReal) := by
      intro x hx y hy
      dsimp [Db]
      rw [ENNReal.coe_toNNReal (isCompact_closedBall _ _).isBounded.ediam_ne_top]
      exact Metric.edist_le_ediam_of_mem hx hy
    have huH : HolderOnWith (Lu * Db ^ ((1 : ℝ) - (α : ℝ))) α u B :=
      hLu.holderOnWith.of_le hDb hαone.le
    have hxH : HolderOnWith (Db ^ ((1 : ℝ) - (α : ℝ))) α (fun x : E2 => x) B := by
      change HolderOnWith (Db ^ ((1 : ℝ) - (α : ℝ))) α id B
      simpa only [NNReal.coe_one, one_mul, id_eq] using ((LipschitzWith.id.holderWith.holderOnWith B).of_le hDb hαone.le)
    let Lg : (Fin 2 → ℝ) →L[ℝ] E2 :=
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.toContinuousLinearMap
    have hgPi : HolderOnWith K α (fun x : E2 => fun i : Fin 2 => planarGradient u x i) B := by
      intro x hx y hy
      have hd : dist (fun i : Fin 2 => planarGradient u x i)
          (fun i : Fin 2 => planarGradient u y i) ≤ (K : ℝ) * dist x y ^ (α : ℝ) := by
        rw [dist_eq_norm]
        apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
        intro i
        simpa only [Pi.sub_apply, ← dist_eq_norm] using (hholder i).dist_le (hBρ hx) (hBρ hy)
      simpa only [edist_dist, ENNReal.ofReal_mul K.coe_nonneg,
        ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,
        ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hd
    have hgH : HolderOnWith (‖Lg‖₊ * K) α (planarGradient u) B := by
      have hp := Lg.lipschitzWith.holderWith.comp_holderOnWith hgPi
      simp only [NNReal.coe_one, NNReal.rpow_one, one_mul, Function.comp_def] at hp
      have he : (fun x : E2 => Lg (fun i : Fin 2 => planarGradient u x i)) = planarGradient u := by
        funext x
        ext i
        rfl
      simpa only [he] using hp
    have hprod {X F G : Type} [PseudoMetricSpace X] [NormedAddCommGroup F] [NormedAddCommGroup G]
        {A : Set X} {f : X → F} {g : X → G} {C D : NNReal}
        (hf : HolderOnWith C α f A) (hg : HolderOnWith D α g A) :
        HolderOnWith (C + D) α (fun x => (f x, g x)) A := by
      intro x hx y hy
      have hr : dist (f x, g x) (f y, g y) ≤ ((C + D : NNReal) : ℝ) * dist x y ^ (α : ℝ) := by
        rw [Prod.dist_eq]
        apply max_le
        · exact (hf.dist_le hx hy).trans (mul_le_mul_of_nonneg_right
            (by simpa only [NNReal.coe_add] using le_add_of_nonneg_right D.coe_nonneg)
            (Real.rpow_nonneg dist_nonneg _))
        · exact (hg.dist_le hx hy).trans (mul_le_mul_of_nonneg_right
            (by simpa only [NNReal.coe_add] using le_add_of_nonneg_left C.coe_nonneg)
            (Real.rpow_nonneg dist_nonneg _))
      simpa only [edist_dist, ENNReal.ofReal_mul (NNReal.coe_nonneg _),
        ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,
        ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hr
    have hjH := hprod hxH (hprod huH hgH)
    let P : E3 →L[ℝ] E2 :=
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.pi (fun i => EuclideanSpace.proj (Fin.castSucc i)))
    have hP (y : E3) : P y = planarPart y := by ext i; fin_cases i <;> rfl
    let Y := Metric.closedBall (liftedPoint x₀ 0) s
    have hmaps : MapsTo P Y B := by
      intro y hy
      have hn := HolderAssembly.planar_part_norm_le (y - liftedPoint x₀ 0)
      rw [HolderAssembly.planar_part_sub, HolderAssembly.planar_lift_zero] at hn
      rw [hP, Metric.mem_closedBall, dist_eq_norm]
      have hy0 : ‖y - liftedPoint x₀ 0‖ ≤ s := by
        simpa only [Y, Metric.mem_closedBall, dist_eq_norm] using hy
      exact hn.trans (hy0.trans hsρ)
    let Dy : NNReal := (Metric.ediam Y).toNNReal
    have hid : HolderOnWith (Dy ^ ((1 : ℝ) - (α : ℝ))) α (fun y : E3 => y) Y := by
      change HolderOnWith (Dy ^ ((1 : ℝ) - (α : ℝ))) α id Y
      simpa only [NNReal.coe_one, one_mul, id_eq] using (LipschitzWith.id.holderWith.holderOnWith Y).of_le
        (D := Dy) (fun y hy z hz => by
          dsimp [Dy]
          rw [ENNReal.coe_toNNReal (isCompact_closedBall _ _).isBounded.ediam_ne_top]
          exact Metric.edist_le_ediam_of_mem hy hz) hαone.le
    let U : Set (E3 × Jet × ℝ) := {w | w.2.1 ∈ J}
    have hU : IsOpen U := hJ.preimage (by fun_prop)
    have hDf : ContDiffOn ℝ 1 (fun w : E3 × Jet × ℝ => fderiv ℝ Q.flux w.2.1) U :=
      (Q.flux_smooth.fderiv_of_isOpen hJ (by simp)).comp
        (by fun_prop) (fun _ hw => hw)
    have hDb : ContDiffOn ℝ 1 (fun w : E3 × Jet × ℝ => fderiv ℝ Q.lowerOrder w.2.1) U :=
      (Q.lowerOrder_smooth.fderiv_of_isOpen hJ (by simp)).comp
        (by fun_prop) (fun _ hw => hw)
    have hf (ζ : Jet) (i : Fin 2) : ContDiffOn ℝ 1
        (fun w : E3 × Jet × ℝ => (fderiv ℝ Q.flux w.2.1 ζ) i) U := by
      simpa only [Function.comp_def, EuclideanSpace.proj, PiLp.proj_apply] using
        (EuclideanSpace.proj i).contDiff.comp_contDiffOn (hDf.clm_apply contDiffOn_const)
    have hb (ζ : Jet) : ContDiffOn ℝ 1
        (fun w : E3 × Jet × ℝ => fderiv ℝ Q.lowerOrder w.2.1 ζ) U :=
      hDb.clm_apply contDiffOn_const
    have hv : ContDiffOn ℝ 1 (fun w : E3 × Jet × ℝ => w.2.2) U := by fun_prop
    have hy : ContDiffOn ℝ 1 (fun w : E3 × Jet × ℝ => w.1 2) U := by fun_prop
    letI : NormedAddCommGroup (Matrix (Fin 3) (Fin 3) ℝ) := Matrix.normedAddCommGroup
    letI : NormedSpace ℝ (Matrix (Fin 3) (Fin 3) ℝ) := Matrix.normedSpace
    let F (k : Fin 2) (w : E3 × Jet × ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
      !![(fderiv ℝ Q.flux w.2.1 (0, (0, coordinateVector 2 0))) 0,
        (fderiv ℝ Q.flux w.2.1 (0, (0, coordinateVector 2 1))) 0,
        w.2.2 * (fderiv ℝ Q.flux w.2.1 (0, (1, 0))) 0 +
          (fderiv ℝ Q.flux w.2.1 (coordinateVector 2 k, (0, 0))) 0;
        (fderiv ℝ Q.flux w.2.1 (0, (0, coordinateVector 2 0))) 1,
        (fderiv ℝ Q.flux w.2.1 (0, (0, coordinateVector 2 1))) 1,
        w.2.2 * (fderiv ℝ Q.flux w.2.1 (0, (1, 0))) 1 +
          (fderiv ℝ Q.flux w.2.1 (coordinateVector 2 k, (0, 0))) 1;
        w.1 2 * fderiv ℝ Q.lowerOrder w.2.1 (0, (0, coordinateVector 2 0)),
        w.1 2 * fderiv ℝ Q.lowerOrder w.2.1 (0, (0, coordinateVector 2 1)),
        liftD κ M M + w.1 2 * (fderiv ℝ Q.lowerOrder w.2.1 (0, (1, 0)) * w.2.2 +
          fderiv ℝ Q.lowerOrder w.2.1 (coordinateVector 2 k, (0, 0)))]
    have hF (k : Fin 2) : ContDiffOn ℝ 1 (F k) U := by
      apply contDiffOn_pi.mpr
      intro i
      apply contDiffOn_pi.mpr
      intro j
      fin_cases i <;> fin_cases j <;> dsimp [F]
      all_goals first
      | exact hf _ _
      | exact (hv.mul (hf _ _)).add (hf _ _)
      | exact hy.mul (hb _)
      | exact contDiffOn_const.add (hy.mul (((hb _).mul hv).add (hb _)))
    let G (k : Fin 2) (y : E3) : E3 × Jet × ℝ := (y, firstJet u (P y), planarGradient u (P y) k)
    have hGH (k : Fin 2) : ∃ C : NNReal, HolderOnWith C α (G k) Y := by
      have hJH := hjH.comp (P.lipschitzWith.holderWith.holderOnWith Y) hmaps
      have hvH := ((hholder k).mono hBρ).comp (P.lipschitzWith.holderWith.holderOnWith Y) hmaps
      simp only [mul_one, Function.comp_def] at hJH hvH
      exact ⟨_, hprod hid (hprod hJH hvH)⟩
    have hGF (k : Fin 2) : ∃ C : NNReal, HolderOnWith C α
        (liftMatrix (differentiatedCoefficients Q u k)
          (fun x => planarGradient u x k) (liftD κ M M)) Y := by
      obtain ⟨C, hG⟩ := hGH k
      have hc : IsCompact (G k '' Y) :=
        (isCompact_closedBall _ _).image_of_continuousOn (hG.continuousOn hα)
      have hGU : G k '' Y ⊆ U := by
        rintro w ⟨y, hy, rfl⟩
        exact hjets _ (hBΩ (hmaps hy))
      have hlocal : LocallyLipschitzOn U (F k) := by
        intro w hw
        obtain ⟨L, V, hV, hL⟩ := ((hF k).contDiffAt (hU.mem_nhds hw)).exists_lipschitzOnWith
        exact ⟨L, V, mem_nhdsWithin_of_mem_nhds hV, hL⟩
      obtain ⟨L, hL⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hc (hlocal.mono hGU)
      have hcomp := hL.holderOnWith.comp hG (fun y hy => mem_image_of_mem (G k) hy)
      simp only [NNReal.coe_one, NNReal.rpow_one, one_mul] at hcomp
      refine ⟨L * C, ?_⟩
      have he (y : E3) (hy : y ∈ Y) : F k (G k y) =
          liftMatrix (differentiatedCoefficients Q u k)
            (fun x => planarGradient u x k) (liftD κ M M) y := by
        have hq := (Q.flux_smooth.contDiffAt (hJ.mem_nhds (hjets _ (hBΩ (hmaps hy))))).differentiableAt (by simp)
        have hl := (Q.lowerOrder_smooth.contDiffAt (hJ.mem_nhds (hjets _ (hBΩ (hmaps hy))))).differentiableAt (by simp)
        rw [hP] at hq hl
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp only [F, G, hP, liftMatrix, differentiatedCoefficients, fluxDp, fluxDx, fluxDz,
            lowerDp, lowerDx, lowerDz, Helpers.fderiv_p_slice _ _ hq,
            Helpers.fderiv_x_slice _ _ hq, Helpers.fderiv_z_slice _ _ hq,
            Helpers.fderiv_p_slice _ _ hl, Helpers.fderiv_x_slice _ _ hl,
            Helpers.fderiv_z_slice _ _ hl, ContinuousLinearMap.comp_apply,
            ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply,
            Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
            PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, mul_comm]
        all_goals first | rfl | ring
      intro y hy z hz
      simpa only [Function.comp_def, he y hy, he z hz] using hcomp y hy z hz
    choose Ck hCk using hGF
    let H := Ck 0 + Ck 1
    refine ⟨H, ?_⟩
    intro k i j y hy z hz
    have hk : Ck k ≤ H := by fin_cases k <;> simp [H]
    have hr := ((hCk k).mono_const hk).dist_le (Metric.ball_subset_closedBall hy) (Metric.ball_subset_closedBall hz)
    have hn : |liftMatrix (differentiatedCoefficients Q u k) (fun x => planarGradient u x k) (liftD κ M M) y i j -
        liftMatrix (differentiatedCoefficients Q u k) (fun x => planarGradient u x k) (liftD κ M M) z i j| ≤
        (H : ℝ) * dist y z ^ (α : ℝ) := by
      have h1 := norm_le_pi_norm (liftMatrix (differentiatedCoefficients Q u k) (fun x => planarGradient u x k) (liftD κ M M) y -
        liftMatrix (differentiatedCoefficients Q u k) (fun x => planarGradient u x k) (liftD κ M M) z) i
      have h2 := norm_le_pi_norm ((liftMatrix (differentiatedCoefficients Q u k) (fun x => planarGradient u x k) (liftD κ M M) y -
        liftMatrix (differentiatedCoefficients Q u k) (fun x => planarGradient u x k) (liftD κ M M) z) i) j
      have he : |liftMatrix (differentiatedCoefficients Q u k) (fun x => planarGradient u x k) (liftD κ M M) y i j -
          liftMatrix (differentiatedCoefficients Q u k) (fun x => planarGradient u x k) (liftD κ M M) z i j| ≤
          ‖liftMatrix (differentiatedCoefficients Q u k) (fun x => planarGradient u x k) (liftD κ M M) y -
            liftMatrix (differentiatedCoefficients Q u k) (fun x => planarGradient u x k) (liftD κ M M) z‖ := by
        convert h2.trans h1 using 1 <;> rfl
      exact he.trans (by simpa only [dist_eq_norm] using hr)
    simpa only [edist_dist, Real.dist_eq, ENNReal.ofReal_mul H.coe_nonneg,
      ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,
      ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hn
  obtain ⟨H, hH⟩ := hcoeffHolder
  refine ⟨s, H, hs, hsρ, hs1, ?_⟩
  intro k
  let C := differentiatedCoefficients Q u k
  let v : E2 → ℝ := fun x => planarGradient u x k
  have hC : SeifertSurfaces.QuasilinearLocalization.CoefficientBounds
      (Metric.ball x₀ ρ) C κ M :=
    EnergyHelpers.differentiated_coefficients_bounds J Q u x₀ ρ κ M hρ T hjTρ hboundρ k
  have hcont := EnergyHelpers.differentiated_coefficients_continuous Ω hΩ J hJ Q u hC1 hjets k
  have hBΩ : Metric.ball x₀ ρ ⊆ Ω :=
    (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))).trans hballρ
  have hmeas : CoefficientMeasurableOn (Metric.ball x₀ ρ) C :=
    ⟨(hcont.1.mono hBΩ).aestronglyMeasurable Metric.isOpen_ball.measurableSet,
      (hcont.2.1.mono hBΩ).aestronglyMeasurable Metric.isOpen_ball.measurableSet,
      (hcont.2.2.1.mono hBΩ).aestronglyMeasurable Metric.isOpen_ball.measurableSet,
      (hcont.2.2.2.1.mono hBΩ).aestronglyMeasurable Metric.isOpen_ball.measurableSet,
      (hcont.2.2.2.2.1.mono hBΩ).aestronglyMeasurable Metric.isOpen_ball.measurableSet,
      (hcont.2.2.2.2.2.mono hBΩ).aestronglyMeasurable Metric.isOpen_ball.measurableSet⟩
  have heq : ProviderLinearWeakEquation (Metric.ball x₀ ρ) C v :=
    R2_differentiated_weak_equation Ω hΩ J hJ Q u hC1 hjets hweak x₀ ρ κ M hρ T
      hballρ hT hTJ hjTρ hboundρ k
  let hw := heq.1.someWitness
  let hV := (SeifertSurfaces.QuasilinearProviderBridge.Helpers.liftWitness Metric.isOpen_ball
    Metric.isBounded_ball hw).restrict Metric.isOpen_ball hcy
  have hentry := R3_lift_entries_bounded (Metric.ball x₀ ρ) C v κ M M
    hbound.1 hbound.2.1 hM0 hC (hvbound k)
  have hbds : SeifertSurfaces.WeakSchauder.CoefficientBounds
      (liftMatrix C v (liftD κ M M)) (Metric.ball (liftedPoint x₀ 0) s)
      (min (κ / 2) 1) (3 * liftEntryBound κ M M) := by
    constructor
    · intro i j
      exact (SeifertSurfaces.QuasilinearProviderBridge.Helpers.liftMatrix_aemeasurable
        Metric.isOpen_ball C v (liftD κ M M) hmeas hw.memLp i j).mono_measure
          (Measure.restrict_mono_set volume hcy)
    · intro y hy ξ
      have hc := R3_lift_coercive (Metric.ball x₀ ρ) C v κ M M hbound.1 hbound.2.1 hM0
        hC (hvbound k) y (hcy hy) ξ
      have hn := HolderAssembly.planar_part_norm_sq ξ
      have hminκ := min_le_left (κ / 2) 1
      have hmin1 := min_le_right (κ / 2) 1
      have hp := mul_le_mul_of_nonneg_right hminκ (sq_nonneg ‖planarPart ξ‖)
      have hv := mul_le_mul_of_nonneg_right hmin1 (sq_nonneg (ξ 2))
      rw [real_inner_comm]
      change min (κ / 2) 1 * ‖ξ‖ ^ 2 ≤ inner ℝ (matrixAction _ ξ) ξ
      nlinarith
    · intro y hy ξ η
      change |inner ℝ (matrixAction _ ξ) η| ≤ _
      have hnorm := SeifertSurfaces.QuasilinearProviderBridge.Helpers.matrixAction_norm_le_of_entries
        _ _ hentry.1 (hentry.2 y (hcy hy)) ξ
      exact (abs_real_inner_le_norm _ _).trans
        (by simpa only [mul_assoc] using (mul_le_mul_of_nonneg_right hnorm (norm_nonneg η)))
  have hraw := R3_lift_provider_weak_equation (Metric.ball x₀ ρ) Metric.isOpen_ball
    Metric.isBounded_ball C hmeas κ M hC v heq hw (liftD κ M M)
  have hsmall := SeifertSurfaces.QuasilinearProviderBridge.Helpers.liftWeakEquation_restrict hcy hraw
  have hsmooth : SeifertSurfaces.WeakSchauder.SmoothWeakEquation
      (liftMatrix C v (liftD κ M M)) hV.weakGrad (Metric.ball (liftedPoint x₀ 0) s) := by
    intro φ hφ hcompact hsub
    have hi := hsmall φ hφ hcompact hsub
    have he (y : E3) : inner ℝ
        (matrixAction (liftMatrix C v (liftD κ M M) y) (liftGradient hw.weakGrad y))
        (gradient3 φ y) = ∑ i : Fin 3,
          DeGiorgi.matMulE (liftMatrix C v (liftD κ M M) y) (hV.weakGrad y) i *
            fderiv ℝ φ y (EuclideanSpace.single i 1) := by
      change inner ℝ (matrixAction _ (liftGradient hw.weakGrad y)) (gradient3 φ y) = _
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
      apply Finset.sum_congr rfl
      intro i _
      have hg : gradient3 φ y i = fderiv ℝ φ y (EuclideanSpace.single i 1) := by
        fin_cases i <;> simp [gradient3, Fin.sum_univ_succ, coordinateVector, EuclideanSpace.single]
      rw [hg]
      change _ * (matrixAction _ (liftGradient hw.weakGrad y)) i =
        (matrixAction _ (liftGradient hw.weakGrad y)) i * _
      ring
    simpa only [he] using hi
  have hveq := (SeifertSurfaces.WeakSchauder.smooth_tests_iff_H01_tests (liftedPoint x₀ 0)
    s (min (κ / 2) 1) (3 * liftEntryBound κ M M) hs _ hbds _ hV).mp hsmooth
  have hvcont : ContinuousOn v (Metric.ball x₀ ρ) :=
    ((EuclideanSpace.proj k).continuous.continuousOn.comp
      (SeifertSurfaces.QuasilinearLocalization.Helpers.gradient_continuousOn Ω hΩ u hC1)
      (mapsTo_univ _ _)).mono hBΩ
  exact ⟨hw, hV, Filter.EventuallyEq.rfl, hbds, hH k, hveq,
    (HolderAssembly.lift_continuous _ v hvcont).mono hcy⟩

/-- Restrict the actual lifted C1 solution to the zero slice and identify its
classical derivative there. This transfers regularity to the supplied v. -/
theorem R4_zero_slice_derivative_recovery
    (v : E2 → ℝ) (x₀ : E2) (R : ℝ) (hR : 0 < R) (K β : NNReal)
    (hβ : 0 < β) (hβone : β < 1)
    (hC1 : ContDiffOn ℝ 1 (liftFunction v) (Metric.ball (liftedPoint x₀ 0) R))
    (hholder : HolderOnWith K β (fderiv ℝ (liftFunction v))
      (Metric.ball (liftedPoint x₀ 0) R)) :
    ContDiffOn ℝ 1 v (Metric.ball x₀ R) ∧
      (∀ x ∈ Metric.ball x₀ R, ∀ ξ : E2,
        fderiv ℝ v x ξ =
          fderiv ℝ (liftFunction v) (liftedPoint x 0) (liftedPoint ξ 0)) ∧
      ∃ K' : NNReal, HolderOnWith K' β (fderiv ℝ v) (Metric.ball x₀ R) := by
  let L : E2 →L[ℝ] E3 :=
    { toFun := fun x => liftedPoint x 0
      map_add' := by intro x y; ext i; fin_cases i <;> simp [liftedPoint]
      map_smul' := by intro c x; ext i; fin_cases i <;> simp [liftedPoint]
      cont := by unfold liftedPoint; fun_prop }
  have hL (x : E2) : L x = liftedPoint x 0 := rfl
  have hmaps : MapsTo L (Metric.ball x₀ R) (Metric.ball (liftedPoint x₀ 0) R) := by
    intro x hx
    simpa only [Metric.mem_ball, hL, HolderAssembly.lifted_zero_distance] using hx
  have heq : (fun x => liftFunction v (L x)) = v := by
    funext x
    simp only [hL, liftFunction, HolderAssembly.planar_lift_zero,
      HolderAssembly.vertical_lift_zero, add_zero]
  have hvC1 : ContDiffOn ℝ 1 v (Metric.ball x₀ R) := by
    rw [← heq]
    exact hC1.comp L.contDiff.contDiffOn hmaps
  have hder (x : E2) (hx : x ∈ Metric.ball x₀ R) :
      fderiv ℝ v x = (fderiv ℝ (liftFunction v) (L x)).comp L := by
    conv_lhs => rw [← heq]
    exact ((hC1.contDiffAt (Metric.isOpen_ball.mem_nhds (hmaps hx))).differentiableAt
      (by simp)).hasFDerivAt.comp x L.hasFDerivAt |>.fderiv
  have hLip : LipschitzWith 1 L := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [hL, HolderAssembly.lifted_zero_distance, NNReal.coe_one, one_mul, le_refl]
  have hsliced : HolderOnWith K β
      (fun x => fderiv ℝ (liftFunction v) (L x)) (Metric.ball x₀ R) := by
    simpa only [NNReal.one_rpow, mul_one, Function.comp_def] using
      hholder.comp (hLip.holderWith.holderOnWith _) hmaps
  let P : (E3 →L[ℝ] ℝ) →L[ℝ] E2 →L[ℝ] ℝ :=
    (ContinuousLinearMap.compL ℝ E2 E3 ℝ).flip L
  have hP (A : E3 →L[ℝ] ℝ) : P A = A.comp L := rfl
  refine ⟨hvC1, ?_, ‖P‖₊ * K, ?_⟩
  · intro x hx ξ
    rw [hder x hx]
    rfl
  · have hp := P.lipschitz.holderWith.comp_holderOnWith hsliced
    simp only [NNReal.coe_one, NNReal.rpow_one, one_mul, Function.comp_def] at hp
    intro x hx y hy
    simpa only [hP, ← hder x hx, ← hder y hy] using hp x hx y hy

/-- Recover the actual second Fréchet derivative of u from all actual planar
first derivatives; no unrelated a.e. smooth representative is substituted. -/
theorem R4_planar_second_derivative_recovery
    (u : E2 → ℝ) (x₀ : E2) (R : ℝ) (hR : 0 < R) (K β : NNReal)
    (hβ : 0 < β) (hβone : β < 1)
    (hC1 : ContDiffOn ℝ 1 u (Metric.ball x₀ R))
    (hgradC1 : ∀ k : Fin 2,
      ContDiffOn ℝ 1 (fun x => planarGradient u x k) (Metric.ball x₀ R))
    (hgradHolder : ∀ k : Fin 2,
      HolderOnWith K β (fderiv ℝ (fun x => planarGradient u x k))
        (Metric.ball x₀ R)) :
    ContDiffOn ℝ 2 u (Metric.ball x₀ R) ∧
      ∃ K' : NNReal,
        HolderOnWith K' β (iteratedFDeriv ℝ 2 u) (Metric.ball x₀ R) := by
  classical
  let p (k : Fin 2) : E2 →L[ℝ] ℝ := EuclideanSpace.proj k
  have hrep : fderiv ℝ u = fun x => ∑ k : Fin 2, planarGradient u x k • p k := by
    funext x
    ext ξ
    rw [← R1_planarGradient_pairing u x ξ]
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, p]
    simp [PiLp.inner_apply, EuclideanSpace.proj, mul_comm]
  have hdu : ContDiffOn ℝ 1 (fderiv ℝ u) (Metric.ball x₀ R) := by
    rw [hrep]
    exact ContDiffOn.sum (fun k _ => (hgradC1 k).smul_const (p k))
  have hu2 : ContDiffOn ℝ 2 u (Metric.ball x₀ R) := by
    apply (contDiffOn_succ_iff_fderiv_of_isOpen (n := 1) Metric.isOpen_ball).mpr
    exact ⟨hC1.differentiableOn (by simp), by simp, hdu⟩
  let T : (Fin 2 → E2 →L[ℝ] ℝ) →L[ℝ] E2 →L[ℝ] E2 →L[ℝ] ℝ :=
    ∑ k : Fin 2,
      ((ContinuousLinearMap.smulRightL ℝ E2 (E2 →L[ℝ] ℝ)).flip (p k)).comp
        (ContinuousLinearMap.proj k)
  let G (x : E2) : Fin 2 → E2 →L[ℝ] ℝ :=
    fun k => fderiv ℝ (fun y => planarGradient u y k) x
  have hT (x : E2) (hx : x ∈ Metric.ball x₀ R) :
      fderiv ℝ (fderiv ℝ u) x = T (G x) := by
    rw [hrep]
    rw [fderiv_fun_sum (fun k _ =>
      ((hgradC1 k).contDiffAt (Metric.isOpen_ball.mem_nhds hx)).differentiableAt
        (by simp) |>.smul_const (p k))]
    simp only [fderiv_smul_const
      (((hgradC1 _).contDiffAt (Metric.isOpen_ball.mem_nhds hx)).differentiableAt
        (by simp))]
    rfl
  have hG : HolderOnWith K β G (Metric.ball x₀ R) := by
    intro x hx y hy
    have hn : dist (G x) (G y) ≤ (K : ℝ) * dist x y ^ (β : ℝ) := by
      rw [dist_eq_norm]
      apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
      intro k
      simpa only [G, Pi.sub_apply, ← dist_eq_norm] using (hgradHolder k).dist_le hx hy
    rw [edist_dist, edist_dist,
      ENNReal.ofReal_rpow_of_nonneg (dist_nonneg) β.coe_nonneg,
      ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul K.coe_nonneg]
    exact ENNReal.ofReal_le_ofReal hn
  have hH : HolderOnWith (‖T‖₊ * K) β (fderiv ℝ (fderiv ℝ u))
      (Metric.ball x₀ R) := by
    have ht := T.lipschitzWith.holderWith.comp_holderOnWith hG
    simp only [NNReal.coe_one, NNReal.rpow_one, one_mul, Function.comp_def] at ht
    intro x hx y hy
    simpa only [← hT x hx, ← hT y hy] using ht x hx y hy
  let S : (E2 →L[ℝ] E2 →L[ℝ] ℝ) →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E2) ℝ :=
    ((continuousMultilinearCurryFin1 ℝ E2 (E2 →L[ℝ] ℝ)).symm.trans
    (continuousMultilinearCurryRightEquiv' ℝ 1 E2 ℝ).symm).toContinuousLinearMap
  have hS (x : E2) : iteratedFDeriv ℝ 2 u x = S (fderiv ℝ (fderiv ℝ u) x) := by
    ext ξ
    rw [iteratedFDeriv_two_apply]
    simp [S, Fin.init]
  refine ⟨hu2, ‖S‖₊ * (‖T‖₊ * K), ?_⟩
  have hs := S.lipschitzWith.holderWith.comp_holderOnWith hH
  simp only [NNReal.coe_one, NNReal.rpow_one, one_mul, Function.comp_def] at hs
  intro x hx y hy
  simpa only [← hS x, ← hS y] using hs x hx y hy

/-- Early application bridge: R1-R3 and the independent R4 gain yield a
buffered C2,beta neighborhood of the original C1 weak solution. -/
theorem R4_first_planar_gain
    (Ω : Set E2) (hΩ : IsOpen Ω) (J : Set Jet) (hJ : IsOpen J)
    (Q : SmoothQuasilinearOperator J) (u : E2 → ℝ) (hC1 : ContDiffOn ℝ 1 u Ω)
    (hjets : ∀ x ∈ Ω, firstJet u x ∈ J)
    (hweak : IsWeakDivergenceSolutionOn Ω Q.flux Q.lowerOrder u)
    (x₀ : E2) (r κ M : ℝ) (hr : 0 < r) (T : Set Jet)
    (hball : Metric.closedBall x₀ (4 * r) ⊆ Ω)
    (hT : Convex ℝ T) (hTJ : closure T ⊆ J)
    (hjetsT : ∀ x ∈ Metric.closedBall x₀ (4 * r), firstJet u x ∈ T)
    (hbound : JetTubeBounds Q u x₀ r κ M T) :
    ∃ s : ℝ, ∃ K β : NNReal, 0 < s ∧ 4 * s ≤ r ∧ 0 < β ∧ β < 1 ∧
      PlanarHolderJetBound 2 u (Metric.ball x₀ (2 * s)) β K := by
  classical
  obtain ⟨ρ, K, α, hρ, hρr, hα, hαone, hh⟩ := R3_local_holder_gradient
    Ω hΩ J hJ Q u hC1 hjets hweak x₀ r κ M hr T hball hT hTJ hjetsT hbound
  obtain ⟨S, H, hS, hSρ, hS1, hd⟩ := R4_differentiated_lift_schauder_data
    Ω hΩ J hJ Q u hC1 hjets hweak x₀ r κ M hr T hball hT hTJ hjetsT hbound
    ρ hρ hρr K α hα hαone hh
  have hκ : 0 < min (κ / 2) 1 := lt_min (by linarith [hbound.1]) (by norm_num)
  have hκΛ : min (κ / 2) 1 ≤ 3 * liftEntryBound κ M M := by
    have hM := hbound.2.1
    have hκ0 := hbound.1
    have hM0 : 0 ≤ M := by linarith
    have hD : 0 ≤ liftD κ M M := by unfold liftD; positivity
    have : 1 ≤ liftEntryBound κ M M := by unfold liftEntryBound; nlinarith
    exact (min_le_right _ _).trans (by linarith)
  obtain ⟨A, hA, hgain⟩ := SeifertSurfaces.WeakSchauder.weak_divergence_schauder_gain_from_L2
    (min (κ / 2) 1) (3 * liftEntryBound κ M M) S hκ hκΛ hS H α hα hαone
  have hb : 0 < α / 2 := by positivity
  have hb1 : α / 2 < 1 := (half_lt_self hα).trans hαone
  have hrec (k : Fin 2) : ContDiffOn ℝ 1 (fun x => planarGradient u x k)
      (Metric.ball x₀ (S / 2)) ∧ ∃ Ck : NNReal,
      HolderOnWith Ck (α / 2) (fderiv ℝ (fun x => planarGradient u x k))
        (Metric.ball x₀ (S / 2)) := by
    obtain ⟨hw, hv, hgrad, ha, hah, he, hc⟩ := hd k
    obtain ⟨hc1, _, Ck, _, hder⟩ := hgain (liftedPoint x₀ 0) _ ha hah _ hv hc he
    have hs := R4_zero_slice_derivative_recovery _ x₀ (S / 2) (by linarith) Ck
      (α / 2) hb hb1 hc1 hder
    exact ⟨hs.1, hs.2.2⟩
  choose Ck hCk using fun k => (hrec k).2
  let C := ∑ k : Fin 2, Ck k
  have hKk (k : Fin 2) : Ck k ≤ C :=
    Finset.single_le_sum (fun _ _ => by positivity) (Finset.mem_univ k)
  have hBΩ : Metric.ball x₀ (S / 2) ⊆ Ω := by
    apply Metric.ball_subset_closedBall.trans
    apply (Metric.closedBall_subset_closedBall ?_).trans hball
    linarith
  obtain ⟨hc2, K2, hjet2⟩ := R4_planar_second_derivative_recovery u x₀ (S / 2)
    (by linarith) C (α / 2) hb hb1 (hC1.mono hBΩ) (fun k => (hrec k).1)
    (fun k => (hCk k).mono_const (hKk k))
  let s := S / 16
  have hs : 0 < s := by dsimp [s]; positivity
  have hsmall : 4 * s ≤ r := by dsimp [s]; linarith
  let B := Metric.closedBall x₀ (2 * s)
  have hB : B ⊆ Metric.ball x₀ (S / 2) :=
    Metric.closedBall_subset_ball (by dsimp [s]; linarith)
  have hcc := isCompact_closedBall x₀ (2 * s)
  have hq (q : Fin 3) : ∃ Cq : NNReal,
      (∀ x ∈ B, ‖iteratedFDeriv ℝ (q : ℕ) u x‖ ≤ (Cq : ℝ)) ∧
      HolderOnWith Cq (α / 2) (iteratedFDeriv ℝ (q : ℕ) u) B := by
    rcases q with ⟨q, hqbound⟩
    have hc : ContinuousOn (iteratedFDeriv ℝ (q : ℕ) u) B := by
      intro x hx
      exact ((hc2.contDiffAt (Metric.isOpen_ball.mem_nhds (hB hx))).continuousAt_iteratedFDeriv
        (by norm_cast; omega)).continuousWithinAt
    obtain ⟨D, hD⟩ := hcc.exists_bound_of_continuousOn hc
    have hhq : ∃ L : NNReal, HolderOnWith L (α / 2) (iteratedFDeriv ℝ (q : ℕ) u) B := by
      by_cases hq2 : (q : ℕ) = 2
      · subst q
        exact ⟨K2, hjet2.mono hB⟩
      · have hfq : ContDiffOn ℝ 1 (iteratedFDeriv ℝ (q : ℕ) u) B := by
          have hqle : (q : ℕ) ≤ 1 := by omega
          interval_cases hqv : (q : ℕ)
          · let L := (continuousMultilinearCurryFin0 ℝ E2 ℝ).symm.toContinuousLinearMap
            have hf : iteratedFDeriv ℝ 0 u = fun x => L (u x) := by
              funext x; ext ξ; simp [L]
            rw [hf]
            exact L.contDiff.comp_contDiffOn ((hc2.of_le (by norm_num)).mono hB)
          · let L := (continuousMultilinearCurryFin1 ℝ E2 ℝ).symm.toContinuousLinearMap
            have hf : iteratedFDeriv ℝ 1 u = fun x => L (fderiv ℝ u x) := by
              funext x; ext ξ; simp [L, iteratedFDeriv_one_apply]
            rw [hf]
            exact L.contDiff.comp_contDiffOn
              ((hc2.fderiv_of_isOpen Metric.isOpen_ball (by norm_num)).mono hB)
        obtain ⟨L, hL⟩ := hfq.exists_lipschitzOnWith one_ne_zero (convex_closedBall _ _) hcc
        let D0 : NNReal := (Metric.ediam B).toNNReal
        refine ⟨L * D0 ^ ((1 : ℝ) - ((α / 2 : NNReal) : ℝ)), ?_⟩
        exact hL.holderOnWith.of_le (fun x hx y hy => by
          change edist x y ≤ ↑((Metric.ediam B).toNNReal)
          rw [ENNReal.coe_toNNReal hcc.isBounded.ediam_ne_top]
          exact Metric.edist_le_ediam_of_mem hx hy) hb1.le
    obtain ⟨L, hL⟩ := hhq
    refine ⟨Real.toNNReal D + L, ?_, hL.mono_const (le_add_left le_rfl)⟩
    intro x hx
    exact (hD x hx).trans ((Real.le_coe_toNNReal D).trans (by simp))
  choose Cq hCq using hq
  let K' := ∑ q : Fin 3, Cq q
  have hKq (q : Fin 3) : Cq q ≤ K' :=
    Finset.single_le_sum (fun _ _ => by positivity) (Finset.mem_univ q)
  refine ⟨s, K', α / 2, hs, hsmall, hb, hb1, hc2.mono
    (Metric.ball_subset_closedBall.trans hB), ?_⟩
  intro q hqle
  let q' : Fin 3 := ⟨q, by omega⟩
  exact ⟨fun x hx => ((hCq q').1 x (Metric.ball_subset_closedBall hx)).trans
      (NNReal.coe_le_coe.mpr (hKq q')),
    ((hCq q').2.mono Metric.ball_subset_closedBall).mono_const (hKq q')⟩

end SeifertSurfaces.QuasilinearBootstrap
