import B1TangencyGraph

noncomputable section
open Set Topology Function MeasureTheory
open scoped Manifold ContDiff BigOperators

namespace SeifertSurfaces.OriginalEndpoints.B1GraphCoefficients
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency

universe v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}

/-- G06: an ambient open tube for the literal supplied window coefficients. -/
theorem actual_coefficient_open_tube (D : B1OriginalData g J) (s : Circle)
    (W : CollarWindow D s) :
    ∃ O : Set E2, IsOpen O ∧ B1Tangency.closedHalfDisc W.R ⊆ O ∧ O ⊆ W.U ∧
      (∀ x ∈ O, ∀ t ∈ Icc (0 : ℝ) 1, jetPoint (W.segmentJet x t) ∈ W.V) ∧
      ContDiffOn ℝ ∞ (localHeight D s) O ∧
      ContDiffOn ℝ ∞ (planarGradient (localHeight D s)) O ∧
      (∀ i j : Fin 2, ContDiffOn ℝ ∞ (fun x => W.a x i j) O) ∧
      ContDiffOn ℝ ∞ W.q O ∧ ContDiffOn ℝ ∞ W.lowerGradient O ∧
      ContDiffOn ℝ ∞ W.lowerHeight O ∧ ContDiffOn ℝ ∞ W.b O ∧
      ContDiffOn ℝ ∞ W.c O := by
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
  have hasFD : ∀ (G : Type) [NormedAddCommGroup G] [NormedSpace ℝ G]
    (O : Set E2) (Q : Set ℝ) (hO : IsOpen O) (hQ : IsOpen Q)
    (hIQ : Icc (0 : ℝ) 1 ⊆ Q) (F : E2 × ℝ → G)
    (hF : ContDiffOn ℝ ∞ F (O ×ˢ Q)) (x : E2) (hx : x ∈ O),
    HasFDerivAt (fun y => ∫ t in (0 : ℝ)..1, F (y,t))
      (∫ t in (0 : ℝ)..1,
        (fderiv ℝ F (x,t)).comp (ContinuousLinearMap.inl ℝ E2 ℝ)) x := by
    intro G _ _ O Q hO hQ hIQ F hF x hx
    let D : E2 × ℝ → E2 →L[ℝ] G := fun p =>
      (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ E2 ℝ)
    have hD : ContDiffOn ℝ ∞ D (O ×ˢ Q) :=
      (hF.fderiv_of_isOpen (hO.prod hQ) (by simp)).clm_comp contDiffOn_const
    have hslic (y : E2) (hy : y ∈ O) : ContinuousOn (fun t : ℝ => F (y,t)) (Icc (0 : ℝ) 1) :=
      hF.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun t ht => ⟨hy,hIQ ht⟩)
    have hslicD (y : E2) (hy : y ∈ O) : ContinuousOn (fun t : ℝ => D (y,t)) (Icc (0 : ℝ) 1) :=
      hD.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun t ht => ⟨hy,hIQ ht⟩)
    obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hO.mem_nhds hx)
    have hprod : Metric.closedBall x r ×ˢ Icc (0 : ℝ) 1 ⊆ O ×ˢ Q :=
      Set.prod_mono hball hIQ
    obtain ⟨C, hC⟩ := ((isCompact_closedBall x r).prod isCompact_Icc).exists_bound_of_continuousOn
      (hD.continuousOn.mono hprod)
    apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F := fun y t => F (y,t)) (F' := fun y t => D (y,t))
      (bound := fun _ => C) (s := Metric.closedBall x r)
      (Metric.closedBall_mem_nhds x hr)
    · filter_upwards [hO.mem_nhds hx] with y hy
      simpa only [uIoc_of_le zero_le_one] using
        ((hslic y hy).mono Ioc_subset_Icc_self).aestronglyMeasurable (μ := volume) measurableSet_Ioc
    · have h : ContinuousOn (fun t : ℝ => F (x,t)) (uIcc (0 : ℝ) 1) := by
        simpa only [uIcc_of_le zero_le_one] using hslic x hx
      exact h.intervalIntegrable
    · simpa only [uIoc_of_le zero_le_one] using
        ((hslicD x hx).mono Ioc_subset_Icc_self).aestronglyMeasurable (μ := volume) measurableSet_Ioc
    · exact Filter.Eventually.of_forall fun t ht y hy => hC (y,t) ⟨hy, uIoc_subset_uIcc.trans (by simp only [uIcc_of_le zero_le_one]; exact Subset.rfl) ht⟩
    · exact intervalIntegrable_const
    · apply Filter.Eventually.of_forall
      intro t ht y hy
      have hyt : (y,t) ∈ O ×ˢ Q := ⟨hball hy,hIQ (uIoc_subset_uIcc.trans (by simp only [uIcc_of_le zero_le_one]; exact Subset.rfl) ht)⟩
      exact ((hF.contDiffAt ((hO.prod hQ).mem_nhds hyt)).differentiableAt (by simp)).hasFDerivAt.comp y
        ((hasFDerivAt_id y).prodMk (hasFDerivAt_const t y))
  have integralN : ∀ (n : ℕ),
    ∀ (G : Type) [NormedAddCommGroup G] [NormedSpace ℝ G]
    (O : Set E2) (Q : Set ℝ) (hO : IsOpen O) (hQ : IsOpen Q)
    (hIQ : Icc (0 : ℝ) 1 ⊆ Q) (F : E2 × ℝ → G),
    ContDiffOn ℝ ∞ F (O ×ˢ Q) →
    ContDiffOn ℝ (n : ℕ∞ω) (fun x => ∫ t in (0 : ℝ)..1, F (x,t)) O := by
    intro n
    induction n with
    | zero =>
      intro G _ _ O Q hO hQ hIQ F hF
      apply contDiffOn_zero.mpr
      intro x hx
      exact (hasFD G O Q hO hQ hIQ F hF x hx).continuousAt.continuousWithinAt
    | succ n ih =>
      intro G _ _ O Q hO hQ hIQ F hF
      let D : E2 × ℝ → E2 →L[ℝ] G := fun p =>
        (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ E2 ℝ)
      have hD : ContDiffOn ℝ ∞ D (O ×ˢ Q) :=
        (hF.fderiv_of_isOpen (hO.prod hQ) (by simp)).clm_comp contDiffOn_const
      have hderiv (x : E2) (hx : x ∈ O) := hasFD G O Q hO hQ hIQ F hF x hx
      rw [Nat.cast_add, Nat.cast_one]
      apply (contDiffOn_succ_iff_fderiv_of_isOpen hO).mpr
      refine ⟨fun x hx => (hderiv x hx).differentiableAt.differentiableWithinAt, ?_, ?_⟩
      · simp
      · exact (ih (E2 →L[ℝ] G) O Q hO hQ hIQ D hD).congr fun x hx => (hderiv x hx).fderiv
  have integralSmooth : ∀ (G : Type) [NormedAddCommGroup G] [NormedSpace ℝ G]
      (O : Set E2) (Q : Set ℝ) (hO : IsOpen O) (hQ : IsOpen Q)
      (hIQ : Icc (0 : ℝ) 1 ⊆ Q) (F : E2 × ℝ → G),
      ContDiffOn ℝ ∞ F (O ×ˢ Q) →
      ContDiffOn ℝ ∞ (fun x => ∫ t in (0 : ℝ)..1, F (x,t)) O := by
    intro G _ _ O Q hO hQ hIQ F hF
    exact contDiffOn_infty.mpr fun n => integralN n G O Q hO hQ hIQ F hF
  have hg : ContDiffOn ℝ ∞ (planarGradient (localHeight D s)) W.U := by
    unfold planarGradient
    have hd : ContDiffOn ℝ ∞ (fderiv ℝ (localHeight D s)) W.U :=
      W.height_smooth.fderiv_of_isOpen W.U_open (by simp)
    exact ContDiffOn.sum (fun i _ => (hd.clm_apply contDiffOn_const).smul_const _)
  let P : Set (E2 × ℝ) := {p | p.1 ∈ W.U ∧ jetPoint (W.segmentJet p.1 p.2) ∈ W.V}
  have hp : ContDiffOn ℝ ∞ (fun p : E2 × ℝ => jetPoint (W.segmentJet p.1 p.2))
      (W.U ×ˢ univ) := by
    have hf : ContDiffOn ℝ ∞ (fun p : E2 × ℝ => localHeight D s p.1) (W.U ×ˢ univ) :=
      W.height_smooth.comp contDiffOn_fst (fun p hp => hp.1)
    unfold jetPoint CollarWindow.segmentJet
    apply (EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff.comp_contDiffOn
    apply contDiffOn_pi.mpr
    intro i
    fin_cases i
    · exact (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff.comp_contDiffOn contDiffOn_fst
    · exact (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff.comp_contDiffOn contDiffOn_fst
    · exact contDiffOn_snd.mul hf
  have hP : IsOpen P := by
    have h := hp.continuousOn.isOpen_inter_preimage (W.U_open.prod isOpen_univ) W.V_open
    simpa [P, Set.prod_univ, Set.preimage, Set.inter_def] using h
  have hH : IsCompact (B1Tangency.closedHalfDisc W.R) := by
    exact (isCompact_closedBall (0 : E2) W.R).inter_right
      (isClosed_le continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous)
  obtain ⟨O, Q, hO, hQ, hHO, hIQ, hOP⟩ := generalized_tube_lemma hH
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)) hP (by
      intro p hp
      exact ⟨W.U_contains hp.1, W.jets_inside p.1 hp.1 p.2 hp.2⟩)
  have hOU : O ⊆ W.U := by
    intro x hx
    exact (hOP (show (x, (0 : ℝ)) ∈ O ×ˢ Q from ⟨hx, hIQ (by simp)⟩)).1

  have hsegments : ∀ x ∈ O, ∀ t ∈ Q, jetPoint (W.segmentJet x t) ∈ W.V :=
    fun x hx t ht => (hOP (show (x,t) ∈ O ×ˢ Q from ⟨hx,ht⟩)).2
  have hheight := W.height_smooth.mono hOU
  have hgrad := hg.mono hOU
  have hsegment : ContDiffOn ℝ ∞ (fun p : E2 × ℝ => W.segmentJet p.1 p.2) (O ×ˢ Q) := by
    have hh : ContDiffOn ℝ ∞ (fun p : E2 × ℝ => localHeight D s p.1) (O ×ˢ Q) :=
      hheight.comp contDiffOn_fst (fun p hp => hp.1)
    have hhg : ContDiffOn ℝ ∞ (fun p : E2 × ℝ => planarGradient (localHeight D s) p.1) (O ×ˢ Q) :=
      hgrad.comp contDiffOn_fst (fun p hp => hp.1)
    exact contDiffOn_fst.prodMk ((contDiffOn_snd.mul hh).prodMk (contDiffOn_snd.smul hhg))
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
  have partialP (F : Jet → ℝ) (hF : ContDiffOn ℝ ∞ F (jetPoint ⁻¹' W.V)) (i : Fin 2) :
      ContDiffOn ℝ ∞ (fun j : Jet => fderiv ℝ (fun p : E2 => F (j.1,j.2.1,p))
        j.2.2 (coordinateVector 2 i)) (jetPoint ⁻¹' W.V) := by
    intro j hj
    apply ContDiffAt.contDiffWithinAt
    have hD := hF.contDiffAt (hA.mem_nhds hj)
    have hpair : ContDiffAt ℝ ∞
        (fun p : Jet × E2 => (p.1.1, p.1.2.1, p.2)) (j,j.2.2) :=
      contDiffAt_fst.fst.prodMk (contDiffAt_fst.snd.fst.prodMk contDiffAt_snd)
    exact ((hD.comp (j,j.2.2) hpair).fderiv contDiffAt_snd.snd (by simp)).clm_apply contDiffAt_const
  have partialZ (F : Jet → ℝ) (hF : ContDiffOn ℝ ∞ F (jetPoint ⁻¹' W.V)) :
      ContDiffOn ℝ ∞ (fun j : Jet => deriv (fun z : ℝ => F (j.1,z,j.2.2))
        j.2.1) (jetPoint ⁻¹' W.V) := by
    intro j hj
    apply ContDiffAt.contDiffWithinAt
    have hD := hF.contDiffAt (hA.mem_nhds hj)
    have hpair : ContDiffAt ℝ ∞
        (fun p : Jet × ℝ => (p.1.1, p.2, p.1.2.2)) (j,j.2.1) :=
      contDiffAt_fst.fst.prodMk (contDiffAt_snd.prodMk contDiffAt_fst.snd.snd)
    exact ((hD.comp (j,j.2.1) hpair).fderiv contDiffAt_snd.fst (by simp)).clm_apply contDiffAt_const
  have hfluxi (i : Fin 2) : ContDiffOn ℝ ∞ (fun j : Jet => W.flux j i) (jetPoint ⁻¹' W.V) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp_contDiffOn hfl.1
  have ha (i j : Fin 2) : ContDiffOn ℝ ∞ (fun x => W.a x i j) O :=
    integralSmooth ℝ O Q hO hQ hIQ _
      ((partialP (fun j : Jet => W.flux j i) (hfluxi i) j).comp hsegment
        (fun p hp => hsegments p.1 hp.1 p.2 hp.2))
  have hq : ContDiffOn ℝ ∞ W.q O := by
    apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.contDiff.comp_contDiffOn
    apply contDiffOn_pi.mpr
    intro i
    exact integralSmooth ℝ O Q hO hQ hIQ _
      ((partialZ (fun j : Jet => W.flux j i) (hfluxi i)).comp hsegment
        (fun p hp => hsegments p.1 hp.1 p.2 hp.2))
  have hlg : ContDiffOn ℝ ∞ W.lowerGradient O := by
    apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.contDiff.comp_contDiffOn
    apply contDiffOn_pi.mpr
    intro i
    exact integralSmooth ℝ O Q hO hQ hIQ _
      ((partialP W.lower hfl.2 i).comp hsegment
        (fun p hp => hsegments p.1 hp.1 p.2 hp.2))
  have hlh : ContDiffOn ℝ ∞ W.lowerHeight O :=
    integralSmooth ℝ O Q hO hQ hIQ _
      ((partialZ W.lower hfl.2).comp hsegment
        (fun p hp => hsegments p.1 hp.1 p.2 hp.2))
  have hb : ContDiffOn ℝ ∞ W.b O := hq.add hlg
  have hc : ContDiffOn ℝ ∞ W.c O := by
    apply ContDiffOn.add _ hlh
    apply ContDiffOn.sum
    intro i hi
    have hqi : ContDiffOn ℝ ∞ (fun y => W.q y i) O :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp_contDiffOn hq
    exact (hqi.fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const
  exact ⟨O,hO,hHO,hOU,fun x hx t ht => hsegments x hx t (hIQ ht),
    hheight,hgrad,ha,hq,hlg,hlh,hb,hc⟩

/-- G07: the open tube and q-regularity are the relevant output of G06.
The height's smoothness on W.U is already part of the same supplied W. -/
theorem actual_coefficient_mean_value (D : B1OriginalData g J) (s : Circle)
    (W : CollarWindow D s) (O : Set E2) (hO : IsOpen O) (hU : O ⊆ W.U)
    (hsegments : ∀ x ∈ O, ∀ t ∈ Icc (0 : ℝ) 1,
      jetPoint (W.segmentJet x t) ∈ W.V)
    (hq : ContDiffOn ℝ ∞ W.q O) :
    (∀ x ∈ O, ∀ i j : Fin 2,
      IntervalIntegrable (fun t : ℝ =>
        fderiv ℝ (fun p : E2 => W.flux (x, (W.segmentJet x t).2.1, p) i)
          (W.segmentJet x t).2.2 (coordinateVector 2 j)) volume 0 1) ∧
    (∀ x ∈ O, ∀ i : Fin 2,
      IntervalIntegrable (fun t : ℝ =>
        deriv (fun z : ℝ => W.flux (x, z, (W.segmentJet x t).2.2) i)
          (W.segmentJet x t).2.1) volume 0 1) ∧
    (∀ x ∈ O, ∀ i : Fin 2,
      IntervalIntegrable (fun t : ℝ =>
        fderiv ℝ (fun p : E2 => W.lower (x, (W.segmentJet x t).2.1, p))
          (W.segmentJet x t).2.2 (coordinateVector 2 i)) volume 0 1) ∧
    (∀ x ∈ O,
      IntervalIntegrable (fun t : ℝ =>
        deriv (fun z : ℝ => W.lower (x, z, (W.segmentJet x t).2.2))
          (W.segmentJet x t).2.1) volume 0 1) ∧
    (∀ x ∈ O,
      W.flux (x, localHeight D s x, planarGradient (localHeight D s) x) -
          W.flux (x, 0, 0) =
        matrixAction (W.a x) (planarGradient (localHeight D s) x) +
          localHeight D s x • W.q x) ∧
    (∀ x ∈ O,
      W.lower (x, localHeight D s x, planarGradient (localHeight D s) x) -
          W.lower (x, 0, 0) =
        inner ℝ (W.lowerGradient x) (planarGradient (localHeight D s) x) +
          W.lowerHeight x * localHeight D s x) ∧
    (∀ x ∈ O,
      W.residual (localHeight D s) x - W.residual (fun _ => 0) x =
        classicalL W.a W.b W.c (localHeight D s) x) := by
  have jp_smooth : ContDiff ℝ ∞ jetPoint := by
    unfold jetPoint
    apply (EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff.comp
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> simp <;> fun_prop
  have jt_smooth (i : Fin 2) (a : Fin 3) :
      ContDiff ℝ ∞ (fun j : Jet => jetTangent j.2.2 i a) := by
    delta jetTangent
    change ContDiff ℝ ∞ (fun j : Jet => coordinateVector 3 (Fin.castSucc i) a +
      j.2.2 i * coordinateVector 3 2 a)
    fun_prop
  have gram_smooth (D : B1OriginalData g J) (s : Circle) (W : CollarWindow D s)
      (i k : Fin 2) :
      ContDiffOn ℝ ∞ (fun j : Jet => W.gram j i k) (jetPoint ⁻¹' W.V) := by
    have hm (a b : Fin 3) : ContDiffOn ℝ ∞
        (fun j : Jet => W.metric.tensor (jetPoint j) a b) (jetPoint ⁻¹' W.V) :=
      (W.metric.smooth a b).comp jp_smooth.contDiffOn (fun _ h => h)
    delta CollarWindow.gram coordinateInner
    apply ContDiffOn.sum
    intro a ha
    apply ContDiffOn.sum
    intro b hb
    exact ((hm a b).mul (jt_smooth i a).contDiffOn).mul (jt_smooth k b).contDiffOn
  have gram_pos (D : B1OriginalData g J) (s : Circle) (W : CollarWindow D s)
      (j : Jet) (hj : jetPoint j ∈ W.V) : (W.gram j).PosDef := by
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
      let v : E3 := (EuclideanSpace.equiv (Fin 3) ℝ).symm ![p 0, p 1, j.2.2 0 * p 0 + j.2.2 1 * p 1]
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
        delta CollarWindow.gram coordinateInner jetTangent
        simp [dotProduct, Matrix.mulVec,
          coordinateVector, v, Fin.sum_univ_two, Fin.sum_univ_three]
        <;> ring
      simpa only [star_trivial, heq] using hpos
  have density_smooth (D : B1OriginalData g J) (s : Circle) (W : CollarWindow D s) :
      ContDiffOn ℝ ∞ W.density (jetPoint ⁻¹' W.V) := by
    have hd : ContDiffOn ℝ ∞ (fun j => Matrix.det (W.gram j)) (jetPoint ⁻¹' W.V) := by
      simp only [Matrix.det_fin_two]
      exact ((gram_smooth D s W 0 0).mul (gram_smooth D s W 1 1)).sub
        ((gram_smooth D s W 0 1).mul (gram_smooth D s W 1 0))
    exact hd.sqrt (fun j hj => (gram_pos D s W j hj).det_pos.ne')
  have p_slice (f : Jet → ℝ) (j : Jet) (hf : DifferentiableAt ℝ f j) (p : E2) :
      fderiv ℝ (fun p : E2 => f (j.1, j.2.1, p)) j.2.2 p =
        fderiv ℝ f j (0, 0, p) := by
    have hs := (hasFDerivAt_const (𝕜 := ℝ) j.1 j.2.2).prodMk
      ((hasFDerivAt_const (𝕜 := ℝ) j.2.1 j.2.2).prodMk (hasFDerivAt_id (𝕜 := ℝ) j.2.2))
    have hh := hf.hasFDerivAt.comp j.2.2 hs
    exact congrArg (fun L : E2 →L[ℝ] ℝ => L p) hh.fderiv
  have z_slice (f : Jet → ℝ) (j : Jet) (hf : DifferentiableAt ℝ f j) :
      deriv (fun z : ℝ => f (j.1, z, j.2.2)) j.2.1 =
        fderiv ℝ f j (0, 1, 0) := by
    have hs := (hasFDerivAt_const (𝕜 := ℝ) j.1 j.2.1).prodMk
      ((hasFDerivAt_id (𝕜 := ℝ) j.2.1).prodMk (hasFDerivAt_const (𝕜 := ℝ) j.2.2 j.2.1))
    have hh := hf.hasFDerivAt.comp j.2.1 hs
    exact congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) hh.fderiv
  have partial_p_smooth (A : Set Jet) (hA : IsOpen A) (f : Jet → ℝ)
      (hf : ContDiffOn ℝ ∞ f A) (p : E2) :
      ContDiffOn ℝ ∞ (fun j : Jet =>
        fderiv ℝ (fun p : E2 => f (j.1,j.2.1,p)) j.2.2 p) A := by
    apply ((hf.fderiv_of_isOpen hA (by simp)).clm_apply
      (contDiffOn_const (c := ((0, (0, p)) : Jet)))).congr
    intro j hj
    exact (p_slice f j ((hf.contDiffAt (hA.mem_nhds hj)).differentiableAt (by simp)) p)
  have partial_z_smooth (A : Set Jet) (hA : IsOpen A) (f : Jet → ℝ)
      (hf : ContDiffOn ℝ ∞ f A) :
      ContDiffOn ℝ ∞ (fun j : Jet => deriv (fun z : ℝ => f (j.1,z,j.2.2)) j.2.1) A := by
    apply ((hf.fderiv_of_isOpen hA (by simp)).clm_apply
      (contDiffOn_const (c := ((0, (1, 0)) : Jet)))).congr
    intro j hj
    exact (z_slice f j ((hf.contDiffAt (hA.mem_nhds hj)).differentiableAt (by simp)))
  have flux_lower_smooth (D : B1OriginalData g J) (s : Circle) (W : CollarWindow D s) :
      (∀ i : Fin 2, ContDiffOn ℝ ∞ (fun j => W.flux j i) (jetPoint ⁻¹' W.V)) ∧
      ContDiffOn ℝ ∞ W.lower (jetPoint ⁻¹' W.V) := by
    have hA : IsOpen (jetPoint ⁻¹' W.V) := W.V_open.preimage jp_smooth.continuous
    have hd := density_smooth D s W
    constructor
    · intro i
      have hh := partial_p_smooth _ hA W.density hd (coordinateVector 2 i)
      apply hh.congr
      intro j hj
      delta CollarWindow.flux
      fin_cases i <;> simp [planarGradient, Fin.sum_univ_two,
        coordinateVector, EuclideanSpace.single, PiLp.single_apply]
    · exact (partial_z_smooth _ hA W.density hd).neg
  have scalar_mv (A : Set Jet) (hA : IsOpen A) (f : Jet → ℝ)
      (hf : ContDiffOn ℝ ∞ f A) (x p : E2) (u : ℝ)
      (hs : ∀ t ∈ Icc (0 : ℝ) 1, (x,t*u,t • p) ∈ A) :
      (∀ i : Fin 2, IntervalIntegrable (fun t : ℝ =>
        fderiv ℝ (fun p' : E2 => f (x,t*u,p')) (t • p) (coordinateVector 2 i)) volume 0 1) ∧
      IntervalIntegrable (fun t : ℝ => deriv (fun z : ℝ => f (x,z,t • p)) (t*u)) volume 0 1 ∧
      f (x,u,p) - f (x,0,0) =
        (∑ i : Fin 2, (∫ t in (0 : ℝ)..1,
          fderiv ℝ (fun p' : E2 => f (x,t*u,p')) (t • p) (coordinateVector 2 i)) * p i) +
        (∫ t in (0 : ℝ)..1, deriv (fun z : ℝ => f (x,z,t • p)) (t*u)) * u := by
    let S : ℝ → Jet := fun t => (x,t*u,t • p)
    let P : Fin 2 → ℝ → ℝ := fun i t =>
      fderiv ℝ (fun p' : E2 => f (x,t*u,p')) (t • p) (coordinateVector 2 i)
    let Z : ℝ → ℝ := fun t => deriv (fun z : ℝ => f (x,z,t • p)) (t*u)
    have hc : Continuous S := by dsimp [S]; fun_prop
    have hp (i : Fin 2) : IntervalIntegrable (P i) volume 0 1 := by
      have hh := ((partial_p_smooth A hA f hf (coordinateVector 2 i)).continuousOn.comp hc.continuousOn hs)
      exact (show ContinuousOn (P i) (uIcc (0 : ℝ) 1) by simpa [P,S,Function.comp_def] using hh).intervalIntegrable
    have hz : IntervalIntegrable Z volume 0 1 := by
      have hh := ((partial_z_smooth A hA f hf).continuousOn.comp hc.continuousOn hs)
      exact (show ContinuousOn Z (uIcc (0 : ℝ) 1) by simpa [Z,S,Function.comp_def] using hh).intervalIntegrable
    refine ⟨hp,hz,?_⟩
    have hex : p = p 0 • coordinateVector 2 0 + p 1 • coordinateVector 2 1 := by
      ext i
      fin_cases i <;> simp [coordinateVector, EuclideanSpace.single]
    have hd : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun t => f (S t))
        (P 0 t * p 0 + P 1 t * p 1 + Z t * u) t := by
      intro t ht
      have hft := (hf.contDiffAt (hA.mem_nhds (hs t (by simpa using ht)))).differentiableAt (by simp)
      have hst : HasDerivAt S (0,u,p) t := by
        simpa [S] using (hasDerivAt_const t x).prodMk
          (((hasDerivAt_id t).mul_const u).prodMk ((hasDerivAt_id t).smul_const p))
      have hh := hft.hasFDerivAt.comp_hasDerivAt t hst
      convert hh using 1 <;> try rfl
      rw [show ((0,u,p) : Jet) = (0,0,p) + u • (0,1,0) by ext <;> simp]
      rw [map_add, map_smul, ← p_slice f (S t) hft p, ← z_slice f (S t) hft]
      change _ = fderiv ℝ (fun p' : E2 => f (x,t*u,p')) (t • p) p + u * Z t
      conv_rhs => arg 1; arg 2; rw [hex]
      simp only [map_add,map_smul,smul_eq_mul]
      dsimp [P]
      ring
    have hi := ((hp 0).mul_const (p 0)).add ((hp 1).mul_const (p 1))
    have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hi.add (hz.mul_const u))
    rw [intervalIntegral.integral_add hi (hz.mul_const u),
      intervalIntegral.integral_add ((hp 0).mul_const (p 0)) ((hp 1).mul_const (p 1)),
      intervalIntegral.integral_mul_const,intervalIntegral.integral_mul_const,
      intervalIntegral.integral_mul_const] at heq
    simpa [S,P,Z,Fin.sum_univ_two] using heq.symm
  have grad_smooth (U : Set E2) (hU : IsOpen U) (u : E2 → ℝ)
      (hu : ContDiffOn ℝ ∞ u U) : ContDiffOn ℝ ∞ (planarGradient u) U := by
    unfold planarGradient
    apply ContDiffOn.sum
    intro i hi
    exact ((hu.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const).smul contDiffOn_const
  have smooth_coord (U : Set E2) (f : E2 → E2)
      (hf : ContDiffOn ℝ ∞ f U) (i : Fin 2) : ContDiffOn ℝ ∞ (fun x => f x i) U := by
    exact (show ContDiff ℝ ∞ (fun p : E2 => p i) by fun_prop).comp_contDiffOn hf
  have residual_identity (D : B1OriginalData g J) (s : Circle)
      (W : CollarWindow D s) (O : Set E2) (hO : IsOpen O) (hU : O ⊆ W.U)
      (hs : ∀ x ∈ O, ∀ t ∈ Icc (0 : ℝ) 1, jetPoint (W.segmentJet x t) ∈ W.V)
      (hq : ContDiffOn ℝ ∞ W.q O)
      (hF : ∀ x ∈ O, W.flux (x, localHeight D s x, planarGradient (localHeight D s) x) -
        W.flux (x, 0, 0) = matrixAction (W.a x) (planarGradient (localHeight D s) x) +
          localHeight D s x • W.q x)
      (hL : ∀ x ∈ O, W.lower (x, localHeight D s x, planarGradient (localHeight D s) x) -
        W.lower (x, 0, 0) = inner ℝ (W.lowerGradient x) (planarGradient (localHeight D s) x) +
          W.lowerHeight x * localHeight D s x) :
      ∀ x ∈ O, W.residual (localHeight D s) x - W.residual (fun _ => 0) x =
        classicalL W.a W.b W.c (localHeight D s) x := by
    let u := localHeight D s
    have hu : ContDiffOn ℝ ∞ u O := W.height_smooth.mono hU
    have hg : ContDiffOn ℝ ∞ (planarGradient u) O := grad_smooth O hO u hu
    have hJ : IsOpen (jetPoint ⁻¹' W.V) := W.V_open.preimage jp_smooth.continuous
    have hf := (flux_lower_smooth D s W).1
    have hjet : ContDiffOn ℝ ∞ (fun x : E2 => (x,u x,planarGradient u x) : E2 → Jet) O :=
      contDiffOn_id.prodMk (hu.prodMk hg)
    have hzjet : ContDiffOn ℝ ∞ (fun x : E2 => (x,0,0) : E2 → Jet) O :=
      contDiffOn_id.prodMk (contDiffOn_const.prodMk contDiffOn_const)
    have hFi (i : Fin 2) : ContDiffOn ℝ ∞
        (fun x : E2 => W.flux (x,u x,planarGradient u x) i) O := by
      apply (hf i).comp hjet
      intro x hx
      have ht := hs x hx 1 (by norm_num)
      change jetPoint (x, 1 * localHeight D s x, (1 : ℝ) • planarGradient (localHeight D s) x) ∈ W.V at ht
      simpa [u] using ht
    have hZi (i : Fin 2) : ContDiffOn ℝ ∞ (fun x : E2 => W.flux (x,0,0) i) O := by
      apply (hf i).comp hzjet
      intro x hx
      have ht := hs x hx 0 (by norm_num)
      change jetPoint (x, 0 * localHeight D s x, (0 : ℝ) • planarGradient (localHeight D s) x) ∈ W.V at ht
      simpa using ht
    have hqi (i : Fin 2) := smooth_coord O W.q hq i
    have hMi (i : Fin 2) : ContDiffOn ℝ ∞
        (fun x : E2 => matrixAction (W.a x) (planarGradient u x) i) O := by
      apply (((hFi i).sub (hZi i)).sub (hu.mul (hqi i))).congr
      intro x hx
      have he := congrArg (fun p : E2 => p i) (hF x hx)
      change W.flux (x,u x,planarGradient u x) i - W.flux (x,0,0) i =
        matrixAction (W.a x) (planarGradient u x) i + u x * W.q x i at he
      dsimp only
      linarith
    have hgrad (x : E2) (i : Fin 2) : planarGradient u x i =
        fderiv ℝ u x (coordinateVector 2 i) := by
      fin_cases i <;> simp [planarGradient,Fin.sum_univ_two,coordinateVector,EuclideanSpace.single]
    intro x hx
    have hdu := (hu.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
    have hdF (i : Fin 2) := ((hFi i).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
    have hdZ (i : Fin 2) := ((hZi i).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
    have hdQ (i : Fin 2) := ((hqi i).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
    have hdM (i : Fin 2) := ((hMi i).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
    have he (i : Fin 2) :
        fderiv ℝ (fun y : E2 => W.flux (y,u y,planarGradient u y) i) x (coordinateVector 2 i) -
        fderiv ℝ (fun y : E2 => W.flux (y,0,0) i) x (coordinateVector 2 i) =
        fderiv ℝ (fun y : E2 => matrixAction (W.a y) (planarGradient u y) i) x (coordinateVector 2 i) +
        u x * fderiv ℝ (fun y : E2 => W.q y i) x (coordinateVector 2 i) +
          W.q x i * planarGradient u x i := by
      have hev : (fun y : E2 => W.flux (y,u y,planarGradient u y) i - W.flux (y,0,0) i) =ᶠ[𝓝 x]
          (fun y : E2 => matrixAction (W.a y) (planarGradient u y) i + u y * W.q y i) := by
        filter_upwards [hO.mem_nhds hx] with y hy
        exact congrArg (fun p : E2 => p i) (hF y hy)
      have hh := congrArg (fun L : E2 →L[ℝ] ℝ => L (coordinateVector 2 i)) hev.fderiv_eq
      have hr := (hdM i).hasFDerivAt.add (hdu.hasFDerivAt.mul (hdQ i).hasFDerivAt)
      have hl := (hdF i).hasFDerivAt.sub (hdZ i).hasFDerivAt
      have hl' : fderiv ℝ (fun y : E2 => W.flux (y,u y,planarGradient u y) i - W.flux (y,0,0) i) x =
        fderiv ℝ (fun y : E2 => W.flux (y,u y,planarGradient u y) i) x -
        fderiv ℝ (fun y : E2 => W.flux (y,0,0) i) x := hl.fderiv
      have hr' : fderiv ℝ (fun y : E2 => matrixAction (W.a y) (planarGradient u y) i + u y * W.q y i) x =
        fderiv ℝ (fun y : E2 => matrixAction (W.a y) (planarGradient u y) i) x +
        (u x • fderiv ℝ (fun y : E2 => W.q y i) x + W.q x i • fderiv ℝ u x) := hr.fderiv
      rw [hl',hr'] at hh
      simpa [hgrad,add_assoc] using hh
    have hzero : planarGradient (fun _ : E2 => (0 : ℝ)) = 0 := by
      funext y
      simp [planarGradient]
    have hl := hL x hx
    have he0 := he 0
    have he1 := he 1
    delta CollarWindow.residual classicalL CollarWindow.b CollarWindow.c
    simp only [hzero,Pi.zero_apply,Fin.sum_univ_two,
      EuclideanSpace.inner_eq_star_dotProduct,dotProduct,
      star_trivial,PiLp.add_apply] at *
    dsimp only [u] at *
    nlinarith
  have hA : IsOpen (jetPoint ⁻¹' W.V) := W.V_open.preimage jp_smooth.continuous
  have hf := flux_lower_smooth D s W
  have hMVF (x : E2) (hx : x ∈ O) (i : Fin 2) :=
    scalar_mv _ hA (fun j => W.flux j i) (hf.1 i) x
      (planarGradient (localHeight D s) x) (localHeight D s x) (hsegments x hx)
  have hMVL (x : E2) (hx : x ∈ O) :=
    scalar_mv _ hA W.lower hf.2 x
      (planarGradient (localHeight D s) x) (localHeight D s x) (hsegments x hx)
  have hF : ∀ x ∈ O,
      W.flux (x,localHeight D s x,planarGradient (localHeight D s) x) - W.flux (x,0,0) =
        matrixAction (W.a x) (planarGradient (localHeight D s) x) + localHeight D s x • W.q x := by
    intro x hx
    ext i
    delta matrixAction CollarWindow.a CollarWindow.q CollarWindow.segmentJet
    simpa [mul_comm]
      using (hMVF x hx i).2.2
  have hL : ∀ x ∈ O,
      W.lower (x,localHeight D s x,planarGradient (localHeight D s) x) - W.lower (x,0,0) =
        inner ℝ (W.lowerGradient x) (planarGradient (localHeight D s) x) +
          W.lowerHeight x * localHeight D s x := by
    intro x hx
    delta CollarWindow.lowerGradient CollarWindow.lowerHeight CollarWindow.segmentJet
    simpa [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,mul_comm]
      using (hMVL x hx).2.2
  exact ⟨(fun x hx i j => (hMVF x hx i).1 j),
    (fun x hx i => (hMVF x hx i).2.1),
    (fun x hx i => (hMVL x hx).1 i),
    (fun x hx => (hMVL x hx).2.1),hF,hL,
    residual_identity D s W O hO hU hsegments hq hF hL⟩

set_option maxHeartbeats 0
set_option maxRecDepth 30000

/-- G08: the standard-coordinate specialization of the A3 slope formula,
and simultaneous lower/upper bounds for the actual segment-integrated a. -/
theorem actual_slope_hessian_uniform_bounds (D : B1OriginalData g J) (s : Circle)
    (W : CollarWindow D s) :
    (∀ j : Jet, jetPoint j ∈ W.V → ∀ i k : Fin 2,
      fderiv ℝ (fun p : E2 => W.flux (j.1, j.2.1, p) i) j.2.2
          (coordinateVector 2 k) =
        Matrix.det (W.metric.tensor (jetPoint j)) / W.density j *
          (W.gram j)⁻¹ i k) ∧
    (∀ x ∈ B1Tangency.closedHalfDisc W.R, ∀ i j : Fin 2, W.a x i j = W.a x j i) ∧
    (∃ ell C : ℝ, 0 < ell ∧ 0 < C ∧
      ∀ x ∈ B1Tangency.closedHalfDisc W.R, ∀ p : E2,
        ell * ‖p‖ ^ 2 ≤ inner ℝ p (matrixAction (W.a x) p) ∧
        inner ℝ p (matrixAction (W.a x) p) ≤ C * ‖p‖ ^ 2) := by
  set_option maxHeartbeats 0 in
  set_option maxRecDepth 30000 in
    classical
    let slopeGram (B : Matrix (Fin 3) (Fin 3) ℝ) (L : E2 →L[ℝ] E3)
        (n : E3) (p : E2) : Matrix (Fin 2) (Fin 2) ℝ :=
      fun i j => coordinateInner (fun _ => B) 0
        (L (coordinateVector 2 i) + p i • n)
        (L (coordinateVector 2 j) + p j • n)
    let splittingGram (B : Matrix (Fin 3) (Fin 3) ℝ) (L : E2 →L[ℝ] E3)
        (n : E3) : Matrix (Fin 3) (Fin 3) ℝ :=
      fun i j => coordinateInner (fun _ => B) 0
        (if i = 0 then L (coordinateVector 2 0)
          else if i = 1 then L (coordinateVector 2 1) else n)
        (if j = 0 then L (coordinateVector 2 0)
          else if j = 1 then L (coordinateVector 2 1) else n)
    let slopeArea (B : Matrix (Fin 3) (Fin 3) ℝ) (L : E2 →L[ℝ] E3)
        (n : E3) (p : E2) : ℝ :=
      Real.sqrt (Matrix.det (slopeGram B L n p))
    let slopeFlux (B : Matrix (Fin 3) (Fin 3) ℝ) (L : E2 →L[ℝ] E3)
        (n : E3) (p : E2) : E2 :=
      planarGradient (slopeArea B L n) p
    let slopeHessian (B : Matrix (Fin 3) (Fin 3) ℝ) (L : E2 →L[ℝ] E3)
        (n : E3) (p : E2) : Matrix (Fin 2) (Fin 2) ℝ :=
      fun i j => fderiv ℝ (fun q : E2 => slopeFlux B L n q i) p
        (coordinateVector 2 j)
    have slope_area_hessian_formula
        (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.PosDef)
        (L : E2 →L[ℝ] E3) (n : E3)
        (hsplit : Function.Bijective (fun z : E2 × ℝ => L z.1 + z.2 • n))
        (p : E2) (i j : Fin 2) :
        slopeHessian B L n p i j =
          Matrix.det (splittingGram B L n) / slopeArea B L n p *
            (slopeGram B L n p)⁻¹ i j := by
      classical
      have hgram (q : E2) : (slopeGram B L n q).PosDef := by
        let v : Fin 2 → E3 := fun i => L (coordinateVector 2 i) + q i • n
        have hli : LinearIndependent ℝ v := by
          apply Fintype.linearIndependent_iff.mpr
          intro a ha
          have hs : L (∑ i : Fin 2, a i • coordinateVector 2 i) +
              (∑ i : Fin 2, a i * q i) • n = 0 := by
            simpa only [v, smul_add, Finset.sum_add_distrib,
              map_sum, map_smul, mul_smul, Finset.sum_smul] using ha
          have he : ((∑ i : Fin 2, a i • coordinateVector 2 i), ∑ i : Fin 2, a i * q i) =
              ((0 : E2), (0 : ℝ)) := by
            apply hsplit.injective
            simpa only [map_zero, zero_smul, add_zero] using hs
          have hz := congrArg Prod.fst he
          intro i
          have heval := congrArg (fun z : E2 => z i) hz
          fin_cases i <;> simpa [coordinateVector, EuclideanSpace.single, Pi.single_apply] using heval
        let V : Matrix (Fin 3) (Fin 2) ℝ := fun a i => v i a
        have hV : Function.Injective V.mulVec := by
          intro x y hxy
          have hsum : ∑ i, (x i - y i) • v i = 0 := by
            ext a
            have hh := congrFun hxy a
            simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hh
            simpa only [Fin.sum_univ_two, PiLp.add_apply, PiLp.smul_apply,
              smul_eq_mul, sub_mul, PiLp.zero_apply] using (by
                dsimp [V] at hh
                nlinarith [hh] : (x 0 - y 0) * v 0 a + (x 1 - y 1) * v 1 a = 0)
          have he := Fintype.linearIndependent_iff.mp hli _ hsum
          funext i
          exact sub_eq_zero.mp (he i)
        have heq : slopeGram B L n q = V.conjTranspose * B * V := by
          ext i j
          change (∑ a : Fin 3, ∑ b : Fin 3, B a b * v i a * v j b) =
            ∑ b : Fin 3, (∑ a : Fin 3, v i a * B a b) * v j b
          simp only [Fin.sum_univ_three]
          ring
        rw [heq]
        exact hB.conjTranspose_mul_mul_same hV
      let ci : E3 → E3 → ℝ := coordinateInner (fun _ => B) 0
      have hsym (v w : E3) : ci v w = ci w v := by
        dsimp [ci, coordinateInner]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        have hb : B b a = B a b := hB.isHermitian.apply a b
        rw [hb]
        ring
      have hbil (v w : E3) (s t : ℝ) :
          ci (v + s • n) (w + t • n) = ci v w + s * ci n w +
            t * ci v n + s*t*ci n n := by
        simp only [ci, coordinateInner, Fin.sum_univ_three, PiLp.add_apply,
          PiLp.smul_apply, smul_eq_mul]
        ring
      let a := ci (L (coordinateVector 2 0)) (L (coordinateVector 2 0))
      let b := ci (L (coordinateVector 2 0)) (L (coordinateVector 2 1))
      let c := ci (L (coordinateVector 2 1)) (L (coordinateVector 2 1))
      let d := ci (L (coordinateVector 2 0)) n
      let e := ci (L (coordinateVector 2 1)) n
      let f := ci n n
      have g00 (q : E2) : slopeGram B L n q 0 0 = a + 2*d*q 0 + f*(q 0)^2 := by
        change ci _ _ = _
        rw [hbil, hsym n (L (coordinateVector 2 0))]
        dsimp [a, d, f]
        ring
      have g01 (q : E2) : slopeGram B L n q 0 1 = b+e*q 0+d*q 1+f*q 0*q 1 := by
        change ci _ _ = _
        rw [hbil, hsym n (L (coordinateVector 2 1))]
        dsimp [b, d, e, f]
        ring
      have g10 (q : E2) : slopeGram B L n q 1 0 = b+e*q 0+d*q 1+f*q 0*q 1 := by
        change ci _ _ = _
        rw [hsym]
        exact g01 q
      have g11 (q : E2) : slopeGram B L n q 1 1 = c + 2*e*q 1 + f*(q 1)^2 := by
        change ci _ _ = _
        rw [hbil, hsym n (L (coordinateVector 2 1))]
        dsimp [c, e, f]
        ring
      let Q : E2 → ℝ := fun q => Matrix.det (slopeGram B L n q)
      have hQpos (q : E2) : 0 < Q q := (hgram q).det_pos
      have hQdef (q : E2) : Q q = (c*f-e^2)*(q 0)^2 +
          2*(d*e-b*f)*q 0*q 1+(a*f-d^2)*(q 1)^2+
          2*(c*d-b*e)*q 0+2*(a*e-b*d)*q 1+(a*c-b^2) := by
        dsimp [Q]
        rw [Matrix.det_fin_two, g00, g01, g10, g11]
        ring
      have hsplitdet : Matrix.det (splittingGram B L n) =
          a*c*f-a*e^2-b^2*f+2*b*d*e-c*d^2 := by
        rw [Matrix.det_fin_three]
        change a*c*f-a*e*ci n (L (coordinateVector 2 1))-
          b*ci (L (coordinateVector 2 1)) (L (coordinateVector 2 0))*f+
          b*e*ci n (L (coordinateVector 2 0))+
          d*ci (L (coordinateVector 2 1)) (L (coordinateVector 2 0))*ci n (L (coordinateVector 2 1))-
          d*c*ci n (L (coordinateVector 2 0)) = _
        rw [hsym n (L (coordinateVector 2 0)), hsym n (L (coordinateVector 2 1)),
          hsym (L (coordinateVector 2 1)) (L (coordinateVector 2 0))]
        change a*c*f-a*e*e-b*b*f+b*e*d+d*b*e-d*c*d = _
        ring
      have hquad (a b c d e f : ℝ) (Q : E2 → ℝ)
          (hQdef : ∀ x, Q x = a * (x 0)^2 + 2*b*x 0*x 1 + c*(x 1)^2 + 2*d*x 0 + 2*e*x 1+f)
          (hpos : ∀ x, 0 < Q x) (p : E2) (i j : Fin 2) :
          fderiv ℝ (fun q : E2 => planarGradient (fun x => Real.sqrt (Q x)) q i) p
            (coordinateVector 2 j) =
          (if i = j then (if i = 0 then a else c) else b) / Real.sqrt (Q p) -
            (if i = 0 then a*p 0+b*p 1+d else b*p 0+c*p 1+e) *
            (if j = 0 then a*p 0+b*p 1+d else b*p 0+c*p 1+e) / (Real.sqrt (Q p))^3 := by
        let π0 : E2 →L[ℝ] ℝ := EuclideanSpace.proj 0
        let π1 : E2 →L[ℝ] ℝ := EuclideanSpace.proj 1
        let N0 := fun x : E2 => a*x 0+b*x 1+d
        let N1 := fun x : E2 => b*x 0+c*x 1+e
        have hQ (x : E2) : HasFDerivAt Q ((2*N0 x) • π0 + (2*N1 x) • π1) x := by
          have h0 : HasFDerivAt (fun x : E2 => x 0) π0 x := π0.hasFDerivAt
          have h1 : HasFDerivAt (fun x : E2 => x 1) π1 x := π1.hasFDerivAt
          have h := (((((h0.mul h0).const_mul a).add (((h0.const_mul (2*b)).mul h1))).add
            ((h1.mul h1).const_mul c)).add (h0.const_mul (2*d))).add (h1.const_mul (2*e))
          convert h.add_const f using 1
          · funext y
            rw [hQdef]
            simp only [Pi.add_apply, Pi.mul_apply]
            ring
          · ext v
            simp [N0, N1, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
              ContinuousLinearMap.smulRight_apply, smul_eq_mul]
            <;> ring
        have hF (x : E2) := (hQ x).sqrt (ne_of_gt (hpos x))
        have hsqrt (x : E2) : Real.sqrt (Q x) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (hpos x))
        have hgrad (x : E2) (k : Fin 2) :
            planarGradient (fun x => Real.sqrt (Q x)) x k =
              (if k = 0 then N0 x else N1 x) / Real.sqrt (Q x) := by
          unfold planarGradient
          rw [(hF x).fderiv]
          fin_cases k <;>
            simp [Fin.sum_univ_two, coordinateVector, EuclideanSpace.single, π0, π1,
              Pi.single_apply, N0, N1] <;> field_simp (disch := first | exact hsqrt _ | exact ne_of_gt (hpos _) | positivity | norm_num) <;> ring
        have hN0 (x : E2) : HasFDerivAt N0 (a • π0 + b • π1) x := by
          exact ((π0.hasFDerivAt.const_mul a).add (π1.hasFDerivAt.const_mul b)).add_const d
        have hN1 (x : E2) : HasFDerivAt N1 (b • π0 + c • π1) x := by
          exact ((π0.hasFDerivAt.const_mul b).add (π1.hasFDerivAt.const_mul c)).add_const e
        have hi := (hasDerivAt_inv (hsqrt p)).comp_hasFDerivAt p (hF p)
        have h0 := (hN0 p).mul hi
        have h1 := (hN1 p).mul hi
        change HasFDerivAt (fun q : E2 => N0 q * (Real.sqrt (Q q))⁻¹) _ p at h0
        change HasFDerivAt (fun q : E2 => N1 q * (Real.sqrt (Q q))⁻¹) _ p at h1
        have heq : (fun q : E2 => planarGradient (fun x => Real.sqrt (Q x)) q i) =
            (fun q => (if i = 0 then N0 q else N1 q) * (Real.sqrt (Q q))⁻¹) := by
          funext q
          rw [hgrad, div_eq_mul_inv]
        rw [heq]
        fin_cases i <;> fin_cases j <;>
          simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceEq, ite_true, ite_false] <;>
          first | rw [h0.fderiv] | rw [h1.fderiv]
        all_goals
          simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
            coordinateVector, π0, π1, EuclideanSpace.single, Pi.single_apply, N0, N1]
          <;> field_simp (disch := first | exact hsqrt _ | exact ne_of_gt (hpos _) | positivity | norm_num) <;> ring
      have h := hquad (c*f-e^2) (d*e-b*f) (a*f-d^2) (c*d-b*e) (a*e-b*d)
        (a*c-b^2) Q hQdef hQpos p i j
      change slopeHessian B L n p i j = _
      change fderiv ℝ (fun q : E2 => planarGradient (fun x => Real.sqrt (Q x)) q i) p
        (coordinateVector 2 j) = _
      rw [h, Matrix.inv_def, Matrix.adjugate_fin_two, hsplitdet]
      have hs : Real.sqrt (Q p) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (hQpos p))
      have hsq : Real.sqrt (Q p)^2 = Q p := Real.sq_sqrt (hQpos p).le
      have hpow : Real.sqrt (Q p)^3 = Real.sqrt (Q p) * Q p := by
        rw [pow_succ, hsq]
        ring
      change _ = (a*c*f-a*e^2-b^2*f+2*b*d*e-c*d^2) / Real.sqrt (Q p) *
        ((Ring.inverse (Q p)) • !![slopeGram B L n p 1 1, -slopeGram B L n p 0 1;
          -slopeGram B L n p 1 0, slopeGram B L n p 0 0]) i j
      rw [Ring.inverse_eq_inv, hpow]
      fin_cases i <;> fin_cases j <;>
        simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ite_true, ite_false,
          Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_fin_one, g00, g01, g10, g11]
      all_goals
        field_simp (disch := first | assumption | exact ne_of_gt (hQpos p) | positivity | norm_num)
        rw [hQdef]
        ring
    have slope_area_hessian_posDef
        (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.PosDef)
        (L : E2 →L[ℝ] E3) (n : E3)
        (hsplit : Function.Bijective (fun z : E2 × ℝ => L z.1 + z.2 • n))
        (p : E2) :
        (slopeHessian B L n p).PosDef := by
      classical
      have hgram (q : E2) : (slopeGram B L n q).PosDef := by
        let v : Fin 2 → E3 := fun i => L (coordinateVector 2 i) + q i • n
        have hli : LinearIndependent ℝ v := by
          apply Fintype.linearIndependent_iff.mpr
          intro a ha
          have hs : L (∑ i : Fin 2, a i • coordinateVector 2 i) +
              (∑ i : Fin 2, a i * q i) • n = 0 := by
            simpa only [v, smul_add, Finset.sum_add_distrib,
              map_sum, map_smul, mul_smul, Finset.sum_smul] using ha
          have he : ((∑ i : Fin 2, a i • coordinateVector 2 i), ∑ i : Fin 2, a i * q i) =
              ((0 : E2), (0 : ℝ)) := by
            apply hsplit.injective
            simpa only [map_zero, zero_smul, add_zero] using hs
          have hz := congrArg Prod.fst he
          intro i
          have heval := congrArg (fun z : E2 => z i) hz
          fin_cases i <;> simpa [coordinateVector, EuclideanSpace.single, Pi.single_apply] using heval
        let V : Matrix (Fin 3) (Fin 2) ℝ := fun a i => v i a
        have hV : Function.Injective V.mulVec := by
          intro x y hxy
          have hsum : ∑ i, (x i - y i) • v i = 0 := by
            ext a
            have hh := congrFun hxy a
            simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hh
            simpa only [Fin.sum_univ_two, PiLp.add_apply, PiLp.smul_apply,
              smul_eq_mul, sub_mul, PiLp.zero_apply] using (by
                dsimp [V] at hh
                nlinarith [hh] : (x 0 - y 0) * v 0 a + (x 1 - y 1) * v 1 a = 0)
          have he := Fintype.linearIndependent_iff.mp hli _ hsum
          funext i
          exact sub_eq_zero.mp (he i)
        have heq : slopeGram B L n q = V.conjTranspose * B * V := by
          ext i j
          change (∑ a : Fin 3, ∑ b : Fin 3, B a b * v i a * v j b) =
            ∑ b : Fin 3, (∑ a : Fin 3, v i a * B a b) * v j b
          simp only [Fin.sum_univ_three]
          ring
        rw [heq]
        exact hB.conjTranspose_mul_mul_same hV
      let v : Fin 3 → E3 := fun i => if i = 0 then L (coordinateVector 2 0)
        else if i = 1 then L (coordinateVector 2 1) else n
      let V : Matrix (Fin 3) (Fin 3) ℝ := fun a i => v i a
      have hV : Function.Injective V.mulVec := by
        intro x y hxy
        have hs : L ((x 0-y 0) • coordinateVector 2 0 + (x 1-y 1) • coordinateVector 2 1) +
            (x 2-y 2) • n = 0 := by
          ext a
          have hh := congrFun hxy a
          simp [Matrix.mulVec, dotProduct, V, v, Fin.sum_univ_three] at hh
          simp only [map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.zero_apply]
          nlinarith [hh]
        have he : (((x 0-y 0) • coordinateVector 2 0 + (x 1-y 1) • coordinateVector 2 1), x 2-y 2) =
            ((0 : E2), (0 : ℝ)) := by
          apply hsplit.injective
          simpa only [map_zero, zero_smul, add_zero] using hs
        have h0 := congrArg (fun z : E2 × ℝ => z.1 0) he
        have h1 := congrArg (fun z : E2 × ℝ => z.1 1) he
        have h2 := congrArg Prod.snd he
        simp [coordinateVector, EuclideanSpace.single, Pi.single_apply] at h0 h1
        funext i
        fin_cases i
        · exact sub_eq_zero.mp h0
        · exact sub_eq_zero.mp h1
        · exact sub_eq_zero.mp h2
      have heq : splittingGram B L n = V.conjTranspose * B * V := by
        ext i j
        change (∑ a : Fin 3, ∑ b : Fin 3, B a b * v i a * v j b) =
          ∑ b : Fin 3, (∑ a : Fin 3, v i a * B a b) * v j b
        simp only [Fin.sum_univ_three]
        ring
      have hf : (splittingGram B L n).PosDef := by
        rw [heq]
        exact hB.conjTranspose_mul_mul_same hV
      have ha : 0 < slopeArea B L n p := Real.sqrt_pos.mpr (hgram p).det_pos
      have hh : slopeHessian B L n p =
          (Matrix.det (splittingGram B L n) / slopeArea B L n p) • (slopeGram B L n p)⁻¹ := by
        ext i j
        exact slope_area_hessian_formula B hB L n hsplit p i j
      rw [hh]
      exact (hgram p).inv.smul (div_pos hf.det_pos ha)
    have compact_metric_slope_hessian_lower_bound
        (K : Set (Matrix (Fin 3) (Fin 3) ℝ)) (hK : IsCompact K)
        (hpositive : ∀ B ∈ K, B.PosDef)
        (P : Set E2) (hP : IsCompact P)
        (L : E2 →L[ℝ] E3) (n : E3)
        (hsplit : Function.Bijective (fun z : E2 × ℝ => L z.1 + z.2 • n)) :
        ∃ d a ℓ : ℝ, 0 < d ∧ 0 < a ∧ 0 < ℓ ∧
          (∀ B ∈ K, d ≤ Matrix.det (splittingGram B L n)) ∧
          (∀ B ∈ K, ∀ p ∈ P, slopeArea B L n p ≤ a ∧
            ∀ ξ : E2,
              (∑ i : Fin 2, ∑ j : Fin 2,
                slopeGram B L n p i j * ξ i * ξ j) ≤ ℓ * ‖ξ‖ ^ 2 ∧
              d / (a * ℓ) * ‖ξ‖ ^ 2 ≤
                inner ℝ (fderiv ℝ (slopeFlux B L n) p ξ) ξ) := by
      classical
      have hgeom (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.PosDef) :
          (splittingGram B L n).PosDef ∧ ∀ p, (slopeGram B L n p).PosDef := by
        have hgram (q : E2) : (slopeGram B L n q).PosDef := by
          let v : Fin 2 → E3 := fun i => L (coordinateVector 2 i) + q i • n
          have hli : LinearIndependent ℝ v := by
            apply Fintype.linearIndependent_iff.mpr
            intro a ha
            have hs : L (∑ i : Fin 2, a i • coordinateVector 2 i) +
                (∑ i : Fin 2, a i * q i) • n = 0 := by
              simpa only [v, smul_add, Finset.sum_add_distrib,
                map_sum, map_smul, mul_smul, Finset.sum_smul] using ha
            have he : ((∑ i : Fin 2, a i • coordinateVector 2 i), ∑ i : Fin 2, a i * q i) =
                ((0 : E2), (0 : ℝ)) := by
              apply hsplit.injective
              simpa only [map_zero, zero_smul, add_zero] using hs
            have hz := congrArg Prod.fst he
            intro i
            have heval := congrArg (fun z : E2 => z i) hz
            fin_cases i <;> simpa [coordinateVector, EuclideanSpace.single, Pi.single_apply] using heval
          let V : Matrix (Fin 3) (Fin 2) ℝ := fun a i => v i a
          have hV : Function.Injective V.mulVec := by
            intro x y hxy
            have hsum : ∑ i, (x i - y i) • v i = 0 := by
              ext a
              have hh := congrFun hxy a
              simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hh
              simpa only [Fin.sum_univ_two, PiLp.add_apply, PiLp.smul_apply,
                smul_eq_mul, sub_mul, PiLp.zero_apply] using (by
                  dsimp [V] at hh
                  nlinarith [hh] : (x 0 - y 0) * v 0 a + (x 1 - y 1) * v 1 a = 0)
            have he := Fintype.linearIndependent_iff.mp hli _ hsum
            funext i
            exact sub_eq_zero.mp (he i)
          have heq : slopeGram B L n q = V.conjTranspose * B * V := by
            ext i j
            change (∑ a : Fin 3, ∑ b : Fin 3, B a b * v i a * v j b) =
              ∑ b : Fin 3, (∑ a : Fin 3, v i a * B a b) * v j b
            simp only [Fin.sum_univ_three]
            ring
          rw [heq]
          exact hB.conjTranspose_mul_mul_same hV
        let v : Fin 3 → E3 := fun i => if i = 0 then L (coordinateVector 2 0)
          else if i = 1 then L (coordinateVector 2 1) else n
        let V : Matrix (Fin 3) (Fin 3) ℝ := fun a i => v i a
        have hV : Function.Injective V.mulVec := by
          intro x y hxy
          have hs : L ((x 0-y 0) • coordinateVector 2 0 + (x 1-y 1) • coordinateVector 2 1) +
              (x 2-y 2) • n = 0 := by
            ext a
            have hh := congrFun hxy a
            simp [Matrix.mulVec, dotProduct, V, v, Fin.sum_univ_three] at hh
            simp only [map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.zero_apply]
            nlinarith [hh]
          have he : (((x 0-y 0) • coordinateVector 2 0 + (x 1-y 1) • coordinateVector 2 1), x 2-y 2) =
              ((0 : E2), (0 : ℝ)) := by
            apply hsplit.injective
            simpa only [map_zero, zero_smul, add_zero] using hs
          have h0 := congrArg (fun z : E2 × ℝ => z.1 0) he
          have h1 := congrArg (fun z : E2 × ℝ => z.1 1) he
          have h2 := congrArg Prod.snd he
          simp [coordinateVector, EuclideanSpace.single, Pi.single_apply] at h0 h1
          funext i
          fin_cases i
          · exact sub_eq_zero.mp h0
          · exact sub_eq_zero.mp h1
          · exact sub_eq_zero.mp h2
        have heq : splittingGram B L n = V.conjTranspose * B * V := by
          ext i j
          change (∑ a : Fin 3, ∑ b : Fin 3, B a b * v i a * v j b) =
            ∑ b : Fin 3, (∑ a : Fin 3, v i a * B a b) * v j b
          simp only [Fin.sum_univ_three]
          ring
        have hf : (splittingGram B L n).PosDef := by
          rw [heq]
          exact hB.conjTranspose_mul_mul_same hV
        exact ⟨hf, hgram⟩
      have hinner (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.PosDef)
        (L : E2 →L[ℝ] E3) (n : E3)
        (hsplit : Function.Bijective (fun z : E2 × ℝ => L z.1 + z.2 • n))
        (p ξ : E2) :
        inner ℝ (fderiv ℝ (slopeFlux B L n) p ξ) ξ =
          ∑ i : Fin 2, ∑ j : Fin 2, slopeHessian B L n p i j * ξ i * ξ j := by
        classical
        have hc (i : Fin 2) : DifferentiableAt ℝ (fun q : E2 => slopeFlux B L n q i) p := by
          by_contra hn
          have hp : 0 < slopeHessian B L n p i i :=
            (slope_area_hessian_posDef B hB L n hsplit p).diag_pos
          change 0 < (fderiv ℝ (fun q : E2 => slopeFlux B L n q i) p) (coordinateVector 2 i) at hp
          rw [fderiv_zero_of_not_differentiableAt hn, ContinuousLinearMap.zero_apply] at hp
          exact (lt_irrefl 0) hp
        have hf : DifferentiableAt ℝ (slopeFlux B L n) p :=
          (differentiableAt_piLp 2).mpr hc
        have hi (i : Fin 2) : fderiv ℝ (fun q : E2 => slopeFlux B L n q i) p =
            (EuclideanSpace.proj i).comp (fderiv ℝ (slopeFlux B L n) p) := by
          exact ((EuclideanSpace.proj i).hasFDerivAt.comp p hf.hasFDerivAt).fderiv
        have hx : ξ = ∑ j : Fin 2, ξ j • coordinateVector 2 j := by
          ext i
          fin_cases i <;> simp [coordinateVector, EuclideanSpace.single]
        rw [PiLp.inner_apply, Fin.sum_univ_two]
        simp only [RCLike.inner_apply, conj_trivial]
        have hh (i : Fin 2) : (fderiv ℝ (slopeFlux B L n) p ξ) i =
            ∑ j : Fin 2, ξ j * slopeHessian B L n p i j := by
          change (EuclideanSpace.proj i) (fderiv ℝ (slopeFlux B L n) p ξ) = _
          rw [← ContinuousLinearMap.comp_apply, ← hi]
          conv_lhs => rw [hx]
          simp only [map_sum, map_smul, smul_eq_mul]
          rfl
        rw [hh 0, hh 1]
        simp only [Fin.sum_univ_two]
        ring
      have hinv (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : A.PosDef)
        (ℓ : ℝ) (hℓ : 0 < ℓ)
        (hbound : ∀ ξ : E2, (∑ i : Fin 2, ∑ j : Fin 2, A i j * ξ i * ξ j) ≤ ℓ * ‖ξ‖^2)
        (ξ : E2) : ‖ξ‖^2 / ℓ ≤ ∑ i : Fin 2, ∑ j : Fin 2, A⁻¹ i j * ξ i * ξ j := by
        classical
        have hn : ‖ξ‖^2 = ξ 0 * ξ 0 + ξ 1 * ξ 1 := by
          rw [← real_inner_self_eq_norm_sq ξ, PiLp.inner_apply]
          simp [Fin.sum_univ_two, RCLike.inner_apply, pow_two]
        have hq (M : Matrix (Fin 2) (Fin 2) ℝ) :
            (∑ i : Fin 2, ∑ j : Fin 2, M i j * ξ i * ξ j) =
              dotProduct (star (WithLp.ofLp ξ)) (Matrix.mulVec M (WithLp.ofLp ξ)) := by
          simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
          ring
        have hc := hA.star_dotProduct_mulVec_mul_le (WithLp.ofLp ξ) (Matrix.mulVec A⁻¹ (WithLp.ofLp ξ))
        have he : Matrix.mulVec A (Matrix.mulVec A⁻¹ (WithLp.ofLp ξ)) = WithLp.ofLp ξ := by
          rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA.det_pos.ne'), Matrix.one_mulVec]
        rw [he] at hc
        have hs : dotProduct (star (Matrix.mulVec A⁻¹ (WithLp.ofLp ξ))) (WithLp.ofLp ξ) =
            dotProduct (star (WithLp.ofLp ξ)) (Matrix.mulVec A⁻¹ (WithLp.ofLp ξ)) := by
          simp only [star_trivial]
          exact dotProduct_comm _ _
        rw [hs, ← hq A, ← hq A⁻¹] at hc
        have hd : dotProduct (star (WithLp.ofLp ξ)) (WithLp.ofLp ξ) = ‖ξ‖^2 := by
          simp only [dotProduct, Fin.sum_univ_two, Pi.star_apply, star_trivial, hn]
        rw [hd, star_trivial] at hc
        have hp : 0 ≤ ∑ i : Fin 2, ∑ j : Fin 2, A⁻¹ i j * ξ i * ξ j := by
          rw [hq]
          exact hA.inv.posSemidef.dotProduct_mulVec_nonneg _
        have hc' := hc.trans (mul_le_mul_of_nonneg_right (hbound ξ) hp)
        by_cases hx : ξ = 0
        · simp [hx]
        · have hnorm : 0 < ‖ξ‖^2 := pow_pos (norm_pos_iff.mpr hx) _
          apply (div_le_iff₀ hℓ).mpr
          nlinarith
      have hbounds :
          ∃ d a ℓ : ℝ, 0 < d ∧ 0 < a ∧ 0 < ℓ ∧
            (∀ B ∈ K, d ≤ Matrix.det (splittingGram B L n)) ∧
            (∀ B ∈ K, ∀ p ∈ P, slopeArea B L n p ≤ a ∧
              ∀ ξ : E2, (∑ i : Fin 2, ∑ j : Fin 2,
                slopeGram B L n p i j * ξ i * ξ j) ≤ ℓ * ‖ξ‖ ^ 2)
          := by
        have hdcont : Continuous (fun B => Matrix.det (splittingGram B L n)) := by
          apply Continuous.matrix_det
          apply continuous_pi; intro i
          apply continuous_pi; intro j
          change Continuous (fun B : Matrix (Fin 3) (Fin 3) ℝ => ∑ a : Fin 3, ∑ b : Fin 3, B a b *
            (if i = 0 then L (coordinateVector 2 0) else if i = 1 then L (coordinateVector 2 1) else n) a *
            (if j = 0 then L (coordinateVector 2 0) else if j = 1 then L (coordinateVector 2 1) else n) b)
          fun_prop
        obtain ⟨d, hd, hdb⟩ := hK.exists_forall_le' hdcont.continuousOn
          (fun B hB => (hgeom B (hpositive B hB)).1.det_pos)
        have hacont : Continuous (fun z : Matrix (Fin 3) (Fin 3) ℝ × E2 => slopeArea z.1 L n z.2) := by
          apply Real.continuous_sqrt.comp
          apply Continuous.matrix_det
          apply continuous_pi; intro i
          apply continuous_pi; intro j
          unfold slopeGram coordinateInner
          simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
          fun_prop
        obtain ⟨a₀, ha₀⟩ := (hK.prod hP).bddAbove_image hacont.continuousOn
        let c := fun z : Matrix (Fin 3) (Fin 3) ℝ × E2 =>
          ∑ i : Fin 2, ∑ j : Fin 2, |slopeGram z.1 L n z.2 i j|
        have hccont : Continuous c := by
          unfold c slopeGram coordinateInner
          simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
          fun_prop
        obtain ⟨ℓ₀, hℓ₀⟩ := (hK.prod hP).bddAbove_image hccont.continuousOn
        refine ⟨d, max a₀ 1, max ℓ₀ 1, hd, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
          lt_of_lt_of_le zero_lt_one (le_max_right _ _), hdb, ?_⟩
        intro B hB p hp
        refine ⟨(ha₀ ⟨(B,p), ⟨hB,hp⟩, rfl⟩).trans (le_max_left _ _), ?_⟩
        intro ξ
        have hnorm (i : Fin 2) : |ξ i| ≤ ‖ξ‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le ξ i
        have hterm (i j : Fin 2) : slopeGram B L n p i j * ξ i * ξ j ≤
            |slopeGram B L n p i j| * ‖ξ‖^2 := by
          calc
            _ ≤ |slopeGram B L n p i j * ξ i * ξ j| := le_abs_self _
            _ = |slopeGram B L n p i j| * (|ξ i| * |ξ j|) := by rw [abs_mul,abs_mul];ring
            _ ≤ |slopeGram B L n p i j| * (‖ξ‖ * ‖ξ‖) :=
              mul_le_mul_of_nonneg_left (mul_le_mul (hnorm i) (hnorm j) (abs_nonneg _) (norm_nonneg _)) (abs_nonneg _)
            _ = _ := by ring
        calc
          _ ≤ ∑ i : Fin 2, ∑ j : Fin 2, |slopeGram B L n p i j| * ‖ξ‖^2 :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
          _ = c (B,p) * ‖ξ‖^2 := by simp only [c,Finset.sum_mul]
          _ ≤ max ℓ₀ 1 * ‖ξ‖^2 := mul_le_mul_of_nonneg_right
            ((hℓ₀ ⟨(B,p), ⟨hB,hp⟩, rfl⟩).trans (le_max_left _ _)) (sq_nonneg _)
      obtain ⟨d,a,ℓ,hd,ha,hℓ,hdet,hbounds⟩ := hbounds
      refine ⟨d,a,ℓ,hd,ha,hℓ,hdet,?_⟩
      intro B hB p hp
      refine ⟨(hbounds B hB p hp).1, ?_⟩
      intro ξ
      refine ⟨(hbounds B hB p hp).2 ξ, ?_⟩
      have hA := hgeom B (hpositive B hB)
      have harea : 0 < slopeArea B L n p := Real.sqrt_pos.mpr (hA.2 p).det_pos
      have hratio : d/a ≤ (Matrix.det (splittingGram B L n))/slopeArea B L n p := by
        apply (div_le_div_iff₀ ha harea).mpr
        exact (mul_le_mul_of_nonneg_left (hbounds B hB p hp).1 hd.le).trans
          (mul_le_mul_of_nonneg_right (hdet B hB) ha.le)
      rw [hinner B (hpositive B hB) L n hsplit p ξ]
      have hsum : (∑ i : Fin 2, ∑ j : Fin 2, slopeHessian B L n p i j * ξ i * ξ j) =
          (Matrix.det (splittingGram B L n)/slopeArea B L n p) *
            (∑ i : Fin 2, ∑ j : Fin 2, (slopeGram B L n p)⁻¹ i j * ξ i * ξ j) := by
        simp_rw [slope_area_hessian_formula B (hpositive B hB) L n hsplit p]
        simp only [Fin.sum_univ_two]
        ring
      rw [hsum]
      calc
        d/(a*ℓ)*‖ξ‖^2 = (d/a)*(‖ξ‖^2/ℓ) := by ring
        _ ≤ (Matrix.det (splittingGram B L n)/slopeArea B L n p)*(‖ξ‖^2/ℓ) :=
          mul_le_mul_of_nonneg_right hratio (div_nonneg (sq_nonneg _) hℓ.le)
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (hinv (slopeGram B L n p) (hA.2 p) ℓ hℓ (hbounds B hB p hp).2 ξ)
          (div_nonneg hA.1.det_pos.le harea.le)
    let L : E2 →L[ℝ] E3 :=
      (EuclideanSpace.proj 0).smulRight (coordinateVector 3 0) +
        (EuclideanSpace.proj 1).smulRight (coordinateVector 3 1)
    let n : E3 := coordinateVector 3 2
    have hL (i : Fin 2) : L (coordinateVector 2 i) = coordinateVector 3 (Fin.castSucc i) := by
      fin_cases i <;> ext k <;> fin_cases k <;>
        simp [L, coordinateVector, EuclideanSpace.single]
    have hsplit : Function.Bijective (fun z : E2 × ℝ => L z.1 + z.2 • n) := by
      constructor
      · intro z w h
        have h0 := congrArg (fun y : E3 => y 0) h
        have h1 := congrArg (fun y : E3 => y 1) h
        have h2 := congrArg (fun y : E3 => y 2) h
        simp [L,n,coordinateVector,EuclideanSpace.single] at h0 h1 h2
        apply Prod.ext
        · ext i
          fin_cases i
          · exact h0
          · exact h1
        · exact h2
      · intro y
        refine ⟨((EuclideanSpace.equiv (Fin 2) ℝ).symm ![y 0,y 1],y 2),?_⟩
        ext k
        fin_cases k <;> simp [L,n,coordinateVector,EuclideanSpace.single]
    have hsplitGram (B : Matrix (Fin 3) (Fin 3) ℝ) : splittingGram B L n = B := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [splittingGram,coordinateInner,L,n,coordinateVector,EuclideanSpace.single,
          Fin.sum_univ_three]
    have hmetric (y : E3) (hy : y ∈ W.V) : (W.metric.tensor y).PosDef := by
      apply Matrix.PosDef.of_dotProduct_mulVec_pos
      · ext a c
        exact W.metric.symmetric y hy c a
      · intro x hx
        let w : E3 := WithLp.toLp 2 x
        have hw : w ≠ 0 := by
          intro he
          apply hx
          exact congrArg WithLp.ofLp he
        have hp := W.metric.positive y hy w hw
        convert hp using 1
        simp only [coordinateInner,dotProduct,Matrix.mulVec,Fin.sum_univ_three,
          Pi.star_apply,star_trivial]
        dsimp [w]
        ring
    have hgram_eq (x : E2) (z : ℝ) (p : E2) :
        slopeGram (W.metric.tensor (jetPoint (x,z,p))) L n p = W.gram (x,z,p) := by
      ext i k
      dsimp [slopeGram,CollarWindow.gram,jetTangent]
      rw [hL i,hL k]
      rfl
    have harea_eq (x : E2) (z : ℝ) :
        slopeArea (W.metric.tensor (jetPoint (x,z,0))) L n =
          (fun p : E2 => W.density (x,z,p)) := by
      funext p
      exact congrArg (fun A : Mat2 => Real.sqrt (Matrix.det A)) (hgram_eq x z p)
    have hflux_eq (x : E2) (z : ℝ) :
        slopeFlux (W.metric.tensor (jetPoint (x,z,0))) L n =
          (fun p : E2 => W.flux (x,z,p)) := by
      dsimp [slopeFlux,CollarWindow.flux]
      rw [harea_eq]
    have hhessian_eq (j : Jet) :
        slopeHessian (W.metric.tensor (jetPoint j)) L n j.2.2 =
          (Matrix.of fun i k => fderiv ℝ (fun p : E2 => W.flux (j.1,j.2.1,p) i)
            j.2.2 (coordinateVector 2 k)) := by
      rcases j with ⟨x,z,p⟩
      ext i k
      dsimp [slopeHessian]
      change fderiv ℝ (fun q : E2 => slopeFlux (W.metric.tensor (jetPoint (x,z,0))) L n q i)
        p (coordinateVector 2 k) = _
      rw [hflux_eq x z]
    have hformula (j : Jet) (hj : jetPoint j ∈ W.V) (i k : Fin 2) :
        fderiv ℝ (fun p : E2 => W.flux (j.1,j.2.1,p) i) j.2.2
          (coordinateVector 2 k) = Matrix.det (W.metric.tensor (jetPoint j)) / W.density j *
            (W.gram j)⁻¹ i k := by
      have h := slope_area_hessian_formula (W.metric.tensor (jetPoint j))
        (hmetric _ hj) L n hsplit j.2.2 i k
      rw [hsplitGram, hhessian_eq] at h
      change _ = Matrix.det (W.metric.tensor (jetPoint j)) / Real.sqrt (Matrix.det (W.gram j)) *
        (W.gram j)⁻¹ i k
      simpa only [slopeArea,hgram_eq,Prod.eta,Matrix.of_apply] using h
    have hsym (j : Jet) (hj : jetPoint j ∈ W.V) (i k : Fin 2) :
        fderiv ℝ (fun p : E2 => W.flux (j.1,j.2.1,p) i) j.2.2
          (coordinateVector 2 k) =
        fderiv ℝ (fun p : E2 => W.flux (j.1,j.2.1,p) k) j.2.2
          (coordinateVector 2 i) := by
      have h := (slope_area_hessian_posDef (W.metric.tensor (jetPoint j))
        (hmetric _ hj) L n hsplit j.2.2).isHermitian.apply k i
      rw [hhessian_eq] at h
      simpa only [star_trivial,Matrix.of_apply] using h
    have hgrampos (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.PosDef) (q : E2) : (slopeGram B L n q).PosDef := by
      let v : Fin 2 → E3 := fun i => L (coordinateVector 2 i) + q i • n
      have hli : LinearIndependent ℝ v := by
        apply Fintype.linearIndependent_iff.mpr
        intro a ha
        have hs : L (∑ i : Fin 2, a i • coordinateVector 2 i) +
            (∑ i : Fin 2, a i * q i) • n = 0 := by
          simpa only [v, smul_add, Finset.sum_add_distrib,
            map_sum, map_smul, mul_smul, Finset.sum_smul] using ha
        have he : ((∑ i : Fin 2, a i • coordinateVector 2 i), ∑ i : Fin 2, a i * q i) =
            ((0 : E2), (0 : ℝ)) := by
          apply hsplit.injective
          simpa only [map_zero, zero_smul, add_zero] using hs
        have hz := congrArg Prod.fst he
        intro i
        have heval := congrArg (fun z : E2 => z i) hz
        fin_cases i <;> simpa [coordinateVector, EuclideanSpace.single, Pi.single_apply] using heval
      let V : Matrix (Fin 3) (Fin 2) ℝ := fun a i => v i a
      have hV : Function.Injective V.mulVec := by
        intro x y hxy
        have hsum : ∑ i, (x i - y i) • v i = 0 := by
          ext a
          have hh := congrFun hxy a
          simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hh
          simpa only [Fin.sum_univ_two, PiLp.add_apply, PiLp.smul_apply,
            smul_eq_mul, sub_mul, PiLp.zero_apply] using (by
              dsimp [V] at hh
              nlinarith [hh] : (x 0 - y 0) * v 0 a + (x 1 - y 1) * v 1 a = 0)
        have he := Fintype.linearIndependent_iff.mp hli _ hsum
        funext i
        exact sub_eq_zero.mp (he i)
      have heq : slopeGram B L n q = V.conjTranspose * B * V := by
        ext i j
        change (∑ a : Fin 3, ∑ b : Fin 3, B a b * v i a * v j b) =
          ∑ b : Fin 3, (∑ a : Fin 3, v i a * B a b) * v j b
        simp only [Fin.sum_univ_three]
        ring
      rw [heq]
      exact hB.conjTranspose_mul_mul_same hV
    have hinner (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.PosDef)
      (L : E2 →L[ℝ] E3) (n : E3)
      (hsplit : Function.Bijective (fun z : E2 × ℝ => L z.1 + z.2 • n))
      (p ξ : E2) :
      inner ℝ (fderiv ℝ (slopeFlux B L n) p ξ) ξ =
        ∑ i : Fin 2, ∑ j : Fin 2, slopeHessian B L n p i j * ξ i * ξ j := by
      classical
      have hc (i : Fin 2) : DifferentiableAt ℝ (fun q : E2 => slopeFlux B L n q i) p := by
        by_contra hn
        have hp : 0 < slopeHessian B L n p i i :=
          (slope_area_hessian_posDef B hB L n hsplit p).diag_pos
        change 0 < (fderiv ℝ (fun q : E2 => slopeFlux B L n q i) p) (coordinateVector 2 i) at hp
        rw [fderiv_zero_of_not_differentiableAt hn, ContinuousLinearMap.zero_apply] at hp
        exact (lt_irrefl 0) hp
      have hf : DifferentiableAt ℝ (slopeFlux B L n) p :=
        (differentiableAt_piLp 2).mpr hc
      have hi (i : Fin 2) : fderiv ℝ (fun q : E2 => slopeFlux B L n q i) p =
          (EuclideanSpace.proj i).comp (fderiv ℝ (slopeFlux B L n) p) := by
        exact ((EuclideanSpace.proj i).hasFDerivAt.comp p hf.hasFDerivAt).fderiv
      have hx : ξ = ∑ j : Fin 2, ξ j • coordinateVector 2 j := by
        ext i
        fin_cases i <;> simp [coordinateVector, EuclideanSpace.single]
      rw [PiLp.inner_apply, Fin.sum_univ_two]
      simp only [RCLike.inner_apply, conj_trivial]
      have hh (i : Fin 2) : (fderiv ℝ (slopeFlux B L n) p ξ) i =
          ∑ j : Fin 2, ξ j * slopeHessian B L n p i j := by
        change (EuclideanSpace.proj i) (fderiv ℝ (slopeFlux B L n) p ξ) = _
        rw [← ContinuousLinearMap.comp_apply, ← hi]
        conv_lhs => rw [hx]
        simp only [map_sum, map_smul, smul_eq_mul]
        rfl
      rw [hh 0, hh 1]
      simp only [Fin.sum_univ_two]
      ring
    have hclosed : IsCompact (B1Tangency.closedHalfDisc W.R) := by
      change IsCompact (Metric.closedBall (0 : E2) W.R ∩ {x : E2 | 0 ≤ x 1})
      exact (isCompact_closedBall (0 : E2) W.R).inter_right
        (isClosed_le continuous_const (by fun_prop))
    have hgradU : ContinuousOn (planarGradient (localHeight D s)) W.U := by
      have hdu : ContinuousOn (fderiv ℝ (localHeight D s)) W.U := by
        intro x hx
        exact (((W.height_smooth x hx).contDiffAt (W.U_open.mem_nhds hx)).fderiv_right
          (m := 0) (by simp)).continuousAt.continuousWithinAt
      unfold planarGradient
      apply continuousOn_finsetSum
      intro i hi
      exact (hdu.clm_apply continuousOn_const).smul continuousOn_const
    let X : Set (E2 × ℝ) := B1Tangency.closedHalfDisc W.R ×ˢ Icc (0 : ℝ) 1
    have hX : IsCompact X := hclosed.prod isCompact_Icc
    let jmap : E2 × ℝ → Jet := fun z => W.segmentJet z.1 z.2
    have hjmap : ContinuousOn jmap X := by
      exact continuousOn_fst.prodMk
        ((continuousOn_snd.mul (W.height_smooth.continuousOn.comp continuousOn_fst
          (fun z hz => W.U_contains hz.1))).prodMk
          (continuousOn_snd.smul (hgradU.comp continuousOn_fst
            (fun z hz => W.U_contains hz.1))))
    have hjV (z : E2 × ℝ) (hz : z ∈ X) : jetPoint (jmap z) ∈ W.V :=
      W.jets_inside z.1 hz.1 z.2 hz.2
    have hjpoint : Continuous jetPoint := by unfold jetPoint; fun_prop
    let B : E2 × ℝ → Matrix (Fin 3) (Fin 3) ℝ := fun z => W.metric.tensor (jetPoint (jmap z))
    have hBcont : ContinuousOn B X := by
      apply continuousOn_pi.mpr; intro i
      apply continuousOn_pi.mpr; intro k
      exact (W.metric.smooth i k).continuousOn.comp
        (hjpoint.continuousOn.comp hjmap (fun z hz => mem_univ _)) hjV
    have hBpositive : ∀ b ∈ B '' X, b.PosDef := by
      rintro b ⟨z,hz,rfl⟩
      exact hmetric _ (hjV z hz)
    let P : Set E2 := (fun z : E2 × ℝ => (jmap z).2.2) '' X
    have hP : IsCompact P := hX.image_of_continuousOn (continuousOn_snd.comp
      (continuousOn_snd.comp hjmap (fun z hz => mem_univ _)) (fun z hz => mem_univ _))
    obtain ⟨d,a₀,l₀,hd,ha₀,hl₀,hdet,hbound⟩ :=
      compact_metric_slope_hessian_lower_bound (B '' X) (hX.image_of_continuousOn hBcont)
        hBpositive P hP L n hsplit
    let ell : ℝ := d / (a₀*l₀)
    have hell : 0 < ell := div_pos hd (mul_pos ha₀ hl₀)
    let A : E2 × ℝ → Mat2 := fun z => slopeGram (B z) L n (jmap z).2.2
    let H : E2 × ℝ → Mat2 := fun z => slopeHessian (B z) L n (jmap z).2.2
    have hApositive (z : E2 × ℝ) (hz : z ∈ X) : (A z).PosDef :=
      hgrampos (B z) (hmetric _ (hjV z hz)) _
    have hAcont : ContinuousOn A X := by
      have hg : Continuous (fun z : Matrix (Fin 3) (Fin 3) ℝ × E2 => slopeGram z.1 L n z.2) := by
        apply continuous_pi; intro i
        apply continuous_pi; intro k
        unfold slopeGram coordinateInner
        simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
        fun_prop
      exact hg.continuousOn.comp (hBcont.prodMk (continuousOn_snd.comp
        (continuousOn_snd.comp hjmap (fun z hz => mem_univ _)) (fun z hz => mem_univ _)))
        (fun z hz => mem_univ _)
    have hinvcont : ContinuousOn (fun z => (A z)⁻¹) X := by
      intro z hz
      apply (continuousAt_matrix_inv (A z) ?_).comp_continuousWithinAt (hAcont z hz)
      have heq : (Ring.inverse : ℝ → ℝ) = Inv.inv := by
        funext r
        exact Ring.inverse_eq_inv r
      rw [heq]
      exact continuousAt_inv₀ (hApositive z hz).det_pos.ne'
    have hcoefcont : ContinuousOn (fun z => Matrix.det (B z) / Real.sqrt (Matrix.det (A z))) X :=
      (continuous_id.matrix_det.continuousOn.comp hBcont (fun z hz => mem_univ _)).div
        (Real.continuous_sqrt.continuousOn.comp
          (continuous_id.matrix_det.continuousOn.comp hAcont (fun z hz => mem_univ _))
        (fun z hz => mem_univ _)) (fun z hz => (Real.sqrt_pos.mpr (hApositive z hz).det_pos).ne')
    have hHcont : ContinuousOn H X := by
      apply (hcoefcont.smul hinvcont).congr
      intro z hz
      ext i k
      exact slope_area_hessian_formula (B z) (hmetric _ (hjV z hz)) L n hsplit
        (jmap z).2.2 i k |>.trans (by rw [hsplitGram]; rfl)
    let sumAbs : E2 × ℝ → ℝ := fun z => ∑ i : Fin 2, ∑ k : Fin 2, |H z i k|
    have hsumcont : ContinuousOn sumAbs X := by
      apply continuousOn_finsetSum
      intro i hi
      apply continuousOn_finsetSum
      intro k hk
      exact ((continuous_apply k).comp_continuousOn
        ((continuous_apply i).comp_continuousOn hHcont)).abs
    obtain ⟨C₀,hC₀⟩ := hX.bddAbove_image hsumcont
    let C : ℝ := max C₀ 1
    have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have hquad (M : Mat2) (p : E2) :
        inner ℝ p (matrixAction M p) = ∑ i : Fin 2, ∑ k : Fin 2, M i k * p i * p k := by
      change inner ℝ p ((EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i => ∑ k, M i k * p k)) = _
      simp [PiLp.inner_apply,Fin.sum_univ_two,RCLike.inner_apply]
      ring
    have hpointwise (z : E2 × ℝ) (hz : z ∈ X) (p : E2) :
        ell*‖p‖^2 ≤ inner ℝ p (matrixAction (H z) p) ∧
          inner ℝ p (matrixAction (H z) p) ≤ C*‖p‖^2 := by
      constructor
      · have h := ((hbound (B z) (mem_image_of_mem B hz) (jmap z).2.2
          (mem_image_of_mem (fun z : E2 × ℝ => (jmap z).2.2) hz)).2 p).2
        rw [hinner (B z) (hmetric _ (hjV z hz)) L n hsplit, ← hquad] at h
        exact h
      · have hnorm (i : Fin 2) : |p i| ≤ ‖p‖ := by
          simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le p i
        have hterm (i k : Fin 2) : H z i k * p i * p k ≤ |H z i k| * ‖p‖^2 := by
          calc
            _ ≤ |H z i k * p i * p k| := le_abs_self _
            _ = |H z i k| * (|p i| * |p k|) := by rw [abs_mul,abs_mul]; ring
            _ ≤ |H z i k| * (‖p‖*‖p‖) := mul_le_mul_of_nonneg_left
              (mul_le_mul (hnorm i) (hnorm k) (abs_nonneg _) (norm_nonneg _)) (abs_nonneg _)
            _ = _ := by ring
        rw [hquad]
        calc
          _ ≤ ∑ i : Fin 2, ∑ k : Fin 2, |H z i k| * ‖p‖^2 :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => hterm i k
          _ = sumAbs z * ‖p‖^2 := by simp only [sumAbs,Finset.sum_mul]
          _ ≤ C*‖p‖^2 := mul_le_mul_of_nonneg_right
            ((hC₀ (mem_image_of_mem sumAbs hz)).trans (le_max_left _ _)) (sq_nonneg _)
    refine ⟨hformula, ?_, ell,C,hell,hC,?_⟩
    · intro x hx i j
      apply intervalIntegral.integral_congr
      intro t ht
      exact hsym (W.segmentJet x t) (W.jets_inside x hx t (by simpa using ht)) i j
    · intro x hx p
      have htmap : Continuous (fun t : ℝ => (x,t)) := continuous_const.prodMk continuous_id
      have hentrycont (i k : Fin 2) : ContinuousOn (fun t : ℝ => H (x,t) i k) (Icc (0 : ℝ) 1) :=
        ((continuous_apply k).comp_continuousOn ((continuous_apply i).comp_continuousOn hHcont)).comp
          htmap.continuousOn (fun t ht => ⟨hx,ht⟩)
      have hint (i k : Fin 2) : IntervalIntegrable (fun t : ℝ => H (x,t) i k) volume 0 1 := by
        apply ContinuousOn.intervalIntegrable
        simpa only [uIcc_of_le zero_le_one] using hentrycont i k
      have hQint : IntervalIntegrable
          (fun t : ℝ => inner ℝ p (matrixAction (H (x,t)) p)) volume 0 1 := by
        simp_rw [hquad]
        exact IntervalIntegrable.sum Finset.univ fun i _ => IntervalIntegrable.sum Finset.univ fun k _ =>
          ((hint i k).mul_const (p i)).mul_const (p k)
      have haeq (i k : Fin 2) : W.a x i k = ∫ t in (0 : ℝ)..1, H (x,t) i k := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact (congrFun (congrFun (hhessian_eq (W.segmentJet x t)) i) k).symm
      have hQeq : inner ℝ p (matrixAction (W.a x) p) =
          ∫ t in (0 : ℝ)..1, inner ℝ p (matrixAction (H (x,t)) p) := by
        simp_rw [hquad,haeq]
        rw [intervalIntegral.integral_finsetSum (s := Finset.univ)
          (f := fun i t => ∑ k : Fin 2, H (x,t) i k * p i * p k)
          (fun i _ => IntervalIntegrable.sum Finset.univ fun k _ =>
            ((hint i k).mul_const (p i)).mul_const (p k))]
        apply Finset.sum_congr rfl
        intro i hi
        rw [intervalIntegral.integral_finsetSum (s := Finset.univ)
          (f := fun k t => H (x,t) i k * p i * p k)
          (fun k _ => ((hint i k).mul_const (p i)).mul_const (p k))]
        simp_rw [intervalIntegral.integral_mul_const]
      rw [hQeq]
      constructor
      · have h := intervalIntegral.integral_mono_on zero_le_one
          (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => ell*‖p‖^2) volume 0 1)
          hQint (fun t ht => (hpointwise (x,t) ⟨hx,ht⟩ p).1)
        simpa only [intervalIntegral.integral_const,sub_zero,one_smul] using h
      · have h := intervalIntegral.integral_mono_on zero_le_one hQint
          (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => C*‖p‖^2) volume 0 1)
          (fun t ht => (hpointwise (x,t) ⟨hx,ht⟩ p).2)
        simpa only [intervalIntegral.integral_const,sub_zero,one_smul] using h

end SeifertSurfaces.OriginalEndpoints.B1GraphCoefficients
