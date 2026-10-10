import B1InteriorCoefficientData_v475
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped Manifold ContDiff BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
theorem native_interior_coefficient_open_tube_v475 (W : NativeInteriorGraphWindow_v475) :
    ∃ O : Set E2, IsOpen O ∧ W.compactBase ⊆ O ∧ O ⊆ W.U ∧
      (∀ x ∈ O, ∀ t ∈ Icc (0 : ℝ) 1, jetPoint (W.segmentJet x t) ∈ W.V) ∧
      ContDiffOn ℝ ∞ (W.height) O ∧
      ContDiffOn ℝ ∞ (planarGradient (W.height)) O ∧
      (∀ i j : Fin 2, ContDiffOn ℝ ∞ (fun x => W.a x i j) O) ∧
      ContDiffOn ℝ ∞ W.q O ∧ ContDiffOn ℝ ∞ W.lowerGradient O ∧
      ContDiffOn ℝ ∞ W.lowerHeight O ∧ ContDiffOn ℝ ∞ W.b O ∧
      ContDiffOn ℝ ∞ W.c O := by
  have hcal := native_interior_graph_jet_calculus_v475 W.V W.V_open W.metric
  have hd : ContDiffOn ℝ ∞ W.density (jetPoint ⁻¹' W.V) := hcal.1
  have hfl : ContDiffOn ℝ ∞ W.flux (jetPoint ⁻¹' W.V) ∧
      ContDiffOn ℝ ∞ W.lower (jetPoint ⁻¹' W.V) := hcal.2
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
  have hg : ContDiffOn ℝ ∞ (planarGradient (W.height)) W.U := by
    unfold planarGradient
    have hd : ContDiffOn ℝ ∞ (fderiv ℝ (W.height)) W.U :=
      W.height_smooth.fderiv_of_isOpen W.U_open (by simp)
    exact ContDiffOn.sum (fun i _ => (hd.clm_apply contDiffOn_const).smul_const _)
  let P : Set (E2 × ℝ) := {p | p.1 ∈ W.U ∧ jetPoint (W.segmentJet p.1 p.2) ∈ W.V}
  have hp : ContDiffOn ℝ ∞ (fun p : E2 × ℝ => jetPoint (W.segmentJet p.1 p.2))
      (W.U ×ˢ univ) := by
    have hf : ContDiffOn ℝ ∞ (fun p : E2 × ℝ => W.height p.1) (W.U ×ˢ univ) :=
      W.height_smooth.comp contDiffOn_fst (fun p hp => hp.1)
    unfold jetPoint NativeInteriorGraphWindow_v475.segmentJet
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
  have hH : IsCompact W.compactBase := W.compactBase_compact
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
    have hh : ContDiffOn ℝ ∞ (fun p : E2 × ℝ => W.height p.1) (O ×ˢ Q) :=
      hheight.comp contDiffOn_fst (fun p hp => hp.1)
    have hhg : ContDiffOn ℝ ∞ (fun p : E2 × ℝ => planarGradient (W.height) p.1) (O ×ˢ Q) :=
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


#print axioms native_interior_coefficient_open_tube_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
