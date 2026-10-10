import A5BoundaryBootstrapDefinitionsV465

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity

theorem openHalfDisc_isOpen (ρ : ℝ) : IsOpen (openHalfDisc ρ) := by
  exact Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (0 : Fin 2)).continuous)

theorem openHalfDisc_subset_closedHalfDisc (ρ : ℝ) :
    openHalfDisc ρ ⊆ closedHalfDisc ρ := by
  intro x hx
  have hxpos : 0 < x 0 := hx.2
  exact ⟨Metric.mem_closedBall.mpr (Metric.mem_ball.mp hx.1).le, hxpos.le⟩

theorem openHalfDisc_subset_interior_closedHalfDisc (ρ : ℝ) :
    openHalfDisc ρ ⊆ interior (closedHalfDisc ρ) :=
  interior_maximal (openHalfDisc_subset_closedHalfDisc ρ) (openHalfDisc_isOpen ρ)

theorem closedHalfDisc_mono {r ρ : ℝ} (h : r ≤ ρ) :
    closedHalfDisc r ⊆ closedHalfDisc ρ := by
  intro x hx
  exact ⟨Metric.closedBall_subset_closedBall h hx.1, hx.2⟩

theorem closedHalfDisc_convex (ρ : ℝ) : Convex ℝ (closedHalfDisc ρ) := by
  exact (convex_closedBall (0 : E2) ρ).inter
    ((convex_Ici (0 : ℝ)).linear_preimage
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).toLinearMap)

theorem closedHalfDisc_isCompact (ρ : ℝ) : IsCompact (closedHalfDisc ρ) := by
  apply (isCompact_closedBall (0 : E2) ρ).inter_right
  exact isClosed_le continuous_const (EuclideanSpace.proj (0 : Fin 2)).continuous

theorem closedHalfDisc_uniqueDiffOn {ρ : ℝ} (hρ : 0 < ρ) :
    UniqueDiffOn ℝ (closedHalfDisc ρ) := by
  apply uniqueDiffOn_convex (closedHalfDisc_convex ρ)
  obtain ⟨c, s, hs, hball, _⟩ := halfDisc_has_interiorSphere ρ hρ
  exact ⟨c, hball (Metric.mem_ball_self hs)⟩

theorem fderivWithin_closedHalfDisc_eq_fderiv {ρ : ℝ} (u : E2 → ℝ)
    {x : E2} (hx : x ∈ openHalfDisc ρ) :
    fderivWithin ℝ u (closedHalfDisc ρ) x = fderiv ℝ u x := by
  apply fderivWithin_of_mem_nhds
  exact mem_of_superset ((openHalfDisc_isOpen ρ).mem_nhds hx)
    (openHalfDisc_subset_closedHalfDisc ρ)

theorem planarGradientWithin_closedHalfDisc_eq {ρ : ℝ} (u : E2 → ℝ)
    {x : E2} (hx : x ∈ openHalfDisc ρ) :
    planarGradientWithin u (closedHalfDisc ρ) x = planarGradient u x := by
  simp only [planarGradientWithin, planarGradient,
    fderivWithin_closedHalfDisc_eq_fderiv u hx]

theorem firstJetWithin_eq_firstJet {ρ : ℝ} (u : E2 → ℝ)
    {x : E2} (hx : x ∈ openHalfDisc ρ) :
    firstJetWithin ρ u x = QuasilinearLocalization.firstJet u x := by
  simp only [firstJetWithin, QuasilinearLocalization.firstJet,
    planarGradientWithin_closedHalfDisc_eq u hx]

theorem C1QuasilinearDirichletSolution.smooth_on_openHalfDisc
    {ρ : ℝ} {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u) :
    ContDiffOn ℝ ∞ u (openHalfDisc ρ) := by
  apply smooth_of_C1_weak_uniformlyElliptic (openHalfDisc ρ)
    (openHalfDisc_isOpen ρ) J hsolution.jet_domain_open Q
    hsolution.uniformly_elliptic u
    (hsolution.c1.mono (openHalfDisc_subset_closedHalfDisc ρ))
  · intro x hx
    have hj := hsolution.attained_jets x (openHalfDisc_subset_closedHalfDisc ρ hx)
    simpa only [firstJetWithin_eq_firstJet u hx, QuasilinearLocalization.firstJet] using hj
  · exact hsolution.weak_equation

theorem continuousOn_planarGradientWithin_closedHalfDisc
    {ρ : ℝ} (hρ : 0 < ρ) {u : E2 → ℝ}
    (hc1 : ContDiffOn ℝ 1 u (closedHalfDisc ρ)) :
    ContinuousOn (planarGradientWithin u (closedHalfDisc ρ)) (closedHalfDisc ρ) := by
  have hd := hc1.continuousOn_fderivWithin (closedHalfDisc_uniqueDiffOn hρ) (by norm_num)
  unfold planarGradientWithin
  exact continuousOn_finsetSum _ (fun i _ =>
    (hd.clm_apply continuousOn_const).smul continuousOn_const)

theorem continuousOn_firstJetWithin {ρ : ℝ} (hρ : 0 < ρ) {u : E2 → ℝ}
    (hc1 : ContDiffOn ℝ 1 u (closedHalfDisc ρ)) :
    ContinuousOn (firstJetWithin ρ u) (closedHalfDisc ρ) := by
  exact continuousOn_id.prodMk
    (hc1.continuousOn.prodMk (continuousOn_planarGradientWithin_closedHalfDisc hρ hc1))

theorem compact_attained_boundary_jets {ρ : ℝ} (hρ : 0 < ρ) {u : E2 → ℝ}
    (hc1 : ContDiffOn ℝ 1 u (closedHalfDisc ρ)) :
    IsCompact (firstJetWithin ρ u '' closedHalfDisc ρ) :=
  (closedHalfDisc_isCompact ρ).image_of_continuousOn (continuousOn_firstJetWithin hρ hc1)

theorem C1QuasilinearDirichletSolution.continuous_boundary_coefficients
    {ρ : ℝ} (hρ : 0 < ρ) {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u) :
    ContinuousOn (fun x => Q.flux (firstJetWithin ρ u x)) (closedHalfDisc ρ) ∧
    ContinuousOn (fun x => Q.lowerOrder (firstJetWithin ρ u x)) (closedHalfDisc ρ) ∧
    ContinuousOn (fun x => fderiv ℝ Q.flux (firstJetWithin ρ u x)) (closedHalfDisc ρ) ∧
    ContinuousOn (fun x => fderiv ℝ Q.lowerOrder (firstJetWithin ρ u x)) (closedHalfDisc ρ) := by
  have hjet := continuousOn_firstJetWithin hρ hsolution.c1
  exact ⟨Q.flux_smooth.continuousOn.comp hjet hsolution.attained_jets,
    Q.lowerOrder_smooth.continuousOn.comp hjet hsolution.attained_jets,
    (Q.flux_smooth.continuousOn_fderiv_of_isOpen hsolution.jet_domain_open (by simp)).comp
      hjet hsolution.attained_jets,
    (Q.lowerOrder_smooth.continuousOn_fderiv_of_isOpen hsolution.jet_domain_open (by simp)).comp
      hjet hsolution.attained_jets⟩

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
