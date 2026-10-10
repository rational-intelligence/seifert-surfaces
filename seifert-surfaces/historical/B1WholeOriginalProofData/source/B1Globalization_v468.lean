import VM03ExactCaller_v464
import B1TangencyGlobal
import Section5Analysis
noncomputable section
open Set Topology Function MeasureTheory
open scoped Manifold ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
universe v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem same_circle_compact_globalization (D : B1OriginalData g J)
    (hlocal : ∀ s : Circle, LocalBoundaryIsolation D s) :
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ D.r0 ∧
      (∀ s : Circle, ∀ r ∈ Ioo (0 : ℝ) rho,
        mfderiv ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ)
          (fun p : Circle × ℝ => D.f p.1 p.2) (s, r) ≠ 0) ∧
      Set.Finite {s : Circle |
        mfderiv ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ)
          (fun p : Circle × ℝ => D.f p.1 p.2) (s, 0) = 0} := by
  classical
  choose U hUopen hUmem hUiso using hlocal
  have hball : ∀ s : Circle, ∃ e : ℝ, 0 < e ∧ Metric.ball (s, (0 : ℝ)) e ⊆ U s := by
    intro s
    exact Metric.isOpen_iff.mp (hUopen s) (s, 0) (hUmem s)
  choose e hepos heU using hball
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover
    (fun s : Circle => Metric.ball s (e s / 2)) (fun _ => Metric.isOpen_ball) (by
      intro s _
      exact mem_iUnion.mpr ⟨s, Metric.mem_ball_self (half_pos (hepos s))⟩)
  have hradius : ∃ rho : ℝ, 0 < rho ∧ rho ≤ D.r0 ∧ ∀ s ∈ T, rho ≤ e s / 2 := by
    clear hT
    induction T using Finset.induction_on with
    | empty => exact ⟨D.r0, D.r0_pos, le_rfl, by simp⟩
    | @insert s T hs ih =>
      obtain ⟨rho, hrho, hle, hTle⟩ := ih
      refine ⟨min rho (e s / 2), lt_min hrho (half_pos (hepos s)), (min_le_left _ _).trans hle, ?_⟩
      intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hTle t ht)
  obtain ⟨rho, hrho, hr0, hsmall⟩ := hradius
  refine ⟨rho, hrho, hr0, ?_, ?_⟩
  · intro s r hr
    obtain ⟨t, ht, hst⟩ := mem_iUnion₂.mp (hT (mem_univ s))
    apply hUiso t (s, r)
    · refine ⟨heU t ?_, ?_⟩
      · rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
        constructor
        · exact (Metric.mem_ball.mp hst).trans (by have := hepos t; linarith)
        · simp only [Real.dist_eq, sub_zero, abs_of_pos hr.1]
          exact hr.2.trans_le ((hsmall t ht).trans (by have := hepos t; linarith))
      · exact ⟨hr.1.le, hr.2.le.trans hr0⟩
    · intro h
      have := congrArg Prod.snd h
      exact (ne_of_gt hr.1) this
  · apply T.finite_toSet.subset
    intro s hs
    obtain ⟨t, ht, hst⟩ := mem_iUnion₂.mp (hT (mem_univ s))
    have hst_eq : s = t := by
      by_contra hne
      apply hUiso t (s, 0) _ (by exact fun h => hne (congrArg Prod.fst h)) hs
      refine ⟨heU t ?_, ?_⟩
      · rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
        exact ⟨(Metric.mem_ball.mp hst).trans (by have := hepos t; linarith), by simpa using hepos t⟩
      · exact ⟨le_rfl, D.r0_pos.le⟩
    exact hst_eq ▸ ht


end SeifertSurfaces.OriginalEndpoints.B1Tangency
