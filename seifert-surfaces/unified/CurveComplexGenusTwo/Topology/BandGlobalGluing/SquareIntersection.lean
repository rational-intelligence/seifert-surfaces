import CurveComplexGenusTwo.Topology.FrontierCircle.GlobalBandScaffold

open Set Topology unitInterval
namespace CurveComplex

/-- The first outside arc meets the closed crossing square only at its two
specified port centers. -/
theorem OneCrossingBandBase.firstArc_square_intersection
    {S : Type} [TopologicalSpace S] {a b : Curve S}
    (D : OneCrossingBandBase a b) :
    Set.range D.firstArc ∩ Set.range D.square =
      {D.firstArc (0:I), D.firstArc (1:I)} := by
  apply Set.Subset.antisymm
  · rintro x ⟨⟨t,rfl⟩,z,hz⟩
    have hcurve : D.square z ∈ a.image := by
      have h := D.firstArc_range ▸ (Set.mem_range_self t : D.firstArc t ∈ Set.range D.firstArc)
      exact hz ▸ h.1
    have haxis : z.val.1 = 0 := (D.first_axis z).mp hcurve
    have hnot_open : D.square z ∉ D.openSquare := by
      have h := D.firstArc_range ▸ (Set.mem_range_self t : D.firstArc t ∈ Set.range D.firstArc)
      exact hz ▸ h.2
    have hnot_ball : z.val ∉ Metric.ball ((0,0):ℝ×ℝ) D.radius := by
      intro hb
      apply hnot_open
      rw [D.openSquare_eq]
      exact ⟨z,hb,rfl⟩
    have hclosed : max |z.val.1| |z.val.2| ≤ D.radius := by
      simpa only [Metric.mem_closedBall, dist_eq_norm, Prod.norm_def,
        Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero,
        sub_zero, Real.norm_eq_abs] using z.property
    have hboundary : ¬ max |z.val.1| |z.val.2| < D.radius := by
      simpa [Metric.mem_ball, dist_eq_norm, Prod.norm_def,
        Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero,
        sub_zero, Real.norm_eq_abs] using hnot_ball
    have hyabs : |z.val.2| = D.radius := by
      simp [haxis] at hclosed hboundary
      exact le_antisymm hclosed hboundary
    rcases le_total 0 z.val.2 with hy | hy
    · have hy' : z.val.2 = D.radius := by rwa [abs_of_nonneg hy] at hyabs
      have hzport : z = squarePort D.radius D.radius_pos 0 ⟨0,by norm_num⟩ := by
        apply Subtype.ext
        apply Prod.ext
        · simpa [squarePort,crossingEndRectangle] using haxis
        · simpa [squarePort,crossingEndRectangle] using hy'
      have htarget : D.square z = D.firstArc (1:I) := by
        rw [hzport]
        exact D.firstArc.target.symm
      exact Or.inr (hz.symm.trans htarget)
    · have hy' : z.val.2 = -D.radius := by
        rw [abs_of_nonpos hy] at hyabs
        linarith
      have hzport : z = squarePort D.radius D.radius_pos 2 ⟨0,by norm_num⟩ := by
        apply Subtype.ext
        apply Prod.ext
        · simpa [squarePort,crossingEndRectangle] using haxis
        · simpa [squarePort,crossingEndRectangle] using hy'
      have hsource : D.square z = D.firstArc (0:I) := by
        rw [hzport]
        exact D.firstArc.source.symm
      exact Or.inl (hz.symm.trans hsource)
  · intro x hx
    rcases hx with h | h
    · subst x
      exact ⟨Set.mem_range_self _,⟨squarePort D.radius D.radius_pos 2 ⟨0,by norm_num⟩,
        D.firstArc.source.symm⟩⟩
    · subst x
      exact ⟨Set.mem_range_self _,⟨squarePort D.radius D.radius_pos 0 ⟨0,by norm_num⟩,
        D.firstArc.target.symm⟩⟩

#print axioms OneCrossingBandBase.firstArc_square_intersection
end CurveComplex
