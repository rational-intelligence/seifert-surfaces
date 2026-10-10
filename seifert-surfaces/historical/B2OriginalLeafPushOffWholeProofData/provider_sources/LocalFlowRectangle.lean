import LocalSpatialFlow

open scoped Manifold ContDiff
open Set Filter Topology Bundle
namespace SeifertSurfaces.Foundations.AmbientNeatTransport
noncomputable section
universe v
variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M] [T2Space M]

def timeWindow (s : Time) (ε : ℝ) : Set Time :=
  {t | (s : ℝ) - ε < t ∧ (t : ℝ) < s + ε}

theorem timeWindow_isOpen (s : Time) (ε : ℝ) : IsOpen (timeWindow s ε) :=
  isOpen_Ioo.preimage continuous_subtype_val

theorem timeWindow_ordConnected (s : Time) (ε : ℝ) : OrdConnected (timeWindow s ε) := by
  constructor
  intro a ha b hb t ht
  exact ⟨ha.1.trans_le ht.1,(show (t : ℝ) ≤ (b : ℝ) from ht.2).trans_lt hb.2⟩

/-- A rectangle gives one local representative valid for every pair of start
and end times in a neighbourhood of the diagonal. -/
theorem exists_local_spatial_flow_rectangle
    (Y : (q : Time × M) → TangentSpace (𝓡∂ 3) q.2)
    (hY : ContMDiff ((𝓡∂ 1).prod (𝓡∂ 3)) (𝓡∂ 3).tangent ∞
      (fun q => (⟨q.2,Y q⟩ : TangentBundle (𝓡∂ 3) M)))
    (hYb : ∀ q, q.2 ∈ (𝓡∂ 3).boundary M → inwardCoordinate q.2 (Y q) = 0)
    (p : Time × M) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ U : Set M, IsOpen U ∧ p.2 ∈ U ∧
      ∃ Φ : ℝ → ℝ → M → M,
        ContMDiff ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod (𝓡∂ 3)) (𝓡∂ 3) ∞
          (fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2) ∧
        (∀ s x, Φ s s x = x) ∧
        ∀ s ∈ timeWindow p.1 ε, ∀ t ∈ timeWindow p.1 ε, ∀ x ∈ U,
          HasMFDerivAt 𝓘(ℝ,ℝ) (𝓡∂ 3) (fun u => Φ (s : ℝ) u x) (t : ℝ)
            ((ContinuousLinearMap.id ℝ ℝ).smulRight (Y (t,Φ (s : ℝ) (t : ℝ) x))) := by
  obtain ⟨Φ,hΦ,hinit,hinv,htrans,hdiff,A,hA,hpA,hode⟩ := exists_local_spatial_flow Y hY hYb p
  obtain ⟨B,U,hB,hU,hpB,hpU,hBU⟩ := isOpen_prod_iff.mp hA (p.1,p.1) p.2 hpA
  obtain ⟨B₁,B₂,hB₁,hB₂,hpB₁,hpB₂,hBB⟩ := isOpen_prod_iff.mp hB p.1 p.1 hpB
  obtain ⟨ε,hε,hεB⟩ := Metric.mem_nhds_iff.mp ((hB₁.inter hB₂).mem_nhds ⟨hpB₁,hpB₂⟩)
  have hwin : timeWindow p.1 ε ⊆ B₁ ∩ B₂ := by
    intro t ht
    apply hεB
    change dist (t : ℝ) (p.1 : ℝ) < ε
    rw [Real.dist_eq,abs_lt]
    change (p.1 : ℝ) - ε < t ∧ (t : ℝ) < p.1 + ε at ht
    constructor <;> linarith [ht.1,ht.2]
  refine ⟨ε,hε,U,hU,hpU,Φ,hΦ,hinit,?_⟩
  intro s hs t ht x hx
  exact hode ((s,t),x) (hBU ⟨hBB ⟨(hwin hs).1,(hwin ht).2⟩,hx⟩)

end
end SeifertSurfaces.Foundations.AmbientNeatTransport
