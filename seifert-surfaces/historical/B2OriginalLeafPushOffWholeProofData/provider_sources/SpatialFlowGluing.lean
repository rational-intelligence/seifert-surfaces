import IntrinsicClosedInterval
import LocalSpatialFlow

open scoped Manifold ContDiff
open Set Filter Topology Bundle
namespace SeifertSurfaces.Foundations.AmbientNeatTransport
noncomputable section
universe v w
variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M] [T2Space M]

/-- Uniqueness compares different smooth local representatives of one field. -/
theorem spatial_flow_representatives_agree
    (Y : (q : Time × M) → TangentSpace (𝓡∂ 3) q.2)
    (hY : ContMDiff ((𝓡∂ 1).prod (𝓡∂ 3)) (𝓡∂ 3).tangent ∞
      (fun q => (⟨q.2,Y q⟩ : TangentBundle (𝓡∂ 3) M)))
    (hYb : ∀ q, q.2 ∈ (𝓡∂ 3).boundary M → inwardCoordinate q.2 (Y q) = 0)
    {a b s : ℝ} (hab : Icc a b ⊆ Icc (0 : ℝ) 1) (hs : s ∈ Icc a b)
    {γ η : ℝ → M} (hγ : Continuous γ) (hη : Continuous η)
    (hγd : ∀ t ∈ Icc a b, HasMFDerivAt 𝓘(ℝ,ℝ) (𝓡∂ 3) γ t
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (Y (projIcc 0 1 (by norm_num) t,γ t))))
    (hηd : ∀ t ∈ Icc a b, HasMFDerivAt 𝓘(ℝ,ℝ) (𝓡∂ 3) η t
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (Y (projIcc 0 1 (by norm_num) t,η t))))
    (heq : γ s = η s) : EqOn γ η (Icc a b) :=
  spatial_solution_unique_Icc Y hY hYb hab hγ.continuousOn hη.continuousOn
    (fun t ht => (hγd t ht).hasMFDerivWithinAt)
    (fun t ht => (hηd t ht).hasMFDerivWithinAt) hs heq

set_option maxHeartbeats 1000000 in
/-- Gluing keeps one field: each selected local representative solves `Y`.
Uniqueness pays overlap, the inverse, and the two-time composition law. -/
theorem glue_spatial_flows_on_interval
    (Y : (q : Time × M) → TangentSpace (𝓡∂ 3) q.2)
    (hY : ContMDiff ((𝓡∂ 1).prod (𝓡∂ 3)) (𝓡∂ 3).tangent ∞
      (fun q => (⟨q.2,Y q⟩ : TangentBundle (𝓡∂ 3) M)))
    (hYb : ∀ q, q.2 ∈ (𝓡∂ 3).boundary M → inwardCoordinate q.2 (Y q) = 0)
    {a b : ℝ} (hab : Icc a b ⊆ Icc (0 : ℝ) 1)
    {ι : Type w} (U : ι → Set M) (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (P : ι → ℝ → ℝ → M → M)
    (hP : ∀ i, ContMDiff ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod (𝓡∂ 3)) (𝓡∂ 3) ∞
      (fun q : (ℝ × ℝ) × M => P i q.1.1 q.1.2 q.2))
    (hinit : ∀ i s x, P i s s x = x)
    (hode : ∀ i, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ∀ x ∈ U i,
      HasMFDerivAt 𝓘(ℝ,ℝ) (𝓡∂ 3) (fun u => P i s u x) t
        ((ContinuousLinearMap.id ℝ ℝ).smulRight (Y (projIcc 0 1 (by norm_num) t,P i s t x)))) :
    ∃ Φ : ℝ → ℝ → M → M,
      ContMDiffOn ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod (𝓡∂ 3)) (𝓡∂ 3) ∞
        (fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2) ((Icc a b ×ˢ Icc a b) ×ˢ univ) ∧
      (∀ s ∈ Icc a b, ∀ x, Φ s s x = x) ∧
      (∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ∀ x, Φ t s (Φ s t x) = x) ∧
      (∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ∀ u ∈ Icc a b, ∀ x,
        Φ t u (Φ s t x) = Φ s u x) ∧
      (∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ∀ x,
        HasMFDerivAt 𝓘(ℝ,ℝ) (𝓡∂ 3) (fun u => Φ s u x) t
          ((ContinuousLinearMap.id ℝ ℝ).smulRight (Y (projIcc 0 1 (by norm_num) t,Φ s t x)))) ∧
      ∀ i, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ∀ x ∈ U i, Φ s t x = P i s t x := by
  classical
  choose c hc using hcover
  let Φ : ℝ → ℝ → M → M := fun s t x => P (c x) s t x
  have hPc (i : ι) (s : ℝ) (x : M) : Continuous (fun t => P i s t x) :=
    (hP i).continuous.comp ((continuous_const.prodMk continuous_id).prodMk continuous_const)
  have hagree (i) (s) (hs : s ∈ Icc a b) (t) (ht : t ∈ Icc a b) (x) (hx : x ∈ U i) :
      Φ s t x = P i s t x := by
    apply spatial_flow_representatives_agree Y hY hYb hab hs
      (hPc (c x) s x) (hPc i s x)
      (fun u hu => hode (c x) s hs u hu x (hc x))
      (fun u hu => hode i s hs u hu x hx)
      (by rw [hinit,hinit]) ht
  have hΦ : ContMDiffOn ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod (𝓡∂ 3)) (𝓡∂ 3) ∞
      (fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2) ((Icc a b ×ˢ Icc a b) ×ˢ univ) := by
    intro q hq
    have heq : (fun r : (ℝ × ℝ) × M => Φ r.1.1 r.1.2 r.2) =ᶠ[
        𝓝[((Icc a b ×ˢ Icc a b) ×ˢ univ)] q]
        (fun r : (ℝ × ℝ) × M => P (c q.2) r.1.1 r.1.2 r.2) := by
      have hn : {r : (ℝ × ℝ) × M | r.2 ∈ U (c q.2)} ∈ 𝓝 q :=
        continuous_snd.continuousAt.preimage_mem_nhds ((hU _).mem_nhds (hc q.2))
      filter_upwards [nhdsWithin_le_nhds hn,self_mem_nhdsWithin] with r hr hrC
      exact hagree _ _ hrC.1.1 _ hrC.1.2 _ hr
    exact ((hP (c q.2)).contMDiffAt.contMDiffWithinAt).congr_of_eventuallyEq heq
      (hagree _ _ hq.1.1 _ hq.1.2 _ (hc q.2))
  have hΦd (s) (hs : s ∈ Icc a b) (t) (ht : t ∈ Icc a b) (x) :
      HasMFDerivAt 𝓘(ℝ,ℝ) (𝓡∂ 3) (fun u => Φ s u x) t
        ((ContinuousLinearMap.id ℝ ℝ).smulRight (Y (projIcc 0 1 (by norm_num) t,Φ s t x))) :=
    hode (c x) s hs t ht x (hc x)
  have hΦc (s) (x) : Continuous (fun t => Φ s t x) := hPc (c x) s x
  have hΦi (s) (x) : Φ s s x = x := hinit (c x) s x
  have htrans (s) (hs : s ∈ Icc a b) (t) (ht : t ∈ Icc a b)
      (u) (hu : u ∈ Icc a b) (x) : Φ t u (Φ s t x) = Φ s u x :=
    spatial_flow_representatives_agree Y hY hYb hab ht
      (hΦc t (Φ s t x)) (hΦc s x)
      (fun z hz => hΦd t ht z hz (Φ s t x)) (fun z hz => hΦd s hs z hz x)
      (hΦi t (Φ s t x)) hu
  refine ⟨Φ,hΦ,fun s _ x => hΦi s x,?_,htrans,hΦd,hagree⟩
  intro s hs t ht x
  rw [htrans s hs t ht s hs x,hΦi]

end
end SeifertSurfaces.Foundations.AmbientNeatTransport
