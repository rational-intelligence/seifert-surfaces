import SpatialFlowGluing
import LocalFlowRectangle
import CompactDiagonalHorizon

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff
open Set Filter Topology Bundle
namespace SeifertSurfaces.Foundations.AmbientNeatTransport
noncomputable section
universe v
variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M] [T2Space M]

def SpatialFlowOn
    (Y : (q : Time × M) → TangentSpace (𝓡∂ 3) q.2)
    (a b : ℝ) (Φ : ℝ → ℝ → M → M) : Prop :=
  ContMDiffOn ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod (𝓡∂ 3)) (𝓡∂ 3) ∞
    (fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2) ((Icc a b ×ˢ Icc a b) ×ˢ univ) ∧
  (∀ s ∈ Icc a b, ∀ x, Φ s s x = x) ∧
  (∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ∀ x, Φ t s (Φ s t x) = x) ∧
  (∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ∀ u ∈ Icc a b, ∀ x,
    Φ t u (Φ s t x) = Φ s u x) ∧
  (∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ∀ x,
    HasMFDerivAt 𝓘(ℝ,ℝ) (𝓡∂ 3) (fun u => Φ s u x) t
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (Y (projIcc 0 1 (by norm_num) t,Φ s t x))))

/-- Compact support supplies a uniform positive step. The resulting flow
integrates the same field at every spatial point, including outside its support. -/
theorem exists_uniform_short_spatial_flow
    (Y : (q : Time × M) → TangentSpace (𝓡∂ 3) q.2)
    (hY : ContMDiff ((𝓡∂ 1).prod (𝓡∂ 3)) (𝓡∂ 3).tangent ∞
      (fun q => (⟨q.2,Y q⟩ : TangentBundle (𝓡∂ 3) M)))
    (hYb : ∀ q, q.2 ∈ (𝓡∂ 3).boundary M → inwardCoordinate q.2 (Y q) = 0)
    {K : Set M} (hK : IsCompact K) (hsupp : ∀ q, q.2 ∉ K → Y q = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a b : ℝ, a ≤ b → a ∈ Icc (0 : ℝ) 1 → b ∈ Icc (0 : ℝ) 1 →
      dist a b < ε → ∃ Φ : ℝ → ℝ → M → M, SpatialFlowOn Y a b Φ := by
  classical
  have hlocal (p : Time × M) := exists_local_spatial_flow_rectangle Y hY hYb p
  choose δ hδ U hU hpU P hP hinit hode using hlocal
  let A : Set ((Time × Time) × M) := ⋃ p : Time × M,
    ((timeWindow p.1 (δ p) ×ˢ timeWindow p.1 (δ p)) ×ˢ U p)
  have hA : IsOpen A := isOpen_iUnion fun p =>
    ((timeWindow_isOpen p.1 (δ p)).prod (timeWindow_isOpen p.1 (δ p))).prod (hU p)
  have hdiag (s : Time) (x : M) (_hx : x ∈ K) : ((s,s),x) ∈ A := by
    apply mem_iUnion.mpr
    have hs : s ∈ timeWindow s (δ (s,x)) := by
      change (s : ℝ) - δ (s,x) < s ∧ (s : ℝ) < s + δ (s,x)
      constructor <;> linarith [hδ (s,x)]
    exact ⟨(s,x),⟨⟨hs,hs⟩,hpU (s,x)⟩⟩
  obtain ⟨ε,hε,horizon⟩ := compact_time_diagonal_horizon hK hA hdiag
  refine ⟨ε,hε,?_⟩
  intro a b hab ha hb habε
  let aT : Time := ⟨a,ha⟩
  let bT : Time := ⟨b,hb⟩
  let J := {p : Time × M // aT ∈ timeWindow p.1 (δ p) ∧ bT ∈ timeWindow p.1 (δ p)}
  let W : Option J → Set M := fun j => match j with
    | none => Kᶜ
    | some p => U p.1
  let Q : Option J → ℝ → ℝ → M → M := fun j => match j with
    | none => fun _ _ x => x
    | some p => P p.1
  have hW (j : Option J) : IsOpen (W j) := by
    cases j with
    | none => exact hK.isClosed.isOpen_compl
    | some p => exact hU p.1
  have hcover (x : M) : ∃ j : Option J, x ∈ W j := by
    by_cases hx : x ∈ K
    · have hh := horizon aT bT x hx habε
      obtain ⟨p,hp⟩ := mem_iUnion.mp hh
      exact ⟨some ⟨p,⟨hp.1.1,hp.1.2⟩⟩,hp.2⟩
    · exact ⟨none,hx⟩
  have hQ (j : Option J) :
      ContMDiff ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod (𝓡∂ 3)) (𝓡∂ 3) ∞
        (fun q : (ℝ × ℝ) × M => Q j q.1.1 q.1.2 q.2) := by
    cases j with
    | none => exact contMDiff_snd
    | some p => exact hP p.1
  have hQi (j : Option J) (s : ℝ) (x : M) : Q j s s x = x := by
    cases j with
    | none => rfl
    | some p => exact hinit p.1 s x
  have htime (t : ℝ) (ht : t ∈ Icc a b) : (projIcc 0 1 (by norm_num) t : ℝ) = t :=
    congrArg Subtype.val (projIcc_of_mem (by norm_num) ⟨ha.1.trans ht.1,ht.2.trans hb.2⟩)
  have hwin (p : J) (t : ℝ) (ht : t ∈ Icc a b) :
      projIcc 0 1 (by norm_num) t ∈ timeWindow p.1.1 (δ p.1) := by
    apply (timeWindow_ordConnected p.1.1 (δ p.1)).out p.2.1 p.2.2
    change a ≤ (projIcc 0 1 (by norm_num) t : ℝ) ∧ (projIcc 0 1 (by norm_num) t : ℝ) ≤ b
    rw [htime t ht]
    exact ht
  have hQo (j : Option J) (s : ℝ) (hs : s ∈ Icc a b) (t : ℝ) (ht : t ∈ Icc a b)
      (x : M) (hx : x ∈ W j) :
      HasMFDerivAt 𝓘(ℝ,ℝ) (𝓡∂ 3) (fun u => Q j s u x) t
        ((ContinuousLinearMap.id ℝ ℝ).smulRight (Y (projIcc 0 1 (by norm_num) t,Q j s t x))) := by
    cases j with
    | none =>
      have hz := hsupp (projIcc 0 1 (by norm_num) t,x) hx
      have hc : HasMFDerivAt 𝓘(ℝ,ℝ) (𝓡∂ 3) (fun _ : ℝ => x) t 0 :=
        hasMFDerivAt_const x t
      dsimp only [Q]
      rw [hz,ContinuousLinearMap.smulRight_zero]
      exact hc
    | some p =>
      have hh := hode p.1 (projIcc 0 1 (by norm_num) s) (hwin p s hs)
        (projIcc 0 1 (by norm_num) t) (hwin p t ht) x hx
      dsimp only [Q]
      have hs0 : projIcc 0 1 (by norm_num) s = (⟨s,⟨ha.1.trans hs.1,hs.2.trans hb.2⟩⟩ : Time) :=
        projIcc_of_mem (by norm_num) ⟨ha.1.trans hs.1,hs.2.trans hb.2⟩
      have ht0 : projIcc 0 1 (by norm_num) t = (⟨t,⟨ha.1.trans ht.1,ht.2.trans hb.2⟩⟩ : Time) :=
        projIcc_of_mem (by norm_num) ⟨ha.1.trans ht.1,ht.2.trans hb.2⟩
      rw [hs0,ht0] at hh
      rw [ht0]
      exact hh
  obtain ⟨Φ,hΦ,hΦi,hΦinv,hΦtrans,hΦode,hΦagree⟩ :=
    glue_spatial_flows_on_interval Y hY hYb (Icc_subset_Icc ha.1 hb.2) W hW hcover Q hQ hQi hQo
  exact ⟨Φ,hΦ,hΦi,hΦinv,hΦtrans,hΦode⟩

end
end SeifertSurfaces.Foundations.AmbientNeatTransport
