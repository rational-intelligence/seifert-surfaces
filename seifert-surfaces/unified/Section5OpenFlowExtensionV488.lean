import Section5CutoffProductFlowV488
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ V H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable (U : TopologicalSpace.Opens M) (Φ : Flow ℝ U)

def extendOpenFlowMap (t : ℝ) (x : M) : M := by
  classical
  exact if hx : x ∈ U then (Φ t ⟨x,hx⟩ : M) else x

theorem extend_open_flow_map_inside (t : ℝ) (x : U) :
    extendOpenFlowMap U Φ t (x : M) = (Φ t x : M) := by
  simp only [extendOpenFlowMap,dite_eq_left x.property]

theorem extend_open_flow_map_outside (t : ℝ) (x : M) (hx : x ∉ U) :
    extendOpenFlowMap U Φ t x = x := by
  simp only [extendOpenFlowMap,dite_eq_right hx]

theorem extend_open_flow_map_fixed {K : Set M}
    (hfix : ∀ t (x : U), (x : M) ∉ K → Φ t x = x)
    (t : ℝ) (x : M) (hx : x ∉ K) : extendOpenFlowMap U Φ t x = x := by
  by_cases h : x ∈ U
  · rw [show x = ((⟨x,h⟩ : U) : M) from rfl,extend_open_flow_map_inside]
    exact congrArg Subtype.val (hfix t ⟨x,h⟩ hx)
  · exact extend_open_flow_map_outside U Φ t x h

theorem extend_open_flow_smooth
    (hΦ : ContMDiff (𝓘(ℝ).prod I) I ∞ (fun p : ℝ × U => Φ p.1 p.2))
    {K : Set M} (hK : IsClosed K) (hKU : K ⊆ U)
    (hfix : ∀ t (x : U), (x : M) ∉ K → Φ t x = x) :
    ContMDiff (𝓘(ℝ).prod I) I ∞ (fun p : ℝ × M => extendOpenFlowMap U Φ p.1 p.2) := by
  intro p
  by_cases hp : p.2 ∈ U
  · let W : TopologicalSpace.Opens (ℝ × M) := ⟨univ ×ˢ (U : Set M),isOpen_univ.prod U.isOpen⟩
    let q : W := ⟨p,⟨mem_univ _,hp⟩⟩
    let a : W → ℝ := fun z => z.val.1
    let b : W → U := fun z => ⟨z.val.2,z.property.2⟩
    have ha : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) ∞ a := contMDiff_subtype_val.fst
    have hb : ContMDiff (𝓘(ℝ).prod I) I ∞ b := by
      apply (ContMDiff.subtypeVal_comp_iff U b).mp
      exact contMDiff_subtype_val.snd
    have hs : ContMDiff (𝓘(ℝ).prod I) I ∞
        (fun z : W => extendOpenFlowMap U Φ z.val.1 z.val.2) := by
      apply (contMDiff_subtype_val.comp (hΦ.comp (ha.prodMk hb))).congr
      intro z
      exact extend_open_flow_map_inside U Φ z.val.1 (b z)
    exact (contMDiffAt_subtype_iff (I := 𝓘(ℝ).prod I) (I' := I) (U := W)
      (f := fun z : ℝ × M => extendOpenFlowMap U Φ z.1 z.2) (x := q)).mp (hs q)
  · have hpk : p.2 ∈ Kᶜ := fun hk => hp (hKU hk)
    have hs : ContMDiffAt (𝓘(ℝ).prod I) I ∞ (fun z : ℝ × M => z.2) p := contMDiffAt_snd
    apply hs.congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds (hK.isOpen_compl.mem_nhds hpk)] with z hz
    exact extend_open_flow_map_fixed U Φ hfix z.1 z.2 hz

def extendOpenFlow
    (hΦ : ContMDiff (𝓘(ℝ).prod I) I ∞ (fun p : ℝ × U => Φ p.1 p.2))
    {K : Set M} (hK : IsClosed K) (hKU : K ⊆ U)
    (hfix : ∀ t (x : U), (x : M) ∉ K → Φ t x = x) : Flow ℝ M where
  toFun := extendOpenFlowMap U Φ
  cont' := (extend_open_flow_smooth U Φ hΦ hK hKU hfix).continuous
  map_add' t u x := by
    by_cases hx : x ∈ U
    · let y : U := ⟨x,hx⟩
      change extendOpenFlowMap U Φ (t+u) (y : M) =
        extendOpenFlowMap U Φ t (extendOpenFlowMap U Φ u (y : M))
      rw [extend_open_flow_map_inside,extend_open_flow_map_inside,extend_open_flow_map_inside,Flow.map_add]
    · rw [extend_open_flow_map_outside U Φ _ _ hx,extend_open_flow_map_outside U Φ _ _ hx,
        extend_open_flow_map_outside U Φ _ _ hx]
  map_zero' x := by
    by_cases hx : x ∈ U
    · let y : U := ⟨x,hx⟩
      change extendOpenFlowMap U Φ 0 (y : M) = x
      rw [extend_open_flow_map_inside,Flow.map_zero_apply]
    · exact extend_open_flow_map_outside U Φ 0 x hx

#print axioms extendOpenFlow
end
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
