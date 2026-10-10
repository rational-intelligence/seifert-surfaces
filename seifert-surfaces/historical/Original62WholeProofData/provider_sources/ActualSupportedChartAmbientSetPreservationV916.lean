import ActualSupportedChartAmbientIsotopyV846
import ActualDisjointSupportedAmbientCompositionV881

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped Manifold ContDiff
open Set Topology Manifold
open SeifertSurfaces.Foundations
noncomputable section
namespace CompressionActualSupportedChartAmbientSetPreservationV916

/-- Actual chart-supported isotopies preserve a specified ambient set
    whenever the full supported block map preserves its point predicate. -/
theorem supported_chart_ambient_set_preservation
    {X M : Type} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanHalfSpace 3) M]
    (e : OpenPartialHomeomorph X M) (W : Set X) (hW : IsOpen W)
    (hWc : IsCompact (closure W)) (hWs : closure W ⊆ e.source)
    (L : Time → X ≃ₜ X) (hL : Continuous (fun p : Time × X => L p.1 p.2))
    (hL0 : ∀ x,L 0 x = x) (hoff : ∀ t x,x ∉ W → L t x = x)
    (Z : Set M) (hZ : Disjoint (e '' closure W) Z)
    (hbd : Disjoint (e '' closure W) ((𝓡∂ 3).boundary M))
    (S : Set M) (hLS : ∀ t x,x ∈ closure W → (e (L t x) ∈ S ↔ e x ∈ S)) :
    ∃ I : TopologicalAmbientIsotopy M,
      IsOpen (e '' W) ∧ IsCompact (closure (e '' W)) ∧
      Disjoint (closure (e '' W)) Z ∧
      Disjoint (closure (e '' W)) ((𝓡∂ 3).boundary M) ∧
      (∀ t x,x ∉ e '' W → I.stage t x = x) ∧
      (∀ t x,x ∈ (𝓡∂ 3).boundary M → I.stage t x = x) ∧
      (∀ t x,x ∈ closure W → I.stage t (e x) = e (L t x)) ∧
      (∀ t x,I.stage t x ∈ S ↔ x ∈ S) ∧
      ∀ t,I.stage t '' S = S := by
  obtain ⟨I,hV,hVc,hVZ,hVbd,hIo,hIbd,hIon⟩ :=
    CompressionActualSupportedChartAmbientIsotopyV846.supported_chart_ambient_isotopy
      e W hW hWc hWs L hL hL0 hoff Z hZ hbd
  have hIiff (t : Time) (x : M) : I.stage t x ∈ S ↔ x ∈ S := by
    by_cases hx : x ∈ e '' W
    · obtain ⟨p,hp,rfl⟩ := hx
      rw [hIon _ _ (subset_closure hp)]
      exact hLS t p (subset_closure hp)
    · rw [hIo _ _ hx]
  refine ⟨I,hV,hVc,hVZ,hVbd,hIo,hIbd,hIon,hIiff,?_⟩
  intro t
  apply Subset.antisymm
  · rintro y ⟨x,hx,rfl⟩
    exact (hIiff t x).mpr hx
  · intro y hy
    refine ⟨(I.stage t).symm y,?_,(I.stage t).apply_symm_apply _⟩
    exact (hIiff t _).mp (by rwa [(I.stage t).apply_symm_apply])

/-- An actual normal block map preserving its normal coordinate retains
    the zero-slice surface predicate on its ENTIRE supported closure. -/
theorem normal_block_preserves_zero_surface
    {M : Type} [TopologicalSpace M] (e : OpenPartialHomeomorph (Schoenflies.Plane × ℝ) M)
    (W : Set (Schoenflies.Plane × ℝ)) (hWs : closure W ⊆ e.source)
    (L : Time → (Schoenflies.Plane × ℝ) ≃ₜ (Schoenflies.Plane × ℝ))
    (hoff : ∀ t p,p ∉ W → L t p = p)
    (hLn : ∀ t p,(L t p).2 = p.2)
    (S : Set M) (heS : ∀ p,p ∈ e.source → (e p ∈ S ↔ p.2 = 0)) :
    ∀ t p,p ∈ closure W → (e (L t p) ∈ S ↔ e p ∈ S) := by
  intro t p hp
  have hclosedoff (q : Schoenflies.Plane × ℝ) (hq : q ∉ closure W) : L t q = q :=
    hoff t q (fun hw => hq (subset_closure hw))
  have hLp : L t p ∈ closure W :=
    CompressionActualDisjointSupportedAmbientCompositionV881.preserves_support
      (L t) (closure W) hclosedoff hp
  rw [heS _ (hWs hLp),heS _ (hWs hp),hLn]

#print axioms supported_chart_ambient_set_preservation
#print axioms normal_block_preserves_zero_surface
end CompressionActualSupportedChartAmbientSetPreservationV916
