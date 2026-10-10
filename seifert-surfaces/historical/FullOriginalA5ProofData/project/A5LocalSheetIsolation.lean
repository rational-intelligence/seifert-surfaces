import A5NativeLocalCover
import A5InteriorInvarianceOfDomain

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations

/-- The actual embeddings isolate small coordinate neighborhoods of finitely
many sheets inside one ambient neighborhood. Cross-sheet collision control
therefore gives injectivity on the whole embedded source. -/
theorem finite_embedded_sheets_projection_injective
    {I X N : Type*} [Finite I] [TopologicalSpace X] [TopologicalSpace N]
    (Y : I → Type*) [∀ i, TopologicalSpace (Y i)]
    (f : X → N) (hf : Function.Injective f) (x : X)
    (g : ∀ i, Y i → N) (hg : ∀ i, IsEmbedding (g i))
    (q : ∀ i, Y i) (hq : ∀ i, g i (q i) = f x)
    (Q : ∀ i, Set (Y i)) (hQ : ∀ i, IsOpen (Q i)) (hqQ : ∀ i, q i ∈ Q i)
    (W : Set N) (hW : IsOpen W) (hxW : f x ∈ W)
    (hcover : ∀ z ∈ range f ∩ W, ∃ i y, g i y = z)
    (π : N → Euc 2)
    (hcollisions : ∀ i j y, y ∈ Q i → ∀ z, z ∈ Q j →
      π (g i y) = π (g j z) → g i y = g j z) :
    ∃ V : Set N, IsOpen V ∧ f x ∈ V ∧ V ⊆ W ∧ InjOn (π ∘ f) (f ⁻¹' V) := by
  classical
  have hex (i : I) : ∃ V : Set N, IsOpen V ∧ f x ∈ V ∧ (g i) ⁻¹' V ⊆ Q i := by
    obtain ⟨V, hV, hqV, _, hpre, _⟩ :=
      A3GraphLower.embedding_ambient_open_source_isolation (g i) (hg i) (q i)
        (Q i) (hQ i) (hqQ i) univ isOpen_univ (mem_univ _)
    exact ⟨V, hV, hq i ▸ hqV, hpre⟩
  choose V hV hxV hpre using hex
  let Z := W ∩ ⋂ i, V i
  refine ⟨Z, hW.inter (isOpen_iInter_of_finite hV), ⟨hxW, mem_iInter.mpr hxV⟩,
    inter_subset_left, ?_⟩
  intro a ha b hb he
  obtain ⟨i, y, hy⟩ := hcover (f a) ⟨⟨a, rfl⟩, ha.1⟩
  obtain ⟨j, z, hz⟩ := hcover (f b) ⟨⟨b, rfl⟩, hb.1⟩
  have hyQ : y ∈ Q i := hpre i (by change g i y ∈ V i; rw [hy]; exact mem_iInter.mp ha.2 i)
  have hzQ : z ∈ Q j := hpre j (by change g j z ∈ V j; rw [hz]; exact mem_iInter.mp hb.2 j)
  apply hf
  rw [← hy, ← hz]
  exact hcollisions i j y hyQ z hzQ (by rw [hy, hz]; exact he)

/-- A native interior source point covered by finitely many embedded sheets
has a local projection homeomorphism once all small-sheet collisions agree.
The ambient neighborhood and invariance-of-domain step are constructed. -/
theorem native_local_projection_of_sheet_collisions
    {I N : Type*} [Finite I] [TopologicalSpace N]
    (S : CompactOrientedSurface) (f : S → N) (hf : IsEmbedding f)
    (x : S) (hx : x ∈ (𝓡∂ 2).interior S)
    (Y : I → Type*) [∀ i, TopologicalSpace (Y i)]
    (g : ∀ i, Y i → N) (hg : ∀ i, IsEmbedding (g i))
    (q : ∀ i, Y i) (hq : ∀ i, g i (q i) = f x)
    (Q : ∀ i, Set (Y i)) (hQ : ∀ i, IsOpen (Q i)) (hqQ : ∀ i, q i ∈ Q i)
    (W : Set N) (hW : IsOpen W) (hxW : f x ∈ W)
    (hcover : ∀ z ∈ range f ∩ W, ∃ i y, g i y = z)
    (π : N → Euc 2) (hπ : ContinuousOn π W)
    (hcollisions : ∀ i j y, y ∈ Q i → ∀ z, z ∈ Q j →
      π (g i y) = π (g j z) → g i y = g j z) :
    IsLocalHomeomorphOn (π ∘ f) {x} := by
  obtain ⟨V, hV, hxV, hVW, hinj⟩ := finite_embedded_sheets_projection_injective
    Y f hf.injective x g hg q hq Q hQ hqQ W hW hxW hcover π hcollisions
  exact native_interior_local_homeomorph_of_injective S x hx (f ⁻¹' V)
    (hV.preimage hf.continuous) hxV (π ∘ f)
    (hπ.comp hf.continuous.continuousOn (fun _ hz => hVW hz)) hinj

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
