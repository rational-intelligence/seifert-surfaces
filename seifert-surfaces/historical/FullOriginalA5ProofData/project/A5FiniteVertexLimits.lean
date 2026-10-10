import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.LocallyFinite

set_option autoImplicit false
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal

/-- Continuous extensions on finitely many closed incident pieces have the
same vertex value if they agree off the vertex and arbitrarily small punctured
neighborhoods are connected. No cyclic ordering is assumed. -/
theorem finite_incident_limits_agree
    {X Y ι : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] [Finite ι]
    (x : X) (regions : ι → Set X) (hclosed : ∀ i, IsClosed (regions i))
    (hcover : (⋃ i, regions i) ∈ 𝓝 x)
    (hacc : ∀ i, x ∈ closure (regions i \ {x}))
    (g : ι → X → Y) (hg : ∀ i, ContinuousWithinAt (g i) (regions i) x)
    (hmatch : ∀ i j y, y ∈ regions i → y ∈ regions j → y ≠ x → g i y = g j y)
    (hpuncture : ∀ V : Set X, IsOpen V → x ∈ V →
      ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ W ⊆ V ∧ IsPreconnected (W \ {x})) :
    ∀ i j, g i x = g j x := by
  classical
  have same_of_acc (i j : ι) (h : x ∈ closure ((regions i ∩ regions j) \ {x})) :
      g i x = g j x := by
    let T := (regions i ∩ regions j) \ {x}
    let _ : NeBot (𝓝[T] x) := mem_closure_iff_nhdsWithin_neBot.mp h
    have hi : Tendsto (g i) (𝓝[T] x) (𝓝 (g i x)) :=
      (hg i).mono (fun _ hy => hy.1.1)
    have hj : Tendsto (g j) (𝓝[T] x) (𝓝 (g j x)) :=
      (hg j).mono (fun _ hy => hy.1.2)
    have he : g i =ᶠ[𝓝[T] x] g j := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact hmatch i j y hy.1.1 hy.1.2 hy.2
    exact tendsto_nhds_unique hi (hj.congr' he.symm)
  let bad (p : ι × ι) : Set X := if g p.1 x = g p.2 x then ∅ else
    closure ((regions p.1 ∩ regions p.2) \ {x})
  have hbadclosed (p : ι × ι) : IsClosed (bad p) := by
    dsimp only [bad]
    split <;> first | exact isClosed_empty | exact isClosed_closure
  have hxnot : x ∉ ⋃ p, bad p := by
    intro hx
    obtain ⟨p, hp⟩ := mem_iUnion.mp hx
    dsimp only [bad] at hp
    split at hp
    · exact hp
    · exact ‹g p.1 x ≠ g p.2 x› (same_of_acc p.1 p.2 hp)
  have hV : (⋃ p, bad p)ᶜ ∩ ⋃ i, regions i ∈ 𝓝 x :=
    inter_mem ((isClosed_iUnion_of_finite hbadclosed).isOpen_compl.mem_nhds hxnot) hcover
  obtain ⟨V, hVsub, hVo, hxV⟩ := mem_nhds_iff.mp hV
  obtain ⟨W, hWo, hxW, hWV, hWpre⟩ := hpuncture V hVo hxV
  have hWcover : W ⊆ ⋃ i, regions i := fun _ hy => (hVsub (hWV hy)).2
  have hequal (i j : ι) (y : X) (hyW : y ∈ W) (hyi : y ∈ regions i)
      (hyj : y ∈ regions j) (hyx : y ≠ x) : g i x = g j x := by
    by_contra he
    apply (hVsub (hWV hyW)).1
    exact mem_iUnion.mpr ⟨(i, j), by
      simp only [bad, he, ↓reduceIte]
      exact subset_closure ⟨⟨hyi, hyj⟩, hyx⟩⟩
  intro i j
  by_contra hij
  let A : Set X := ⋃ k : {k : ι // g k x = g i x}, regions k.val
  let B : Set X := ⋃ k : {k : ι // g k x ≠ g i x}, regions k.val
  have hAc : IsClosed A := isClosed_iUnion_of_finite fun k => hclosed k.val
  have hBc : IsClosed B := isClosed_iUnion_of_finite fun k => hclosed k.val
  have hsub : W \ {x} ⊆ A ∪ B := by
    intro y hy
    obtain ⟨k, hk⟩ := mem_iUnion.mp (hWcover hy.1)
    by_cases he : g k x = g i x
    · exact Or.inl (mem_iUnion.mpr ⟨⟨k, he⟩, hk⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨k, he⟩, hk⟩)
  have hdis : (W \ {x}) ∩ (A ∩ B) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro y ⟨hyW, hyA, hyB⟩
    obtain ⟨a, ha⟩ := mem_iUnion.mp hyA
    obtain ⟨b, hb⟩ := mem_iUnion.mp hyB
    exact b.property ((hequal a.val b.val y hyW.1 ha hb hyW.2).symm.trans a.property)
  obtain hleft | hright := isPreconnected_iff_subset_of_disjoint_closed.mp hWpre A B hAc hBc hsub hdis
  · obtain ⟨y, hyW, hyj, hyx⟩ := mem_closure_iff_nhds.mp (hacc j) _ (hWo.mem_nhds hxW)
    have hyA : y ∈ A := hleft ⟨hyW, hyx⟩
    obtain ⟨a, ha⟩ := mem_iUnion.mp hyA
    exact hij ((a.property.symm.trans (hequal a.val j y hyW ha hyj hyx)))
  · obtain ⟨y, hyW, hyi, hyx⟩ := mem_closure_iff_nhds.mp (hacc i) _ (hWo.mem_nhds hxW)
    have hyB : y ∈ B := hright ⟨hyW, hyx⟩
    obtain ⟨b, hb⟩ := mem_iUnion.mp hyB
    exact b.property (hequal b.val i y hyW hb hyi hyx)

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
