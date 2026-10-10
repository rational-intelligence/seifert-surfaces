import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Set.Finite.Lemmas

set_option autoImplicit false
open Set Topology
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal

private theorem finite_ordered_minima_clopen
    {B I : Type*} [TopologicalSpace B] [TopologicalSpace I]
    [DiscreteTopology I] [Finite I] (h : B × I → ℝ) (hc : Continuous h)
    (hinj : ∀ b, Function.Injective (fun i => h (b, i))) :
    IsClopen {p : B × I | ∀ j, h p ≤ h (p.1, j)} := by
  refine ⟨?_, ?_⟩
  · have he : {p : B × I | ∀ j, h p ≤ h (p.1, j)} =
        ⋂ j : I, {p : B × I | h p ≤ h (p.1, j)} := by ext; simp
    rw [he]
    apply isClosed_iInter
    intro j
    exact isClosed_le hc (hc.comp (continuous_fst.prodMk continuous_const))
  · have he : {p : B × I | ∀ j, h p ≤ h (p.1, j)} =
        ⋂ j : I, ({p : B × I | p.2 = j} ∪ {p : B × I | h p < h (p.1, j)}) := by
      ext p
      simp only [mem_ofPred_eq, mem_iInter, mem_union]
      constructor
      · intro hp j
        by_cases hj : p.2 = j
        · exact Or.inl hj
        · exact Or.inr (lt_of_le_of_ne (hp j) (fun he => hj (hinj p.1 he)))
      · intro hp j
        rcases hp j with hj | hj
        · simpa only [← hj] using le_rfl (a := h p)
        · exact hj.le
    rw [he]
    apply isOpen_iInter_of_finite
    intro j
    exact ((isOpen_discrete ({j} : Set I)).preimage continuous_snd).union
      (isOpen_lt hc (hc.comp (continuous_fst.prodMk continuous_const)))

/-- Distinct continuous heights order every finite covering fiber. The lowest
sheet is clopen in the covering space. -/
theorem lowest_sheet_clopen
    {Z B : Type*} [TopologicalSpace Z] [TopologicalSpace B]
    (f : Z → B) (hf : IsCoveringMap f)
    (hfinite : ∀ b, (f ⁻¹' {b}).Finite)
    (height : Z → ℝ) (hheight : Continuous height)
    (hseparate : Function.Injective (fun z => (f z, height z))) :
    IsClopen {z : Z | ∀ y, f y = f z → height z ≤ height y} := by
  let P : Set Z := {z | ∀ y, f y = f z → height z ≤ height y}
  have local_clopen (z : Z) :
      ∃ U : Set Z, IsOpen U ∧ z ∈ U ∧ IsClopen (Subtype.val ⁻¹' P : Set U) := by
    obtain ⟨hd, U, hz, hU, hfU, H, hH⟩ := hf (f z)
    let _ := hd
    let _ : Finite (f ⁻¹' {f z}) := (hfinite (f z)).to_subtype
    let g : U × (f ⁻¹' {f z}) → ℝ := fun p => height (H.symm p)
    have hg : Continuous g := hheight.comp (continuous_subtype_val.comp H.symm.continuous)
    have hgi (b : U) : Function.Injective (fun i => g (b, i)) := by
      intro i j hij
      have hbase : f (H.symm (b, i)) = f (H.symm (b, j)) := by
        rw [← hH (H.symm (b, i)), ← hH (H.symm (b, j))]
        simp
      have he := hseparate (Prod.ext hbase hij)
      have hpair := H.symm.injective (Subtype.ext he)
      exact congrArg Prod.snd hpair
    have hM := finite_ordered_minima_clopen g hg hgi
    have hpre : (Subtype.val ⁻¹' P : Set (f ⁻¹' U)) =
        H ⁻¹' {p | ∀ j, g p ≤ g (p.1, j)} := by
      ext w
      change (∀ y, f y = f w → height w ≤ height y) ↔
        ∀ j, g (H w) ≤ g ((H w).1, j)
      have hgw : g (H w) = height w := by simp [g]
      rw [hgw]
      constructor
      · intro hw j
        apply hw (H.symm ((H w).1, j))
        rw [← hH (H.symm ((H w).1, j))]
        simpa only [H.apply_symm_apply] using hH w
      · intro hw y hy
        have hyU : f y ∈ U := hy ▸ w.property
        let y' : f ⁻¹' U := ⟨y, hyU⟩
        have hfirst : (H y').1 = (H w).1 := by
          apply Subtype.ext
          rw [hH, hH]
          exact hy
        have hpair : ((H w).1, (H y').2) = H y' := by
          exact Prod.ext hfirst.symm rfl
        have hb := hw (H y').2
        rw [hpair] at hb
        simpa [g, y'] using hb
    refine ⟨f ⁻¹' U, hfU, hz, ?_⟩
    rw [hpre]
    exact hM.preimage H.continuous
  have open_of_local (Q : Set Z)
      (hQ : ∀ z, ∃ U : Set Z, IsOpen U ∧ z ∈ U ∧
        IsOpen (Subtype.val ⁻¹' Q : Set U)) : IsOpen Q := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    obtain ⟨U, hU, hzU, hQU⟩ := hQ z
    have ho : IsOpen (Subtype.val '' (Subtype.val ⁻¹' Q : Set U)) :=
      hU.isOpenMap_subtype_val _ hQU
    apply Filter.mem_of_superset (ho.mem_nhds ⟨⟨z, hzU⟩, hz, rfl⟩)
    rintro y ⟨w, hw, rfl⟩
    exact hw
  have hPo : IsOpen P := open_of_local P fun z => by
    obtain ⟨U, hU, hzU, hc⟩ := local_clopen z
    exact ⟨U, hU, hzU, hc.isOpen⟩
  have hPc : IsOpen Pᶜ := open_of_local Pᶜ fun z => by
    obtain ⟨U, hU, hzU, hc⟩ := local_clopen z
    exact ⟨U, hU, hzU, hc.isClosed.isOpen_compl⟩
  exact ⟨isOpen_compl_iff.mp hPc, hPo⟩

theorem lowest_sheet_all
    {Z B : Type*} [TopologicalSpace Z] [TopologicalSpace B]
    [PreconnectedSpace Z] (f : Z → B) (hf : IsCoveringMap f)
    (hfinite : ∀ b, (f ⁻¹' {b}).Finite)
    (height : Z → ℝ) (hheight : Continuous height)
    (hseparate : Function.Injective (fun z => (f z, height z)))
    (z₀ : Z) (hz₀ : ∀ y, f y = f z₀ → height z₀ ≤ height y) :
    ∀ z y, f y = f z → height z ≤ height y := by
  have hc := lowest_sheet_clopen f hf hfinite height hheight hseparate
  have hall := IsClopen.eq_univ hc ⟨z₀, hz₀⟩
  intro z y hy
  have hz : z ∈ {z : Z | ∀ y, f y = f z → height z ≤ height y} := by
    rw [hall]
    exact Set.mem_univ z
  exact hz y hy

/-- A connected finite covering embedded with a real height has one sheet. -/
theorem finite_covering_injective_of_ordered_heights
    {Z B : Type*} [TopologicalSpace Z] [TopologicalSpace B]
    [PreconnectedSpace Z] (f : Z → B) (hf : IsCoveringMap f)
    (hfinite : ∀ b, (f ⁻¹' {b}).Finite)
    (height : Z → ℝ) (hheight : Continuous height)
    (hseparate : Function.Injective (fun z => (f z, height z))) :
    Function.Injective f := by
  intro x y hxy
  obtain ⟨z, hz, hzmin⟩ := Set.exists_min_image (f ⁻¹' {f x}) height
    (hfinite (f x)) ⟨x, rfl⟩
  have hz₀ : ∀ w, f w = f z → height z ≤ height w := by
    intro w hw
    exact hzmin w (hw.trans hz)
  have hall := lowest_sheet_all f hf hfinite height hheight hseparate z hz₀
  apply hseparate
  exact Prod.ext hxy (le_antisymm (hall x y hxy.symm) (hall y x hxy))

theorem finite_covering_homeomorph_of_ordered_heights
    {Z B : Type*} [TopologicalSpace Z] [TopologicalSpace B]
    [PreconnectedSpace Z] (f : Z → B) (hf : IsCoveringMap f)
    (hfinite : ∀ b, (f ⁻¹' {b}).Finite) (hsurj : Function.Surjective f)
    (height : Z → ℝ) (hheight : Continuous height)
    (hseparate : Function.Injective (fun z => (f z, height z))) :
    IsHomeomorph f :=
  ⟨hf.continuous, hf.isOpenMap,
    finite_covering_injective_of_ordered_heights f hf hfinite height hheight hseparate, hsurj⟩

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
