import SectorPieces
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.InnerProductSpace.Dual

set_option autoImplicit false
open scoped Pointwise
open Set Topology Module
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations

private theorem vector_outside_finite_subspaces
    {ι : Type*} [Finite ι] (S : ι → Submodule ℝ (Euc 3)) (hS : ∀ i, S i ≠ ⊤) :
    ∃ v : Euc 3, ∀ i, v ∉ S i := by
  have hc (i : ι) : IsClosed (S i : Set (Euc 3)) := (S i).closed_of_finiteDimensional
  have hd (i : ι) : Dense (S i : Set (Euc 3))ᶜ := by
    apply interior_eq_empty_iff_dense_compl.mp
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro v hv
    exact hS i ((S i).eq_top_of_nonempty_interior' ⟨v, hv⟩)
  obtain ⟨v, hv⟩ := (dense_iInter_of_isOpen (fun i => (hc i).isOpen_compl) hd).nonempty
  exact ⟨v, mem_iInter.mp hv⟩

/-- Finitely many rank-two tangent maps in three-dimensional space admit one
common transverse projection. No common tangent plane is assumed. -/
theorem finite_rank_two_common_projection_with_height
    {ι : Type*} [Finite ι] (D : ι → Euc 2 →L[ℝ] Euc 3)
    (hD : ∀ i, Function.Injective (D i)) :
    ∃ P : Euc 3 →L[ℝ] Euc 2, ∃ h : Euc 3 →L[ℝ] ℝ,
      Function.Injective (fun x => (P x, h x)) ∧
      ∀ i, Function.Bijective (P.comp (D i)) := by
  let S : Option ι → Submodule ℝ (Euc 3) := fun i =>
    match i with
    | none => ⊥
    | some j => (D j).toLinearMap.range
  have hS (i : Option ι) : S i ≠ ⊤ := by
    cases i with
    | none => exact bot_ne_top
    | some i =>
      intro he
      have hn := LinearMap.finrank_range_of_inj (hD i)
      change Module.finrank ℝ (D i).toLinearMap.range = Module.finrank ℝ (Euc 2) at hn
      change (D i).toLinearMap.range = ⊤ at he
      rw [he] at hn
      norm_num [Euc] at hn
  obtain ⟨v, hv⟩ := vector_outside_finite_subspaces S hS
  have hv0 : v ≠ 0 := by simpa [S] using hv none
  let V : Submodule ℝ (Euc 3) := ℝ ∙ v
  let _ : IsClosed (V : Set (Euc 3)) := Submodule.closed_of_finiteDimensional V
  have hdim : Module.finrank ℝ ((Euc 3) ⧸ V) = Module.finrank ℝ (Euc 2) := by
    have h := V.finrank_quotient_add_finrank
    have hV : Module.finrank ℝ V = 1 := finrank_span_singleton hv0
    rw [hV] at h
    norm_num [Euc] at h ⊢
    omega
  let Q : Euc 3 →L[ℝ] ((Euc 3) ⧸ V) := V.mkQ.toContinuousLinearMap
  let e : ((Euc 3) ⧸ V) ≃L[ℝ] Euc 2 := ContinuousLinearEquiv.ofFinrankEq hdim
  let P : Euc 3 →L[ℝ] Euc 2 := e.toContinuousLinearMap.comp Q
  let h : Euc 3 →L[ℝ] ℝ := innerSL ℝ v
  have hpair : Function.Injective (fun x => (P x, h x)) := by
    intro x y hxy
    have hp : P (x - y) = 0 := by
      rw [map_sub, show P x = P y from congrArg Prod.fst hxy, sub_self]
    have hh : h (x - y) = 0 := by
      rw [map_sub, show h x = h y from congrArg Prod.snd hxy, sub_self]
    have hQ : Q (x - y) = 0 := e.injective (by simpa [P] using hp)
    have hmem : x - y ∈ V := (Submodule.Quotient.mk_eq_zero V).mp hQ
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
    have hvpos : 0 < inner ℝ v v := real_inner_self_pos.mpr hv0
    have ha0 : a = 0 := by
      rw [← ha] at hh
      change inner ℝ v (a • v) = 0 at hh
      rw [inner_smul_right] at hh
      exact (mul_eq_zero.mp hh).resolve_right (ne_of_gt hvpos)
    exact sub_eq_zero.mp (by simpa [ha0] using ha.symm)
  refine ⟨P, h, hpair, ?_⟩
  intro i
  have hinj : Function.Injective (P.comp (D i)) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro w hw
    have hQ : Q (D i w) = 0 := e.injective (by simpa [P] using hw)
    have hmem : D i w ∈ V := (Submodule.Quotient.mk_eq_zero V).mp hQ
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
    by_cases ha0 : a = 0
    · have hzero : D i w = 0 := by simpa [ha0] using ha.symm
      exact (hD i).eq_iff.mp (by simpa using hzero)
    · have hvin : v ∈ (D i).toLinearMap.range := by
        have hm : a • v ∈ (D i).toLinearMap.range := ha.symm ▸ ⟨w, rfl⟩
        have hm' := (D i).toLinearMap.range.smul_mem a⁻¹ hm
        simpa [smul_smul, ha0] using hm'
      exact (hv (some i) hvin).elim
  exact ⟨hinj, (LinearMap.injective_iff_surjective (f := (P.comp (D i)).toLinearMap)).mp hinj⟩

/-- Common transverse projection, forgetting the separating height. -/
theorem finite_rank_two_common_projection
    {ι : Type*} [Finite ι] (D : ι → Euc 2 →L[ℝ] Euc 3)
    (hD : ∀ i, Function.Injective (D i)) :
    ∃ P : Euc 3 →L[ℝ] Euc 2, ∀ i, Function.Bijective (P.comp (D i)) := by
  obtain ⟨P, _, _, hP⟩ := finite_rank_two_common_projection_with_height D hD
  exact ⟨P, hP⟩

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
