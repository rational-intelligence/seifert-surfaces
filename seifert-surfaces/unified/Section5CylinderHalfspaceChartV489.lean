import Section5ActualSurfaceBoundaryV489
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
open Set Function Filter Manifold Topology
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.SurfaceInverseV489
open SeifertSurfaces.Foundations SeifertSurfaces.AppendixACoordinates
noncomputable section

/-- The actual product model is smoothly identical to the two-dimensional
half-space, with its radial coordinate first. -/
theorem cylinder_model_diffeomorph :
    ∃ d : Diffeomorph ((𝓡 1).prod (𝓡∂ 1)) (𝓡∂ 2)
      (EuclideanSpace ℝ (Fin 1) × EuclideanHalfSpace 1) (EuclideanHalfSpace 2) ∞,
      ∀ p, (d p).val = !₂[p.2.val 0,p.1 0] := by
  let I := (𝓡 1).prod (𝓡∂ 1)
  let l : (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) ≃ₗ[ℝ] E2 := {
    toFun := fun p => !₂[p.2 0,p.1 0]
    invFun := fun w => (!₂[w 1],!₂[w 0])
    left_inv := by intro p; apply Prod.ext <;> ext i <;> fin_cases i <;> rfl
    right_inv := by intro w; ext i; fin_cases i <;> rfl
    map_add' := by intro p q; ext i; fin_cases i <;> rfl
    map_smul' := by intro r p; ext i; fin_cases i <;> rfl }
  let L := l.toContinuousLinearEquiv
  let e : (EuclideanSpace ℝ (Fin 1) × EuclideanHalfSpace 1) ≃ EuclideanHalfSpace 2 := {
    toFun := fun p => ⟨L (p.1,p.2.val),p.2.property⟩
    invFun := fun w => ((L.symm w.val).1,⟨(L.symm w.val).2,w.property⟩)
    left_inv := by
      intro p
      apply Prod.ext
      · ext i; fin_cases i; rfl
      · apply Subtype.ext; ext i; fin_cases i; rfl
    right_inv := by intro w; apply Subtype.ext; exact L.apply_symm_apply w.val }
  have hcompat (p) : (𝓡∂ 2) (e p) = L (I p) := rfl
  have hf : (fun p => (𝓡∂ 2).symm (L (I p))) = e := by
    funext p
    rw [← hcompat]
    exact (𝓡∂ 2).left_inv _
  have hi : (fun p => I.symm (L.symm ((𝓡∂ 2) p))) = e.symm := by
    funext p
    have he := hcompat (e.symm p)
    rw [e.apply_symm_apply] at he
    rw [he,L.symm_apply_apply]
    exact I.left_inv _
  have hc : ContMDiff I 𝓘(ℝ,EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) ∞
      (fun p : EuclideanSpace ℝ (Fin 1) × EuclideanHalfSpace 1 => (p.1,(𝓡∂ 1) p.2)) := by
    rw [modelWithCornersSelf_prod,← chartedSpaceSelf_prod]
    exact contMDiff_fst.prodMk ((𝓡∂ 1).contMDiff.comp contMDiff_snd)
  have he : ContMDiff I (𝓡∂ 2) ∞ e := by
    rw [← hf]
    apply (𝓡∂ 2).contMDiffOn_symm.comp_contMDiff (L.contDiff.contMDiff.comp hc)
    intro p
    change L (I p) ∈ range (𝓡∂ 2)
    rw [← hcompat]
    exact mem_range_self _
  have hes : ContMDiff (𝓡∂ 2) I ∞ e.symm := by
    rw [← hi]
    have hh := L.symm.contDiff.contMDiff.comp (𝓡∂ 2).contMDiff (n:=∞)
    rw [modelWithCornersSelf_prod,← chartedSpaceSelf_prod] at hh
    exact hh.fst.prodMk ((𝓡∂ 1).contMDiffOn_symm.comp_contMDiff hh.snd (by
      intro p
      have he := hcompat (e.symm p)
      rw [e.apply_symm_apply] at he
      rw [he,L.symm_apply_apply]
      exact mem_range_self _))
  exact ⟨⟨e,he,hes⟩,fun _ => rfl⟩

/-- A genuine smooth half-space chart on the cylinder at its lower boundary. -/
theorem cylinder_boundary_halfspace_chart (z : Circle) :
    ∃ d : PartialDiffeomorph ((𝓡 1).prod (𝓡∂ 1)) (𝓡∂ 2)
      (Circle × Time) (EuclideanHalfSpace 2) ∞,
      (z,0) ∈ d.source ∧
      (∀ q ∈ d.source, (d q).val 0 = (q.2 : ℝ)) := by
  obtain ⟨db,hdb⟩ := cylinder_model_diffeomorph
  let cc := chartAt (EuclideanSpace ℝ (Fin 1)) z
  have hcc : cc ∈ IsManifold.maximalAtlas (𝓡 1) ∞ Circle := IsManifold.chart_mem_maximalAtlas _
  have hct : IccLeftChart 0 1 ∈ IsManifold.maximalAtlas (𝓡∂ 1) ∞ Time := by
    rw [← Icc_chartedSpaceChartAt_of_le_top (z:=(0:Time)) (by norm_num)]
    exact IsManifold.chart_mem_maximalAtlas _
  let dom := cc.prod (IccLeftChart 0 1)
  let cd : PartialDiffeomorph ((𝓡 1).prod (𝓡∂ 1)) ((𝓡 1).prod (𝓡∂ 1))
      (Circle × Time) (EuclideanSpace ℝ (Fin 1) × EuclideanHalfSpace 1) ∞ := {
    toPartialEquiv := dom.toPartialEquiv
    open_source := dom.open_source
    open_target := dom.open_target
    contMDiffOn_toFun :=
      ((contMDiffOn_of_mem_maximalAtlas hcc).comp contMDiff_fst.contMDiffOn (fun _ h => h.1)).prodMk
      ((contMDiffOn_of_mem_maximalAtlas hct).comp contMDiff_snd.contMDiffOn (fun _ h => h.2))
    contMDiffOn_invFun :=
      ((contMDiffOn_symm_of_mem_maximalAtlas hcc).comp contMDiff_fst.contMDiffOn (fun _ h => h.1)).prodMk
      ((contMDiffOn_symm_of_mem_maximalAtlas hct).comp contMDiff_snd.contMDiffOn (fun _ h => h.2)) }
  refine ⟨cd.trans db.toPartialDiffeomorph,?_,?_⟩
  · refine ⟨⟨mem_chart_source _ _,?_⟩,mem_univ _⟩
    change (0:Time) ∈ (IccLeftChart (0:ℝ) 1).source
    simp [IccLeftChart]
  · intro q hq
    change (db (cd q)).val 0 = _
    rw [hdb]
    change (IccLeftChart (0:ℝ) 1 q.2).val 0 = _
    simp [IccLeftChart]

#print axioms cylinder_model_diffeomorph
#print axioms cylinder_boundary_halfspace_chart
end
end SeifertSurfaces.OriginalEndpoints.Section5.SurfaceInverseV489
