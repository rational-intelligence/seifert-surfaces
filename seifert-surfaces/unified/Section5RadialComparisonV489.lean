import Section5LocalDistanceV489
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
noncomputable section
universe u
variable {N : Type u} [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold 𝓘(ℝ,E3) ∞ N]

theorem ambient_metric_nonneg (h : AmbientMetric N) (p : N)
    (v : TangentSpace 𝓘(ℝ,E3) p) : 0 ≤ h.inner p v v := by
  by_cases hv : v = 0
  · simp [hv]
  · exact (h.pos p v hv).le

theorem ambient_unit_pairing_le_one (h : AmbientMetric N) (p : N)
    (v w : TangentSpace 𝓘(ℝ,E3) p)
    (hv : h.inner p v v = 1) (hw : h.inner p w w = 1) : h.inner p v w ≤ 1 := by
  have hq := ambient_metric_nonneg h p (v-w)
  simp only [map_sub,sub_apply] at hq
  rw [h.symm p w v,hv,hw] at hq
  linarith

def radialLine (y : E3) (t : ℝ) : E3 := y + (t-y 0) • coordinateVector 3 0

theorem radial_line_self (y : E3) : radialLine y (y 0) = y := by simp [radialLine]

theorem radial_line_zero_coordinate (y : E3) (t : ℝ) : radialLine y t 0 = t := by
  simp [radialLine,coordinateVector,EuclideanSpace.single]

theorem radial_line_hasDerivAt (y : E3) (t : ℝ) :
    HasDerivAt (radialLine y) (coordinateVector 3 0) t := by
  change HasDerivAt (fun s : ℝ => y + (s-y 0) • coordinateVector 3 0) _ t
  simpa only [one_smul] using! (((hasDerivAt_id t).sub_const (y 0)).smul_const
    (coordinateVector 3 0)).const_add y

theorem warped_radial_transition_hasDerivAt {h : AmbientMetric N} {M : Set N}
    (C D : WarpedBoundaryCollar h M) (y : E3) (t : ℝ)
    (hc : radialLine y t ∈ C.coordinates.chart.target)
    (hd : C.coordinates.chart.symm (radialLine y t) ∈ D.coordinates.chart.source) :
    HasDerivAt (fun s => D.radial (C.coordinates.chart.symm (radialLine y s)))
      (h.inner (C.coordinates.chart.symm (radialLine y t))
        (warpedMetricNormal D (C.coordinates.chart.symm (radialLine y t)))
        (warpedMetricNormal C (C.coordinates.chart.symm (radialLine y t)))) t := by
  let q := C.coordinates.chart.symm (radialLine y t)
  have hl := radial_line_hasDerivAt y t
  have hC : MDifferentiableAt 𝓘(ℝ,E3) 𝓘(ℝ,E3) C.coordinates.chart.symm (radialLine y t) :=
    ((C.coordinates.inverse_smooth _ hc).contMDiffAt
      (C.coordinates.chart.open_target.mem_nhds hc)).mdifferentiableAt (by simp)
  have hD : MDifferentiableAt 𝓘(ℝ,E3) 𝓘(ℝ) D.radial q :=
    ((D.radial_smooth _ hd).contMDiffAt
      (D.coordinates.chart.open_source.mem_nhds hd)).mdifferentiableAt (by simp)
  have hf : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ)
      (D.radial ∘ (C.coordinates.chart.symm ∘ radialLine y)) t :=
    hD.comp t (hC.comp t hl.differentiableAt.mdifferentiableAt)
  have hder : deriv (D.radial ∘ (C.coordinates.chart.symm ∘ radialLine y)) t =
      h.inner q (warpedMetricNormal D q) (warpedMetricNormal C q) := by
    have heq : mfderiv 𝓘(ℝ) 𝓘(ℝ) (D.radial ∘ (C.coordinates.chart.symm ∘ radialLine y)) t =
        fderiv ℝ (D.radial ∘ (C.coordinates.chart.symm ∘ radialLine y)) t := by
      rw [mfderiv_eq_fderiv]
      rfl
    rw [← fderiv_apply_one_eq_deriv, ← heq]
    rw [mfderiv_comp t hD (hC.comp t hl.differentiableAt.mdifferentiableAt),
      mfderiv_comp t hC hl.differentiableAt.mdifferentiableAt]
    change mfderiv 𝓘(ℝ,E3) 𝓘(ℝ) D.radial q
      (mfderiv 𝓘(ℝ,E3) 𝓘(ℝ,E3) C.coordinates.chart.symm (radialLine y t)
        (mfderiv 𝓘(ℝ) 𝓘(ℝ,E3) (radialLine y) t 1)) = _
    have he : mfderiv 𝓘(ℝ) 𝓘(ℝ,E3) (radialLine y) t 1 = coordinateVector 3 0 := by
      rw [mfderiv_eq_fderiv]
      change fderiv ℝ (radialLine y) t 1 = _
      rw [hl.hasFDerivAt.fderiv]
      simp
    rw [he,← warped_metric_normal_pairing D q hd]
    congr 1
    unfold warpedMetricNormal q
    rw [C.coordinates.chart.right_inv hc]
    rfl
  exact hder ▸ (mdifferentiableAt_iff_differentiableAt.mp hf).hasDerivAt

theorem warped_radial_comparison {h : AmbientMetric N} {M : Set N}
    (C D : WarpedBoundaryCollar h M) (p : N)
    (hp : p ∈ C.coordinates.chart.source) (hr : 0 ≤ C.radial p)
    (hline : ∀ t ∈ Icc (0 : ℝ) (C.radial p),
      radialLine (C.coordinates.chart p) t ∈ C.coordinates.chart.target ∧
      C.coordinates.chart.symm (radialLine (C.coordinates.chart p) t) ∈
        D.coordinates.chart.source) : D.radial p ≤ C.radial p := by
  let y := C.coordinates.chart p
  let f := fun t => D.radial (C.coordinates.chart.symm (radialLine y t))
  have ht (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (C.radial p)) :=
    warped_radial_transition_hasDerivAt C D y t (hline t ht).1 (hline t ht).2
  have hzero : f 0 = 0 := by
    apply (D.boundary_identification _ (hline 0 ⟨le_rfl,hr⟩).2).mp
    apply (C.boundary_identification _
      (C.coordinates.chart.map_target (hline 0 ⟨le_rfl,hr⟩).1)).mpr
    rw [C.radial_coordinate _ (C.coordinates.chart.map_target (hline 0 ⟨le_rfl,hr⟩).1),
      C.coordinates.chart.right_inv (hline 0 ⟨le_rfl,hr⟩).1,radial_line_zero_coordinate]
  have hend : f (C.radial p) = D.radial p := by
    dsimp [f,y]
    rw [C.radial_coordinate p hp,radial_line_self,C.coordinates.chart.left_inv hp]
  have hle : f (C.radial p) ≤ C.radial p := by
    apply image_le_of_deriv_right_le_deriv_boundary
      (fun t ht' => (ht t ht').continuousAt.continuousWithinAt)
      (fun t ht' => (ht t (Ico_subset_Icc_self ht')).hasDerivWithinAt)
      (by change f 0 ≤ 0; rw [hzero]) continuousOn_id
      (fun t _ => (hasDerivAt_id t).hasDerivWithinAt) ?_ ⟨hr,le_rfl⟩
    intro t ht'
    have hl := hline t (Ico_subset_Icc_self ht')
    exact ambient_unit_pairing_le_one h _ _ _
      (warped_metric_normal_unit D _ hl.2)
      (warped_metric_normal_unit C _ (C.coordinates.chart.map_target hl.1))
  rwa [hend] at hle

#print axioms warped_radial_comparison
end
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
