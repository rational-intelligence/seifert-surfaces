import NativeFiniteClockLiftProbe

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set Topology Filter
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
universe u
variable {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)

/-- Actual native arc geometry supplies one original affine clock and a
common neighbourhood with C1 regular boundary lifts in every incident whole
piece. The incident pieces and the lifts are outputs of the native category. -/
theorem native_arc_finite_regular_boundary_lifts
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (a : Fin F.seam.arcCount) (s : Time)
    (hleft : 0 < (s : ℝ)) (hright : (s : ℝ) < 1) :
    ∃ r : ℝ, 0 < r ∧ 0 < (s : ℝ) - r ∧ (s : ℝ) + r < 1 ∧
      ∃ parameter : Ioo (-1 : ℝ) 1 → Time,
      (∀ t, (parameter t : ℝ) = (s : ℝ) + r * (t : ℝ)) ∧
      IsEmbedding parameter ∧ IsOpen (range parameter) ∧
      parameter ⟨0, neg_one_lt_zero, zero_lt_one⟩ = s ∧
      ∃ γ : ℝ → ThreeSphere,
      (∀ t : Ioo (-1 : ℝ) 1, γ t = E.toSphere (F.map (F.seam.arc a (parameter t)))) ∧
      ContMDiffOn 𝓘(ℝ) (𝓡 3) ∞ γ (Ioo (-1 : ℝ) 1) ∧
      (∀ t : Ioo (-1 : ℝ) 1, mfderiv 𝓘(ℝ) (𝓡 3) γ (t : ℝ) 1 ≠ 0) ∧
      ∃ Q : Set ℝ, IsOpen Q ∧ Q ⊆ Ioo (-1 : ℝ) 1 ∧ 0 ∈ Q ∧
      ∀ i : Fin F.pieceCount, F.seam.arc a s ∈ range (F.parametrization i) →
        ∃ j : Fin (F.domain i).count, ∃ q : ℝ → Euc 2,
          MapsTo q Q (((F.domain i).chart j).map.target ∩
            frontier ((F.domain i).chart j).map.target) ∧
          (∀ t ∈ Q, E.toSphere (sectorCoordinateMap (F.map ∘ F.parametrization i) j (q t)) = γ t) ∧
          ContDiffOn ℝ 1 q Q ∧ (∀ t ∈ Q, deriv q t ≠ 0) := by
  classical
  obtain ⟨r, hr, hl, hu, parameter, hformula, _, γ, hγformula, hγ, hreg⟩ :=
    native_arc_affine_clock E F a s hleft hright
  obtain ⟨hpemb, hpr, hp0⟩ := positive_affine_native_arc_clock_topology s r hr parameter hformula
  let W := Ioo (-1 : ℝ) 1
  let β : ℝ → S := fun t => if h : t ∈ W then F.seam.arc a (parameter ⟨t, h⟩) else F.seam.arc a s
  have hβ (t : W) : β t = F.seam.arc a (parameter t) := by
    simp only [β, dif_pos t.property]
    rfl
  have hβ0 : β 0 = F.seam.arc a s := by
    have h0 : (0 : ℝ) ∈ W := ⟨neg_one_lt_zero, zero_lt_one⟩
    simp only [β, dif_pos h0]
    rw [hp0]
  have hβemb : IsEmbedding (fun t : W => β t) := by
    have heq : (fun t : W => β t) = F.seam.arc a ∘ parameter := funext hβ
    rw [heq]
    exact (F.seam.arc_embedding a).comp hpemb
  obtain ⟨U, hU, hsU, hUB, hcut⟩ := native_arc_isolated_source_window E F a s hleft hright
  have hUβ : β 0 ∈ U := by rw [hβ0]; exact hsU
  obtain ⟨V, hV, hsV, _, hVB, hVcut⟩ := native_compact_clock_source_window
    (F.seam.arc a) (F.seam.arc_embedding a) W parameter hpr β hβ
      ⟨0, neg_one_lt_zero, zero_lt_one⟩ F.seam.carrier U hU hUβ hUB
        (fun x hx => (hcut ▸ hx).1)
  have hsseam : β 0 ∈ F.seam.carrier := by
    rw [hβ0]
    exact Or.inl (mem_iUnion.mpr ⟨a, s, rfl⟩)
  obtain ⟨Q, hQ, hQW, h0Q, hlifts⟩ := native_finite_incident_boundary_clock_lifts E F W β
    hβemb 0 ⟨neg_one_lt_zero, zero_lt_one⟩ V hV hsV hVB hVcut hsseam
  refine ⟨r, hr, hl, hu, parameter, hformula, hpemb, hpr, hp0,
    γ, hγformula, hγ, hreg, Q, hQ, hQW, h0Q, ?_⟩
  intro i hi
  obtain ⟨j, q, hqb, hqi⟩ := hlifts i (by rw [hβ0]; exact hi)
  have heq (t : ℝ) (ht : t ∈ Q) :
      E.toSphere (sectorCoordinateMap (F.map ∘ F.parametrization i) j (q t)) = γ t := by
    change E.toSphere (F.map (F.parametrization i (((F.domain i).chart j).map.symm (q t)))) = γ t
    rw [hqi t ht, hβ ⟨t, hQW ht⟩]
    exact (hγformula ⟨t, hQW ht⟩).symm
  have hγQ : ContMDiffOn 𝓘(ℝ) (𝓡 3) 1 γ Q := (hγ.of_le (by simp)).mono hQW
  have hqt : MapsTo q Q ((F.domain i).chart j).map.target := fun t ht => (hqb ht).1
  exact ⟨j, q, hqb, heq, native_piece_curve_coordinates_c1_all E F i j Q hQ γ q hγQ hqt heq,
    native_piece_curve_coordinates_regular E F i j Q hQ γ q hγQ hqt heq
      (fun t ht => hreg ⟨t, hQW ht⟩)⟩

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
