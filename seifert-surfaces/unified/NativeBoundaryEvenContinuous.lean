import NativeBoundaryNormalFluxAssembly

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization

def nativeEvenExtension (f : E2 → ℝ) (x : E2) : ℝ :=
  if 0 ≤ x 0 then f x else f (normalReflection x)

theorem continuous_native_even_extension
    (ρ : ℝ) (f : E2 → ℝ) (hf : ContinuousOn f (closedHalfDisc ρ)) :
    ContinuousOn (nativeEvenExtension f) (Metric.ball 0 ρ) := by
  have hupper : ∀ x ∈ Metric.ball (0 : E2) ρ, 0 ≤ x 0 → x ∈ closedHalfDisc ρ :=
    fun x hx hn => ⟨Metric.ball_subset_closedBall hx, hn⟩
  have hlower : ∀ x ∈ Metric.ball (0 : E2) ρ, x 0 ≤ 0 →
      normalReflection x ∈ closedHalfDisc ρ := by
    intro x hx hn
    refine ⟨Metric.ball_subset_closedBall (normalReflection_maps_ball ρ hx), ?_⟩
    change 0 ≤ normalReflection x 0
    rw [normalReflection_zero]
    linarith
  have hclosedUpper : IsClosed {x : E2 | 0 ≤ x 0} :=
    isClosed_le continuous_const (EuclideanSpace.proj (0 : Fin 2)).continuous
  have hclosedLower : IsClosed {x : E2 | x 0 ≤ 0} :=
    isClosed_le (EuclideanSpace.proj (0 : Fin 2)).continuous continuous_const
  have hclLower : closure {x : E2 | ¬0 ≤ x 0} ⊆ {x : E2 | x 0 ≤ 0} :=
    closure_minimal (fun x hx => (not_le.mp hx).le) hclosedLower
  have hfront : ∀ x ∈ frontier {y : E2 | 0 ≤ y 0}, x 0 = 0 := by
    intro x hx
    have hp : 0 ≤ x 0 := by
      have hh := hx.1
      rwa [hclosedUpper.closure_eq] at hh
    have hn : x 0 ≤ 0 := hclLower (by
      change x ∈ closure ({y : E2 | 0 ≤ y 0}ᶜ)
      rw [closure_compl]
      exact hx.2)
    exact le_antisymm hn hp
  unfold nativeEvenExtension
  apply ContinuousOn.if
  · intro x hx
    rw [normalReflection_flat (hfront x hx.2)]
  · exact hf.mono (fun x hx => hupper x hx.1 (by
      have hh := hx.2
      rwa [hclosedUpper.closure_eq] at hh))
  · have hm : MapsTo normalReflection
        (Metric.ball (0 : E2) ρ ∩ closure {x : E2 | ¬0 ≤ x 0}) (closedHalfDisc ρ) :=
      fun x hx => hlower x hx.1 (hclLower hx.2)
    exact hf.comp normalReflection.continuous.continuousOn hm

theorem native_even_extension_eq_reflected_off_flat
    (ρ : ℝ) (f : E2 → ℝ) (x : E2) (hx : x ∈ Metric.ball 0 ρ) (hn : x 0 ≠ 0) :
    nativeEvenExtension f x = nativeEvenReflectedSource ρ f x := by
  have hRx := normalReflection_maps_ball ρ hx
  rcases lt_or_gt_of_ne hn with hneg | hpos
  · have hxU : x ∉ openHalfDisc ρ := fun hh => (not_lt_of_ge hneg.le) hh.2
    have hRU : normalReflection x ∈ openHalfDisc ρ :=
      ⟨hRx, by change 0 < normalReflection x 0; rw [normalReflection_zero]; linarith⟩
    simp only [nativeEvenExtension, if_neg (not_le.mpr hneg), nativeEvenReflectedSource,
      indicator_of_notMem hxU, indicator_of_mem hRU, zero_add]
  · have hxU : x ∈ openHalfDisc ρ := ⟨hx, hpos⟩
    have hRU : normalReflection x ∉ openHalfDisc ρ := by
      intro hh
      have hp : 0 < normalReflection x 0 := hh.2
      rw [normalReflection_zero] at hp
      linarith
    simp only [nativeEvenExtension, if_pos hpos.le, nativeEvenReflectedSource,
      indicator_of_mem hxU, indicator_of_notMem hRU, add_zero]

theorem native_memW1p_congr_ae
    (U : Set E2) (f F : E2 → ℝ) (he : f =ᵐ[volume.restrict U] F)
    (hf : DeGiorgi.MemW1p 2 f U) : DeGiorgi.MemW1p 2 F U := by
  refine ⟨(memLp_congr_ae he).mp hf.1, ?_⟩
  intro i
  obtain ⟨G, hG, hw⟩ := hf.2 i
  refine ⟨G, hG, ?_⟩
  intro ψ hs hc ht
  have hi : (∫ x in U, F x * fderiv ℝ ψ x (EuclideanSpace.single i 1)) =
      ∫ x in U, f x * fderiv ℝ ψ x (EuclideanSpace.single i 1) := by
    apply integral_congr_ae
    filter_upwards [he] with x hx
    rw [hx]
  rw [hi]
  exact hw ψ hs hc ht

theorem native_even_extension_memW1p
    (ρ : ℝ) (f : E2 → ℝ) (hf : DeGiorgi.MemW1p 2 f (openHalfDisc ρ)) :
    DeGiorgi.MemW1p 2 (nativeEvenExtension f) (Metric.ball 0 ρ) := by
  apply native_memW1p_congr_ae _ _ _ ?_ (native_even_reflected_memW1p ρ f hf)
  have hflat : ∀ᵐ x : E2 ∂volume, x 0 ≠ 0 := by
    simpa only [ae_iff, not_not] using native_flat_plane_null
  filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet,
    ae_restrict_of_ae hflat] with x hx hn
  exact (native_even_extension_eq_reflected_off_flat ρ f x hx hn).symm

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
