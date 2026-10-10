import CurveComplexGenusTwo.Topology.CompletedJordan

open Set Schoenflies

/-- A compact parameter interval of a continuous injective planar line is an
arc with the actual endpoint values. -/
theorem continuous_injective_interval_isArcBetween
    (f : C(ℝ, Plane)) (hf : Function.Injective f)
    {r s : ℝ} (hrs : r < s) :
    IsArcBetween (f '' Icc r s) (f r) (f s) := by
  refine ⟨fun u => f (r + (s - r) * u), by fun_prop, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    have hh := hf hxy
    nlinarith
  · ext z
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨r + (s - r) * u,
        ⟨by nlinarith [hu.1], by nlinarith [hu.2]⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨(x - r) / (s - r), ⟨?_, ?_⟩, ?_⟩
      · apply div_nonneg (by linarith [hx.1]) (by linarith)
      · apply (div_le_iff₀ (by linarith : 0 < s - r)).mpr
        linarith [hx.2]
      · apply congrArg f
        field_simp [sub_ne_zero.mpr (ne_of_gt hrs)]
        ring
  · simp
  · change f (r + (s - r) * 1) = f s
    congr 1
    ring

#print axioms continuous_injective_interval_isArcBetween
