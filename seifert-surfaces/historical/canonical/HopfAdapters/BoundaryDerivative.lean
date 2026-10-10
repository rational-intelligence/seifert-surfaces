import HopfAdapters.Definitions

noncomputable section
open Set Metric Function
open scoped Topology BigOperators ContDiff

namespace SeifertSurfaces.AppendixACoordinates.HopfAdapters

theorem affine_extension_eqOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set E) (f : E → ℝ) (x₀ : E) (D : E →L[ℝ] ℝ) :
    EqOn (affineOutsideExtension K f x₀ D) f K := by
  intro x hx
  simp only [affineOutsideExtension, ite_eq_left hx]

theorem affine_extension_hasFDerivAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (K : Set E) (f : E → ℝ) (x₀ : E) (hx₀ : x₀ ∈ K)
    (D : E →L[ℝ] ℝ) (hD : HasFDerivWithinAt f D K x₀) :
    HasFDerivAt (affineOutsideExtension K f x₀ D) D x₀ := by
  have hinside : HasFDerivWithinAt (affineOutsideExtension K f x₀ D) D K x₀ :=
    hD.congr' (affine_extension_eqOn K f x₀ D) hx₀
  have haffine : HasFDerivAt (fun x => f x₀ + D (x - x₀)) D x₀ := by
    simpa using (D.hasFDerivAt.comp x₀ ((hasFDerivAt_id x₀).sub_const x₀)).const_add (f x₀)
  have houtside : HasFDerivWithinAt (affineOutsideExtension K f x₀ D) D Kᶜ x₀ := by
    apply haffine.hasFDerivWithinAt.congr
    · intro x hx
      simp only [affineOutsideExtension, ite_eq_right hx]
    · simp [affineOutsideExtension, hx₀]
  simpa only [union_compl_self, hasFDerivWithinAt_univ] using hinside.union houtside

theorem affine_extension_continuousOn {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (K : Set E) (f : E → ℝ) (x₀ : E) (D : E →L[ℝ] ℝ)
    (hf : ContinuousOn f K) : ContinuousOn (affineOutsideExtension K f x₀ D) K := by
  exact hf.congr (affine_extension_eqOn K f x₀ D)

theorem affine_extension_contDiffOn_interior {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (K : Set E) (f : E → ℝ) (x₀ : E) (D : E →L[ℝ] ℝ)
    (n : WithTop ℕ∞) (hf : ContDiffOn ℝ n f (interior K)) :
    ContDiffOn ℝ n (affineOutsideExtension K f x₀ D) (interior K) := by
  exact hf.congr ((affine_extension_eqOn K f x₀ D).mono interior_subset)

theorem affine_extension_nondivOp_eq {d : ℕ}
    (a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ)
    (b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ) (c : EuclideanSpace ℝ (Fin d) → ℝ)
    (K : Set (EuclideanSpace ℝ (Fin d))) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin d)) (D : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ interior K) :
    nondivOp a b c (affineOutsideExtension K f x₀ D) x = nondivOp a b c f x := by
  have heq : affineOutsideExtension K f x₀ D =ᶠ[𝓝 x] f :=
    Filter.eventually_of_mem (isOpen_interior.mem_nhds hx)
      (fun y hy => affine_extension_eqOn K f x₀ D (interior_subset hy))
  have hpartial (j : Fin d) :
      partialD j (affineOutsideExtension K f x₀ D) =ᶠ[𝓝 x] partialD j f :=
    (heq.fderiv (𝕜 := ℝ)).mono fun y hy => congrArg (fun T => T (EuclideanSpace.single j 1)) hy
  have hfirst (i : Fin d) :
      partialD i (affineOutsideExtension K f x₀ D) x = partialD i f x :=
    congrArg (fun T => T (EuclideanSpace.single i 1)) (heq.fderiv_eq (𝕜 := ℝ))
  have hsecond (i j : Fin d) :
      partialD i (partialD j (affineOutsideExtension K f x₀ D)) x =
        partialD i (partialD j f) x :=
    congrArg (fun T => T (EuclideanSpace.single i 1)) ((hpartial j).fderiv_eq (𝕜 := ℝ))
  simp only [nondivOp, hfirst, hsecond, heq.eq_of_nhds]

end SeifertSurfaces.AppendixACoordinates.HopfAdapters
