import RoughLift

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology BigOperators ContDiff ENNReal
namespace SeifertSurfaces.QuasilinearProviderBridge.Helpers
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.QuasilinearLocalization

lemma planar_pullback_aestronglyMeasurable {F : Type*} [TopologicalSpace F] {B : Set E2}
    (hB : IsOpen B) {f : E2 → F} (hf : AEStronglyMeasurable f (volume.restrict B)) :
    AEStronglyMeasurable (fun y => f (planarPart y)) (volume.restrict (cylinder B)) := by
  rw [← productCLE_map_cylinder hB]
  apply productCLE.toHomeomorph.measurableEmbedding.aestronglyMeasurable_map_iff.mpr
  change AEStronglyMeasurable (fun p : E2 × ℝ => f (planarPart (productCLE p))) _
  simpa only [productCLE_apply, planarPart_lifted] using
    (hf.comp_fst : AEStronglyMeasurable (fun p : E2 × ℝ => f p.1)
      ((volume.restrict B).prod (volume.restrict (Ioo (-1 : ℝ) 1))))

lemma liftMatrix_aemeasurable {B : Set E2} (hB : IsOpen B) (C : LinearizedCoefficients)
    (v : E2 → ℝ) (D : ℝ) (hmeas : CoefficientMeasurableOn B C)
    (hv : MemLp v 2 (volume.restrict B)) :
    ∀ i j : Fin 3, AEMeasurable (fun y => liftMatrix C v D y i j)
      (volume.restrict (cylinder B)) := by
  let μ : Measure E3 := volume.restrict (cylinder B)
  have hp := fun {F : Type} [TopologicalSpace F] (f : E2 → F) =>
    planar_pullback_aestronglyMeasurable (F := F) hB (f := f)
  rcases hmeas with ⟨ha, hc, hd, hb, hq, hf⟩
  have hv' := (planar_pullback_memLp hB hv).aestronglyMeasurable
  have hF : AEStronglyMeasurable (fun y => v (planarPart y) • C.c (planarPart y) + C.d (planarPart y)) μ :=
    (hv'.smul (hp C.c hc)).add (hp C.d hd)
  have hFcomp (i : Fin 2) : AEStronglyMeasurable (fun y =>
      (v (planarPart y) • C.c (planarPart y) + C.d (planarPart y)) i) μ :=
    (EuclideanSpace.proj i).continuous.comp_aestronglyMeasurable hF
  have ha' (i j : Fin 2) : AEStronglyMeasurable
      (fun y => C.a (planarPart y) (coordinateVector 2 j) i) μ :=
    (EuclideanSpace.proj i).continuous.comp_aestronglyMeasurable
      ((hp C.a ha).apply_continuousLinearMap (coordinateVector 2 j))
  have hb' (i : Fin 2) : AEStronglyMeasurable
      (fun y => y 2 * C.b (planarPart y) (coordinateVector 2 i)) μ :=
    (EuclideanSpace.proj (2 : Fin 3)).continuous.measurable.aestronglyMeasurable.mul
      ((hp C.b hb).apply_continuousLinearMap (coordinateVector 2 i))
  have hg : AEStronglyMeasurable (fun y => D + y 2 *
      (C.q (planarPart y) * v (planarPart y) + C.f (planarPart y))) μ :=
    aestronglyMeasurable_const.add
      ((EuclideanSpace.proj (2 : Fin 3)).continuous.measurable.aestronglyMeasurable.mul
        (((hp C.q hq).mul hv').add (hp C.f hf)))
  intro i j
  fin_cases i <;> fin_cases j
  · simpa [liftMatrix, μ] using (ha' 0 0).aemeasurable
  · simpa [liftMatrix, μ] using (ha' 0 1).aemeasurable
  · simpa [liftMatrix, μ] using (hFcomp 0).aemeasurable
  · simpa [liftMatrix, μ] using (ha' 1 0).aemeasurable
  · simpa [liftMatrix, μ] using (ha' 1 1).aemeasurable
  · simpa [liftMatrix, μ] using (hFcomp 1).aemeasurable
  · simpa [liftMatrix, μ] using (hb' 0).aemeasurable
  · simpa [liftMatrix, μ] using (hb' 1).aemeasurable
  · simpa [liftMatrix, μ] using hg.aemeasurable

end SeifertSurfaces.QuasilinearProviderBridge.Helpers
