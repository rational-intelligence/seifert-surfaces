import WeakTestExtension
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.MeasureTheory.Measure.SeparableMeasure

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace SeifertSurfaces.QuasilinearProviderBridge.EnergyHelpers

theorem hilbert_weak_subsequence {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (u : ℕ → H) (C : ℝ) (hu : ∀ n, ‖u n‖ ≤ C) :
    ∃ g : H, ∃ s : ℕ → ℕ, StrictMono s ∧
      ∀ v : H, Tendsto (fun n => inner ℝ (u (s n)) v) atTop (𝓝 (inner ℝ g v)) := by
  let w : ℕ → WeakDual ℝ H := fun n => StrongDual.toWeakDual ((InnerProductSpace.toDual ℝ H) (u n))
  have hw (n : ℕ) : w n ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ H) C := by
    change dist ((InnerProductSpace.toDual ℝ H) (u n)) 0 ≤ C
    simpa only [dist_zero_right, (InnerProductSpace.toDual ℝ H).norm_map] using hu n
  obtain ⟨L, -, s, hs, hconv⟩ := (WeakDual.isSeqCompact_closedBall ℝ H 0 C).subseq_of_frequently_in
    (Frequently.of_forall hw)
  let g := (InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual L)
  refine ⟨g, s, hs, ?_⟩
  intro v
  have ht := ((WeakDual.eval_continuous v).tendsto L).comp hconv
  have hL : inner ℝ g v = L v := by
    change (InnerProductSpace.toDual ℝ H) g v = _
    simp [g]
  rw [hL]
  exact ht

theorem planar_L2_separable (B : Set (EuclideanSpace ℝ (Fin 2))) :
    TopologicalSpace.SeparableSpace (Lp (EuclideanSpace ℝ (Fin 2)) 2 (volume.restrict B)) := by
  haveI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  infer_instance

end SeifertSurfaces.QuasilinearProviderBridge.EnergyHelpers
