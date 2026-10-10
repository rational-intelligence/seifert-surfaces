import NativeHalfStripPackageProbe
import Mathlib.Topology.VectorBundle.Riemannian

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped Manifold ContDiff Bundle
open Set Topology Filter
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
universe u
variable {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)

theorem native_tangent_totalSpace_eq_cast
    (x y : ThreeSphere) (h : x = y) (v : TangentSpace (𝓡 3) x) :
    Bundle.TotalSpace.mk' (Euc 3) x v =
      Bundle.TotalSpace.mk' (Euc 3) y (h ▸ v) := by
  cases h
  rfl

/-- Native C1 regularity on the genuine closed sector makes its actual
within differential continuous along every continuous coordinate lift and
continuous source vector, in tangent total space. -/
theorem native_actual_differential_section_continuous
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count)
    {P : Type*} [TopologicalSpace P] (q v : P → Euc 2) (p : P → ThreeSphere)
    (hq : Continuous q) (hv : Continuous v)
    (hqm : ∀ t, q t ∈ ((F.domain i).chart j).map.target)
    (heq : ∀ t, pieceSphereCoordinate E F i j (q t) = p t) :
    Continuous (fun t => Bundle.TotalSpace.mk' (Euc 3) (p t)
      (actualPieceConormal E F i j (q t) (v t) (p t) (heq t))) := by
  let A := ((F.domain i).chart j).map.target
  have hA : UniqueMDiffOn 𝓘(ℝ,Euc 2) A := by
    rw [show A = ((F.domain i).chart j).model.domain from ((F.domain i).chart j).target_eq]
    exact ((F.domain i).chart j).model.uniqueDiffOn_domain.uniqueMDiffOn
  have hf : ContMDiffOn 𝓘(ℝ,Euc 2) (𝓡 3) 1 (pieceSphereCoordinate E F i j) A :=
    (native_piece_sphere_C1_rank E F i j).1
  have ht := hf.continuousOn_tangentMapWithin (by norm_num) hA
  have hinput : Continuous (fun t => (Bundle.TotalSpace.mk' (Euc 2) (q t)
      ((NormedSpace.fromTangentSpace (q t)).symm (v t)) :
      TangentBundle 𝓘(ℝ,Euc 2) (Euc 2))) := by
    exact (tangentBundleModelSpaceHomeomorph 𝓘(ℝ,Euc 2)).symm.continuous.comp (hq.prodMk hv)
  have hcomp := ht.comp_continuous hinput (fun t => hqm t)
  apply hcomp.congr
  intro t
  exact native_tangent_totalSpace_eq_cast _ _ (heq t) _

/-- Continuity of the same actual ambient metric pairing on continuous
native tangent sections, along an arbitrary continuous base clock. -/
theorem native_metric_pair_continuous
    (G : A7.SourceGeometry E) {P : Type*} [TopologicalSpace P]
    (p : P → ThreeSphere) (v w : ∀ t, TangentSpace (𝓡 3) (p t))
    (hv : Continuous (fun t => Bundle.TotalSpace.mk' (Euc 3) (p t) (v t)))
    (hw : Continuous (fun t => Bundle.TotalSpace.mk' (Euc 3) (p t) (w t))) :
    Continuous (fun t => G.extension.inner (p t) (v t) (w t)) := by
  let cg := G.extension.toContinuousRiemannianMetric
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : ThreeSphere → Type _) :=
    ⟨cg.toRiemannianMetric⟩
  exact Continuous.inner_bundle (F := Euc 3) (b := p) hv hw

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
