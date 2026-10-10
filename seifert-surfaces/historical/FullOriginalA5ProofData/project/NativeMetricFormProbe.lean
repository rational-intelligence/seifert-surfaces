import MetricConormalAlgebraProbe

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

def actualPieceDifferential
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count) (y : Euc 2) (p : ThreeSphere)
    (heq : pieceSphereCoordinate E F i j y = p) : Euc 2 →L[ℝ] TangentSpace (𝓡 3) p :=
  heq ▸ (mfderivWithin 𝓘(ℝ,Euc 2) (𝓡 3) (pieceSphereCoordinate E F i j)
    ((F.domain i).chart j).map.target y).comp (NormedSpace.fromTangentSpace y).symm.toContinuousLinearMap

theorem actualPieceDifferential_apply
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count) (y v : Euc 2) (p : ThreeSphere)
    (heq : pieceSphereCoordinate E F i j y = p) :
    actualPieceDifferential E F i j y p heq v = actualPieceConormal E F i j y v p heq := by
  subst p
  rfl

def nativePieceMetricForm (G : A7.SourceGeometry E)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count) (y : Euc 2) (p : ThreeSphere)
    (heq : pieceSphereCoordinate E F i j y = p) : Euc 2 →L[ℝ] Euc 2 →L[ℝ] ℝ :=
  let D := actualPieceDifferential E F i j y p heq
  let B : Euc 2 →ₗ[ℝ] Euc 2 →L[ℝ] ℝ := {
    toFun := fun v => (G.extension.inner p (D v)).comp D
    map_add' := by intro v w; ext z; simp
    map_smul' := by intro c v; ext z; simp }
  B.toContinuousLinearMap

theorem nativePieceMetricForm_apply (G : A7.SourceGeometry E)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count) (y v w : Euc 2) (p : ThreeSphere)
    (heq : pieceSphereCoordinate E F i j y = p) :
    nativePieceMetricForm E G F i j y p heq v w =
      G.extension.inner p (actualPieceConormal E F i j y v p heq)
        (actualPieceConormal E F i j y w p heq) := by
  change G.extension.inner p (actualPieceDifferential E F i j y p heq v)
    (actualPieceDifferential E F i j y p heq w) = _
  rw [actualPieceDifferential_apply, actualPieceDifferential_apply]

/-- Original closed-side rank and actual ambient metric positivity give
positive definiteness of the literal native induced metric. -/
theorem native_piece_metric_form_positive (G : A7.SourceGeometry E)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count) (y : Euc 2)
    (hy : y ∈ ((F.domain i).chart j).map.target) (p : ThreeSphere)
    (heq : pieceSphereCoordinate E F i j y = p) :
    ∀ v : Euc 2, v ≠ 0 → 0 < nativePieceMetricForm E G F i j y p heq v v := by
  intro v hv
  rw [nativePieceMetricForm_apply]
  apply G.extension.pos
  subst p
  have hi := (native_piece_sphere_C1_rank E F i j).2 y hy
  have hn : mfderivWithin 𝓘(ℝ,Euc 2) (𝓡 3) (pieceSphereCoordinate E F i j)
      ((F.domain i).chart j).map.target y v ≠ 0 := by
    intro hz
    exact hv (hi (hz.trans (map_zero _).symm))
  exact hn

/-- Every pairing of the actual induced metric varies continuously along
the native clock for continuous coordinate vectors. -/
theorem native_piece_metric_pair_continuous (G : A7.SourceGeometry E)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count)
    {P : Type*} [TopologicalSpace P] (q v w : P → Euc 2) (p : P → ThreeSphere)
    (hq : Continuous q) (hv : Continuous v) (hw : Continuous w)
    (hqm : ∀ t, q t ∈ ((F.domain i).chart j).map.target)
    (heq : ∀ t, pieceSphereCoordinate E F i j (q t) = p t) :
    Continuous (fun t => nativePieceMetricForm E G F i j (q t) (p t) (heq t) (v t) (w t)) := by
  simp_rw [nativePieceMetricForm_apply]
  exact native_metric_pair_continuous E G p _ _
    (native_actual_differential_section_continuous E F i j q v p hq hv hqm heq)
    (native_actual_differential_section_continuous E F i j q w p hq hw hqm heq)

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
