import ExternalTransportContracts
import BoundaryFoliation

set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff
open Set Topology
namespace SeifertSurfaces.LongitudeProducers
open Foundations MetricFoundations
universe u
noncomputable section

/-- A1: explicit vector-space/model-space normalization; no definitional
identification of ModelProd with the two-dimensional Euclidean model. -/
def torusLinearModel : (Euc 1 × Euc 1) ≃L[ℝ] Euc 2 :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)).symm

def torusModelHomeomorph : ModelProd (Euc 1) (Euc 1) ≃ₜ Euc 2 :=
  TorusModel.toHomeomorph.trans torusLinearModel.toHomeomorph

theorem torus_model_compatibility (y : ModelProd (Euc 1) (Euc 1)) :
    (𝓡 2) (torusModelHomeomorph y) = torusLinearModel (TorusModel y) := by
  rfl

def NormalizedTorus : Type := Circle × Circle
instance : TopologicalSpace NormalizedTorus :=
  inferInstanceAs (TopologicalSpace (Circle × Circle))

def normalizedTorusAtlas : ChartedSpace (Euc 2) NormalizedTorus :=
  letI : ChartedSpace (ModelProd (Euc 1) (Euc 1)) NormalizedTorus :=
    inferInstanceAs (ChartedSpace (ModelProd (Euc 1) (Euc 1)) (Circle × Circle))
  Transport.modelChangedAtlas torusModelHomeomorph

instance : ChartedSpace (Euc 2) NormalizedTorus := normalizedTorusAtlas

def normalizeTorus : Circle × Circle → NormalizedTorus := id
def unnormalizeTorus : NormalizedTorus → Circle × Circle := id

theorem normalized_torus_analytic : IsManifold (𝓡 2) ω NormalizedTorus := by
  exact Transport.modelChangedAtlas_analytic (X := Circle × Circle) TorusModel (𝓡 2)
    torusModelHomeomorph torusLinearModel torus_model_compatibility

theorem normalized_torus_forward_analytic :
    ContMDiff TorusModel (𝓡 2) ω normalizeTorus := by
  exact (Transport.modelChangedAtlas_contMDiff_iff TorusModel (𝓡 2)
    torusModelHomeomorph torusLinearModel torus_model_compatibility
    TorusModel ω (id : Circle × Circle → Circle × Circle)).mpr contMDiff_id

theorem normalized_torus_inverse_analytic :
    ContMDiff (𝓡 2) TorusModel ω unnormalizeTorus := by
  have hsource (p : NormalizedTorus) :
      ((extChartAt (𝓡 2) p).symm : Euc 2 → NormalizedTorus) =
        (extChartAt TorusModel (unnormalizeTorus p)).symm ∘ torusLinearModel.symm := by
    funext y
    rw [extChartAt_coe_symm, extChartAt_coe_symm, Function.comp_apply,
      Function.comp_apply]
    change ((chartAt (ModelProd (Euc 1) (Euc 1)) (unnormalizeTorus p)).trans
      torusModelHomeomorph.toOpenPartialHomeomorph).symm ((𝓡 2).symm y) = _
    simp only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_apply]
    rfl
  intro p
  rw [contMDiffAt_iff_source, hsource]
  have hp : extChartAt (𝓡 2) p p =
      torusLinearModel (extChartAt TorusModel (unnormalizeTorus p) (unnormalizeTorus p)) :=
    congrFun (Transport.modelChangedAtlas_extChart (X := Circle × Circle)
      TorusModel (𝓡 2) torusModelHomeomorph torusLinearModel
      torus_model_compatibility (unnormalizeTorus p)) p
  rw [hp]
  have h := (contMDiffWithinAt_extChartAt_symm_range_self
    (I := TorusModel) (n := ω) (unnormalizeTorus p)).contMDiffAt
    (by simp [TorusModel])
  have hg := (torusLinearModel.symm.contDiff (n := ω)).contMDiff.contMDiffAt
    (x := torusLinearModel (extChartAt TorusModel (unnormalizeTorus p) (unnormalizeTorus p)))
  have h' : ContMDiffAt 𝓘(ℝ, Euc 1 × Euc 1) TorusModel ω
      (extChartAt TorusModel (unnormalizeTorus p)).symm
      (torusLinearModel.symm (torusLinearModel
        (extChartAt TorusModel (unnormalizeTorus p) (unnormalizeTorus p)))) := by
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using h
  change ContMDiffWithinAt 𝓘(ℝ, Euc 2) TorusModel ω
    ((extChartAt TorusModel (unnormalizeTorus p)).symm ∘ torusLinearModel.symm)
    (range (𝓡 2))
    (torusLinearModel (extChartAt TorusModel (unnormalizeTorus p) (unnormalizeTorus p)))
  exact (h'.comp (torusLinearModel
    (extChartAt TorusModel (unnormalizeTorus p) (unnormalizeTorus p))) hg).contMDiffWithinAt

theorem normalized_torus_extended_chart (p : Circle × Circle) :
    (extChartAt (𝓡 2) (normalizeTorus p) : NormalizedTorus → Euc 2) =
      fun q => torusLinearModel (extChartAt TorusModel p (unnormalizeTorus q)) := by
  exact Transport.modelChangedAtlas_extChart TorusModel (𝓡 2)
    torusModelHomeomorph torusLinearModel torus_model_compatibility p

/-- The transition formula is asserted on the genuine chart overlap,
with the explicit inverse linear model identification. -/
theorem normalized_torus_transition (p q : Circle × Circle) (y : Euc 2)
    (hy : y ∈ (extChartAt (𝓡 2) (normalizeTorus p)).target)
    (hq : (extChartAt (𝓡 2) (normalizeTorus p)).symm y ∈
      (extChartAt (𝓡 2) (normalizeTorus q)).source) :
    extChartAt (𝓡 2) (normalizeTorus q)
      ((extChartAt (𝓡 2) (normalizeTorus p)).symm y) =
      torusLinearModel (extChartAt TorusModel q
        ((extChartAt TorusModel p).symm (torusLinearModel.symm y))) := by
  have hsymm :
      ((extChartAt (𝓡 2) (normalizeTorus p)).symm y : NormalizedTorus) =
      (extChartAt TorusModel p).symm (torusLinearModel.symm y) := by
    rw [extChartAt_coe_symm, extChartAt_coe_symm, Function.comp_apply]
    change ((chartAt (ModelProd (Euc 1) (Euc 1)) p).trans
      torusModelHomeomorph.toOpenPartialHomeomorph).symm ((𝓡 2).symm y) = _
    simp only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_apply]
    rfl
  rw [normalized_torus_extended_chart, hsymm]
  rfl

variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}

/-- A1: exact boundaryLift, on the genuine boundary subtype with its existing
subspace topology. Existence follows from actual embedding and coverage. -/
theorem boundary_homeomorph_exists (J : LongitudeFoliation.{u} E) :
    ∃ e : (Circle × Circle) ≃ₜ ((𝓡∂ 3).boundary E.Carrier),
      (e : Circle × Circle → ((𝓡∂ 3).boundary E.Carrier)) = J.boundaryLift := by
  have hi : IsEmbedding J.boundaryLift :=
    IsEmbedding.subtypeVal.of_comp_iff.mp J.smoothEmbedding.isEmbedding
  have hs : Function.Surjective J.boundaryLift := by
    intro y
    have hy : (y : E.Carrier) ∈ Set.range J.torus := by
      rw [J.covers_boundary]
      exact y.property
    obtain ⟨p, hp⟩ := hy
    exact ⟨p, Subtype.ext hp⟩
  exact ⟨hi.toHomeomorphOfSurjective hs, rfl⟩

def boundaryHomeomorph (J : LongitudeFoliation.{u} E) :
    (Circle × Circle) ≃ₜ ((𝓡∂ 3).boundary E.Carrier) :=
  Classical.choose (boundary_homeomorph_exists J)

theorem boundaryHomeomorph_map (J : LongitudeFoliation.{u} E) :
    (boundaryHomeomorph J : Circle × Circle → ((𝓡∂ 3).boundary E.Carrier)) =
      J.boundaryLift := by
  exact Classical.choose_spec (boundary_homeomorph_exists J)

def normalizedBoundaryHomeomorph (J : LongitudeFoliation.{u} E) :
    NormalizedTorus ≃ₜ ((𝓡∂ 3).boundary E.Carrier) := boundaryHomeomorph J

def boundaryAnalyticAtlas (J : LongitudeFoliation.{u} E) :
    ChartedSpace (Euc 2) ((𝓡∂ 3).boundary E.Carrier) :=
  (normalizedBoundaryHomeomorph J).chartedSpace

theorem boundary_atlas_analytic (J : LongitudeFoliation.{u} E) :
    @IsManifold ℝ _ _ _ _ _ _ (𝓡 2) ω ((𝓡∂ 3).boundary E.Carrier) _
      (boundaryAnalyticAtlas J) := by
  letI := normalized_torus_analytic
  exact Transport.homeomorph_atlas_manifold (𝓡 2) ω (normalizedBoundaryHomeomorph J)

theorem boundary_atlas_inverse_analytic (J : LongitudeFoliation.{u} E) :
    @ContMDiff ℝ _ _ _ _ _ _ (𝓡 2) ((𝓡∂ 3).boundary E.Carrier) _
      (boundaryAnalyticAtlas J) _ _ _ _ _ (𝓡 2) NormalizedTorus _ _ ω
      (normalizedBoundaryHomeomorph J).symm := by
  letI := normalized_torus_analytic
  exact Transport.homeomorph_atlas_inverse (𝓡 2) ω (normalizedBoundaryHomeomorph J)

theorem boundary_inclusion_factorization (J : LongitudeFoliation.{u} E) :
    (Subtype.val : ((𝓡∂ 3).boundary E.Carrier) → E.Carrier) =
      J.torus ∘ (boundaryHomeomorph J).symm := by
  funext y
  have h := congrFun (boundaryHomeomorph_map J) ((boundaryHomeomorph J).symm y)
  rw [Homeomorph.apply_symm_apply] at h
  exact congrArg Subtype.val h

theorem boundary_atlas_inclusion_smooth (J : LongitudeFoliation.{u} E) :
    @ContMDiff ℝ _ _ _ _ _ _ (𝓡 2) ((𝓡∂ 3).boundary E.Carrier) _
      (boundaryAnalyticAtlas J) _ _ _ _ _ (𝓡∂ 3) E.Carrier _ _ ∞
      (Subtype.val : ((𝓡∂ 3).boundary E.Carrier) → E.Carrier) := by
  letI := boundaryAnalyticAtlas J
  have hnorm := normalized_torus_inverse_analytic.of_le (show ∞ ≤ ω from le_top)
  have hinv := (boundary_atlas_inverse_analytic J).of_le (show ∞ ≤ ω from le_top)
  have h := J.smoothEmbedding.contMDiff.comp (hnorm.comp hinv)
  change ContMDiff (𝓡 2) (𝓡∂ 3) ∞
    (J.torus ∘ ((boundaryHomeomorph J).symm : _ → Circle × Circle)) at h
  rw [← boundary_inclusion_factorization J] at h
  exact h

theorem boundaryLift_analytic (J : LongitudeFoliation.{u} E) :
    @ContMDiff ℝ _ _ _ _ _ _ TorusModel (Circle × Circle) _ _
      _ _ _ _ _ (𝓡 2) ((𝓡∂ 3).boundary E.Carrier) _ (boundaryAnalyticAtlas J) ω
      J.boundaryLift := by
  letI := normalized_torus_analytic
  letI := boundaryAnalyticAtlas J
  have h := (Transport.homeomorph_atlas_forward (𝓡 2) ω
    (normalizedBoundaryHomeomorph J)).comp normalized_torus_forward_analytic
  change ContMDiff TorusModel (𝓡 2) ω ((boundaryHomeomorph J) ∘ id) at h
  simpa only [Function.comp_id, boundaryHomeomorph_map] using h

theorem analytic_boundary_structure_from_foliation (J : LongitudeFoliation.{u} E) :
    ∃ B : AnalyticBoundaryStructure E, B.charted = boundaryAnalyticAtlas J ∧
      @ContMDiff ℝ _ _ _ _ _ _ TorusModel (Circle × Circle) _ _
        _ _ _ _ _ (𝓡 2) ((𝓡∂ 3).boundary E.Carrier) _ B.charted ω J.boundaryLift := by
  exact ⟨⟨boundaryAnalyticAtlas J, boundary_atlas_analytic J,
    boundary_atlas_inclusion_smooth J⟩, rfl, boundaryLift_analytic J⟩

/-- A3 is independent of every Seifert producer: it starts with a supplied
foliation and constructs its intrinsic analytic atlas. -/
theorem every_longitude_foliation_intrinsically_analytic (J : LongitudeFoliation.{u} E) :
    J.IntrinsicallyAnalytic := by
  obtain ⟨B, hB, h⟩ := analytic_boundary_structure_from_foliation J
  exact ⟨B, h⟩

theorem analytic_longitude_from_smooth_existence
    (hs : Nonempty (LongitudeFoliation.{u} E)) :
    ∃ J : LongitudeFoliation.{u} E, J.IntrinsicallyAnalytic := by
  obtain ⟨J⟩ := hs
  exact ⟨J, every_longitude_foliation_intrinsically_analytic J⟩

end
end SeifertSurfaces.LongitudeProducers
