import A5GeometricCornerLift
import CornerModelTransport
import PiecewiseCurveOperations

set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped Manifold ContDiff
open Set Topology WithLp
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.NearbyDeformations
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
universe u v
abbrev CylinderCornerModel := (𝓡∂ 1).prod CornerModel
abbrev PrismModel := modelWithCornersEuclideanQuadrant 3

def cylinderLinearForward (p : Euc 1 × Euc 2) : Euc 3 :=
  toLp 2 ![p.1 0, p.2 0, p.2 1]
def cylinderLinearInverse (y : Euc 3) : Euc 1 × Euc 2 :=
  (toLp 2 (fun _ : Fin 1 => y 0), toLp 2 ![y 1, y 2])

def cylinderLinear : (Euc 1 × Euc 2) ≃L[ℝ] Euc 3 where
  toFun := cylinderLinearForward
  invFun := cylinderLinearInverse
  left_inv := by
    intro x
    apply Prod.ext <;> apply PiLp.ext
    · intro i; fin_cases i; rfl
    · intro i; fin_cases i <;> rfl
  right_inv := by intro x; apply PiLp.ext; intro i; fin_cases i <;> rfl
  map_add' := by intro x y; apply PiLp.ext; intro i; fin_cases i <;> rfl
  map_smul' := by intro a x; apply PiLp.ext; intro i; fin_cases i <;> rfl
  continuous_toFun := by unfold cylinderLinearForward; fun_prop
  continuous_invFun := by unfold cylinderLinearInverse; fun_prop

def cylinderModelForward (p : EuclideanHalfSpace 1 × EuclideanQuadrant 2) :
    EuclideanQuadrant 3 :=
  ⟨cylinderLinearForward (p.1.val, p.2.val), by
    intro i
    fin_cases i
    · exact p.1.property
    · exact p.2.property 0
    · exact p.2.property 1⟩
def cylinderModelInverse (q : EuclideanQuadrant 3) :
    EuclideanHalfSpace 1 × EuclideanQuadrant 2 :=
  (⟨toLp 2 (fun _ : Fin 1 => q.val 0), q.property 0⟩,
    ⟨toLp 2 ![q.val 1, q.val 2], by
      intro i
      fin_cases i
      · exact q.property 1
      · exact q.property 2⟩)

def cylinderModelHomeomorph :
    (EuclideanHalfSpace 1 × EuclideanQuadrant 2) ≃ₜ EuclideanQuadrant 3 where
  toFun := cylinderModelForward
  invFun := cylinderModelInverse
  left_inv := by
    intro x
    apply Prod.ext <;> apply Subtype.ext <;> apply PiLp.ext
    · intro i; fin_cases i; rfl
    · intro i; fin_cases i <;> rfl
  right_inv := by
    intro x; apply Subtype.ext; apply PiLp.ext; intro i; fin_cases i <;> rfl
  continuous_toFun := by unfold cylinderModelForward cylinderLinearForward; fun_prop
  continuous_invFun := by unfold cylinderModelInverse; fun_prop

theorem cylinder_model_compatible (p : EuclideanHalfSpace 1 × EuclideanQuadrant 2) :
    PrismModel (cylinderModelHomeomorph p) = cylinderLinear (CylinderCornerModel p) := rfl

theorem cylinder_model_inverse (y : Euc 3) :
    CylinderCornerModel.symm (cylinderLinear.symm y) =
      cylinderModelHomeomorph.symm (PrismModel.symm y) := by
  apply Prod.ext <;> apply Subtype.ext <;> apply PiLp.ext
  · intro i; fin_cases i
    simp [CylinderCornerModel, PrismModel, cylinderModelHomeomorph, cylinderModelInverse,
      cylinderLinear, cylinderLinearInverse, modelWithCornersEuclideanHalfSpace_symm_apply,
      modelWithCornersEuclideanQuadrant_symm_apply, ModelWithCorners.prod]
    rfl
  · intro i; fin_cases i
    all_goals
      simp [CylinderCornerModel, PrismModel, cylinderModelHomeomorph, cylinderModelInverse,
        cylinderLinear, cylinderLinearInverse, modelWithCornersEuclideanHalfSpace_symm_apply,
        modelWithCornersEuclideanQuadrant_symm_apply, ModelWithCorners.prod]
      rfl

local instance cornerCylinderProductCharted (P : CompactCornerPiece.{u}) :
    ChartedSpace (EuclideanHalfSpace 1 × EuclideanQuadrant 2) (Time × P) :=
  prodChartedSpace (EuclideanHalfSpace 1) Time (EuclideanQuadrant 2) P

@[instance_reducible]
def cornerCylinderCharted (P : CompactCornerPiece.{u}) :
    ChartedSpace (EuclideanQuadrant 3) (Time × P) :=
  chartedSpaceChangeModel cylinderModelHomeomorph

def cornerCylinder (P : CompactCornerPiece.{u}) : CompactCornerPrism.{u} where
  carrier := Time × P
  charted := cornerCylinderCharted P
  smooth := isManifold_changeModel (X := Time × P) CylinderCornerModel PrismModel cylinderModelHomeomorph
    cylinderLinear cylinder_model_compatible cylinder_model_inverse ∞

/-- The literal identity from the changed quadrant model to the product model. -/
theorem cornerCylinder_projection_smooth (P : CompactCornerPiece.{u}) :
    ContMDiff PrismModel CylinderCornerModel ∞ (fun q : cornerCylinder P =>
      ((q : Time × P).1, (q : Time × P).2)) := by
  exact contMDiff_changeModel_source CylinderCornerModel PrismModel CylinderCornerModel
    cylinderModelHomeomorph cylinderLinear cylinder_model_compatible cylinder_model_inverse
    ∞ (id : Time × P → Time × P) contMDiff_id

theorem cornerCylinder_projection_rank (P : CompactCornerPiece.{u})
    (q : cornerCylinder P) :
    Function.Injective (mfderiv PrismModel CylinderCornerModel
      (fun q : cornerCylinder P => ((q : Time × P).1, (q : Time × P).2)) q) := by
  exact mfderiv_injective_changeModel_source CylinderCornerModel PrismModel CylinderCornerModel
    cylinderModelHomeomorph cylinderLinear cylinder_model_compatible cylinder_model_inverse
    (id : Time × P → Time × P) contMDiff_id q (by
      have hr (x : Time × P) : Function.Injective
          (mfderiv CylinderCornerModel CylinderCornerModel (id : Time × P → Time × P) x) := by
        rw [mfderiv_id]
        exact Function.injective_id
      exact hr q)

theorem cornerCylinder_interior (P : CompactCornerPiece.{u})
    (q : cornerCylinder P) (hq : q ∈ PrismModel.interior (cornerCylinder P)) :
    (q : Time × P).2 ∈ CornerModel.interior P := by
  have hd := (cornerCylinder_projection_smooth P).mdifferentiableAt (by simp) (x := q)
  have hr := cornerCylinder_projection_rank P q
  have hdim : Module.finrank ℝ (Euc 3) = Module.finrank ℝ (Euc 1 × Euc 2) := by
    simp [Module.finrank_prod, finrank_euclideanSpace]
  have hs := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hr
  have hi := MDifferentiableAt.isInteriorPoint_of_surjective_mfderiv
    (N := Time × P) hd hs hq
  have hip : (q : Time × P) ∈ CylinderCornerModel.interior (Time × P) := hi
  rw [ModelWithCorners.interior_prod] at hip
  exact hip.2

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.NearbyDeformations
