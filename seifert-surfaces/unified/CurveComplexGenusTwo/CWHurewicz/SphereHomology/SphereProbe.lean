import CurveComplexGenusTwo.CWHurewicz.CubeSphereGeometry
import CurveComplexGenusTwo.CWHurewicz.SingularRepresentation
import CurveComplexGenusTwo.CWHurewicz.HomotopyHomologyIso
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Analysis.Convex.Contractible
import CurveComplexGenusTwo.CWHurewicz.SphereHomology.SphereBaseStatements
import CurveComplexGenusTwo.CWHurewicz.CWSphereNormBridge

noncomputable section
open CategoryTheory CategoryTheory.Limits Topology Set AlgebraicTopology
open scoped unitInterval
namespace CurveComplexGenusTwo.CWHurewicz.SphereProbe

private def puncturedChart (n : ℕ) (v : SphereSpace n) :
    ↥({v}ᶜ : Set (SphereSpace n)) ≃ₜ EuclideanSpace ℝ (Fin n) := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1))) = n+1) := ⟨by simp⟩
  exact (Homeomorph.setCongr (stereographic'_source v).symm).trans
    ((stereographic' n v).toHomeomorphSourceTarget.trans
      ((Homeomorph.setCongr (stereographic'_target v)).trans (Homeomorph.Set.univ _)))

private theorem puncturedChart_antipode (n : ℕ) (v : SphereSpace n) :
    puncturedChart n v ⟨-v, by simpa using (ne_neg_of_mem_unit_sphere ℝ v).symm⟩ = 0 := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1))) = n+1) := ⟨by simp⟩
  change (stereographic' n v) (-v) = 0
  simp [stereographic', stereographic_apply_neg]

private theorem punctured_contractible (n : ℕ) (v : SphereSpace n) :
    ContractibleSpace ↥({v}ᶜ : Set (SphereSpace n)) :=
  (puncturedChart n v).contractibleSpace

private def overlapChart (n : ℕ) (v : SphereSpace n) :
    ↥(({v}ᶜ : Set (SphereSpace n)) ∩ {-v}ᶜ) ≃ₜ
      ↥({(0 : EuclideanSpace ℝ (Fin n))}ᶜ : Set (EuclideanSpace ℝ (Fin n))) where
  toFun x := ⟨puncturedChart n v ⟨x.val, x.property.1⟩, by
    change puncturedChart n v ⟨x.val, x.property.1⟩ ≠ 0
    rw [← puncturedChart_antipode n v]
    intro h
    have hh := congrArg Subtype.val ((puncturedChart n v).injective h)
    exact x.property.2 hh⟩
  invFun y := ⟨((puncturedChart n v).symm y.val).val,
    ((puncturedChart n v).symm y.val).property, by
    change ((puncturedChart n v).symm y.val).val ≠ -v
    intro h
    apply y.property
    have hh : (puncturedChart n v).symm y.val =
        ⟨-v, by simpa using (ne_neg_of_mem_unit_sphere ℝ v).symm⟩ := Subtype.ext h
    have := congrArg (puncturedChart n v) hh
    simpa [puncturedChart_antipode] using this⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv y := by apply Subtype.ext; simp
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (puncturedChart n v).continuous.comp (continuous_subtype_val.subtype_mk _)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp ((puncturedChart n v).symm.continuous.comp continuous_subtype_val)

private theorem antipodal_open_cover (n : ℕ) (v : SphereSpace n) :
    ({v}ᶜ : Set (SphereSpace n)) ∪ {-v}ᶜ = univ := by
  ext x
  simp only [mem_union, mem_compl_iff, mem_singleton_iff, mem_univ, iff_true]
  by_cases h : x = v
  · right
    subst x
    exact ne_neg_of_mem_unit_sphere ℝ v
  · exact Or.inl h

section Radial
variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
private abbrev Punctured := ↥({(0 : E)}ᶜ : Set E)
private abbrev UnitSphere := ↥(Metric.sphere (0 : E) 1)

private def normalizeMap (x : Punctured E) : UnitSphere E :=
  ⟨NormedSpace.normalize x.val, by
    simpa [Metric.mem_sphere, dist_zero_right] using NormedSpace.norm_normalize x.property⟩
private def sphereIncl (x : UnitSphere E) : Punctured E :=
  ⟨x.val, ne_zero_of_mem_unit_sphere x⟩
private theorem normalize_continuous : Continuous (normalizeMap E) := by
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.norm.inv₀ (fun x => norm_ne_zero_iff.mpr x.property)).smul
    continuous_subtype_val
private theorem sphereIncl_continuous : Continuous (sphereIncl E) := continuous_subtype_val.subtype_mk _
private theorem normalize_incl (x : UnitSphere E) : normalizeMap E (sphereIncl E x) = x := by
  apply Subtype.ext
  exact NormedSpace.normalize_eq_self_of_norm_eq_one (norm_eq_of_mem_sphere x)

private def scale (t : I) (x : Punctured E) : ℝ := 1 - (t : ℝ) + (t : ℝ) * ‖x.val‖⁻¹
private theorem scale_pos (t : I) (x : Punctured E) : 0 < scale E t x := by
  have hq : 0 < ‖x.val‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr x.property)
  have ht0 := t.property.1
  have ht1 := t.property.2
  dsimp [scale]
  by_cases h : (t : ℝ) = 0
  · simp [h]
  · have hm := mul_pos (lt_of_le_of_ne ht0 (Ne.symm h)) hq
    linarith
private def deform (p : I × Punctured E) : Punctured E :=
  ⟨scale E p.1 p.2 • p.2.val, smul_ne_zero (ne_of_gt (scale_pos E p.1 p.2)) p.2.property⟩
private theorem deform_continuous : Continuous (deform E) := by
  apply Continuous.subtype_mk
  have ht : Continuous fun p : I × Punctured E => (p.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have hx : Continuous fun p : I × Punctured E => p.2.val :=
    continuous_subtype_val.comp continuous_snd
  exact ((continuous_const.sub ht).add (ht.mul (hx.norm.inv₀
    (fun p => norm_ne_zero_iff.mpr p.2.property)))).smul hx
private def radialHomotopy : ContinuousMap.Homotopy (ContinuousMap.id (Punctured E))
    ((⟨sphereIncl E, sphereIncl_continuous E⟩ : C(UnitSphere E, Punctured E)).comp
      ⟨normalizeMap E, normalize_continuous E⟩) where
  toFun := deform E
  continuous_toFun := deform_continuous E
  map_zero_left := by intro x; apply Subtype.ext; simp [deform, scale]
  map_one_left := by intro x; apply Subtype.ext; simp [deform, scale, normalizeMap, sphereIncl, NormedSpace.normalize]
private def radialHomologyIso (k : ℕ) : H (Punctured E) k ≅ H (UnitSphere E) k := by
  let r : C(Punctured E, UnitSphere E) := ⟨normalizeMap E, normalize_continuous E⟩
  let i : C(UnitSphere E, Punctured E) := ⟨sphereIncl E, sphereIncl_continuous E⟩
  have hri : r.comp i = ContinuousMap.id (UnitSphere E) := by ext x; exact congrArg Subtype.val (normalize_incl E x)
  exact singularHomologyIsoOfHomotopyInverse (ModuleCat.of ℤ ℤ) k r i
    ⟨(radialHomotopy E).symm⟩ (hri ▸ ⟨ContinuousMap.Homotopy.refl _⟩)
end Radial

private abbrev HF (k : ℕ) := (singularHomologyFunctor (ModuleCat.{0} ℤ) k).obj (ModuleCat.of ℤ ℤ)
private def homeoHomologyIso {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (k : ℕ) : H X k ≅ H Y k := (HF k).mapIso (TopCat.isoOfHomeo e)
private theorem contractible_homology_zero (X : Type) [TopologicalSpace X]
    [ContractibleSpace X] (k : ℕ) (hk : 0 < k) : IsZero (H X k) := by
  let e := (ContractibleSpace.hequiv_unit X).some
  let h := singularHomologyIsoOfHomotopyInverse (ModuleCat.of ℤ ℤ) k
    e.toFun e.invFun e.left_inv e.right_inv
  exact (isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    (ModuleCat.{0} ℤ) k (ModuleCat.of ℤ ℤ) (TopCat.of Unit) (by omega)).of_iso h

private theorem mvConnecting_isIso (X : TopCat) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hc : U ∪ V = univ)
    [ContractibleSpace U] [ContractibleSpace V] (k : ℕ) (hk : 0 < k) :
    IsIso (actualMVConnecting X U V hU hV hc k) := by
  have zU := contractible_homology_zero U k hk
  have zV := contractible_homology_zero V k hk
  have zU' := contractible_homology_zero U (k+1) (by omega)
  have zV' := contractible_homology_zero V (k+1) (by omega)
  letI := ModuleCat.subsingleton_of_isZero zU
  letI := ModuleCat.subsingleton_of_isZero zV
  letI := ModuleCat.subsingleton_of_isZero zU'
  letI := ModuleCat.subsingleton_of_isZero zV'
  have he := (ShortComplex.moduleCat_exact_iff _).mp (actualMV_exact_intersection X U V hU hV hc k)
  have ha := (ShortComplex.moduleCat_exact_iff _).mp (actualMV_exact_ambient X U V hU hV hc k)
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · apply (injective_iff_map_eq_zero (actualMVConnecting X U V hU hV hc k).hom).mpr
    intro x hx
    obtain ⟨y, hy⟩ := ha x hx
    have hy0 : y = 0 := Subsingleton.elim _ _
    simpa [hy0] using hy.symm
  · intro y
    exact he y (Subsingleton.elim _ _)

private def sphereSuspensionIso (n k : ℕ) (hk : 0 < k) (v : SphereSpace (n+1)) :
    H (SphereSpace (n+1)) (k+1) ≅ H (SphereSpace n) k := by
  let X := TopCat.of (SphereSpace (n+1))
  let U : Set X := {v}ᶜ
  let V : Set X := {-v}ᶜ
  let hU : IsOpen U := isClosed_singleton.isOpen_compl
  let hV : IsOpen V := isClosed_singleton.isOpen_compl
  let hc : U ∪ V = univ := antipodal_open_cover (n+1) v
  letI : ContractibleSpace U := punctured_contractible (n+1) v
  letI : ContractibleSpace V := punctured_contractible (n+1) (-v)
  letI := mvConnecting_isIso X U V hU hV hc k hk
  exact asIso (actualMVConnecting X U V hU hV hc k) ≪≫
    homeoHomologyIso (overlapChart (n+1) v) k ≪≫
    radialHomologyIso (EuclideanSpace ℝ (Fin (n+1))) k

private def sphereOneCircleHomeomorph : SphereSpace 1 ≃ₜ Circle :=
  Complex.orthonormalBasisOneI.repr.symm.toHomeomorph.subtype (fun x => by
    have hn := Complex.orthonormalBasisOneI.repr.symm.norm_map x
    constructor <;> intro h
    · have hx : ‖x‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using h
      simpa [Submonoid.unitSphere] using hn.trans hx
    · have hx : ‖(Complex.orthonormalBasisOneI.repr.symm x)‖ = 1 := by
        simpa [Submonoid.unitSphere] using h
      simpa [Metric.mem_sphere, dist_zero_right] using hn.symm.trans hx)

private def spherePole (n : ℕ) : SphereSpace n :=
  ⟨EuclideanSpace.basisFun (Fin (n+1)) ℝ 0, by
    rw [Metric.mem_sphere, dist_zero_right]
    exact (EuclideanSpace.basisFun (Fin (n+1)) ℝ).orthonormal.1 0⟩

def sphereTopIso :
    (n : ℕ) → H (SphereSpace (n + 1)) (n + 1) ≅ ModuleCat.of ℤ ℤ := fun
  | 0 => homeoHomologyIso sphereOneCircleHomeomorph 1 ≪≫ CircleHomologyComputation.circleH1Iso
  | n+1 => sphereSuspensionIso (n+1) (n+1) (by omega) (spherePole (n+2)) ≪≫ sphereTopIso n

def cubeSphereTopIso (n : ℕ) (hn : 0 < n) : H (CubeSphere n) n ≅ ModuleCat.of ℤ ℤ := by
  cases n with
  | zero => omega
  | succ k => exact homeoHomologyIso (cubeSphereHomeomorphic (k+1) (by omega)).some (k+1) ≪≫ sphereTopIso k

def sphereFundamentalClass (n : ℕ) :
    H (SphereSpace (n + 1)) (n + 1) :=
  (sphereTopIso n).inv 1
theorem sphereFundamentalClass_generates (n : ℕ)
    (x : H (SphereSpace (n + 1)) (n + 1)) :
    ∃ a : ℤ, a • sphereFundamentalClass n = x := by
  refine ⟨(sphereTopIso n).hom x, ?_⟩
  have hi : Function.Injective (sphereTopIso n).hom :=
    (ModuleCat.mono_iff_injective _).mp (inferInstance : Mono (sphereTopIso n).hom)
  apply hi
  change (sphereTopIso n).hom ( _ • (sphereTopIso n).inv 1) = (sphereTopIso n).hom x
  simp [sphereFundamentalClass]
theorem sphereFundamentalClass_ne_zero (n : ℕ) : sphereFundamentalClass n ≠ 0 := by
  intro h
  have hh := congrArg (fun x => (sphereTopIso n).hom x) h
  simpa [sphereFundamentalClass] using hh

def sphereSpaceCellSphereHomeomorph (n : ℕ) :
    CellSphere (n + 1) ≃ₜ SphereSpace n :=
  cellSphereEuclideanHomeomorph (n + 1)

def cellSphereTopIso (n : ℕ) :
    H (CellSphere (n + 2)) (n + 1) ≅ ModuleCat.of ℤ ℤ :=
  ((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 1)).obj
    (ModuleCat.of ℤ ℤ)).mapIso
      (TopCat.isoOfHomeo (sphereSpaceCellSphereHomeomorph (n + 1))) ≪≫ sphereTopIso n

def cellSphereFundamentalClass (n : ℕ) :
    H (CellSphere (n + 2)) (n + 1) :=
  (cellSphereTopIso n).inv 1

theorem cellSphereFundamentalClass_generates (n : ℕ)
    (x : H (CellSphere (n + 2)) (n + 1)) :
    ∃ a : ℤ, a • cellSphereFundamentalClass n = x := by
  refine ⟨(cellSphereTopIso n).hom x, ?_⟩
  have hi : Function.Injective (cellSphereTopIso n).hom :=
    (ModuleCat.mono_iff_injective _).mp (inferInstance : Mono (cellSphereTopIso n).hom)
  apply hi
  change (cellSphereTopIso n).hom (_ • (cellSphereTopIso n).inv 1) =
    (cellSphereTopIso n).hom x
  simp [cellSphereFundamentalClass]

theorem cellSphereFundamentalClass_ne_zero (n : ℕ) :
    cellSphereFundamentalClass n ≠ 0 := by
  intro h
  have hh := congrArg (fun x => (cellSphereTopIso n).hom x) h
  simpa [cellSphereFundamentalClass] using hh
end CurveComplexGenusTwo.CWHurewicz.SphereProbe
