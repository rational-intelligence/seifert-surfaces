import CurveComplexGenusTwo.CWHurewicz.HomotopyHomologyIso
import CurveComplexGenusTwo.CWHurewicz.SphereHomology.SphereBaseCircleFundamentalCycle
import Mathlib.Analysis.Normed.Module.Normalize
open CategoryTheory CategoryTheory.Limits
open CurveComplexGenusTwo.CWHurewicz
open scoped unitInterval
noncomputable section
namespace ReflectionRadial
section Radial
variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
abbrev Punctured := ↥({(0 : E)}ᶜ : Set E)
abbrev UnitSphere := ↥(Metric.sphere (0 : E) 1)

def normalizeMap (x : Punctured E) : UnitSphere E :=
  ⟨NormedSpace.normalize x.val, by
    simpa [Metric.mem_sphere, dist_zero_right] using NormedSpace.norm_normalize x.property⟩
def sphereIncl (x : UnitSphere E) : Punctured E :=
  ⟨x.val, ne_zero_of_mem_unit_sphere x⟩
theorem normalize_continuous : Continuous (normalizeMap E) := by
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.norm.inv₀ (fun x => norm_ne_zero_iff.mpr x.property)).smul
    continuous_subtype_val
theorem sphereIncl_continuous : Continuous (sphereIncl E) := continuous_subtype_val.subtype_mk _
theorem normalize_incl (x : UnitSphere E) : normalizeMap E (sphereIncl E x) = x := by
  apply Subtype.ext
  exact NormedSpace.normalize_eq_self_of_norm_eq_one (norm_eq_of_mem_sphere x)

def scale (t : I) (x : Punctured E) : ℝ := 1 - (t : ℝ) + (t : ℝ) * ‖x.val‖⁻¹
theorem scale_pos (t : I) (x : Punctured E) : 0 < scale E t x := by
  have hq : 0 < ‖x.val‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr x.property)
  have ht0 := t.property.1
  have ht1 := t.property.2
  dsimp [scale]
  by_cases h : (t : ℝ) = 0
  · simp [h]
  · have hm := mul_pos (lt_of_le_of_ne ht0 (Ne.symm h)) hq
    linarith
def deform (p : I × Punctured E) : Punctured E :=
  ⟨scale E p.1 p.2 • p.2.val, smul_ne_zero (ne_of_gt (scale_pos E p.1 p.2)) p.2.property⟩
theorem deform_continuous : Continuous (deform E) := by
  apply Continuous.subtype_mk
  have ht : Continuous fun p : I × Punctured E => (p.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have hx : Continuous fun p : I × Punctured E => p.2.val :=
    continuous_subtype_val.comp continuous_snd
  exact ((continuous_const.sub ht).add (ht.mul (hx.norm.inv₀
    (fun p => norm_ne_zero_iff.mpr p.2.property)))).smul hx
def radialHomotopy : ContinuousMap.Homotopy (ContinuousMap.id (Punctured E))
    ((⟨sphereIncl E, sphereIncl_continuous E⟩ : C(UnitSphere E, Punctured E)).comp
      ⟨normalizeMap E, normalize_continuous E⟩) where
  toFun := deform E
  continuous_toFun := deform_continuous E
  map_zero_left := by intro x; apply Subtype.ext; simp [deform, scale]
  map_one_left := by intro x; apply Subtype.ext; simp [deform, scale, normalizeMap, sphereIncl, NormedSpace.normalize]
def radialHomologyIso (k : ℕ) : H (Punctured E) k ≅ H (UnitSphere E) k := by
  let r : C(Punctured E, UnitSphere E) := ⟨normalizeMap E, normalize_continuous E⟩
  let i : C(UnitSphere E, Punctured E) := ⟨sphereIncl E, sphereIncl_continuous E⟩
  have hri : r.comp i = ContinuousMap.id (UnitSphere E) := by ext x; exact congrArg Subtype.val (normalize_incl E x)
  exact singularHomologyIsoOfHomotopyInverse (ModuleCat.of ℤ ℤ) k r i
    ⟨(radialHomotopy E).symm⟩ (hri ▸ ⟨ContinuousMap.Homotopy.refl _⟩)
end Radial
abbrev PPlane := ↥({((0,0) : ℝ × ℝ)}ᶜ : Set (ℝ × ℝ))
def complexPlane : Punctured ℂ ≃ₜ PPlane :=
  Complex.equivRealProdCLM.toHomeomorph.subtype (by
    intro z
    change z ≠ 0 ↔ (z.re,z.im) ≠ (0,0)
    simp only [ne_eq,Prod.mk.injEq,Complex.ext_iff,Complex.zero_re,Complex.zero_im])

def circleInclusion : C(Circle,Punctured ℂ) := ⟨sphereIncl ℂ, sphereIncl_continuous ℂ⟩
def circleRetraction : C(Punctured ℂ,Circle) := ⟨normalizeMap ℂ,normalize_continuous ℂ⟩
def circlePuncturedIso (k : ℕ) : H (Punctured ℂ) k ≅ H Circle k := radialHomologyIso ℂ k

end ReflectionRadial
