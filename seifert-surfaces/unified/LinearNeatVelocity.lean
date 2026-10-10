import NeatBoundaryLinear
import HalfspaceVelocityExtension

open scoped Manifold ContDiff
open Set Topology

namespace SeifertSurfaces.Foundations.AmbientNeatTransport
noncomputable section

def linearHalfspaceRetraction (R : Euc 3 →L[ℝ] Euc 2) (a : ℝ) (ha : 0 < a)
    (hRn : ∀ z, R z 0 = z 0 / a) : EuclideanHalfSpace 3 → EuclideanHalfSpace 2 :=
  fun z => (𝓡∂ 2).symm (R ((𝓡∂ 3) z))

theorem linearHalfspaceRetraction_read (R : Euc 3 →L[ℝ] Euc 2) (a : ℝ) (ha : 0 < a)
    (hRn : ∀ z, R z 0 = z 0 / a) (z : EuclideanHalfSpace 3) :
    (𝓡∂ 2) (linearHalfspaceRetraction R a ha hRn z) = R ((𝓡∂ 3) z) := by
  apply (𝓡∂ 2).right_inv
  rw [range_modelWithCornersEuclideanHalfSpace]
  change 0 ≤ R ((𝓡∂ 3) z) 0
  rw [hRn]
  exact div_nonneg z.property ha.le

theorem linearHalfspaceRetraction_contMDiff (R : Euc 3 →L[ℝ] Euc 2) (a : ℝ) (ha : 0 < a)
    (hRn : ∀ z, R z 0 = z 0 / a) :
    ContMDiff (𝓡∂ 3) (𝓡∂ 2) ∞ (linearHalfspaceRetraction R a ha hRn) := by
  apply (𝓡∂ 2).contMDiffOn_symm.comp_contMDiff (R.contMDiff.comp (𝓡∂ 3).contMDiff)
  intro z
  rw [range_modelWithCornersEuclideanHalfSpace]
  change 0 ≤ R ((𝓡∂ 3) z) 0
  rw [hRn]
  exact div_nonneg z.property ha.le

theorem linearHalfspaceRetraction_boundary (R : Euc 3 →L[ℝ] Euc 2) (a : ℝ) (ha : 0 < a)
    (hRn : ∀ z, R z 0 = z 0 / a) (z : EuclideanHalfSpace 3)
    (hz : (𝓡∂ 3) z 0 = 0) :
    (𝓡∂ 2) (linearHalfspaceRetraction R a ha hRn z) 0 = 0 := by
  rw [linearHalfspaceRetraction_read, hRn, hz, zero_div]

/-- In a linear neat model, the boundary-compatible retraction actually
constructs a smooth Euclidean velocity extension with tangency. -/
theorem linear_neat_velocity_extension
    (A : Euc 2 →L[ℝ] Euc 3) (R : Euc 3 →L[ℝ] Euc 2) (a : ℝ) (ha : 0 < a)
    (hAR : Function.LeftInverse R A) (hAn : ∀ w, A w 0 = a * w 0)
    (hRn : ∀ z, R z 0 = z 0 / a)
    (g : ℝ × EuclideanHalfSpace 2 → Euc 3)
    (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ 2)) 𝓘(ℝ, Euc 3) ∞ g)
    (hgb : ∀ t w, (𝓡∂ 2) w 0 = 0 → g (t,w) 0 = 0) :
    ∃ X : ℝ × Euc 3 → Euc 3, ContDiff ℝ ∞ X ∧
      (∀ t w, X (t,A ((𝓡∂ 2) w)) = g (t,w)) ∧
      ∀ t z, z 0 = 0 → X (t,z) 0 = 0 := by
  let r := linearHalfspaceRetraction R a ha hRn
  let G : ℝ × EuclideanHalfSpace 3 → Euc 3 := fun p => g (p.1,r p.2)
  have hG : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ 3)) 𝓘(ℝ, Euc 3) ∞ G :=
    hg.comp (contMDiff_fst.prodMk ((linearHalfspaceRetraction_contMDiff R a ha hRn).comp
      contMDiff_snd))
  have hGb : ∀ t z, (𝓡∂ 3) z 0 = 0 → G (t,z) 0 = 0 := by
    intro t z hz
    exact hgb t (r z) (linearHalfspaceRetraction_boundary R a ha hRn z hz)
  obtain ⟨X,hX,hXe,hXb⟩ := exists_contDiff_boundary_velocity_extension G hG hGb
  refine ⟨X,hX,?_,hXb⟩
  intro t w
  have hAw : A ((𝓡∂ 2) w) ∈ range (𝓡∂ 3) := by
    rw [range_modelWithCornersEuclideanHalfSpace]
    change 0 ≤ A ((𝓡∂ 2) w) 0
    rw [hAn]
    exact mul_nonneg ha.le w.property
  let z : EuclideanHalfSpace 3 := (𝓡∂ 3).symm (A ((𝓡∂ 2) w))
  have hz : (𝓡∂ 3) z = A ((𝓡∂ 2) w) := (𝓡∂ 3).right_inv hAw
  have hr : r z = w := by
    apply (𝓡∂ 2).injective
    rw [linearHalfspaceRetraction_read, hz, hAR]
  rw [← hz, hXe]
  change g (t,r z) = g (t,w)
  rw [hr]

end
end SeifertSurfaces.Foundations.AmbientNeatTransport
