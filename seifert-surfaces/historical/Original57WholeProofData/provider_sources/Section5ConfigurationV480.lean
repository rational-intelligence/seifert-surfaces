import Section5GeometricDefinitions

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology Function
open scoped Manifold ContDiff

namespace SeifertSurfaces.OriginalEndpoints.Section5.WholeAssemblyV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.GenusLinking SeifertSurfaces.Complexity
open SeifertSurfaces.OriginalEndpoints.Section4
open SeifertSurfaces.AppendixACoordinates

private theorem planes_equal_of_nontransverse {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (hd : Module.finrank ℝ V = 3)
    (P Q : Submodule ℝ V) (hP : Module.finrank ℝ P = 2) (hQ : Module.finrank ℝ Q = 2)
    (h : P ⊔ Q ≠ ⊤) : P = Q := by
  have hupper : Module.finrank ℝ ↥(P ⊔ Q) < 3 := by
    simpa only [hd] using Submodule.finrank_lt h
  have hlower : Module.finrank ℝ P ≤ Module.finrank ℝ ↥(P ⊔ Q) :=
    Submodule.finrank_mono le_sup_left
  have heq : Module.finrank ℝ ↥(P ⊔ Q) = 2 := by omega
  have h1 : P = P ⊔ Q := Submodule.eq_of_le_of_finrank_eq le_sup_left (hP.trans heq.symm)
  have h2 : Q = P ⊔ Q := Submodule.eq_of_le_of_finrank_eq le_sup_right (hQ.trans heq.symm)
  exact h1.trans h2.symm

variable {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)

private theorem tangentPlane_finrank (A : IncompressibleSpanningSurface.{0} E)
    (a : A.1.surface) (p : E.Carrier) (ha : A.1.embedding.toFun a = p) :
    Module.finrank ℝ (AppendixBOriginalV479.tangentPlaneAt A.1.embedding a p ha) = 2 := by
  subst p
  have hr := LinearMap.finrank_range_of_inj
    (A.1.embedding.smoothEmbedding.isImmersion.mfderiv_injective (by norm_num) a)
  exact hr.trans (finrank_euclideanSpace_fin (𝕜 := ℝ))

/-- Distinct longitude leaves are disjoint by the actual embedded torus parameter. -/
theorem leaf_boundary_dichotomy (H : SourceGeometry E)
    (A B : IncompressibleSpanningSurface.{0} E)
    (hA : H.foliation.BoundaryIn A.1.embedding.toFun)
    (hB : H.foliation.BoundaryIn B.1.embedding.toFun) :
    Disjoint (SurfaceBoundary E A) (SurfaceBoundary E B) ∨
      SurfaceBoundary E A = SurfaceBoundary E B := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  by_cases heq : a = b
  · exact Or.inr (ha.trans (heq ▸ hb.symm))
  · left
    rw [SurfaceBoundary, SurfaceBoundary, ha, hb]
    apply Set.disjoint_left.mpr
    rintro p ⟨x, hx⟩ ⟨y, hy⟩
    exact heq (congrArg Prod.fst (H.foliation.smoothEmbedding.isEmbedding.injective
      (hx.trans hy.symm)))

/-- Failure of transversality with disjoint boundary occurs at an actual
interior tangency, using the two-dimensional native tangent planes. -/
theorem nontansverse_has_interior_tangency
    (A B : IncompressibleSpanningSurface.{0} E)
    (hboundary : Disjoint (SurfaceBoundary E A) (SurfaceBoundary E B))
    (htransverse : ¬ AppendixBOriginalV479.Transverse A.1.embedding B.1.embedding) :
    (AppendixBOriginalV479.interiorTangencies A.1.embedding B.1.embedding).Nonempty := by
  classical
  simp only [AppendixBOriginalV479.Transverse, not_forall] at htransverse
  obtain ⟨a, b, hab, hplanes⟩ := htransverse
  let p := B.1.embedding.toFun b
  have ha : A.1.embedding.toFun a = p := hab
  have hp : p ∈ (𝓡∂ 3).interior E.Carrier := by
    rw [← (𝓡∂ 3).compl_boundary]
    intro hpb
    have hAb : p ∈ SurfaceBoundary E A := by
      exact ⟨a, by rw [← A.1.embedding.boundary_preimage]; change A.1.embedding.toFun a ∈ (𝓡∂ 3).boundary E.Carrier; rw [ha]; exact hpb, ha⟩
    have hBb : p ∈ SurfaceBoundary E B := by
      exact ⟨b, by rw [← B.1.embedding.boundary_preimage]; exact hpb, rfl⟩
    exact Set.disjoint_left.mp hboundary hAb hBb
  refine ⟨p, hp, a, b, ha, rfl, ?_⟩
  apply planes_equal_of_nontransverse
  · change Module.finrank ℝ E3 = 3
    simp
  · exact tangentPlane_finrank E A a p ha
  · exact tangentPlane_finrank E B b p rfl
  · exact hplanes

end SeifertSurfaces.OriginalEndpoints.Section5.WholeAssemblyV480
