import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientTangentLine.QuotientProjectionMap

/-! Continuity of the base projection of the tangent quotient total space (Demailly, V §1,
pp.253–254, §11, p.267, (14.1), p.273; Zhang, §2.1, pp.4–5). -/

open Bundle Set
open scoped Manifold ContDiff Topology _root_.Topology Classical

noncomputable section

namespace HolomorphicAnosov

universe u

variable {d : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]

/-- The projection from the tangent quotient total space to the base is continuous for the coinduced
topology (Demailly, V §1, pp.253–254, §11, p.267, (14.1), p.273). -/
theorem continuous_quotient_base
    (P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)) :
    Continuous (π ℂ (HolomorphicQuotientTangentLine P)) := by
  apply (quotient_projection_quotient_map P).continuous_iff.mpr
  exact FiberBundle.continuous_proj (ComplexModel d) (TangentSpace (complexModel d))


end HolomorphicAnosov
