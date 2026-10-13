import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientTangentLine.Pretrivialization

/-! Complex linearity of local tangent quotient pretrivializations (Demailly, V §1, pp.253–254, §11,
p.267, (14.1), p.273; Zhang, §2.1, pp.4–5). -/

open Bundle Set
open scoped Manifold ContDiff Topology _root_.Topology Classical

noncomputable section

namespace HolomorphicAnosov

universe u

variable {d : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]

/-- The quotient pretrivialization is fibrewise complex linear on its base domain (Demailly, V §1,
pp.253–254, §11, p.267, (14.1), p.273). -/
instance QuotientLocalData.pretrivialization_linear
    {P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)}
    (D : QuotientLocalData P) : D.pretrivialization.IsLinear ℂ where
  linear := by
    intro x hx
    change x ∈ D.V at hx
    change IsLinearMap ℂ (fun v ↦ if h : x ∈ D.V then D.L x h v else 0)
    simp only [dite_eq_left hx]
    exact (D.L x hx).toLinearEquiv.isLinear


end HolomorphicAnosov
