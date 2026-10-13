import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientTangentLine.LocalData

/-! Scalar transition operators between local tangent quotient coordinates (Demailly, V §1,
pp.253–254, §11, p.267, (14.1), p.273; Zhang, §2.1, pp.4–5). -/

open Bundle Set
open scoped Manifold ContDiff Topology _root_.Topology Classical

noncomputable section

namespace HolomorphicAnosov

universe u

variable {d : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]

/-- The scalar transition operator between two local quotient coordinates is multiplication by `D′.θ
x (D.T x)` (Demailly, V §1, pp.253–254, §11, p.267, (14.1), p.273). -/
def QuotientLocalData.transition
    {P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)}
    (D D' : QuotientLocalData P) (x : X) : ℂ →L[ℂ] ℂ :=
  (ContinuousLinearMap.id ℂ ℂ).smulRight (D'.θ x (D.T x))


end HolomorphicAnosov
