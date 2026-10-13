import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientTangentLine.Trivialization
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientTangentLine.PretrivializationLinear

/-! Complex linearity of local tangent quotient trivializations (Demailly, V §1, pp.253–254, §11,
p.267, (14.1), p.273; Zhang, §2.1, pp.4–5). -/

open Bundle Set
open scoped Manifold ContDiff Topology _root_.Topology Classical

noncomputable section

namespace HolomorphicAnosov

universe u

variable {d : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]

/-- The local quotient trivialization is fibrewise complex linear (Demailly, V §1, pp.253–254, §11,
p.267, (14.1), p.273). -/
instance QuotientLocalData.trivialization_linear
    {P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)}
    (D : QuotientLocalData P) : D.trivialization.IsLinear ℂ where
  linear := by
    intro x hx
    change IsLinearMap ℂ (fun v => (D.pretrivialization ⟨x, v⟩).2)
    exact D.pretrivialization.linear ℂ hx


end HolomorphicAnosov
