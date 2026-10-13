import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientTangentLine.ContinuousForward
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientTangentLine.ContinuousInverse
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientTangentLine.ContinuousQuotientBase

/-! Topological trivializations of the tangent quotient for its coinduced topology (Demailly, V §1,
pp.253–254, §11, p.267, (14.1), p.273; Zhang, §2.1, pp.4–5). -/

open Bundle Set
open scoped Manifold ContDiff Topology _root_.Topology Classical

noncomputable section

namespace HolomorphicAnosov

universe u

variable {d : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]

/-- The local quotient trivialization is a homeomorphism for the coinduced total-space topology. -/
def QuotientLocalData.trivialization
    {P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)}
    (D : QuotientLocalData P) : Trivialization ℂ (π ℂ (HolomorphicQuotientTangentLine P)) :=
  { D.pretrivialization with
    open_source := D.V.isOpen.preimage (continuous_quotient_base P)
    continuousOn_toFun := D.continuousOn_forward
    continuousOn_invFun := D.continuousOn_inverse }


end HolomorphicAnosov
