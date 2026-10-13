import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientLineConnection

open Bundle Set _root_.Topology TopologicalSpace
open scoped Manifold ContDiff
attribute [local instance] HolomorphicAnosov.complex_isManifold_real

noncomputable section
namespace HolomorphicAnosov
namespace ConnectionCalculus

universe u
variable {d : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
  [T2Space X] [SecondCountableTopology X] [CompactSpace X]

omit [T2Space X] [SecondCountableTopology X] [CompactSpace X] in
/-- The difference of two quotient-line connection forms is independent of the holomorphic quotient
frame on overlaps. (Zhang, §2.1, (3) and (5)) -/
theorem frame_difference_independent
    {P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)}
    (D D' : QuotientLineConnection.Connection P)
    (V W : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
    (e' : QuotientLineConnection.HolomorphicFrame P W)
    (x : X) (hx : x ∈ V) (hx' : x ∈ W) :
    D'.form V e x - D.form V e x = D'.form W e' x - D.form W e' x := by
  rw [D'.gauge V W e e' x hx hx', D.gauge V W e e' x hx hx']
  abel



end ConnectionCalculus
end HolomorphicAnosov
