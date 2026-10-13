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
/-- Zhang Definition2.1, C8: the difference of two compatible forms is (1,0). -/
theorem compatible_difference_complex_linear
    {P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)}
    (D D' : QuotientLineConnection.Connection P)
    (hD : QuotientLineConnection.IsCompatible D)
    (hD' : QuotientLineConnection.IsCompatible D')
    (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
    (x : X) (hx : x ∈ V) (v : TangentSpace (complexModel d) x) :
    (D'.form V e x - D.form V e x) (complexTangentToReal d x (Complex.I • v)) =
      Complex.I * (D'.form V e x - D.form V e x) (complexTangentToReal d x v) := by
  simp only [sub_apply, hD.1 V e x hx v, hD'.1 V e x hx v,
    mul_sub]



end ConnectionCalculus
end HolomorphicAnosov
