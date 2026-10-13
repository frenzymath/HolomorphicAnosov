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
/-- The antiholomorphic component of a compatible connection is the scalar antiholomorphic derivative in every holomorphic frame (Zhang, Definition 2.1 and (3)). -/
theorem compatible_dolbeault_in_frame
    {P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)}
    (D : QuotientLineConnection.Connection P)
    (hD : QuotientLineConnection.IsCompatible D)
    (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
    (s : (x : X) → QuotientLineConnection.Fibre P x)
    (x : X) (hx : x ∈ V) (v : TangentSpace (complexModel d) x) :
    (1 / 2 : ℂ) •
      (QuotientLineConnection.covariantDerivative D e s x hx
        (complexTangentToReal d x v) +
      Complex.I • QuotientLineConnection.covariantDerivative D e s x hx
        (complexTangentToReal d x (Complex.I • v))) =
      (e.coordinate x hx).symm ((1 / 2 : ℂ) *
        (QuotientLineConnection.realDifferential (e.coefficient s) x
          (complexTangentToReal d x v) +
        Complex.I * QuotientLineConnection.realDifferential (e.coefficient s) x
          (complexTangentToReal d x (Complex.I • v)))) := by
  apply (e.coordinate x hx).injective
  simp only [map_smul, map_add, QuotientLineConnection.covariantDerivative,
    LinearEquiv.apply_symm_apply, smul_eq_mul, hD.1 V e x hx v]
  ring_nf
  simp [Complex.I_sq]



end ConnectionCalculus
end HolomorphicAnosov
