import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientLineConnection
import Mathlib.Analysis.Normed.Module.FiniteDimension
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.QuotientDifferentialEquivalence

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
/-- The differential of a subbundle-preserving biholomorphism induces a continuous complex-linear
equivalence of quotient tangent lines. (Zhang, (5)) -/
theorem quotient_differential_continuous_equivalence
    (P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x))
    {r : ℕ} (hP : IsHolomorphicTangentSubbundle r P)
    (hline : IsQuotientTangentLine P) (f : Biholomorph d d X X)
    (hf : ∀ x (v : TangentSpace (complexModel d) x), v ∈ P x →
      mfderiv (complexModel d) (complexModel d) f x v ∈ P (f x)) :
    ∃ Q : (x : X) → QuotientLineConnection.Fibre P x ≃L[ℂ]
        QuotientLineConnection.Fibre P (f x),
      ∀ x, (Q x).toLinearMap = QuotientLineConnection.quotientDerivative f hf x := by
  obtain ⟨Q, hQ⟩ := quotient_differential_equivalence P hP hline f hf
  have hclosed (x : X) : IsClosed (P x : Set (TangentSpace (complexModel d) x)) :=
    (P x).closed_of_finiteDimensional
  refine ⟨fun x ↦ (Q x).toContinuousLinearEquiv, ?_⟩
  intro x
  exact hQ x



end ConnectionCalculus
end HolomorphicAnosov
