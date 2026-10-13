import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientLineConnection
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

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
/-- The differential of a subbundle-preserving biholomorphism induces a complex-linear equivalence
of quotient tangent lines. (Zhang, (5)) -/
theorem quotient_differential_equivalence
    (P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x))
    {r : ℕ} (_hP : IsHolomorphicTangentSubbundle r P)
    (hline : IsQuotientTangentLine P) (f : Biholomorph d d X X)
    (hf : ∀ x (v : TangentSpace (complexModel d) x), v ∈ P x →
      mfderiv (complexModel d) (complexModel d) f x v ∈ P (f x)) :
    ∃ Q : (x : X) → QuotientLineConnection.Fibre P x ≃ₗ[ℂ]
        QuotientLineConnection.Fibre P (f x),
      ∀ x, (Q x).toLinearMap = QuotientLineConnection.quotientDerivative f hf x := by
  classical
  have he : f.toHomeomorph.toOpenPartialHomeomorph.MDifferentiable
      (complexModel d) (complexModel d) := by
    constructor
    · exact (f.contMDiff.mdifferentiable (by simp)).mdifferentiableOn
    · exact (f.symm.contMDiff.mdifferentiable (by simp)).mdifferentiableOn
  have hs (x : X) : Function.Surjective (QuotientLineConnection.quotientDerivative f hf x) := by
    intro w
    obtain ⟨v, rfl⟩ := (P (f x)).mkQ_surjective w
    obtain ⟨u, hu⟩ := he.mfderiv_surjective (x := x) (by trivial) v
    refine ⟨(P x).mkQ u, ?_⟩
    change (P (f x)).mkQ (mfderiv (complexModel d) (complexModel d) f x u) = _
    exact congrArg (P (f x)).mkQ hu
  have hb (x : X) : Function.Bijective (QuotientLineConnection.quotientDerivative f hf x) :=
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      ((hline x).trans (hline (f x)).symm)).mpr (hs x), hs x⟩
  refine ⟨fun x ↦ (LinearEquiv.ofBijective
    (QuotientLineConnection.quotientDerivative f hf x) (hb x)), ?_⟩
  intro x
  rfl



end ConnectionCalculus
end HolomorphicAnosov
