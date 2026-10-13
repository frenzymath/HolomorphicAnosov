import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientLineConnection
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.FiniteLocalFormsGauge

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

/-- The connection obtained by summing local connection forms with subordinate weights that sum to
one. -/
def finiteLocalConnection
    {P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)}
    {ι : Type*} [Fintype ι] (O : ι → Opens X) (ρ : ι → X → ℂ)
    (hρsupport : ∀ i, Function.support (ρ i) ⊆ O i)
    (hρsum : ∀ x, ∑ i, ρ i x = 1)
    (B : ∀ _i : ι, ∀ V : Opens X, QuotientLineConnection.HolomorphicFrame P V →
      (x : X) → TangentSpace (realModel d) x →L[ℝ] ℂ)
    (hB : ∀ i (V W : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
      (e' : QuotientLineConnection.HolomorphicFrame P W) (x : X),
      x ∈ O i → x ∈ V → x ∈ W → B i W e' x = B i V e x +
        (e.coefficient e'.sectionValue x)⁻¹ •
          QuotientLineConnection.realDifferential (e.coefficient e'.sectionValue) x) :
    QuotientLineConnection.Connection P where
  form V e x := ∑ i, ρ i x • B i V e x
  gauge := finite_local_forms_gauge O ρ hρsupport hρsum B hB



end ConnectionCalculus
end HolomorphicAnosov
