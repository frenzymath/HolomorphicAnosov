import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientLineConnection
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.FiniteLocalConnection

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
/-- The covariant derivative of a partition-of-unity sum of local connections is the weighted sum of
their local covariant derivatives. (Zhang, p.5, after (4)) -/
theorem covariantDerivative_finiteLocalConnection
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
          QuotientLineConnection.realDifferential (e.coefficient e'.sectionValue) x)
    (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
    (s : (x : X) → QuotientLineConnection.Fibre P x)
    (x : X) (hx : x ∈ V) (v : TangentSpace (realModel d) x) :
    QuotientLineConnection.covariantDerivative
      (finiteLocalConnection O ρ hρsupport hρsum B hB) e s x hx v =
      ∑ i, ρ i x • (e.coordinate x hx).symm
        (QuotientLineConnection.realDifferential (e.coefficient s) x v +
          e.coefficient s x * B i V e x v) := by
  apply (e.coordinate x hx).injective
  simp only [QuotientLineConnection.covariantDerivative, LinearEquiv.apply_symm_apply,
    map_sum, map_smul, finiteLocalConnection, sum_apply, smul_apply, smul_eq_mul]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hρsum x, one_mul, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring


end ConnectionCalculus
end HolomorphicAnosov
