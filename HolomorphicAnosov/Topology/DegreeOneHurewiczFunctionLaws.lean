import HolomorphicAnosov.Topology.DegreeOneHurewiczFunction
import HolomorphicAnosov.Topology.DegreeOneHurewiczFunctionOne
import HolomorphicAnosov.Topology.DegreeOneHurewiczFunctionMul

noncomputable section
open CategoryTheory AlgebraicTopology
open scoped Simplicial
universe u
namespace HolomorphicAnosov.Topology

/-- The quotient function preserves the identity and multiplication additively.

Source and proof: Hatcher, p. 166. The constant loop bounds the constant
triangle, so its class is zero. For composable paths `a,b`, let `p=a.trans b`
and map the ordered triangle by `σ(t0,t1,t2)=p(t1/2+t2)`. Its three edges
are `b,p,a`, and its boundary is `b−p+a`. Hence the concatenation class
is the sum of the two path classes. Apply representative induction to
the fundamental-group quotient. Mathlib's multiplication concatenates
the representatives in the opposite order; commutativity of singular
H1 makes the resulting additive equality the displayed one. -/
theorem degreeOneHurewiczFunction_laws {X : Type u} [TopologicalSpace X] (x : X) :
    degreeOneHurewiczFunction x 1 = 0 ∧
    ∀ a b : FundamentalGroup X x,
      degreeOneHurewiczFunction x (a * b) =
        degreeOneHurewiczFunction x a + degreeOneHurewiczFunction x b := by
  exact ⟨degreeOneHurewiczFunction_one x, degreeOneHurewiczFunction_mul x⟩

end HolomorphicAnosov.Topology
