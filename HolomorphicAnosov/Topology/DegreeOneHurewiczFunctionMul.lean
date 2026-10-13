import HolomorphicAnosov.Topology.DegreeOneHurewiczFunction
import HolomorphicAnosov.Topology.LoopSingularClassTrans

namespace HolomorphicAnosov.Topology
universe u
/-- The Hurewicz quotient function sends multiplication to addition.
Source: Hatcher, Algebraic Topology, Theorem 2A.1 p.166. Induct on both loop
representatives, use the concatenation triangle, and commute the two summands
because Mathlib's fundamental-group multiplication reverses path order. -/
theorem degreeOneHurewiczFunction_mul {X : Type u} [TopologicalSpace X] (x : X)
    (a b : FundamentalGroup X x) :
    degreeOneHurewiczFunction x (a * b) =
      degreeOneHurewiczFunction x a + degreeOneHurewiczFunction x b := by
  induction a using Quotient.inductionOn with
  | h α =>
    induction b using Quotient.inductionOn with
    | h β =>
      change loopSingularClass (β.trans α) = loopSingularClass α + loopSingularClass β
      rw [loopSingularClass_trans, add_comm]
end HolomorphicAnosov.Topology
