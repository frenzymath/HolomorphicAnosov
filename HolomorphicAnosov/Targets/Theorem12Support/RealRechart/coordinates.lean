import HolomorphicAnosov.Geometry.ComplexModel
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! Real linear coordinates identify the complex model of dimension `d` with Euclidean space of real
dimension `2*d`. (Zhang, §3, p. 11) -/

namespace HolomorphicAnosov.Theorem12SupportW2

noncomputable section

/-- A real continuous linear equivalence from `ComplexModel d` to Euclidean space of dimension
`2*d`. (Zhang, §3, p. 11) -/
def coordinates (d : ℕ) : ComplexModel d ≃L[ℝ] EuclideanSpace ℝ (Fin (2*d)) :=
  ContinuousLinearEquiv.ofFinrankEq (by
    simp [ComplexModel, finrank_real_of_complex, Module.finrank_pi_fintype,
      finrank_euclideanSpace, Nat.mul_comm])

end

end HolomorphicAnosov.Theorem12SupportW2

